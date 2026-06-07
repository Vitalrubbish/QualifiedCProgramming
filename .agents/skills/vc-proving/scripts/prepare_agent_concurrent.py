#!/usr/bin/env python3
"""Prepare per-group work directories for concurrent proof-group solving.

Partitions goals using a vc-checking proof group plan when available, otherwise
falls back to lexicographic sort + chunk. It creates one ``group_NN/`` work
subdirectory per group, and persists ``groups_manifest.json`` at the base work dir so the run phase
(``run_agent_concurrent.py --skip-prepare``) can pick them up.

This is the required vc-proving preparation entrypoint.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from agent_runner import (
    WORKER_EXECUTION_MODES,
    normalize_worker_execution_mode,
    worker_mode_uses_rocq_mcp,
)
from group_goals import (
    DEFAULT_CHUNK_SIZE,
    fallback_group_entries,
    group_entries_from_plan,
    load_group_plan,
)
from manual_goal_utils import (
    ROCQ_MEMORY_LIMIT_BYTES,
    absolutize_coq_load_paths,
    compile_rocq_files,
    filter_shadowed_simplec_ee_flags,
    load_manifest,
    prepare_simplec_case_dependencies,
    resolve_coqc_flags,
    sorted_dependency_files,
    stale_vo_files,
    write_coqproject,
)
from prepare_group_workdir import prepare_group

GROUPS_MANIFEST_NAME = "groups_manifest.json"

EMBEDDED_GROUP_PLAN_KEYS = (
    "witness_group_plan",
    "proof_group_plan",
)

TASK_LOCAL_MODULE_KEYS = (
    "task_local_scratch_lib_module",
    "task_local_logical_module",
    "case_dependency_task_local_scratch_lib_module",
)


def _numeric_meta(value: object) -> float | None:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    try:
        return float(str(value).strip())
    except ValueError:
        return None


def _list_len(value: object) -> int:
    if isinstance(value, list):
        return len(value)
    if value:
        return 1
    return 0


def estimate_group_difficulty(group_entry: dict) -> float:
    """Return a stable scheduling score; larger groups run earlier."""
    goals = group_entry.get("goals", [])
    score = float(len(goals))
    for key in (
        "estimated_difficulty",
        "difficulty_score",
        "estimated_seconds",
        "expected_seconds",
    ):
        raw = _numeric_meta(group_entry.get(key))
        if raw is not None:
            score += raw
    difficulty = str(group_entry.get("difficulty", "")).strip().lower()
    score += {
        "very_high": 8.0,
        "high": 5.0,
        "medium": 2.0,
        "low": 0.5,
    }.get(difficulty, 0.0)
    confidence = str(group_entry.get("grouping_confidence", "")).strip().lower()
    if confidence in {"low", "weak"}:
        score += 2.0
    score += 0.5 * _list_len(group_entry.get("shared_helper_candidates"))
    score += 0.25 * _list_len(group_entry.get("proving_hints"))
    return score


def _write_preflight_report(base_work_dir: Path, report: dict) -> Path:
    path = base_work_dir / "vc_proving_preflight.json"
    path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return path


def _manifest_task_local_logical_module(manifest: dict) -> str | None:
    for key in TASK_LOCAL_MODULE_KEYS:
        raw = manifest.get(key)
        if raw:
            return str(raw)
    return None


def _pattern_references_by_goal(manifest: dict) -> dict[str, dict]:
    report = manifest.get("partial_proof_packet_pattern_reference")
    if not isinstance(report, dict):
        return {}
    proof_refs = report.get("proof_references", [])
    helper_import_refs = report.get("helper_import_references", [])
    helper_refs = report.get("helper_references", [])
    context_mismatches = report.get("context_mismatches", [])
    by_goal: dict[str, dict] = {}
    for entry in report.get("goals", []):
        if not isinstance(entry, dict):
            continue
        name = entry.get("lemma_name")
        if name:
            enriched = dict(entry)
            enriched.setdefault("packet_proof_reference_pool", proof_refs)
            enriched.setdefault("packet_helper_import_references", helper_import_refs)
            enriched.setdefault("packet_helper_references", helper_refs)
            enriched.setdefault("packet_context_mismatches", context_mismatches)
            by_goal[str(name)] = enriched
    return by_goal


def effective_use_rocq_mcp(requested: bool) -> bool:
    """Windows proof runs use only coqc/coqtop, regardless of CLI opt-in."""
    return False if os.name == "nt" else bool(requested)


def prepare_groups(
    manifest_path: Path,
    lib_file: Path,
    chunk_size: int = DEFAULT_CHUNK_SIZE,
    use_rocq_mcp: bool = True,
    worker_execution_mode: str | None = None,
    group_plan_path: Path | None = None,
    task_local_logical_module: str | None = None,
) -> list[dict]:
    """Partition goals into groups and prepare a work dir for each.

    Writes ``<base_work_dir>/groups_manifest.json`` so the run phase can be
    invoked separately. Returns the list of group manifest dicts.
    """
    manifest = load_manifest(manifest_path)
    task_local_logical_module = (
        task_local_logical_module or _manifest_task_local_logical_module(manifest)
    )
    worker_execution_mode = normalize_worker_execution_mode(
        worker_execution_mode or manifest.get("worker_execution_mode"),
        use_rocq_mcp=use_rocq_mcp,
    )
    use_rocq_mcp = worker_mode_uses_rocq_mcp(worker_execution_mode)
    source_file = Path(str(manifest["source_file"])).resolve()
    lemmas = manifest["lemmas"]
    group_plan_source = "sort_chunk_fallback"
    group_plan_data = None
    if group_plan_path is not None:
        group_plan_path = group_plan_path.resolve()
        group_plan_data = load_group_plan(group_plan_path)
        group_plan_source = f"group_plan_file:{group_plan_path}"
    else:
        for key in EMBEDDED_GROUP_PLAN_KEYS:
            if manifest.get(key) is not None:
                group_plan_data = manifest[key]
                group_plan_source = f"manifest:{key}"
                break

    if group_plan_data is not None:
        group_entries = group_entries_from_plan(lemmas, group_plan_data)
        print(
            f"Grouped {len(lemmas)} goals into {len(group_entries)} proof group(s) "
            f"from {group_plan_source}"
        )
    else:
        group_entries = fallback_group_entries(lemmas, chunk_size=chunk_size)
        print(
            f"Grouped {len(lemmas)} goals into {len(group_entries)} fallback group(s) "
            f"(chunk_size={chunk_size})"
        )

    pattern_references = _pattern_references_by_goal(manifest)
    if pattern_references:
        for group_entry in group_entries:
            refs = [
                pattern_references[str(goal["name"])]
                for goal in group_entry.get("goals", [])
                if str(goal.get("name")) in pattern_references
            ]
            if refs:
                group_entry["proof_reuse_pattern_references"] = refs

    base_work_dir = Path(str(manifest["work_dir"])).resolve()
    coqproject_root, coqc_flags = resolve_coqc_flags(source_file)
    preflight_report: dict[str, object] = {
        "status": "started",
        "source_file": str(source_file),
        "task_local_scratch_lib_file": str(lib_file),
        "worker_execution_mode": worker_execution_mode,
        "use_rocq_mcp": use_rocq_mcp,
        "rocq_memory_limit_bytes": ROCQ_MEMORY_LIMIT_BYTES,
        "group_plan_source": group_plan_source,
        "group_count": len(group_entries),
        "goal_count": len(lemmas),
        "group_plan_covered_goal_count": sum(
            len(entry.get("goals", [])) for entry in group_entries
        ),
    }
    case_deps = prepare_simplec_case_dependencies(
        work_dir=base_work_dir,
        source_file=source_file,
        lib_file=lib_file,
        coqproject_root=coqproject_root,
        coqc_flags=coqc_flags,
        task_local_logical_module=task_local_logical_module,
    )
    preflight_report.update({
        "case_dependency_modules": case_deps["modules"],
        "case_dependency_files": case_deps["files"],
        "case_dependency_task_local_scratch_lib_module": case_deps[
            "task_local_scratch_lib_module"
        ],
        "stale_vo_before_compile": stale_vo_files(case_deps["files"]),
    })
    selected_task_local_logical_module = case_deps.get("task_local_scratch_lib_module")
    filtered_repo_flags = filter_shadowed_simplec_ee_flags(
        absolutize_coq_load_paths(coqproject_root, coqc_flags),
        enable_overlay=bool(case_deps["modules"]),
    )
    base_coqc_flags = list(case_deps["flags"]) + filtered_repo_flags
    write_coqproject(base_work_dir, base_coqc_flags, readonly=True)
    try:
        compile_rocq_files(
            base_work_dir,
            base_coqc_flags,
            sorted_dependency_files([str(path) for path in case_deps["files"]]),
        )
        preflight_report["overlay_compile_status"] = "passed"
        preflight_report["stale_vo_after_compile"] = stale_vo_files(case_deps["files"])
        preflight_report["status"] = "passed"
    except SystemExit as exc:
        preflight_report["overlay_compile_status"] = "failed"
        preflight_report["status"] = "failed"
        preflight_report["failure_exit_code"] = exc.code
        _write_preflight_report(base_work_dir, preflight_report)
        raise
    preflight_path = _write_preflight_report(base_work_dir, preflight_report)
    print(f"Preflight report written to {preflight_path}")

    print("\n=== Preparing group work directories ===")
    group_manifests: list[dict] = []
    canonical_groups: list[dict] = []
    for i, group_entry in enumerate(group_entries):
        group = group_entry["goals"]
        group_work_dir = base_work_dir / f"group_{i:02d}"
        gm = prepare_group(
            work_dir=group_work_dir,
            group_goals=group,
            lib_file=lib_file,
            source_file=source_file,
            use_rocq_mcp=use_rocq_mcp,
            group_meta=group_entry,
            worker_execution_mode=worker_execution_mode,
            task_local_logical_module=(
                str(selected_task_local_logical_module)
                if selected_task_local_logical_module else None
            ),
            case_deps_seed=case_deps,
        )
        gm["estimated_difficulty_score"] = estimate_group_difficulty(group_entry)
        group_manifests.append(gm)
        names = ", ".join(g["name"] for g in group)
        print(f"  Group {i} ({len(group)} goals, id={gm['proof_group_id']}): {names}")
        canonical_groups.append({
            "proof_group_id": gm["proof_group_id"],
            "members": [str(g["name"]) for g in group],
            "representative_witness": gm.get("representative_witness"),
            "natural_language_proof_pattern": gm.get("natural_language_proof_pattern"),
            "shared_helper_candidates": gm.get("shared_helper_candidates"),
            "proving_hints": gm.get("proving_hints"),
            "grouping_confidence": gm.get("grouping_confidence"),
            "difficulty": gm.get("difficulty"),
            "estimated_difficulty": gm.get("estimated_difficulty"),
            "difficulty_score": gm.get("difficulty_score"),
            "estimated_seconds": gm.get("estimated_seconds"),
            "expected_seconds": gm.get("expected_seconds"),
            "grouping_source": gm.get("grouping_source"),
            "estimated_difficulty_score": gm["estimated_difficulty_score"],
        })

    groups_manifest_path = base_work_dir / GROUPS_MANIFEST_NAME
    groups_manifest_path.write_text(
        json.dumps(group_manifests, indent=2), encoding="utf-8"
    )
    print(f"\nGroup manifests written to {groups_manifest_path}")

    # Update top-level manifest so validate_and_merge.py and other downstream
    # tools can find task_local_scratch_lib and coqc_flags.
    manifest["coqproject_root"] = str(base_work_dir)
    manifest["coqc_flags"] = base_coqc_flags
    manifest["base_coqproject_root"] = str(coqproject_root)
    manifest["base_coqc_flags"] = coqc_flags
    manifest["case_dependency_root"] = case_deps["root"]
    manifest["case_dependency_files"] = case_deps["files"]
    manifest["case_dependency_modules"] = case_deps["modules"]
    manifest["case_dependency_module_map"] = case_deps["module_map"]
    manifest["case_dependency_task_local_scratch_lib_module"] = case_deps[
        "task_local_scratch_lib_module"
    ]
    manifest["case_dependency_task_local_scratch_lib_modules"] = case_deps[
        "task_local_scratch_lib_modules"
    ]
    manifest["case_dependency_task_local_scratch_lib_files"] = case_deps[
        "task_local_scratch_lib_files"
    ]
    manifest["dependency_mode"] = "worker_case_dependency_overlay"
    manifest["task_local_scratch_lib_file"] = str(lib_file)
    manifest["task_local_scratch_lib_module"] = case_deps[
        "task_local_scratch_lib_module"
    ]
    manifest["grouping_source"] = group_plan_source
    manifest["proof_groups"] = canonical_groups
    manifest["worker_execution_mode"] = worker_execution_mode
    manifest["use_rocq_mcp"] = use_rocq_mcp
    manifest["vc_proving_preflight_report"] = str(preflight_path)
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    return group_manifests


def load_groups_manifest(base_work_dir: Path) -> list[dict]:
    """Load the persisted list of group manifests written by ``prepare_groups``."""
    path = base_work_dir / GROUPS_MANIFEST_NAME
    if not path.is_file():
        raise SystemExit(
            f"groups_manifest not found at {path}. "
            f"Run prepare_agent_concurrent.py first."
        )
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise SystemExit(f"{path} is not a JSON array")
    return data


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare per-group work directories for concurrent refinement VC solving."
    )
    parser.add_argument("manifest", help="Path to manifest.json (after split_manual_goals.py)")
    parser.add_argument("task_local_scratch_lib", help="Path to task_local_scratch_lib")
    parser.add_argument("--chunk-size", type=int, default=DEFAULT_CHUNK_SIZE,
                        help=f"Fallback goal group size (default: {DEFAULT_CHUNK_SIZE})")
    parser.add_argument("--group-plan", default=None,
                        help="JSON group plan produced by vc-checking. If set, it must "
                             "cover exactly the current manifest witness set.")
    parser.add_argument("--task-local-module", default=None,
                        help="Explicit canonical logical module that maps to "
                             "task_local_scratch_lib, e.g. "
                             "SimpleC.EE.LLM_bench.Algorithms.foo.foo_lib.")
    parser.add_argument("--worker-execution-mode", default=None,
                        choices=sorted(WORKER_EXECUTION_MODES),
                        help="Explicit worker tooling mode. Overrides --no-rocq-mcp "
                             "and any manifest worker_execution_mode.")
    parser.add_argument("--no-rocq-mcp", action="store_true",
                        help="Deprecated no-op: coqc/coqtop mode is the default.")
    args = parser.parse_args()

    manifest_path = Path(args.manifest).expanduser().resolve()
    lib_file = Path(args.task_local_scratch_lib).expanduser().resolve()
    if not lib_file.is_file():
        raise SystemExit(f"task_local_scratch_lib file not found: {lib_file}")

    prepare_groups(
        manifest_path=manifest_path,
        lib_file=lib_file,
        chunk_size=args.chunk_size,
        use_rocq_mcp=not args.no_rocq_mcp,
        worker_execution_mode=args.worker_execution_mode,
        group_plan_path=Path(args.group_plan).expanduser() if args.group_plan else None,
        task_local_logical_module=args.task_local_module,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
