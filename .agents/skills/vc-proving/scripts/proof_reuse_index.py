#!/usr/bin/env python3
"""Build and apply conservative VC proof reuse indexes.

The index is keyed by generated witness Definition body hashes when available,
with statement hash as a fallback.  Reuse is gated by exact
common_case_formal_lib frozen-prefix and helper-suffix hashes; applying reuse
only writes a candidate manual and leaves compilation to the normal vc-proving
gate unless --compile-check is requested.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from manual_goal_utils import (
    block_has_admitted,
    check_rocq_file_with_deps,
    ensure_unique_lemma_names,
    goal_definition_hash_for_lemma,
    lemma_by_name,
    lemma_proof_block_hash,
    lemma_proof_script,
    lemma_statement_hash,
    lemma_statement_text,
    lemma_target_symbol,
    load_manifest,
    manifest_coq_project,
    parse_manual_file,
    proof_block_with_statement,
    stable_text_digest,
)

INDEX_SCHEMA_VERSION = 1
EMPTY_TEXT_HASH = stable_text_digest("")


def _context_hashes(
    lib_file: Path | None,
    frozen_prefix_end_line: int | None,
) -> dict[str, object]:
    if lib_file is None:
        return {
            "lib_file": None,
            "lib_frozen_prefix_end_line": frozen_prefix_end_line,
            "lib_frozen_prefix_hash": EMPTY_TEXT_HASH,
            "helper_suffix_hash": EMPTY_TEXT_HASH,
            "full_lib_hash": EMPTY_TEXT_HASH,
        }
    lib_file = lib_file.expanduser().resolve()
    text = lib_file.read_text(encoding="utf-8")
    if frozen_prefix_end_line is None:
        prefix = text
        suffix = ""
    else:
        lines = text.splitlines(keepends=True)
        prefix = "".join(lines[:frozen_prefix_end_line])
        suffix = "".join(lines[frozen_prefix_end_line:])
    return {
        "lib_file": str(lib_file),
        "lib_frozen_prefix_end_line": frozen_prefix_end_line,
        "lib_frozen_prefix_hash": stable_text_digest(prefix),
        "helper_suffix_hash": stable_text_digest(suffix),
        "full_lib_hash": stable_text_digest(text),
    }


def _manifest_default_lib(manifest: dict[str, object]) -> Path | None:
    for key in (
        "task_local_scratch_lib_file",
        "common_case_formal_lib_file",
        "lib_file",
    ):
        raw = manifest.get(key)
        if raw:
            return Path(str(raw)).expanduser().resolve()
    return None


def _resolve_context(
    *,
    lib_file: str | None,
    frozen_prefix_end_line: int | None,
    manifest: dict[str, object] | None = None,
) -> dict[str, object]:
    selected_lib = Path(lib_file).expanduser().resolve() if lib_file else None
    if selected_lib is None and manifest is not None:
        selected_lib = _manifest_default_lib(manifest)
    if frozen_prefix_end_line is None and manifest is not None:
        raw_line = manifest.get("lib_frozen_prefix_end_line")
        if isinstance(raw_line, int):
            frozen_prefix_end_line = raw_line
    return _context_hashes(selected_lib, frozen_prefix_end_line)


def _lemma_record(
    prelude: str,
    lemma: dict[str, object],
    *,
    source_file: Path,
    module_map: dict[str, str] | None,
    context: dict[str, object],
) -> dict[str, object]:
    goal_hashes = goal_definition_hash_for_lemma(
        prelude,
        lemma,
        source_file=source_file,
        module_map=module_map,
    )
    block = str(lemma["block"])
    return {
        "lemma_name": str(lemma["name"]),
        "target_symbol": lemma_target_symbol(lemma),
        "statement_header": str(lemma["header_line"]),
        "statement_text": lemma_statement_text(lemma),
        "statement_hash": lemma_statement_hash(lemma),
        "goal_body_hash": goal_hashes.get("goal_body_hash"),
        "goal_definition_module": goal_hashes.get("goal_definition_module"),
        "goal_definition_source": goal_hashes.get("goal_definition_source"),
        "proof_block_hash": lemma_proof_block_hash(lemma),
        "proof_block": block,
        "proof_script": lemma_proof_script(lemma),
        "has_admitted": block_has_admitted(block),
        "source_manual": str(source_file),
        "context": context,
    }


def build_index(
    manual_file: Path,
    *,
    lib_file: str | None,
    frozen_prefix_end_line: int | None,
) -> dict[str, object]:
    manual_file = manual_file.expanduser().resolve()
    prelude, lemmas = parse_manual_file(manual_file.read_text(encoding="utf-8"))
    ensure_unique_lemma_names(lemmas)
    context = _resolve_context(
        lib_file=lib_file,
        frozen_prefix_end_line=frozen_prefix_end_line,
    )
    entries: list[dict[str, object]] = []
    skipped: list[dict[str, object]] = []
    for lemma in lemmas:
        record = _lemma_record(
            prelude,
            lemma,
            source_file=manual_file,
            module_map=None,
            context=context,
        )
        if record["has_admitted"]:
            skipped.append({"lemma_name": record["lemma_name"], "reason": "contains_admitted"})
            continue
        if not record["proof_script"]:
            skipped.append({"lemma_name": record["lemma_name"], "reason": "missing_proof_script"})
            continue
        entries.append(record)
    return {
        "schema_version": INDEX_SCHEMA_VERSION,
        "kind": "vc_proof_reuse_index",
        "source_manual": str(manual_file),
        "context": context,
        "entry_count": len(entries),
        "skipped_count": len(skipped),
        "skipped": skipped,
        "entries": entries,
    }


def _entry_context(index: dict[str, object], entry: dict[str, object]) -> dict[str, object]:
    context = entry.get("context")
    if isinstance(context, dict):
        return context
    fallback = index.get("context")
    return fallback if isinstance(fallback, dict) else {}


def _context_matches(
    current_context: dict[str, object],
    index: dict[str, object],
    entry: dict[str, object],
) -> bool:
    entry_context = _entry_context(index, entry)
    return (
        current_context.get("lib_frozen_prefix_hash")
        == entry_context.get("lib_frozen_prefix_hash")
        and current_context.get("helper_suffix_hash")
        == entry_context.get("helper_suffix_hash")
    )


def _matching_entries(
    current: dict[str, object],
    index: dict[str, object],
) -> tuple[str | None, list[dict[str, object]]]:
    entries = [
        entry for entry in index.get("entries", [])
        if isinstance(entry, dict)
    ]
    goal_body_hash = current.get("goal_body_hash")
    if goal_body_hash:
        matches = [
            entry for entry in entries
            if entry.get("goal_body_hash") == goal_body_hash
        ]
        if matches:
            return "goal_body_hash", matches
    statement_hash = current.get("statement_hash")
    matches = [
        entry for entry in entries
        if entry.get("statement_hash") == statement_hash
    ]
    if matches:
        return "statement_hash", matches
    return None, []


def _reuse_note(status: str, match_key: str | None) -> str:
    if status == "reusable" and match_key == "goal_body_hash":
        return (
            "Exact generated witness body and lib/helper context hashes match; "
            "reuse the prior proof script, then require the normal compile gate."
        )
    if status == "reusable":
        return (
            "Generated witness body hash is unavailable, but statement and "
            "lib/helper context hashes match; treat as a compile-gated reuse candidate."
        )
    if status == "context_mismatch":
        return (
            "A proof for the same goal content exists, but lib/helper context "
            "changed; write an informal proof and only adapt the script after review."
        )
    if status == "already_solved":
        return "Current witness is already solved; no reuse action is needed."
    return "No exact reusable proof was found; write an informal proof before proving normally."


def _target_names(manifest: dict[str, object]) -> list[str]:
    raw = manifest.get("target_lemma_order") or manifest.get("lemma_order")
    if isinstance(raw, list):
        return [str(item) for item in raw]
    return [str(entry["name"]) for entry in manifest.get("lemmas", []) if isinstance(entry, dict)]


def analyze_manifest(
    manifest_path: Path,
    index: dict[str, object],
    *,
    lib_file: str | None,
    frozen_prefix_end_line: int | None,
) -> dict[str, object]:
    manifest = load_manifest(manifest_path)
    source_file = Path(str(manifest["source_file"])).expanduser().resolve()
    prelude, lemmas = parse_manual_file(source_file.read_text(encoding="utf-8"))
    ensure_unique_lemma_names(lemmas)
    by_name = lemma_by_name(lemmas)
    module_map_raw = manifest.get("case_dependency_module_map")
    module_map = (
        {str(key): str(value) for key, value in module_map_raw.items()}
        if isinstance(module_map_raw, dict)
        else None
    )
    context = _resolve_context(
        lib_file=lib_file,
        frozen_prefix_end_line=frozen_prefix_end_line,
        manifest=manifest,
    )

    goals: list[dict[str, object]] = []
    for name in _target_names(manifest):
        lemma = by_name.get(name)
        if lemma is None:
            goals.append(
                {
                    "lemma_name": name,
                    "status": "missing_current_lemma",
                    "reusable": False,
                    "informal_reuse_note": "Current manifest refers to a lemma absent from the source manual.",
                }
            )
            continue
        current = _lemma_record(
            prelude,
            lemma,
            source_file=source_file,
            module_map=module_map,
            context=context,
        )
        if not current["has_admitted"]:
            goals.append(
                {
                    **_public_current_fields(current),
                    "status": "already_solved",
                    "reusable": False,
                    "match_key": None,
                    "reused_from": None,
                    "informal_reuse_note": _reuse_note("already_solved", None),
                }
            )
            continue

        match_key, matches = _matching_entries(current, index)
        context_matches = [
            entry for entry in matches
            if _context_matches(context, index, entry)
        ]
        if context_matches:
            selected = _select_candidate(current, context_matches)
            status = "reusable"
            goals.append(
                {
                    **_public_current_fields(current),
                    "status": status,
                    "reusable": True,
                    "match_key": match_key,
                    "candidate_count": len(matches),
                    "reused_from": _public_entry_fields(selected),
                    "informal_reuse_note": _reuse_note(status, match_key),
                }
            )
        elif matches:
            status = "context_mismatch"
            goals.append(
                {
                    **_public_current_fields(current),
                    "status": status,
                    "reusable": False,
                    "match_key": match_key,
                    "candidate_count": len(matches),
                    "context_mismatch_count": len(matches),
                    "reused_from": None,
                    "informal_reuse_note": _reuse_note(status, match_key),
                }
            )
        else:
            status = "no_match"
            goals.append(
                {
                    **_public_current_fields(current),
                    "status": status,
                    "reusable": False,
                    "match_key": None,
                    "candidate_count": 0,
                    "reused_from": None,
                    "informal_reuse_note": _reuse_note(status, None),
                }
            )

    reusable_count = sum(1 for goal in goals if goal.get("reusable") is True)
    return {
        "schema_version": INDEX_SCHEMA_VERSION,
        "kind": "vc_proof_reuse_analysis",
        "manifest": str(manifest_path),
        "source_file": str(source_file),
        "index_source_manual": index.get("source_manual"),
        "context": context,
        "goal_count": len(goals),
        "reusable_count": reusable_count,
        "goals": goals,
    }


def _public_current_fields(current: dict[str, object]) -> dict[str, object]:
    return {
        "lemma_name": current["lemma_name"],
        "target_symbol": current.get("target_symbol"),
        "statement_hash": current.get("statement_hash"),
        "goal_body_hash": current.get("goal_body_hash"),
        "goal_definition_module": current.get("goal_definition_module"),
        "goal_definition_source": current.get("goal_definition_source"),
    }


def _public_entry_fields(entry: dict[str, object]) -> dict[str, object]:
    return {
        "lemma_name": entry.get("lemma_name"),
        "target_symbol": entry.get("target_symbol"),
        "source_manual": entry.get("source_manual"),
        "statement_hash": entry.get("statement_hash"),
        "goal_body_hash": entry.get("goal_body_hash"),
        "proof_block_hash": entry.get("proof_block_hash"),
    }


def _select_candidate(
    current: dict[str, object],
    candidates: list[dict[str, object]],
) -> dict[str, object]:
    current_target = current.get("target_symbol")
    current_name = current.get("lemma_name")
    for candidate in candidates:
        if candidate.get("target_symbol") == current_target:
            return candidate
    for candidate in candidates:
        if candidate.get("lemma_name") == current_name:
            return candidate
    return candidates[0]


def _replace_identifier(text: str, old: object, new: object) -> str:
    if not old or not new or old == new:
        return text
    old_text = str(old)
    new_text = str(new)
    ident = r"A-Za-z0-9_'"
    return re.sub(
        rf"(?<![{ident}]){re.escape(old_text)}(?![{ident}])",
        new_text,
        text,
    )


def _adapt_proof_script(
    entry: dict[str, object],
    current: dict[str, object],
) -> str:
    script = str(entry.get("proof_script") or lemma_proof_script(str(entry.get("proof_block", ""))))
    script = _replace_identifier(script, entry.get("lemma_name"), current.get("lemma_name"))
    script = _replace_identifier(script, entry.get("target_symbol"), current.get("target_symbol"))
    return script


def apply_reuse(
    manifest_path: Path,
    index: dict[str, object],
    *,
    output: Path,
    report_output: Path | None,
    lib_file: str | None,
    frozen_prefix_end_line: int | None,
    compile_check: bool,
) -> dict[str, object]:
    manifest = load_manifest(manifest_path)
    source_file = Path(str(manifest["source_file"])).expanduser().resolve()
    source_text = source_file.read_text(encoding="utf-8")
    prelude, lemmas = parse_manual_file(source_text)
    by_name = lemma_by_name(lemmas)
    analysis = analyze_manifest(
        manifest_path,
        index,
        lib_file=lib_file,
        frozen_prefix_end_line=frozen_prefix_end_line,
    )
    module_map_raw = manifest.get("case_dependency_module_map")
    module_map = (
        {str(key): str(value) for key, value in module_map_raw.items()}
        if isinstance(module_map_raw, dict)
        else None
    )
    reusable_by_name = {
        str(goal["lemma_name"]): goal
        for goal in analysis["goals"]
        if goal.get("reusable") is True
    }

    applied: list[dict[str, object]] = []
    new_blocks: list[str] = []
    for lemma in lemmas:
        name = str(lemma["name"])
        current_block = str(lemma["block"])
        goal = reusable_by_name.get(name)
        if goal is None:
            new_blocks.append(current_block)
            continue
        current = _lemma_record(
            prelude,
            lemma,
            source_file=source_file,
            module_map=module_map,
            context=analysis["context"],
        )
        match_key, matches = _matching_entries(current, index)
        context_matches = [
            entry for entry in matches
            if _context_matches(analysis["context"], index, entry)
        ]
        if not context_matches:
            new_blocks.append(current_block)
            continue
        selected = _select_candidate(current, context_matches)
        adapted_script = _adapt_proof_script(selected, current)
        adapted_block = proof_block_with_statement(
            lemma_statement_text(lemma) + adapted_script,
            lemma_statement_text(lemma),
        )
        new_blocks.append(adapted_block)
        applied.append(
            {
                "lemma_name": name,
                "match_key": match_key,
                "reused_from": _public_entry_fields(selected),
                "status": "reused_pending_compile",
            }
        )

    output = output.expanduser().resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(prelude + "".join(new_blocks), encoding="utf-8")

    if compile_check:
        project = manifest_coq_project(manifest)
        dep_files = [
            Path(str(path)).expanduser().resolve()
            for path in manifest.get("case_dependency_files", [])
        ]
        if project is None:
            check_rocq_file_with_deps(output, dep_files=dep_files)
        else:
            project_root, flags = project
            check_rocq_file_with_deps(
                output,
                dep_files=dep_files,
                project_root=project_root,
                flags=flags,
                force_deps=True,
            )
        for item in applied:
            item["status"] = "reused_compile_checked"

    report = {
        **analysis,
        "kind": "vc_proof_reuse_apply_report",
        "output_manual": str(output),
        "applied_count": len(applied),
        "applied": applied,
    }
    if report_output is not None:
        report_output = report_output.expanduser().resolve()
        report_output.parent.mkdir(parents=True, exist_ok=True)
        report_output.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return report


def _write_json(path: Path, data: dict[str, object]) -> None:
    path = path.expanduser().resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    build = subparsers.add_parser("build", help="Build a reuse index from a solved manual")
    build.add_argument("manual_file", help="Solved/verified proof manual")
    build.add_argument("--output", required=True, help="Destination reuse index JSON")
    build.add_argument("--lib", default=None, help="common_case_formal_lib or task_local_scratch_lib")
    build.add_argument("--lib-frozen-prefix-end-line", type=int, default=None)

    analyze = subparsers.add_parser("analyze", help="Analyze reusable proofs for a split manifest")
    analyze.add_argument("manifest", help="manifest.json from split_manual_goals.py")
    analyze.add_argument("--index", required=True, help="Reuse index JSON")
    analyze.add_argument("--output", required=True, help="Destination analysis JSON")
    analyze.add_argument("--lib", default=None, help="Current common_case_formal_lib/task_local_scratch_lib")
    analyze.add_argument("--lib-frozen-prefix-end-line", type=int, default=None)

    apply = subparsers.add_parser("apply", help="Write a candidate manual with reusable proofs")
    apply.add_argument("manifest", help="manifest.json from split_manual_goals.py")
    apply.add_argument("--index", required=True, help="Reuse index JSON")
    apply.add_argument("--output", required=True, help="Destination candidate manual")
    apply.add_argument("--report-output", default=None, help="Destination apply report JSON")
    apply.add_argument("--lib", default=None, help="Current common_case_formal_lib/task_local_scratch_lib")
    apply.add_argument("--lib-frozen-prefix-end-line", type=int, default=None)
    apply.add_argument("--compile-check", action="store_true", help="Run coqc gate on the candidate")

    args = parser.parse_args()
    if args.command == "build":
        index = build_index(
            Path(args.manual_file),
            lib_file=args.lib,
            frozen_prefix_end_line=args.lib_frozen_prefix_end_line,
        )
        _write_json(Path(args.output), index)
        print(f"Reuse index written to {Path(args.output).expanduser().resolve()}")
        print(f"Indexed solved proofs: {index['entry_count']}")
        return 0

    index = json.loads(Path(args.index).expanduser().resolve().read_text(encoding="utf-8"))
    if args.command == "analyze":
        report = analyze_manifest(
            Path(args.manifest).expanduser().resolve(),
            index,
            lib_file=args.lib,
            frozen_prefix_end_line=args.lib_frozen_prefix_end_line,
        )
        _write_json(Path(args.output), report)
        print(f"Reuse analysis written to {Path(args.output).expanduser().resolve()}")
        print(f"Reusable goals: {report['reusable_count']} / {report['goal_count']}")
        return 0

    if args.command == "apply":
        report = apply_reuse(
            Path(args.manifest).expanduser().resolve(),
            index,
            output=Path(args.output),
            report_output=Path(args.report_output) if args.report_output else None,
            lib_file=args.lib,
            frozen_prefix_end_line=args.lib_frozen_prefix_end_line,
            compile_check=args.compile_check,
        )
        print(f"Candidate manual written to {report['output_manual']}")
        print(f"Applied reusable proofs: {report['applied_count']}")
        return 0

    raise AssertionError(f"unhandled command: {args.command}")


if __name__ == "__main__":
    raise SystemExit(main())
