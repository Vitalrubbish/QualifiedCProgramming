#!/usr/bin/env python3
"""Prepare a work directory for a proof group.

One agent per group sees all assigned goals at once and reuses the proof
pattern supplied by vc-checking when available.
"""
from __future__ import annotations

import argparse
import json
import shutil
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from manual_goal_utils import (
    all_vo_files_current,
    absolutize_coq_load_paths,
    build_compile_cmd,
    compile_rocq_files,
    copy_tutorial,
    filter_shadowed_simplec_ee_flags,
    generate_rocq_mcp_config,
    load_manifest,
    make_readonly,
    make_user_writable,
    parse_manual_file,
    prepare_simplec_case_dependencies,
    resolve_coqc_flags,
    sorted_dependency_files,
    write_coqproject,
    write_rocq_memory_wrappers,
)
from agent_runner import (
    WORKER_EXECUTION_MODES,
    normalize_worker_execution_mode,
    worker_mode_uses_rocq_mcp,
)

SKILL_DIR = SCRIPT_DIR.parent
TUTORIAL_SRC = SKILL_DIR / "docs" / "refinement-vc-tutorial"

TOOLING_ROCQ_MCP = (
    "- Use `rocq-mcp` to develop proofs interactively: step through tactics, "
    "inspect proof state, iterate. A worker-local `.codex/config.toml` is present; "
    "include rocq-mcp proof-state steps in `proof_strategy_report.json`.\n"
    "- If `rocq-mcp` fails to start or a tool call fails in this worker "
    "(for example transport/backend errors, timeout, missing binary, or "
    "`request_user_input is not supported in exec mode`), record the exact "
    "failure in `proof_strategy_report.json` and continue with the generated "
    "`coqc` command. MCP failure alone is not a proof blocker.\n"
    "- In `coqc` fallback, inspect proof state by temporarily inserting Rocq "
    "commands such as `Show.`, `Show n.`, `Show Existentials.`, `Search`, "
    "`Check`, `Print`, or `About`, then re-running `coqc`/`coqtop`. Remove "
    "debug commands before reporting a goal solved."
)

TOOLING_COQC_ONLY = (
    "- Develop proofs by editing the goal file directly and using `coqc` to check.\n"
    "- To inspect intermediate proof state, insert Rocq commands like `Show.`, "
    "`Show n.`, or `Show Existentials.` and re-run `coqc`. Remove these debug commands "
    "before declaring the proof complete.\n"
    "- Use `Search <pattern>.`, `Check <name>.`, `Print <name>.`, and `About <name>.` "
    "to discover lemmas, definitions, and types. Wrap them in a separate scratch lemma "
    "or remove them after use so they don't appear in the final proof."
)

AGENTS_MD_GROUP = """\
# Refinement VC Solver - Proof Group Worker

You are solving the assigned Rocq proof obligation(s) in an isolated worker copy of the proof manual.
Each run assigns one proof group to this worker. The focused goal file(s) are listed below, but your witness-proof edits go into `{worker_manual_name}` and reusable helper lemmas go into worker_helper_scratch_lib `{worker_helper_scratch_lib_name}`.

## Workflow
1. **Inspect the proof group.** Read the assigned `goal_*.v` file(s) and the Proof Group Notes, then edit the matching witness proofs in `{worker_manual_name}`.
2. **Reuse within the group.** Start from the representative or common proof pattern when one is provided. Adapt carefully; do not blindly copy variable names.
{pattern_reference_section}
3. **Record an informal proof/reuse decision.** For every assigned goal, write a brief informal proof and whether the proof script can be reused, adapted, or must be written fresh in `proof_strategy_report.json`.
4. **Put helper lemmas in worker_helper_scratch_lib.** If a reusable fact is needed, add a proved top-level lemma to `{worker_helper_scratch_lib_name}`, not to the manual and not to common_case_formal_lib.
5. **Compile worker_helper_scratch_lib and manual together.** The worker manual already imports `{worker_helper_module}`. Every solved report must be backed by a successful compile of worker_helper_scratch_lib followed by the manual.
6. **Keep proving until done.** Continue until every assigned goal is solved, the process timeout stops you, or you identify a concrete proof-obligation defect.
7. **No difficulty-based admits.** Do not intentionally leave a goal `Admitted.` because it is difficult, long, or lacks a direct helper lemma.

## Current Generated VC Shape
- New `symexec` output may define a final manual VC as `original VC \\/ VC after strategies`. The final checked obligation is still the plain witness lemma, usually `proof_of_<vc_name> : <vc_name>`.
- `pre_process` already selects and reduces the original-VC branch for this disjunctive shape. Do not write an extra `left;` before `pre_process`.
- `aggressive_pre_process` already selects and reduces the strategy-processed branch for this disjunctive shape. Do not write an extra `right;` before `aggressive_pre_process`.
- Pure propositions from the precondition may now appear as named hypotheses such as `PreH1`, `PreH2`.
- Lemmas named like `<vc_name>_split_goal_*` or `<vc_name>_split_goal_spatial` are diagnostic split goals. They may be printed as `Proof. Abort.` and are not final `VC_Correct` obligations. Do not report them as unsolved witness obligations.
- Preserve this case/folder's existing proof style; use these notes only to adapt to the new printer shape.

## Rules
- Read `tutorial/refinement_proof_tutorial.md` first for the overall proof workflow. It links to `tutorial/spatial_proof_tutorial.md` (for spatial entailments) and `tutorial/safeExec_proof_tutorial.md` (for the execution side) — consult them as needed.
- Edit only `{worker_manual_name}`, `{worker_helper_scratch_lib_name}`, `proof_report.json`, and `proof_strategy_report.json`.
- Do not change any assigned witness lemma statement. Preserve the prelude/imports exactly as generated.
- You may add top-level helper lemmas in `{worker_helper_scratch_lib_name}` when needed. Helper lemmas must be proved and must not use `Admitted.`.
- If a helper lemma proof needs an extra library, add a minimal `Require Import ... .` or `From ... Require Import ... .` line in `{worker_helper_scratch_lib_name}` before the helper lemma. Do not add standalone `Import`, `Require Export`, or generated case imports under `SimpleC.EE.*`; the merge pipeline only migrates audited helper-suffix `Require Import` lines.
- Do not add top-level `Definition`, `Fixpoint`, `CoFixpoint`, `Inductive`, `CoInductive`, `Notation`, or `Axiom`.
- Prefer short, tutorial-aligned proofs over clever proofs.
- **Do NOT modify common_case_formal_lib, task_local_scratch_lib `{task_local_scratch_lib_name}`, `{goal_name}`, or the read-only `case_deps/` overlay.** They are compile-only dependencies resolved through the worker `_CoqProject` loadpath. The overlay exposes the current task_local_scratch_lib under the canonical `<case>_lib` logical module name for compilation only. If a proof needs an auxiliary fact, add a proved helper lemma in worker_helper_scratch_lib `{worker_helper_scratch_lib_name}`; the merge pipeline will migrate proved helper lemmas into task_local_scratch_lib after validation.
{tooling_instructions}
- After each goal, verify the worker manual compiles by running:
  ```
  {compile_cmd}
  ```
  Fix compile errors before moving on. Update `proof_report.json` only after `{worker_manual_name}` compiles and the assigned goal no longer contains `Admitted.`.
- `coqc` and `coqtop` in this worker are wrapped with a hard 4 GiB memory kill guard. Use the bare command names so the wrappers stay in effect.
- Your writable and inspectable workspace is this group directory only.
- You may run the generated `coqc` command even though it contains absolute Rocq `-Q`/`-R`/`-I` dependency paths. Those paths are compile-only dependencies.
- Do NOT inspect compile-only dependency paths with shell tools or editor reads. In particular, do not run `cat`, `sed`, `rg`, `grep`, `find`, `ls`, `head`, `tail`, or similar commands on:
{dependency_path_list}
- Allowed reads are limited to `{worker_manual_name}`, `{worker_helper_scratch_lib_name}`, assigned `goal_*.v` files in this group, `AGENTS.md`, `tutorial/*.md`, `_CoqProject`, and optional proof reuse reference `{pattern_reference_file}` if present.
- Allowed uses of dependency paths are `coqc`/`coqtop` compilation or proof-state checking for the current assigned goal only, not browsing unrelated modules or source files.
- Forbidden examples:
  - `rg "lemma_name" /path/to/some_outside_directory/foo.v`
  - `sed -n '1,200p' /path/to/some_outside_directory/foo.v`
  - `find .. -name '*.v'`
  - `cat ../group_01/{worker_manual_name}`
- If you need to understand an external definition, lemma, or notation, use Rocq commands such as `Print`, `Search`, `Check`, and `About` inside `coqtop` or a temporary local scratch `.v` file for the current assigned goal. Do not inspect the external source file with shell/editor reads.
- Do NOT modify anything in `tutorial/`.
- Keep proving until every assigned goal is solved or the process timeout stops you. Do not intentionally admit a goal because the proof is hard, long, or no direct theorem was found.
- You may stop early on an unsolved goal only when you find a concrete proof-obligation defect showing the goal is not provable as stated.
- A proof-obligation defect must include specific Rocq evidence: the reduced goal, contradictory hypotheses, a missing necessary precondition, or a minimal counterexample argument. General statements such as "needs a helper lemma", "no direct theorem found", "large composition proof", or "remaining bound not exposed" are not valid blockers.
- If you find a concrete proof-obligation defect, keep your best partial proof in `{worker_manual_name}` and end the assigned goal with `Admitted.` so the file still compiles. Then write a blocker report explaining the exact defect and the last meaningful proof state reached.

## Reports
After each goal, append an entry to `proof_report.json`:
- Solved: `{{"goal": "<lemma_name>", "status": "solved", "elapsed_seconds": <number>, "coqc_seconds": <number or null>, "slow_steps": ["<optional tactic/compile bottleneck>"]}}`
- Unsolved: `{{"goal": "<lemma_name>", "status": "admitted", "elapsed_seconds": <number>, "coqc_seconds": <number or null>, "report": "<concise explanation of what went wrong and what was tried>"}}`

The file is a JSON array of all entries: `[{{"goal": "...", "status": "solved", "elapsed_seconds": 0.0, "coqc_seconds": null}}, ...]`.
If exact timing is unavailable, use `null` and explain the timing gap in `proof_strategy_report.json`.

When you finish the group, also write `proof_strategy_report.json` describing your clustering and reuse decisions:
```json
{{
  "clusters": [
    {{"name": "A",
      "representative": "<lemma_name_of_representative>",
      "members": ["<lemma_name>", "..."]}}
  ],
  "reuse_decisions": [
    {{"goal": "<lemma_name>",
      "informal_proof": "<one or two sentences>",
      "reuse_decision": "reuse|adapt|fresh|blocked",
      "reason": "<hash match, proof pattern match, context mismatch, or no prior match>"}}
  ],
  "notes": "<short summary of the helper/witness proof strategy>",
  "timing": {{
    "elapsed_seconds": <number or null>,
    "slowest_goals": ["<lemma_name>", "..."],
    "major_time_sinks": ["<proof search, coqc, rocq-mcp startup, etc.>"],
    "timing_gaps": ["<unknown timing and why>"]
  }}
}}
```

## Assigned Goals
{goal_list}

## Proof Group Notes
{proof_group_notes}

## Files
- `{worker_manual_name}` - worker-local full proof manual (editable)
- `{worker_helper_scratch_lib_name}` - worker_helper_scratch_lib (editable)
- `goal_*.v` - assigned goal files for focused reading (read-only)
- `{pattern_reference_file}` - optional JSON proof-pattern references from an earlier checkpoint (read-only if present)
- `tutorial/refinement_proof_tutorial.md` - main proof tutorial (read-only)
- `tutorial/spatial_proof_tutorial.md` - spatial entailment tactics (read-only)
- `tutorial/safeExec_proof_tutorial.md` - execution-side tactics (read-only)
"""

WORKER_HELPER_MODULE_ROOT = "VCWorker"
WORKER_HELPER_DIR_NAME = "worker_helper"
WORKER_HELPER_SCRATCH_LIB_NAME = "worker_helper_scratch_lib.v"


def _case_deps_from_seed(work_dir: Path, seed: dict | None) -> dict[str, object] | None:
    """Copy a prepared base case_deps overlay into a group workdir.

    The prepare phase builds and compiles a canonical overlay once at the base
    workdir.  Group workers need their own local `case_deps/` tree so their
    `_CoqProject` remains self-contained, but they do not need to rediscover
    or recopy the official generated sources.
    """
    if not seed or not seed.get("root"):
        return None
    seed_root = Path(str(seed["root"])).resolve()
    if not seed_root.is_dir():
        return None

    dep_root = work_dir / "case_deps"
    if dep_root.exists():
        shutil.rmtree(dep_root)
    shutil.copytree(seed_root, dep_root, copy_function=shutil.copy2)

    def remap_path(raw: object) -> str:
        path = Path(str(raw)).resolve()
        rel = path.relative_to(seed_root)
        return str((dep_root / rel).resolve())

    remapped_flags: list[str] = []
    flags = [str(flag) for flag in seed.get("flags", [])]
    i = 0
    while i < len(flags):
        flag = flags[i]
        if flag in {"-Q", "-R"} and i + 2 < len(flags):
            path = Path(flags[i + 1]).resolve()
            try:
                rel = path.relative_to(seed_root)
                remapped_flags.extend([flag, str((dep_root / rel).resolve()), flags[i + 2]])
            except ValueError:
                remapped_flags.extend([flag, flags[i + 1], flags[i + 2]])
            i += 3
            continue
        remapped_flags.append(flag)
        i += 1

    module_map = {
        str(logical): remap_path(path)
        for logical, path in dict(seed.get("module_map", {})).items()
    }
    files = [remap_path(path) for path in seed.get("files", [])]
    task_local_files = [
        remap_path(path)
        for path in seed.get("task_local_scratch_lib_files", [])
    ]
    return {
        "root": str(dep_root.resolve()),
        "flags": remapped_flags,
        "files": files,
        "modules": list(seed.get("modules", [])),
        "module_map": module_map,
        "task_local_scratch_lib_module": seed.get("task_local_scratch_lib_module"),
        "task_local_scratch_lib_modules": list(seed.get("task_local_scratch_lib_modules", [])),
        "task_local_scratch_lib_files": task_local_files,
        "cache_mode": "copied_from_base_overlay",
    }


def _insert_helper_import(source_text: str, helper_module: str) -> str:
    prelude, lemmas = parse_manual_file(source_text)
    lemma_text = "".join(str(lemma["block"]) for lemma in lemmas)
    import_line = f"From {WORKER_HELPER_MODULE_ROOT} Require Import {helper_module}.\n"
    if import_line in prelude:
        return source_text
    return prelude + import_line + lemma_text


def _write_worker_helper_scratch_lib(work_dir: Path, source_file: Path) -> Path:
    source_text = source_file.read_text(encoding="utf-8")
    prelude, _lemmas = parse_manual_file(source_text)
    helper_dir = work_dir / WORKER_HELPER_DIR_NAME
    helper_dir.mkdir(parents=True, exist_ok=True)
    helper_lib = helper_dir / WORKER_HELPER_SCRATCH_LIB_NAME
    make_user_writable(helper_lib)
    helper_lib.write_text(
        prelude.rstrip() + "\n\n(* worker_helper_scratch_lib helper lemmas go below. *)\n",
        encoding="utf-8",
    )
    return helper_lib


def _format_list_field(value: object) -> str:
    if value is None:
        return "n/a"
    if isinstance(value, list):
        return ", ".join(str(item) for item in value) if value else "empty"
    return str(value)


def render_proof_group_notes(group_meta: dict | None) -> str:
    """Render vc-checking proof-pattern metadata for the worker prompt."""
    if not group_meta:
        return "- grouping_source: sort_chunk_fallback\n- proof_pattern: not provided"
    lines = [
        f"- proof_group_id: {group_meta.get('proof_group_id', 'n/a')}",
        f"- grouping_source: {group_meta.get('grouping_source', 'n/a')}",
        f"- representative_witness: {group_meta.get('representative_witness', 'n/a')}",
        "- natural_language_proof_pattern: "
        + _format_list_field(group_meta.get("natural_language_proof_pattern")),
        "- shared_helper_candidates: "
        + _format_list_field(group_meta.get("shared_helper_candidates")),
        "- proving_hints: " + _format_list_field(group_meta.get("proving_hints")),
        f"- grouping_confidence: {group_meta.get('grouping_confidence', 'n/a')}",
    ]
    return "\n".join(lines)


def _write_pattern_reference_file(work_dir: Path, group_meta: dict | None) -> str | None:
    if not group_meta:
        return None
    references = group_meta.get("proof_reuse_pattern_references")
    if not isinstance(references, list) or not references:
        return None

    def collect_unique(field: str, identity_fields: tuple[str, ...]) -> list[dict | str]:
        seen: set[str] = set()
        collected: list[dict | str] = []
        for ref in references:
            if not isinstance(ref, dict):
                continue
            values = ref.get(field, [])
            if not isinstance(values, list):
                continue
            for value in values:
                if isinstance(value, dict):
                    identity = "|".join(str(value.get(key, "")) for key in identity_fields)
                    if not identity.strip("|"):
                        identity = json.dumps(value, sort_keys=True)
                else:
                    identity = str(value)
                if identity in seen:
                    continue
                seen.add(identity)
                collected.append(value)
        return collected

    proof_pool = collect_unique(
        "packet_proof_reference_pool",
        ("proof_script_hash", "proof_block_hash", "lemma_name"),
    )
    helper_import_refs = collect_unique("packet_helper_import_references", ())
    helper_refs = collect_unique("packet_helper_references", ("block_hash", "name"))
    goals: list[dict] = []
    for ref in references:
        if not isinstance(ref, dict):
            continue
        goal = dict(ref)
        goal.pop("packet_proof_reference_pool", None)
        goal.pop("packet_helper_import_references", None)
        goal.pop("packet_helper_references", None)
        goals.append(goal)

    path = work_dir / "proof_reuse_pattern_references.json"
    path.write_text(json.dumps({
        "kind": "proof_reuse_pattern_references",
        "instruction": (
            "Use these entries as proof-pattern references only. Adapt them to "
            "the current VC and compile the result before reporting solved. "
            "Helper entries are references to prior helper shapes; recreate "
            "adapted proved helpers in this worker_helper_scratch_lib if needed."
        ),
        "packet_proof_reference_pool": proof_pool,
        "packet_helper_import_references": helper_import_refs,
        "packet_helper_references": helper_refs,
        "goals": goals,
    }, indent=2), encoding="utf-8")
    make_readonly(path)
    return path.name


def compile_dependency_path_list(coqproject_root: Path, flags: list[str]) -> str:
    """Return a markdown list of absolute compile-only dependency paths."""
    paths: list[str] = []
    flags = absolutize_coq_load_paths(coqproject_root, flags)
    i = 0
    while i < len(flags):
        flag = flags[i]
        if flag in {"-Q", "-R"} and i + 1 < len(flags):
            candidate = Path(flags[i + 1]).expanduser()
            if candidate.is_absolute():
                paths.append(str(candidate))
            i += 3
            continue
        if flag == "-I" and i + 1 < len(flags):
            candidate = Path(flags[i + 1]).expanduser()
            if candidate.is_absolute():
                paths.append(str(candidate))
            i += 2
            continue
        i += 1

    unique_paths = list(dict.fromkeys(paths))
    if not unique_paths:
        return "- no absolute compile-only dependency paths were found in `_CoqProject`"
    return "\n".join(f"  - `{path}`" for path in unique_paths)


def prepare_group(
    work_dir: Path,
    group_goals: list[dict],
    lib_file: Path,
    source_file: Path,
    use_rocq_mcp: bool = True,
    worker_execution_mode: str | None = None,
    group_meta: dict | None = None,
    task_local_logical_module: str | None = None,
    case_deps_seed: dict | None = None,
) -> dict:
    """Set up a fresh work dir for one adaptive group agent.

    Parameters
    ----------
    use_rocq_mcp : bool
        If True, generate the config and instruct the agent to use rocq-mcp.
        The default is False for Windows proof runs: use plain ``coqc`` plus
        Rocq vernacular tactics.

    Returns a group manifest dict with metadata for the concurrent runner.
    """
    worker_execution_mode = normalize_worker_execution_mode(
        worker_execution_mode,
        use_rocq_mcp=use_rocq_mcp,
    )
    use_rocq_mcp = worker_mode_uses_rocq_mcp(worker_execution_mode)
    work_dir.mkdir(parents=True, exist_ok=True)
    write_rocq_memory_wrappers(work_dir)

    coqproject_root, coqc_flags = resolve_coqc_flags(source_file)

    case_deps = _case_deps_from_seed(work_dir, case_deps_seed)
    if case_deps is None:
        case_deps = prepare_simplec_case_dependencies(
            work_dir=work_dir,
            source_file=source_file,
            lib_file=lib_file,
            coqproject_root=coqproject_root,
            coqc_flags=coqc_flags,
            task_local_logical_module=task_local_logical_module,
        )

    # Shared setup
    copy_tutorial(work_dir, TUTORIAL_SRC)
    base_coqc_flags = filter_shadowed_simplec_ee_flags(
        absolutize_coq_load_paths(coqproject_root, coqc_flags),
        enable_overlay=bool(case_deps["modules"]),
    )
    worker_helper_dir = work_dir / WORKER_HELPER_DIR_NAME
    worker_helper_dir.mkdir(parents=True, exist_ok=True)
    worker_coqc_flags = [
        "-Q", str(worker_helper_dir.resolve()), WORKER_HELPER_MODULE_ROOT,
    ] + base_coqc_flags + list(case_deps["flags"])
    write_coqproject(work_dir, worker_coqc_flags, readonly=True)
    dependency_files = sorted_dependency_files([str(path) for path in case_deps["files"]])
    dependency_compile_skipped = False
    if case_deps.get("cache_mode") == "copied_from_base_overlay" and all_vo_files_current(
        dependency_files
    ):
        dependency_compile_skipped = True
    else:
        compile_rocq_files(work_dir, worker_coqc_flags, dependency_files)
    if use_rocq_mcp:
        rocq_config = generate_rocq_mcp_config(work_dir, work_dir)
    else:
        rocq_config = None

    worker_helper_scratch_lib = _write_worker_helper_scratch_lib(work_dir, source_file)
    worker_helper_scratch_lib_rel = str(worker_helper_scratch_lib.relative_to(work_dir))
    worker_manual = work_dir / source_file.name
    make_user_writable(worker_manual)
    worker_manual.write_text(
        _insert_helper_import(source_file.read_text(encoding="utf-8"), worker_helper_scratch_lib.stem),
        encoding="utf-8",
    )

    # Copy assigned goal files into work dir as read-only focused references.
    for entry in group_goals:
        src = Path(str(entry["split_rocq_file"])).resolve()
        dest = work_dir / src.name
        if not dest.exists():
            shutil.copy2(src, dest)
        make_readonly(dest)

    # Generate the single adaptive AGENTS.md
    pattern_reference_file = _write_pattern_reference_file(work_dir, group_meta)
    if pattern_reference_file:
        pattern_reference_section = (
            "   - If checkpoint proof-pattern references are present, read "
            f"`{pattern_reference_file}` for similar prior witness proofs. "
            "Inspect both per-goal candidates and the packet proof reference "
            "pool. Treat every proof script and helper block there as a "
            "pattern to study and adapt, not as an already-proved current goal."
        )
    else:
        pattern_reference_section = ""
    helper_compile_cmd = build_compile_cmd(work_dir, worker_coqc_flags, worker_helper_scratch_lib_rel)
    manual_compile_cmd = build_compile_cmd(work_dir, worker_coqc_flags, worker_manual.name)
    dep_compile_cmds = [
        build_compile_cmd(work_dir, worker_coqc_flags, str(dep.resolve()))
        for dep in sorted_dependency_files([str(path) for path in case_deps["files"]])
    ]
    compile_cmd = " && ".join(dep_compile_cmds + [helper_compile_cmd, manual_compile_cmd])
    goal_list = "\n".join(
        f"- `{e['name']}` (`{Path(str(e['split_rocq_file'])).name}`)"
        for e in group_goals
    )
    tooling_instructions = TOOLING_ROCQ_MCP if use_rocq_mcp else TOOLING_COQC_ONLY

    agents_md = AGENTS_MD_GROUP.format(
        task_local_scratch_lib_name=lib_file.name,
        goal_name=source_file.name.replace("_proof_manual.v", "_goal.v"),
        worker_manual_name=worker_manual.name,
        worker_helper_scratch_lib_name=worker_helper_scratch_lib_rel,
        worker_helper_module=f"{WORKER_HELPER_MODULE_ROOT}.{worker_helper_scratch_lib.stem}",
        compile_cmd=compile_cmd,
        dependency_path_list=compile_dependency_path_list(
            work_dir,
            base_coqc_flags + list(case_deps["flags"]),
        ),
        goal_list=goal_list,
        proof_group_notes=render_proof_group_notes(group_meta),
        tooling_instructions=tooling_instructions,
        pattern_reference_section=pattern_reference_section,
        pattern_reference_file=pattern_reference_file or "proof_reuse_pattern_references.json",
    )
    (work_dir / "AGENTS.md").write_text(agents_md, encoding="utf-8")

    proof_group_id = (
        str(group_meta.get("proof_group_id"))
        if group_meta and group_meta.get("proof_group_id") is not None
        else work_dir.name
    )
    return {
        "work_dir": str(work_dir),
        "goals": group_goals,
        "proof_group_id": proof_group_id,
        "grouping_source": (
            group_meta.get("grouping_source", "sort_chunk_fallback")
            if group_meta else "sort_chunk_fallback"
        ),
        "representative_witness": group_meta.get("representative_witness") if group_meta else None,
        "natural_language_proof_pattern": (
            group_meta.get("natural_language_proof_pattern") if group_meta else None
        ),
        "shared_helper_candidates": group_meta.get("shared_helper_candidates") if group_meta else None,
        "proving_hints": group_meta.get("proving_hints") if group_meta else None,
        "proof_reuse_pattern_references": (
            group_meta.get("proof_reuse_pattern_references") if group_meta else None
        ),
        "grouping_confidence": group_meta.get("grouping_confidence") if group_meta else None,
        "difficulty": group_meta.get("difficulty") if group_meta else None,
        "estimated_difficulty": group_meta.get("estimated_difficulty") if group_meta else None,
        "difficulty_score": group_meta.get("difficulty_score") if group_meta else None,
        "estimated_seconds": group_meta.get("estimated_seconds") if group_meta else None,
        "expected_seconds": group_meta.get("expected_seconds") if group_meta else None,
        "source_file": str(source_file),
        "worker_manual_file": str(worker_manual),
        "worker_helper_scratch_lib_file": str(worker_helper_scratch_lib),
        "worker_helper_module": f"{WORKER_HELPER_MODULE_ROOT}.{worker_helper_scratch_lib.stem}",
        "coqproject_root": str(work_dir),
        "coqc_flags": worker_coqc_flags,
        "base_coqproject_root": str(coqproject_root),
        "base_coqc_flags": coqc_flags,
        "task_local_scratch_lib_file": str(lib_file),
        "case_dependency_root": case_deps["root"],
        "case_dependency_files": case_deps["files"],
        "case_dependency_modules": case_deps["modules"],
        "case_dependency_module_map": case_deps["module_map"],
        "case_dependency_task_local_scratch_lib_module": case_deps[
            "task_local_scratch_lib_module"
        ],
        "case_dependency_task_local_scratch_lib_modules": case_deps[
            "task_local_scratch_lib_modules"
        ],
        "case_dependency_task_local_scratch_lib_files": case_deps[
            "task_local_scratch_lib_files"
        ],
        "dependency_mode": "worker_case_dependency_overlay",
        "case_dependency_cache_mode": case_deps.get("cache_mode", "fresh_overlay"),
        "case_dependency_compile_skipped": dependency_compile_skipped,
        "rocq_mcp_config": str(rocq_config) if rocq_config else None,
        "worker_execution_mode": worker_execution_mode,
        "use_rocq_mcp": use_rocq_mcp,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare a group work directory for adaptive concurrent solving."
    )
    parser.add_argument("manifest", help="Path to manifest.json from split_manual_goals.py")
    parser.add_argument("task_local_scratch_lib", help="Path to task_local_scratch_lib")
    parser.add_argument("--group-indices", nargs="+", type=int, required=True,
                        help="1-based indices of lemmas in this group (from manifest)")
    parser.add_argument("--work-dir", required=True, help="Work directory for this group")
    parser.add_argument("--worker-execution-mode", default=None,
                        choices=sorted(WORKER_EXECUTION_MODES),
                        help="Explicit worker tooling mode. Overrides --no-rocq-mcp.")
    parser.add_argument("--task-local-module", default=None,
                        help="Explicit canonical logical module that maps to "
                             "task_local_scratch_lib.")
    parser.add_argument("--no-rocq-mcp", action="store_true",
                        help="Deprecated no-op: coqc/coqtop mode is the default.")
    args = parser.parse_args()

    manifest_path = Path(args.manifest).expanduser().resolve()
    manifest = load_manifest(manifest_path)
    lib_file = Path(args.task_local_scratch_lib).expanduser().resolve()
    work_dir = Path(args.work_dir).expanduser().resolve()

    all_lemmas = manifest["lemmas"]
    group_goals = [all_lemmas[i - 1] for i in args.group_indices]

    source_file = Path(str(manifest["source_file"])).resolve()
    prepare_group(
        work_dir=work_dir,
        group_goals=group_goals,
        lib_file=lib_file,
        source_file=source_file,
        use_rocq_mcp=not args.no_rocq_mcp,
        worker_execution_mode=args.worker_execution_mode,
        task_local_logical_module=args.task_local_module,
    )
    print(f"Prepared group work directory: {work_dir}")
    print(f"  goals: {len(group_goals)}")
    for g in group_goals:
        print(f"    - {g['name']}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
