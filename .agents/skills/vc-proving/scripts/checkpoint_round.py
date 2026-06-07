#!/usr/bin/env python3
"""Build a vc-proving round checkpoint from migrated scratch artifacts.

The checkpoint is a persistent report artifact.  It copies the helper-free
manual and migrated task_local_scratch_lib, builds a reuse index, exports a
partial_proof_packet.json, and writes a single manifest that the next proving
round can consume.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from manual_goal_utils import (
    added_forbidden_toplevels,
    block_has_admitted,
    ensure_unique_lemma_names,
    goal_definition_hash_for_lemma,
    lemma_proof_block_hash,
    lemma_proof_script,
    lemma_statement_hash,
    lemma_statement_text,
    lemma_target_symbol,
    load_manifest,
    parse_manual_file,
    require_import_lines,
    stable_text_digest,
    validate_helper_import_lines,
)
from proof_reuse_index import build_index

CHECKPOINT_SCHEMA_VERSION = 1
PACKET_SCHEMA_VERSION = 1
CHECKPOINT_KIND = "vc_proving_round_checkpoint"
PACKET_KIND = "vc_proving_partial_proof_packet"


def _write_json(path: Path, data: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2), encoding="utf-8")


def _file_hash(path: Path | None) -> str | None:
    if path is None or not path.is_file():
        return None
    return stable_text_digest(path.read_text(encoding="utf-8"))


def _file_raw_sha256(path: Path | None) -> str | None:
    if path is None or not path.is_file():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _split_lib(text: str, frozen_prefix_end_line: int | None) -> tuple[str, str]:
    if frozen_prefix_end_line is None:
        return text, ""
    lines = text.splitlines(keepends=True)
    return "".join(lines[:frozen_prefix_end_line]), "".join(lines[frozen_prefix_end_line:])


def _context_hashes(lib_file: Path, frozen_prefix_end_line: int | None) -> dict[str, object]:
    text = lib_file.read_text(encoding="utf-8")
    prefix, suffix = _split_lib(text, frozen_prefix_end_line)
    return {
        "lib_frozen_prefix_end_line": frozen_prefix_end_line,
        "lib_frozen_prefix_hash": stable_text_digest(prefix),
        "helper_suffix_hash": stable_text_digest(suffix),
        "full_lib_hash": stable_text_digest(text),
    }


def _parse_lemmas_or_empty(text: str) -> tuple[str, list[dict[str, object]]]:
    try:
        prelude, lemmas = parse_manual_file(text)
    except ValueError:
        return "", []
    ensure_unique_lemma_names(lemmas)
    return prelude, lemmas


def _helper_kind(header_line: str) -> str:
    return header_line.split(" ", 1)[0].strip() or "Lemma"


def _helper_payload_hash(helper_imports: list[str], helper_blocks: list[str]) -> str:
    payload = "\n".join(helper_imports).rstrip() + "\n\n" + "\n\n".join(
        block.rstrip() for block in helper_blocks
    ).rstrip()
    return stable_text_digest(payload)


def _build_helper_records(
    lib_file: Path,
    frozen_prefix_end_line: int | None,
) -> tuple[list[str], list[dict[str, object]], str]:
    lib_text = lib_file.read_text(encoding="utf-8")
    _prefix, suffix = _split_lib(lib_text, frozen_prefix_end_line)
    helper_imports = require_import_lines(suffix)
    import_errors = validate_helper_import_lines(helper_imports)
    if import_errors:
        raise SystemExit("Unsupported helper suffix import(s): " + "; ".join(import_errors))
    forbidden = added_forbidden_toplevels("", suffix)
    if forbidden:
        raise SystemExit(
            "Forbidden helper suffix top-level declaration(s): " + "; ".join(forbidden)
        )
    _prelude, helper_lemmas = _parse_lemmas_or_empty(suffix)
    helpers: list[dict[str, object]] = []
    helper_blocks: list[str] = []
    for lemma in helper_lemmas:
        block = str(lemma["block"])
        if block_has_admitted(block):
            raise SystemExit(f"Helper lemma `{lemma['name']}` contains Admitted")
        helper_blocks.append(block)
        helpers.append(
            {
                "name": str(lemma["name"]),
                "kind": _helper_kind(str(lemma["header_line"])),
                "statement_hash": lemma_statement_hash(lemma),
                "block_hash": stable_text_digest(block),
                "helper_block": block,
                "imports": helper_imports,
                "coqc_status": "passed",
            }
        )
    return helper_imports, helpers, _helper_payload_hash(helper_imports, helper_blocks)


def _load_strategy_notes(manifest: dict[str, object]) -> dict[str, dict[str, object]]:
    work_dir_raw = manifest.get("work_dir")
    if not work_dir_raw:
        return {}
    path = Path(str(work_dir_raw)).resolve() / "proof_strategy_report.json"
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}
    notes: dict[str, dict[str, object]] = {}
    reports = data if isinstance(data, list) else [data]
    for report in reports:
        if not isinstance(report, dict):
            continue
        decisions = report.get("reuse_decisions")
        if not isinstance(decisions, list):
            continue
        for decision in decisions:
            if not isinstance(decision, dict):
                continue
            goal = decision.get("goal") or decision.get("lemma_name")
            if goal:
                notes[str(goal)] = decision
    return notes


def build_partial_proof_packet(
    manual_file: Path,
    lib_file: Path,
    *,
    frozen_prefix_end_line: int | None,
    case_id: str,
    round_id: str,
    source_goal_version: str | None,
    manifest: dict[str, object] | None = None,
) -> dict[str, object]:
    manual_file = manual_file.expanduser().resolve()
    lib_file = lib_file.expanduser().resolve()
    manual_text = manual_file.read_text(encoding="utf-8")
    prelude, lemmas = parse_manual_file(manual_text)
    ensure_unique_lemma_names(lemmas)
    module_map_raw = manifest.get("case_dependency_module_map") if manifest else None
    module_map = (
        {str(key): str(value) for key, value in module_map_raw.items()}
        if isinstance(module_map_raw, dict)
        else None
    )
    helper_imports, helpers, helper_payload_hash = _build_helper_records(
        lib_file,
        frozen_prefix_end_line,
    )
    helper_names = [str(helper["name"]) for helper in helpers]
    strategy_notes = _load_strategy_notes(manifest or {})
    context = _context_hashes(lib_file, frozen_prefix_end_line)

    proofs: list[dict[str, object]] = []
    unsolved: list[str] = []
    for lemma in lemmas:
        name = str(lemma["name"])
        block = str(lemma["block"])
        if block_has_admitted(block):
            unsolved.append(name)
            continue
        script = lemma_proof_script(lemma)
        if not script:
            unsolved.append(name)
            continue
        goal_metadata = goal_definition_hash_for_lemma(
            prelude,
            lemma,
            source_file=manual_file,
            module_map=module_map,
        )
        note = strategy_notes.get(name, {})
        proofs.append(
            {
                "lemma_name": name,
                "target_symbol": lemma_target_symbol(lemma),
                "statement_hash": lemma_statement_hash(lemma),
                "goal_body_hash": goal_metadata.get("goal_body_hash"),
                "proof_block_hash": lemma_proof_block_hash(lemma),
                "proof_script_hash": stable_text_digest(script),
                "proof_script": script,
                "informal_proof": note.get("informal_proof", ""),
                "reuse_decision": note.get("reuse_decision", "exact_reuse_candidate"),
                "dependencies": {
                    "helper_lemmas": helper_names,
                    "helper_imports": helper_imports,
                },
                "coqc_status": "passed",
            }
        )

    return {
        "schema_version": PACKET_SCHEMA_VERSION,
        "kind": PACKET_KIND,
        "case_id": case_id,
        "round_id": round_id,
        "source_goal_version": source_goal_version,
        "lib_frozen_prefix_end_line": frozen_prefix_end_line,
        "lib_frozen_prefix_hash": context["lib_frozen_prefix_hash"],
        "helper_suffix_hash": context["helper_suffix_hash"],
        "helper_payload_hash": helper_payload_hash,
        "proofs": proofs,
        "helpers": helpers,
        "helper_imports": helper_imports,
        "unsolved_lemmas": unsolved,
        "packet_status": "compile_checked",
    }


def _resolve_manual_file(manifest: dict[str, object], override: str | None) -> Path:
    if override:
        return Path(override).expanduser().resolve()
    for key in (
        "migrated_proof_manual_file",
        "merged_proof_manual_file",
        "helper_free_proof_manual_file",
    ):
        raw = manifest.get(key)
        if raw:
            path = Path(str(raw)).expanduser().resolve()
            if path.is_file():
                return path
    raise SystemExit("No migrated proof manual found in manifest; pass --manual")


def _resolve_lib_file(manifest: dict[str, object], override: str | None) -> Path:
    if override:
        return Path(override).expanduser().resolve()
    for key in (
        "migrated_task_local_scratch_lib_file",
        "task_local_scratch_lib_file",
        "lib_file",
    ):
        raw = manifest.get(key)
        if raw:
            path = Path(str(raw)).expanduser().resolve()
            if path.is_file():
                return path
    raise SystemExit("No task_local_scratch_lib found in manifest; pass --lib")


def _resolved_optional_file(manifest: dict[str, object], *keys: str) -> Path | None:
    for key in keys:
        raw = manifest.get(key)
        if raw:
            path = Path(str(raw)).expanduser().resolve()
            if path.is_file():
                return path
    return None


def _relative_name(path: Path) -> str:
    return path.name


def _copy_if_distinct(source: Path, dest: Path) -> None:
    if source.resolve() == dest.resolve():
        return
    shutil.copy2(source, dest)


def build_checkpoint(
    manifest_path: Path,
    *,
    output_dir: Path,
    manual_file: Path | None = None,
    lib_file: Path | None = None,
    frozen_prefix_end_line: int | None = None,
    case_id: str | None = None,
    round_id: str | None = None,
    source_goal_version: str | None = None,
    usable: bool = True,
    blockers: list[str] | None = None,
) -> dict[str, object]:
    manifest_path = manifest_path.expanduser().resolve()
    manifest = load_manifest(manifest_path)
    manual_file = manual_file or _resolve_manual_file(manifest, None)
    lib_file = lib_file or _resolve_lib_file(manifest, None)
    if frozen_prefix_end_line is None and isinstance(manifest.get("lib_frozen_prefix_end_line"), int):
        frozen_prefix_end_line = int(manifest["lib_frozen_prefix_end_line"])
    case_id = case_id or str(manifest.get("case_id") or manifest.get("source_file") or manual_file)
    round_id = round_id or output_dir.name
    source_goal_version = source_goal_version or (
        str(manifest.get("source_goal_version")) if manifest.get("source_goal_version") else None
    )

    output_dir = output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    checkpoint_manual = output_dir / "round_migrated_manual.v"
    checkpoint_lib = output_dir / "task_local_scratch_lib.v"
    _copy_if_distinct(manual_file, checkpoint_manual)
    _copy_if_distinct(lib_file, checkpoint_lib)

    reuse_index = build_index(
        checkpoint_manual,
        lib_file=str(checkpoint_lib),
        frozen_prefix_end_line=frozen_prefix_end_line,
    )
    reuse_index_path = output_dir / "reuse_index.json"
    _write_json(reuse_index_path, reuse_index)

    packet = build_partial_proof_packet(
        checkpoint_manual,
        checkpoint_lib,
        frozen_prefix_end_line=frozen_prefix_end_line,
        case_id=case_id,
        round_id=round_id,
        source_goal_version=source_goal_version,
        manifest=manifest,
    )
    packet_path = output_dir / "partial_proof_packet.json"
    _write_json(packet_path, packet)

    context = _context_hashes(checkpoint_lib, frozen_prefix_end_line)
    official_manual = _resolved_optional_file(manifest, "official_proof_manual_file", "seed_proof_manual_file", "source_file")
    common_lib = _resolved_optional_file(manifest, "common_case_formal_lib_file")
    helper_names = [str(helper["name"]) for helper in packet["helpers"] if isinstance(helper, dict)]
    checkpoint = {
        "schema_version": CHECKPOINT_SCHEMA_VERSION,
        "kind": CHECKPOINT_KIND,
        "case_id": case_id,
        "round_id": round_id,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "source_goal_version": source_goal_version,
        "official_proof_manual_hash": _file_hash(official_manual),
        "common_case_formal_lib_hash": _file_hash(common_lib),
        "lib_frozen_prefix_end_line": frozen_prefix_end_line,
        "lib_frozen_prefix_hash": context["lib_frozen_prefix_hash"],
        "helper_suffix_hash": context["helper_suffix_hash"],
        "helper_payload_hash": packet["helper_payload_hash"],
        "checkpoint_task_local_scratch_lib": _relative_name(checkpoint_lib),
        "checkpoint_helper_free_manual": _relative_name(checkpoint_manual),
        "reuse_index": _relative_name(reuse_index_path),
        "partial_proof_packet": _relative_name(packet_path),
        "solved_lemmas": [str(proof["lemma_name"]) for proof in packet["proofs"] if isinstance(proof, dict)],
        "unsolved_lemmas": packet["unsolved_lemmas"],
        "migrated_helper_imports": packet["helper_imports"],
        "migrated_helper_lemmas": helper_names,
        "proof_packet_hash": _file_raw_sha256(packet_path),
        "checkpoint_compile_status": "passed",
        "usable_for_next_round": bool(usable),
        "blockers": blockers or [],
    }
    checkpoint_path = output_dir / "vc_proving_round_checkpoint.json"
    _write_json(checkpoint_path, checkpoint)
    return checkpoint


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", help="manifest.json after validate/migrate")
    parser.add_argument("--output-dir", required=True, help="Persistent checkpoint output dir")
    parser.add_argument("--manual", default=None, help="Helper-free migrated manual")
    parser.add_argument("--lib", default=None, help="Migrated task_local_scratch_lib")
    parser.add_argument("--lib-frozen-prefix-end-line", type=int, default=None)
    parser.add_argument("--case-id", default=None)
    parser.add_argument("--round-id", default=None)
    parser.add_argument("--source-goal-version", default=None)
    parser.add_argument("--unusable", action="store_true", help="Mark checkpoint unusable")
    parser.add_argument("--blocker", action="append", default=None, help="Checkpoint blocker note")
    args = parser.parse_args()

    checkpoint = build_checkpoint(
        Path(args.manifest),
        output_dir=Path(args.output_dir),
        manual_file=Path(args.manual).expanduser().resolve() if args.manual else None,
        lib_file=Path(args.lib).expanduser().resolve() if args.lib else None,
        frozen_prefix_end_line=args.lib_frozen_prefix_end_line,
        case_id=args.case_id,
        round_id=args.round_id,
        source_goal_version=args.source_goal_version,
        usable=not args.unusable,
        blockers=args.blocker,
    )
    print(
        "VC proving checkpoint written to "
        f"{Path(args.output_dir).expanduser().resolve() / 'vc_proving_round_checkpoint.json'}"
    )
    print(
        f"Solved lemmas: {len(checkpoint['solved_lemmas'])}; "
        f"unsolved lemmas: {len(checkpoint['unsolved_lemmas'])}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
