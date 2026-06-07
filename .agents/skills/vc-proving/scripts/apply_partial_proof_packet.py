#!/usr/bin/env python3
"""Apply a compile-gated partial proof packet to a fresh proving scratch.

The packet is a transport artifact, not a formal source file.  This script
reconstructs candidate Rocq source from the current manual statement plus the
packet proof script, optionally appends packet helper payload to the current
task_local_scratch_lib, and leaves the normal vc-proving gates in place.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from manual_goal_utils import (
    added_forbidden_toplevels,
    block_has_admitted,
    check_rocq_file,
    check_rocq_file_with_deps,
    ensure_unique_lemma_names,
    goal_definition_hash_for_lemma,
    lemma_by_name,
    lemma_proof_script,
    lemma_statement_hash,
    lemma_statement_text,
    lemma_target_symbol,
    load_manifest,
    manifest_coq_project,
    parse_manual_file,
    require_import_lines,
    stable_text_digest,
    validate_helper_import_lines,
)

PACKET_SCHEMA_VERSION = 1
CHECKPOINT_SCHEMA_VERSION = 1
PACKET_KIND = "vc_proving_partial_proof_packet"
CHECKPOINT_KIND = "vc_proving_round_checkpoint"
REUSE_POLICIES = (
    "exact",
    "extended_candidate",
    "exact_or_pattern",
    "pattern_reference",
    "disabled",
)


def _read_json(path: Path) -> dict[str, object]:
    path = path.expanduser().resolve()
    if not path.is_file():
        raise SystemExit(f"JSON file not found: {path}")
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit(f"{path} is not a JSON object")
    return data


def _resolve_packet_path(
    checkpoint_path: Path | None,
    packet_path: Path | None,
) -> tuple[dict[str, object] | None, Path]:
    if packet_path is not None:
        return None, packet_path.expanduser().resolve()
    if checkpoint_path is None:
        raise SystemExit("Either --checkpoint or --packet is required")
    checkpoint_path = checkpoint_path.expanduser().resolve()
    checkpoint = _read_json(checkpoint_path)
    if checkpoint.get("schema_version") != CHECKPOINT_SCHEMA_VERSION:
        raise SystemExit(
            f"{checkpoint_path} schema_version must be {CHECKPOINT_SCHEMA_VERSION}"
        )
    if checkpoint.get("kind") != CHECKPOINT_KIND:
        raise SystemExit(f"{checkpoint_path} is not a {CHECKPOINT_KIND}")
    raw_packet = checkpoint.get("partial_proof_packet")
    if not raw_packet:
        raise SystemExit(f"{checkpoint_path} does not name partial_proof_packet")
    resolved = Path(str(raw_packet))
    if not resolved.is_absolute():
        resolved = checkpoint_path.parent / resolved
    return checkpoint, resolved.resolve()


def _validate_packet(packet: dict[str, object], packet_path: Path) -> None:
    if packet.get("schema_version") != PACKET_SCHEMA_VERSION:
        raise SystemExit(
            f"{packet_path} schema_version must be {PACKET_SCHEMA_VERSION}"
        )
    if packet.get("kind") != PACKET_KIND:
        raise SystemExit(f"{packet_path} is not a {PACKET_KIND}")
    if packet.get("packet_status") not in (None, "compile_checked"):
        raise SystemExit(f"{packet_path} packet_status is not compile_checked")
    for proof in packet.get("proofs", []):
        if not isinstance(proof, dict):
            raise SystemExit(f"{packet_path} contains a non-object proof entry")
        script = str(proof.get("proof_script") or "")
        if not script:
            raise SystemExit(f"{packet_path} proof entry is missing proof_script")
        expected = proof.get("proof_script_hash")
        if expected and stable_text_digest(script) != expected:
            raise SystemExit(
                f"{packet_path} proof_script_hash mismatch for {proof.get('lemma_name')}"
            )
        if block_has_admitted(script):
            raise SystemExit(
                f"{packet_path} proof_script for {proof.get('lemma_name')} contains Admitted"
            )
    helper_imports = [
        str(line).strip()
        for line in packet.get("helper_imports", [])
        if str(line).strip()
    ]
    import_errors = validate_helper_import_lines(helper_imports)
    if import_errors:
        raise SystemExit(
            f"{packet_path} contains unsupported helper import(s): "
            + "; ".join(import_errors)
        )
    helper_blocks: list[str] = []
    for helper in packet.get("helpers", []):
        if not isinstance(helper, dict):
            raise SystemExit(f"{packet_path} contains a non-object helper entry")
        block = str(helper.get("helper_block") or "")
        if not block:
            raise SystemExit(f"{packet_path} helper entry is missing helper_block")
        helper_blocks.append(block)
        expected = helper.get("block_hash")
        if expected and stable_text_digest(block) != expected:
            raise SystemExit(
                f"{packet_path} helper block hash mismatch for {helper.get('name')}"
            )
        if block_has_admitted(block):
            raise SystemExit(
                f"{packet_path} helper {helper.get('name')} contains Admitted"
            )
        forbidden = added_forbidden_toplevels("", block)
        if forbidden:
            raise SystemExit(
                f"{packet_path} helper {helper.get('name')} contains forbidden "
                "top-level declaration(s): " + "; ".join(forbidden)
            )
    expected_helper_payload = packet.get("helper_payload_hash")
    if expected_helper_payload:
        payload = "\n".join(helper_imports).rstrip() + "\n\n" + "\n\n".join(
            block.rstrip() for block in helper_blocks
        ).rstrip()
        if stable_text_digest(payload) != expected_helper_payload:
            raise SystemExit(f"{packet_path} helper_payload_hash mismatch")


def _packet_context_mismatches(
    packet: dict[str, object],
    checkpoint: dict[str, object] | None,
    manifest: dict[str, object],
    current_frozen_prefix_end_line: int | None,
) -> list[dict[str, object]]:
    mismatches: list[dict[str, object]] = []
    expected_case = checkpoint.get("case_id") if checkpoint else packet.get("case_id")
    current_case = manifest.get("case_id")
    packet_case = packet.get("case_id")
    if checkpoint and checkpoint.get("case_id") and packet_case and checkpoint.get("case_id") != packet_case:
        mismatches.append(
            {
                "field": "checkpoint_packet_case_id",
                "current": packet_case,
                "checkpoint": checkpoint.get("case_id"),
            }
        )
    if current_case and expected_case and str(current_case) != str(expected_case):
        mismatches.append(
            {
                "field": "case_id",
                "current": str(current_case),
                "checkpoint": str(expected_case),
            }
        )
    elif expected_case and not current_case:
        mismatches.append(
            {
                "field": "case_id",
                "current": "missing",
                "checkpoint": str(expected_case),
            }
        )

    expected_goal = (
        checkpoint.get("source_goal_version")
        if checkpoint and checkpoint.get("source_goal_version") is not None
        else packet.get("source_goal_version")
    )
    packet_goal = packet.get("source_goal_version")
    if (
        checkpoint
        and checkpoint.get("source_goal_version") is not None
        and packet_goal is not None
        and checkpoint.get("source_goal_version") != packet_goal
    ):
        mismatches.append(
            {
                "field": "checkpoint_packet_source_goal_version",
                "current": packet_goal,
                "checkpoint": checkpoint.get("source_goal_version"),
            }
        )
    current_goal = manifest.get("source_goal_version")
    if current_goal and expected_goal and str(current_goal) != str(expected_goal):
        mismatches.append(
            {
                "field": "source_goal_version",
                "current": str(current_goal),
                "checkpoint": str(expected_goal),
            }
        )
    elif expected_goal and not current_goal:
        mismatches.append(
            {
                "field": "source_goal_version",
                "current": "missing",
                "checkpoint": str(expected_goal),
            }
        )

    packet_line = packet.get("lib_frozen_prefix_end_line")
    checkpoint_line = checkpoint.get("lib_frozen_prefix_end_line") if checkpoint else None
    if isinstance(packet_line, int) and current_frozen_prefix_end_line != packet_line:
        mismatches.append(
            {
                "field": "lib_frozen_prefix_end_line",
                "current": current_frozen_prefix_end_line,
                "checkpoint": packet_line,
            }
        )
    if (
        checkpoint
        and isinstance(checkpoint_line, int)
        and isinstance(packet_line, int)
        and checkpoint_line != packet_line
    ):
        mismatches.append(
            {
                "field": "checkpoint_packet_lib_frozen_prefix_end_line",
                "current": packet_line,
                "checkpoint": checkpoint_line,
            }
        )

    if checkpoint:
        for key in ("lib_frozen_prefix_hash", "helper_suffix_hash", "helper_payload_hash"):
            if checkpoint.get(key) and packet.get(key) and checkpoint.get(key) != packet.get(key):
                mismatches.append(
                    {
                        "field": f"checkpoint_packet_{key}",
                        "current": packet.get(key),
                        "checkpoint": checkpoint.get(key),
                    }
                )
    return mismatches


def _split_lib(text: str, frozen_prefix_end_line: int | None) -> tuple[str, str]:
    if frozen_prefix_end_line is None:
        return text, ""
    lines = text.splitlines(keepends=True)
    return "".join(lines[:frozen_prefix_end_line]), "".join(lines[frozen_prefix_end_line:])


def _context_hashes(text: str, frozen_prefix_end_line: int | None) -> dict[str, object]:
    prefix, suffix = _split_lib(text, frozen_prefix_end_line)
    return {
        "lib_frozen_prefix_end_line": frozen_prefix_end_line,
        "lib_frozen_prefix_hash": stable_text_digest(prefix),
        "helper_suffix_hash": stable_text_digest(suffix),
        "full_lib_hash": stable_text_digest(text),
    }


def _resolve_frozen_prefix_end_line(
    packet: dict[str, object],
    manifest: dict[str, object],
    override: int | None,
) -> int | None:
    if override is not None:
        return override
    raw_manifest = manifest.get("lib_frozen_prefix_end_line")
    if isinstance(raw_manifest, int):
        return raw_manifest
    raw_packet = packet.get("lib_frozen_prefix_end_line")
    if isinstance(raw_packet, int):
        return raw_packet
    return None


def _prefix_mismatch(
    packet: dict[str, object],
    lib_text: str,
    frozen_prefix_end_line: int | None,
    lib_file: Path,
) -> tuple[dict[str, object], dict[str, object] | None]:
    current = _context_hashes(lib_text, frozen_prefix_end_line)
    expected = packet.get("lib_frozen_prefix_hash")
    if expected and current.get("lib_frozen_prefix_hash") != expected:
        return current, {
            "field": "lib_frozen_prefix_hash",
            "current": current.get("lib_frozen_prefix_hash"),
            "checkpoint": expected,
            "lib_file": str(lib_file),
        }
    return current, None


def _parse_lemmas_or_empty(text: str) -> list[dict[str, object]]:
    try:
        _prelude, lemmas = parse_manual_file(text)
    except ValueError:
        return []
    ensure_unique_lemma_names(lemmas)
    return lemmas


def _helper_kind(helper: dict[str, object]) -> str:
    raw = str(helper.get("kind") or "")
    return raw if raw else "Lemma"


def _helper_reference_payload(packet: dict[str, object]) -> tuple[list[str], list[dict[str, object]]]:
    helper_imports = [
        str(line).strip()
        for line in packet.get("helper_imports", [])
        if str(line).strip()
    ]
    helpers: list[dict[str, object]] = []
    for helper in packet.get("helpers", []):
        if not isinstance(helper, dict):
            continue
        block = str(helper.get("helper_block") or "")
        helpers.append(
            {
                "name": helper.get("name") or _helper_name_from_block(block),
                "kind": _helper_kind(helper),
                "statement_hash": helper.get("statement_hash"),
                "block_hash": helper.get("block_hash"),
                "helper_block": block,
            }
        )
    return helper_imports, helpers


def _proof_reference_payload(packet: dict[str, object]) -> list[dict[str, object]]:
    proofs: list[dict[str, object]] = []
    for proof in packet.get("proofs", []):
        if not isinstance(proof, dict):
            continue
        proofs.append(
            {
                "lemma_name": proof.get("lemma_name"),
                "target_symbol": proof.get("target_symbol"),
                "statement_hash": proof.get("statement_hash"),
                "goal_body_hash": proof.get("goal_body_hash"),
                "proof_block_hash": proof.get("proof_block_hash"),
                "proof_script_hash": proof.get("proof_script_hash"),
                "informal_proof": proof.get("informal_proof", ""),
                "reuse_decision": proof.get("reuse_decision", "pattern_reference"),
                "dependencies": proof.get("dependencies", {}),
                "proof_script": proof.get("proof_script", ""),
            }
        )
    return proofs


def _helper_name_from_block(block: str) -> str | None:
    try:
        _prelude, lemmas = parse_manual_file(block)
    except ValueError:
        return None
    if len(lemmas) != 1:
        return None
    return str(lemmas[0]["name"])


def _append_packet_helpers(
    lib_text: str,
    packet: dict[str, object],
    *,
    reuse_policy: str,
) -> tuple[str, list[str], list[str], str]:
    if reuse_policy == "disabled":
        return lib_text, [], [], "disabled"
    helper_imports = [str(line).strip() for line in packet.get("helper_imports", []) if str(line).strip()]
    import_errors = validate_helper_import_lines(helper_imports)
    if import_errors:
        raise SystemExit("Unsupported helper suffix import(s): " + "; ".join(import_errors))

    existing_imports = set(require_import_lines(lib_text))
    imports_to_add = [line for line in helper_imports if line not in existing_imports]

    existing_lemmas = _parse_lemmas_or_empty(lib_text)
    existing_by_name = lemma_by_name(existing_lemmas) if existing_lemmas else {}
    helpers_to_add: list[tuple[str, str]] = []
    for helper in packet.get("helpers", []):
        if not isinstance(helper, dict):
            continue
        block = str(helper.get("helper_block") or "")
        name = str(helper.get("name") or _helper_name_from_block(block) or "")
        if not name:
            raise SystemExit("Packet helper block has no parseable lemma name")
        forbidden = added_forbidden_toplevels("", block)
        if forbidden:
            raise SystemExit(
                f"Packet helper {name} contains forbidden top-level declaration(s): "
                + "; ".join(forbidden)
            )
        old = existing_by_name.get(name)
        if old is not None:
            if str(old["block"]).strip() != block.strip():
                raise SystemExit(f"Conflicting helper lemma `{name}` already exists in lib")
            continue
        helpers_to_add.append((name, block))

    if not imports_to_add and not helpers_to_add:
        return lib_text, [], [], "already_present"

    sections: list[str] = []
    if imports_to_add:
        sections.append("\n".join(imports_to_add).rstrip())
    if helpers_to_add:
        sections.append("\n\n".join(block.rstrip() for _name, block in helpers_to_add).rstrip())
    new_text = lib_text.rstrip() + "\n\n" + "\n\n".join(sections).rstrip() + "\n"
    return (
        new_text,
        imports_to_add,
        [name for name, _block in helpers_to_add],
        "extended_candidate_applied" if reuse_policy == "extended_candidate" else "applied",
    )


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
    proof: dict[str, object],
    current: dict[str, object],
) -> str:
    script = str(proof.get("proof_script") or "")
    script = _replace_identifier(script, proof.get("lemma_name"), current.get("lemma_name"))
    script = _replace_identifier(script, proof.get("target_symbol"), current.get("target_symbol"))
    return script


def _current_lemma_record(
    prelude: str,
    lemma: dict[str, object],
    *,
    source_file: Path,
    module_map: dict[str, str] | None,
) -> dict[str, object]:
    goal_metadata = goal_definition_hash_for_lemma(
        prelude,
        lemma,
        source_file=source_file,
        module_map=module_map,
    )
    return {
        "lemma_name": str(lemma["name"]),
        "target_symbol": lemma_target_symbol(lemma),
        "statement_hash": lemma_statement_hash(lemma),
        "goal_body_hash": goal_metadata.get("goal_body_hash"),
    }


def _proof_matches_current(
    proof: dict[str, object],
    current: dict[str, object],
) -> tuple[bool, str | None]:
    goal_body_hash = current.get("goal_body_hash")
    if goal_body_hash and proof.get("goal_body_hash") == goal_body_hash:
        return True, "goal_body_hash"
    if proof.get("statement_hash") == current.get("statement_hash"):
        return True, "statement_hash"
    return False, None


def _token_similarity(left: object, right: object) -> float:
    def tokens(value: object) -> set[str]:
        return {
            token for token in re.split(r"[^A-Za-z0-9']+", str(value or "").lower())
            if token
        }

    left_tokens = tokens(left)
    right_tokens = tokens(right)
    if not left_tokens or not right_tokens:
        return 0.0
    return len(left_tokens & right_tokens) / len(left_tokens | right_tokens)


def _pattern_candidates_for_current(
    proofs: list[dict[str, object]],
    current: dict[str, object],
) -> list[dict[str, object]]:
    candidates: list[dict[str, object]] = []
    for proof in proofs:
        reasons: list[str] = []
        score = 0.0
        if current.get("goal_body_hash") and proof.get("goal_body_hash") == current.get("goal_body_hash"):
            score += 100.0
            reasons.append("goal_body_hash_match")
        if proof.get("statement_hash") == current.get("statement_hash"):
            score += 80.0
            reasons.append("statement_hash_match")
        if proof.get("target_symbol") and proof.get("target_symbol") == current.get("target_symbol"):
            score += 60.0
            reasons.append("target_symbol_match")
        if proof.get("lemma_name") == current.get("lemma_name"):
            score += 40.0
            reasons.append("lemma_name_match")
        target_similarity = _token_similarity(proof.get("target_symbol"), current.get("target_symbol"))
        lemma_similarity = _token_similarity(proof.get("lemma_name"), current.get("lemma_name"))
        similarity = max(target_similarity, lemma_similarity)
        if similarity > 0:
            score += 20.0 * similarity
            reasons.append(f"name_token_similarity:{similarity:.2f}")
        if score <= 0:
            continue
        candidates.append(
            {
                "score": round(score, 3),
                "match_reasons": reasons,
                "lemma_name": proof.get("lemma_name"),
                "target_symbol": proof.get("target_symbol"),
                "statement_hash": proof.get("statement_hash"),
                "goal_body_hash": proof.get("goal_body_hash"),
                "proof_block_hash": proof.get("proof_block_hash"),
                "proof_script_hash": proof.get("proof_script_hash"),
                "informal_proof": proof.get("informal_proof", ""),
                "reuse_decision": proof.get("reuse_decision", "pattern_reference"),
                "dependencies": proof.get("dependencies", {}),
                "proof_script": proof.get("proof_script", ""),
            }
        )
    return sorted(candidates, key=lambda item: float(item["score"]), reverse=True)[:3]


def _build_pattern_reference_report(
    manifest: dict[str, object],
    source_file: Path,
    packet: dict[str, object],
    *,
    packet_path: Path,
    checkpoint_path: Path | None,
    lib_file: Path,
    context_mismatches: list[dict[str, object]],
) -> dict[str, object]:
    source_text = source_file.read_text(encoding="utf-8")
    prelude, lemmas = parse_manual_file(source_text)
    ensure_unique_lemma_names(lemmas)
    module_map_raw = manifest.get("case_dependency_module_map")
    module_map = (
        {str(key): str(value) for key, value in module_map_raw.items()}
        if isinstance(module_map_raw, dict)
        else None
    )
    proofs = [proof for proof in packet.get("proofs", []) if isinstance(proof, dict)]
    proof_refs = _proof_reference_payload(packet)
    target_names = [
        str(entry["name"]) for entry in manifest.get("lemmas", [])
        if isinstance(entry, dict) and entry.get("name") is not None
    ]
    target_set = set(target_names)
    helper_import_refs, helper_refs = _helper_reference_payload(packet)
    goals: list[dict[str, object]] = []
    for lemma in lemmas:
        name = str(lemma["name"])
        if target_set and name not in target_set:
            continue
        current = _current_lemma_record(
            prelude,
            lemma,
            source_file=source_file,
            module_map=module_map,
        )
        candidates = _pattern_candidates_for_current(proofs, current)
        goals.append(
            {
                **current,
                "status": "pattern_reference_available" if candidates else "no_similar_packet_proof",
                "candidates": candidates,
                "packet_proof_reference_pool": proof_refs,
                "packet_helper_import_references": helper_import_refs,
                "packet_helper_references": helper_refs,
            }
        )
    matched = sum(1 for goal in goals if goal.get("candidates"))
    return {
        "schema_version": PACKET_SCHEMA_VERSION,
        "kind": "partial_proof_packet_pattern_reference_report",
        "status": "pattern_reference_only",
        "checkpoint": str(checkpoint_path.expanduser().resolve()) if checkpoint_path else None,
        "packet": str(packet_path),
        "lib_file": str(lib_file),
        "context_mismatches": context_mismatches,
        "proof_references": proof_refs,
        "helper_import_references": helper_import_refs,
        "helper_references": helper_refs,
        "matched_goal_count": matched,
        "goal_count": len(goals),
        "goals": goals,
        "worker_instruction": (
            "Use these packet proofs only as proof-pattern references. "
            "Even when the per-goal candidate list is empty, inspect the "
            "packet proof reference pool for structurally similar VCs. "
            "Helper references describe prior helper shapes only; if useful, "
            "recreate adapted proved helpers in the current worker_helper_scratch_lib. "
            "Do not mark a goal solved unless the adapted current proof compiles."
        ),
    }


def _apply_packet_proofs(
    manifest: dict[str, object],
    source_file: Path,
    packet: dict[str, object],
) -> tuple[str, list[dict[str, object]], list[str]]:
    source_text = source_file.read_text(encoding="utf-8")
    prelude, lemmas = parse_manual_file(source_text)
    ensure_unique_lemma_names(lemmas)
    module_map_raw = manifest.get("case_dependency_module_map")
    module_map = (
        {str(key): str(value) for key, value in module_map_raw.items()}
        if isinstance(module_map_raw, dict)
        else None
    )
    proofs = [proof for proof in packet.get("proofs", []) if isinstance(proof, dict)]
    applied: list[dict[str, object]] = []
    new_blocks: list[str] = []

    for lemma in lemmas:
        current_block = str(lemma["block"])
        if not block_has_admitted(current_block):
            new_blocks.append(current_block)
            continue
        current = _current_lemma_record(
            prelude,
            lemma,
            source_file=source_file,
            module_map=module_map,
        )
        selected: dict[str, object] | None = None
        selected_match_key: str | None = None
        for proof in proofs:
            ok, match_key = _proof_matches_current(proof, current)
            if ok:
                selected = proof
                selected_match_key = match_key
                break
        if selected is None:
            new_blocks.append(current_block)
            continue
        script = _adapt_proof_script(selected, current)
        statement = lemma_statement_text(lemma)
        new_blocks.append(statement.rstrip() + "\n" + script.rstrip() + "\n")
        applied.append(
            {
                "lemma_name": str(lemma["name"]),
                "match_key": selected_match_key,
                "reused_from": {
                    "lemma_name": selected.get("lemma_name"),
                    "target_symbol": selected.get("target_symbol"),
                    "proof_block_hash": selected.get("proof_block_hash"),
                    "proof_script_hash": selected.get("proof_script_hash"),
                },
                "status": "reused_pending_compile",
            }
        )

    target_names = [
        str(entry["name"]) for entry in manifest.get("lemmas", [])
        if isinstance(entry, dict) and entry.get("name") is not None
    ]
    new_text = prelude + "".join(block if block.endswith("\n") else block + "\n" for block in new_blocks)
    _new_prelude, new_lemmas = parse_manual_file(new_text)
    by_name = lemma_by_name(new_lemmas)
    remaining = [
        name for name in target_names
        if name in by_name and block_has_admitted(str(by_name[name]["block"]))
    ]
    return new_text, applied, remaining


def _compile_candidate(
    manifest: dict[str, object],
    manual_file: Path,
    lib_file: Path,
) -> None:
    project = manifest_coq_project(manifest)
    dep_files = [
        Path(str(path)).expanduser().resolve()
        for path in manifest.get("case_dependency_files", [])
    ]
    if lib_file.is_file() and lib_file not in dep_files:
        dep_files.append(lib_file)
    if project is not None:
        project_root, flags = project
        check_rocq_file_with_deps(
            manual_file,
            dep_files=dep_files,
            project_root=project_root,
            flags=flags,
            force_deps=True,
        )
    else:
        try:
            check_rocq_file_with_deps(manual_file, dep_files=dep_files, force_deps=True)
        except SystemExit:
            check_rocq_file(manual_file)


def _write_pattern_reference_report(
    manifest_path: Path,
    manifest: dict[str, object],
    source_file: Path,
    packet: dict[str, object],
    *,
    packet_path: Path,
    checkpoint_path: Path | None,
    lib_file: Path,
    report_output: Path,
    context_mismatches: list[dict[str, object]],
) -> dict[str, object]:
    report_output.parent.mkdir(parents=True, exist_ok=True)
    report = _build_pattern_reference_report(
        manifest,
        source_file,
        packet,
        packet_path=packet_path,
        checkpoint_path=checkpoint_path,
        lib_file=lib_file,
        context_mismatches=context_mismatches,
    )
    report["report_output"] = str(report_output)
    report_output.write_text(json.dumps(report, indent=2), encoding="utf-8")
    manifest["partial_proof_packet_pattern_reference"] = report
    manifest["partial_proof_packet_prepass"] = {
        "schema_version": PACKET_SCHEMA_VERSION,
        "kind": "partial_proof_packet_apply_report",
        "status": "pattern_reference_only",
        "checkpoint": str(checkpoint_path.expanduser().resolve()) if checkpoint_path else None,
        "packet": str(packet_path),
        "report_output": str(report_output),
        "reuse_policy": "pattern_reference",
        "applied_count": 0,
        "applied": [],
        "reused_goal_names": [],
        "remaining_goal_names": [
            str(entry["name"]) for entry in manifest.get("lemmas", [])
            if isinstance(entry, dict) and entry.get("name") is not None
        ],
        "pattern_reference_report": str(report_output),
        "pattern_reference_goal_count": report.get("goal_count", 0),
        "pattern_reference_matched_goal_count": report.get("matched_goal_count", 0),
    }
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return report


def apply_partial_proof_packet(
    manifest_path: Path,
    *,
    lib_file: Path,
    checkpoint_path: Path | None = None,
    packet_path: Path | None = None,
    output_manual: Path | None = None,
    lib_output: Path | None = None,
    report_output: Path | None = None,
    frozen_prefix_end_line: int | None = None,
    reuse_policy: str = "exact_or_pattern",
    compile_check: bool = True,
) -> dict[str, object]:
    if reuse_policy not in REUSE_POLICIES:
        raise SystemExit(f"Unsupported checkpoint reuse policy: {reuse_policy}")
    if reuse_policy == "disabled":
        return {
            "schema_version": PACKET_SCHEMA_VERSION,
            "kind": "partial_proof_packet_apply_report",
            "status": "disabled",
            "applied_count": 0,
            "applied": [],
            "remaining_goal_names": [],
        }
    checkpoint, resolved_packet_path = _resolve_packet_path(checkpoint_path, packet_path)
    packet = _read_json(resolved_packet_path)
    _validate_packet(packet, resolved_packet_path)

    checkpoint_unusable_mismatch: dict[str, object] | None = None
    if checkpoint is not None:
        expected_hash = checkpoint.get("proof_packet_hash")
        actual_hash = hashlib.sha256(resolved_packet_path.read_bytes()).hexdigest()
        if expected_hash and actual_hash != expected_hash:
            raise SystemExit(f"proof_packet_hash mismatch for {resolved_packet_path}")
        if checkpoint.get("usable_for_next_round") is False:
            blockers = [str(item) for item in checkpoint.get("blockers", [])]
            if any("annotation-bug" in item or "annotation_bug" in item for item in blockers):
                raise SystemExit(
                    f"Checkpoint is marked unusable due to annotation bug: {checkpoint_path}"
                )
            if reuse_policy not in {"exact_or_pattern", "pattern_reference"}:
                raise SystemExit(f"Checkpoint is marked unusable: {checkpoint_path}")
            checkpoint_unusable_mismatch = {
                "field": "checkpoint_usable_for_next_round",
                "current": "pattern_reference_only",
                "checkpoint": False,
                "blockers": blockers,
            }

    manifest_path = manifest_path.expanduser().resolve()
    manifest = load_manifest(manifest_path)
    manifest.pop("partial_proof_packet_prepass", None)
    manifest.pop("partial_proof_packet_pattern_reference", None)
    source_file = Path(str(manifest["source_file"])).expanduser().resolve()
    lib_file = lib_file.expanduser().resolve()
    lib_output = lib_output.expanduser().resolve() if lib_output else lib_file
    base_work_dir = Path(str(manifest["work_dir"])).expanduser().resolve()
    output_manual = (
        output_manual.expanduser().resolve()
        if output_manual
        else base_work_dir / "partial_proof_packet_candidate_proof_manual.v"
    )
    report_output = (
        report_output.expanduser().resolve()
        if report_output
        else base_work_dir / "partial_proof_packet_apply_report.json"
    )

    frozen_prefix_end_line = _resolve_frozen_prefix_end_line(
        packet,
        manifest,
        frozen_prefix_end_line,
    )
    lib_text = lib_file.read_text(encoding="utf-8")
    original_lib_output_text = (
        lib_output.read_text(encoding="utf-8") if lib_output.exists() else None
    )
    context_mismatches = _packet_context_mismatches(
        packet,
        checkpoint,
        manifest,
        frozen_prefix_end_line,
    )
    if checkpoint_unusable_mismatch is not None:
        context_mismatches.append(checkpoint_unusable_mismatch)
    current_context, prefix_mismatch = _prefix_mismatch(
        packet,
        lib_text,
        frozen_prefix_end_line,
        lib_file,
    )
    if prefix_mismatch is not None:
        context_mismatches.append(prefix_mismatch)

    if reuse_policy == "pattern_reference" or (
        reuse_policy == "exact_or_pattern" and context_mismatches
    ):
        return _write_pattern_reference_report(
            manifest_path,
            manifest,
            source_file,
            packet,
            packet_path=resolved_packet_path,
            checkpoint_path=checkpoint_path,
            lib_file=lib_file,
            report_output=report_output,
            context_mismatches=context_mismatches,
        )

    if context_mismatches:
        raise SystemExit(
            "Checkpoint context mismatch: "
            + "; ".join(
                f"{item.get('field')} current={item.get('current')} checkpoint={item.get('checkpoint')}"
                for item in context_mismatches
            )
        )

    if not compile_check:
        if reuse_policy != "exact_or_pattern":
            raise SystemExit("Direct partial proof packet reuse requires compile_check")
        return _write_pattern_reference_report(
            manifest_path,
            manifest,
            source_file,
            packet,
            packet_path=resolved_packet_path,
            checkpoint_path=checkpoint_path,
            lib_file=lib_file,
            report_output=report_output,
            context_mismatches=[
                {
                    "field": "direct_reuse_compile_check",
                    "current": "disabled",
                    "checkpoint": "direct reuse requires compile gate",
                }
            ],
        )

    try:
        new_lib_text, helper_imports, helper_lemmas, helper_status = _append_packet_helpers(
            lib_text,
            packet,
            reuse_policy=reuse_policy,
        )
    except SystemExit as exc:
        if reuse_policy != "exact_or_pattern":
            raise
        return _write_pattern_reference_report(
            manifest_path,
            manifest,
            source_file,
            packet,
            packet_path=resolved_packet_path,
            checkpoint_path=checkpoint_path,
            lib_file=lib_file,
            report_output=report_output,
            context_mismatches=[
                {
                    "field": "direct_reuse_helper_payload",
                    "current": "not_applied",
                    "checkpoint": str(exc),
                }
            ],
        )
    lib_output.parent.mkdir(parents=True, exist_ok=True)
    lib_output.write_text(new_lib_text, encoding="utf-8")

    manual_text, applied, remaining = _apply_packet_proofs(manifest, source_file, packet)
    output_manual.parent.mkdir(parents=True, exist_ok=True)
    output_manual.write_text(manual_text, encoding="utf-8")

    if compile_check:
        try:
            _compile_candidate(manifest, output_manual, lib_output)
        except SystemExit as exc:
            if original_lib_output_text is None:
                try:
                    lib_output.unlink()
                except FileNotFoundError:
                    pass
            else:
                lib_output.write_text(original_lib_output_text, encoding="utf-8")
            if reuse_policy != "exact_or_pattern":
                raise
            return _write_pattern_reference_report(
                manifest_path,
                manifest,
                source_file,
                packet,
                packet_path=resolved_packet_path,
                checkpoint_path=checkpoint_path,
                lib_file=lib_file,
                report_output=report_output,
                context_mismatches=[
                    {
                        "field": "direct_reuse_compile_gate",
                        "current": "candidate_compile_failed",
                        "checkpoint": str(exc),
                        "failed_candidate_manual": str(output_manual),
                        "failed_candidate_lib_output": str(lib_output),
                    }
                ],
            )
        for item in applied:
            item["status"] = "reused_compile_checked"

    applied_names = [
        str(item["lemma_name"]) for item in applied
        if isinstance(item, dict) and item.get("lemma_name")
    ]
    report = {
        "schema_version": PACKET_SCHEMA_VERSION,
        "kind": "partial_proof_packet_apply_report",
        "status": "applied" if applied or helper_imports or helper_lemmas else "no_applicable_payload",
        "checkpoint": str(checkpoint_path.expanduser().resolve()) if checkpoint_path else None,
        "packet": str(resolved_packet_path),
        "report_output": str(report_output),
        "reuse_policy": reuse_policy,
        "source_file": str(source_file),
        "output_manual": str(output_manual),
        "lib_file": str(lib_file),
        "lib_output": str(lib_output),
        "current_context_before_helpers": current_context,
        "context_after_helpers": _context_hashes(new_lib_text, frozen_prefix_end_line),
        "helper_status": helper_status,
        "applied_helper_imports": helper_imports,
        "applied_helper_lemmas": helper_lemmas,
        "applied_count": len(applied),
        "applied": applied,
        "reused_goal_names": applied_names,
        "remaining_goal_names": remaining,
        "compile_check": compile_check,
    }

    manifest.setdefault("source_lemma_order", manifest.get("lemma_order", applied_names + remaining))
    manifest["partial_proof_packet_prepass"] = report
    if applied:
        remaining_set = set(remaining)
        manifest["source_file"] = str(output_manual)
        manifest["lemmas"] = [
            entry for entry in manifest.get("lemmas", [])
            if isinstance(entry, dict) and str(entry.get("name")) in remaining_set
        ]
        manifest["lemma_order"] = remaining
        manifest["target_lemma_order"] = remaining
        manifest["goal_count"] = len(remaining)
    report_output.parent.mkdir(parents=True, exist_ok=True)
    if reuse_policy == "exact_or_pattern" and remaining:
        pattern_report_output = report_output.with_name(
            "partial_proof_packet_pattern_reference_report.json"
        )
        pattern_manifest = dict(manifest)
        pattern_manifest["source_file"] = str(output_manual)
        pattern_report = _build_pattern_reference_report(
            pattern_manifest,
            output_manual,
            packet,
            packet_path=resolved_packet_path,
            checkpoint_path=checkpoint_path,
            lib_file=lib_file,
            context_mismatches=[
                {
                    "field": "direct_reuse_unmatched_goals",
                    "current": remaining,
                    "checkpoint": "packet contains no exact hash match for these current goals",
                }
            ],
        )
        pattern_report["report_output"] = str(pattern_report_output)
        pattern_report_output.write_text(
            json.dumps(pattern_report, indent=2),
            encoding="utf-8",
        )
        manifest["partial_proof_packet_pattern_reference"] = pattern_report
        report["pattern_reference_report"] = str(pattern_report_output)
        report["pattern_reference_goal_count"] = pattern_report.get("goal_count", 0)
        report["pattern_reference_matched_goal_count"] = pattern_report.get(
            "matched_goal_count",
            0,
        )
        manifest["partial_proof_packet_prepass"] = report
    report_output.write_text(json.dumps(report, indent=2), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", help="manifest.json from split_manual_goals.py")
    parser.add_argument("task_local_scratch_lib", help="Current fresh task_local_scratch_lib")
    parser.add_argument("--checkpoint", default=None, help="vc_proving_round_checkpoint.json")
    parser.add_argument("--packet", default=None, help="partial_proof_packet.json")
    parser.add_argument("--output", default=None, help="Candidate manual output path")
    parser.add_argument("--lib-output", default=None, help="task_local_scratch_lib output path")
    parser.add_argument("--report-output", default=None, help="Apply report JSON output path")
    parser.add_argument("--lib-frozen-prefix-end-line", type=int, default=None)
    parser.add_argument(
        "--reuse-policy",
        choices=REUSE_POLICIES,
        default="exact_or_pattern",
        help="Checkpoint reuse policy",
    )
    parser.add_argument(
        "--no-compile-check",
        action="store_true",
        help="Disable direct reuse; exact_or_pattern emits proof-pattern references instead",
    )
    args = parser.parse_args()

    report = apply_partial_proof_packet(
        Path(args.manifest),
        lib_file=Path(args.task_local_scratch_lib),
        checkpoint_path=Path(args.checkpoint) if args.checkpoint else None,
        packet_path=Path(args.packet) if args.packet else None,
        output_manual=Path(args.output) if args.output else None,
        lib_output=Path(args.lib_output) if args.lib_output else None,
        report_output=Path(args.report_output) if args.report_output else None,
        frozen_prefix_end_line=args.lib_frozen_prefix_end_line,
        reuse_policy=args.reuse_policy,
        compile_check=not args.no_compile_check,
    )
    print(f"Partial proof packet apply report written to {report.get('report_output')}")
    if report.get("kind") == "partial_proof_packet_pattern_reference_report":
        print(
            "Partial proof packet pattern reference: "
            f"{report.get('matched_goal_count', 0)} similar goal(s)"
        )
    else:
        print(
            "Partial proof packet prepass: "
            f"{report.get('applied_count', 0)} reused, "
            f"{len(report.get('remaining_goal_names', []))} remaining"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
