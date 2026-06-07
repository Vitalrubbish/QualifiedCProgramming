#!/usr/bin/env python3
"""Tests for vc-proving round checkpoint and partial proof packets."""

from __future__ import annotations

import json
from pathlib import Path

import apply_partial_proof_packet as packet_apply
from apply_partial_proof_packet import apply_partial_proof_packet
from checkpoint_round import build_checkpoint, build_partial_proof_packet
from run_agent_concurrent import apply_reuse_prepass, finalize


def _write_packet_case(tmp_path: Path) -> dict[str, Path]:
    (tmp_path / "_CoqProject").write_text("-Q . MyLib\n", encoding="utf-8")
    solved_manual = tmp_path / "round_migrated_manual.v"
    solved_manual.write_text(
        "Require Import MyLib.\n\n"
        "Lemma proof_of_old : True.\n"
        "Proof. exact I. Qed.\n\n"
        "Lemma proof_of_unsolved : True.\n"
        "Proof. Admitted.\n",
        encoding="utf-8",
    )
    packet_lib = tmp_path / "packet_lib.v"
    packet_lib.write_text(
        "Definition frozen_spec := True.\n"
        "Require Import Coq.Init.Logic.\n\n"
        "Lemma helper_a : True.\n"
        "Proof. exact I. Qed.\n",
        encoding="utf-8",
    )
    current_manual = tmp_path / "current_manual.v"
    current_manual.write_text(
        "Require Import MyLib.\n\n"
        "Lemma proof_of_new : True.\n"
        "Proof. Admitted.\n",
        encoding="utf-8",
    )
    current_lib = tmp_path / "current_lib.v"
    current_lib.write_text("Definition frozen_spec := True.\n", encoding="utf-8")
    work_dir = tmp_path / "work"
    work_dir.mkdir()
    manifest = {
        "source_file": str(current_manual),
        "work_dir": str(work_dir),
        "case_id": "case",
        "source_goal_version": "goal-hash",
        "lemma_order": ["proof_of_new"],
        "target_lemma_order": ["proof_of_new"],
        "lemmas": [
            {
                "name": "proof_of_new",
                "statement_header": "Lemma proof_of_new : True.",
            }
        ],
        "lib_frozen_prefix_end_line": 1,
        "migrated_proof_manual_file": str(solved_manual),
        "migrated_task_local_scratch_lib_file": str(packet_lib),
    }
    manifest_path = work_dir / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    return {
        "solved_manual": solved_manual,
        "packet_lib": packet_lib,
        "current_manual": current_manual,
        "current_lib": current_lib,
        "work_dir": work_dir,
        "manifest": manifest_path,
    }


def test_partial_proof_packet_exports_solved_only_and_helper_payload(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    packet = build_partial_proof_packet(
        paths["solved_manual"],
        paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
        manifest=json.loads(paths["manifest"].read_text(encoding="utf-8")),
    )

    assert packet["kind"] == "vc_proving_partial_proof_packet"
    assert [proof["lemma_name"] for proof in packet["proofs"]] == ["proof_of_old"]
    assert packet["unsolved_lemmas"] == ["proof_of_unsolved"]
    assert packet["helper_imports"] == ["Require Import Coq.Init.Logic."]
    assert [helper["name"] for helper in packet["helpers"]] == ["helper_a"]
    assert packet["proofs"][0]["proof_script_hash"]


def test_partial_proof_packet_applies_to_current_statement_and_lib(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    packet = build_partial_proof_packet(
        paths["solved_manual"],
        paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
        manifest=json.loads(paths["manifest"].read_text(encoding="utf-8")),
    )
    packet_path = paths["work_dir"] / "partial_proof_packet.json"
    packet_path.write_text(json.dumps(packet, indent=2), encoding="utf-8")
    original_compile = packet_apply._compile_candidate
    packet_apply._compile_candidate = lambda *_args, **_kwargs: None

    try:
        report = apply_partial_proof_packet(
            paths["manifest"],
            lib_file=paths["current_lib"],
            packet_path=packet_path,
            compile_check=True,
        )
    finally:
        packet_apply._compile_candidate = original_compile

    assert report["applied_count"] == 1
    assert report["helper_status"] == "applied"
    assert report["reused_goal_names"] == ["proof_of_new"]
    assert report["remaining_goal_names"] == []
    candidate = Path(report["output_manual"]).read_text(encoding="utf-8")
    assert "Lemma proof_of_new : True." in candidate
    assert "Proof. exact I. Qed." in candidate
    assert "Admitted." not in candidate
    lib_text = paths["current_lib"].read_text(encoding="utf-8")
    assert "Require Import Coq.Init.Logic." in lib_text
    assert "Lemma helper_a : True." in lib_text


def test_checkpoint_manifest_drives_runner_prepass(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    checkpoint_dir = paths["work_dir"] / "reuse_checkpoints" / "r1"
    checkpoint = build_checkpoint(
        paths["manifest"],
        output_dir=checkpoint_dir,
        manual_file=paths["solved_manual"],
        lib_file=paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
    )
    checkpoint_path = checkpoint_dir / "vc_proving_round_checkpoint.json"
    original_compile = packet_apply._compile_candidate
    packet_apply._compile_candidate = lambda *_args, **_kwargs: None

    try:
        report = apply_reuse_prepass(
            manifest_path=paths["manifest"],
            lib_file=paths["current_lib"],
            reuse_checkpoint_path=checkpoint_path,
            compile_check=True,
        )
    finally:
        packet_apply._compile_candidate = original_compile

    assert checkpoint["solved_lemmas"] == ["proof_of_old"]
    assert report is not None
    assert report["reused_goal_names"] == ["proof_of_new"]
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    assert manifest["lemmas"] == []
    summary = finalize([], paths["work_dir"], manifest_path=paths["manifest"])
    assert summary["status_counts"]["solved"] == 1


def test_prefix_mismatch_generates_pattern_reference_not_solved(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    checkpoint_dir = paths["work_dir"] / "reuse_checkpoints" / "r1"
    build_checkpoint(
        paths["manifest"],
        output_dir=checkpoint_dir,
        manual_file=paths["solved_manual"],
        lib_file=paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
    )
    paths["current_lib"].write_text("Definition changed_spec := True.\n", encoding="utf-8")

    report = apply_reuse_prepass(
        manifest_path=paths["manifest"],
        lib_file=paths["current_lib"],
        reuse_checkpoint_path=checkpoint_dir / "vc_proving_round_checkpoint.json",
        compile_check=False,
    )

    assert report is not None
    assert report["kind"] == "partial_proof_packet_pattern_reference_report"
    assert report["matched_goal_count"] == 1
    assert report["goals"][0]["lemma_name"] == "proof_of_new"
    assert report["goals"][0]["candidates"][0]["proof_script"]
    assert report["proof_references"][0]["lemma_name"] == "proof_of_old"
    assert report["goals"][0]["packet_proof_reference_pool"][0]["lemma_name"] == "proof_of_old"
    assert report["helper_import_references"] == ["Require Import Coq.Init.Logic."]
    assert report["helper_references"][0]["name"] == "helper_a"
    assert report["goals"][0]["packet_helper_references"][0]["name"] == "helper_a"
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    assert [entry["name"] for entry in manifest["lemmas"]] == ["proof_of_new"]
    assert "partial_proof_packet_pattern_reference" in manifest


def test_prefix_line_mismatch_generates_pattern_reference_not_solved(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    packet = build_partial_proof_packet(
        paths["solved_manual"],
        paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
        manifest=json.loads(paths["manifest"].read_text(encoding="utf-8")),
    )
    packet_path = paths["work_dir"] / "partial_proof_packet.json"
    packet_path.write_text(json.dumps(packet, indent=2), encoding="utf-8")
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    manifest["lib_frozen_prefix_end_line"] = 0
    paths["manifest"].write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    report = apply_partial_proof_packet(
        paths["manifest"],
        lib_file=paths["current_lib"],
        packet_path=packet_path,
        compile_check=False,
    )

    assert report["kind"] == "partial_proof_packet_pattern_reference_report"
    assert any(
        item["field"] == "lib_frozen_prefix_end_line"
        for item in report["context_mismatches"]
    )
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    assert [entry["name"] for entry in manifest["lemmas"]] == ["proof_of_new"]


def test_missing_context_fields_do_not_direct_reuse(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    packet = build_partial_proof_packet(
        paths["solved_manual"],
        paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
        manifest=json.loads(paths["manifest"].read_text(encoding="utf-8")),
    )
    packet_path = paths["work_dir"] / "partial_proof_packet.json"
    packet_path.write_text(json.dumps(packet, indent=2), encoding="utf-8")
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    manifest.pop("case_id")
    manifest.pop("source_goal_version")
    paths["manifest"].write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    report = apply_partial_proof_packet(
        paths["manifest"],
        lib_file=paths["current_lib"],
        packet_path=packet_path,
        compile_check=True,
    )

    assert report["kind"] == "partial_proof_packet_pattern_reference_report"
    fields = {item["field"] for item in report["context_mismatches"]}
    assert "case_id" in fields
    assert "source_goal_version" in fields
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    assert [entry["name"] for entry in manifest["lemmas"]] == ["proof_of_new"]


def test_context_match_unmatched_goal_gets_pattern_reference_pool(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    packet = build_partial_proof_packet(
        paths["solved_manual"],
        paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
        manifest=json.loads(paths["manifest"].read_text(encoding="utf-8")),
    )
    packet_path = paths["work_dir"] / "partial_proof_packet.json"
    packet_path.write_text(json.dumps(packet, indent=2), encoding="utf-8")
    paths["current_manual"].write_text(
        "Require Import MyLib.\n\n"
        "Lemma unrelated : True /\\ True.\n"
        "Proof. Admitted.\n",
        encoding="utf-8",
    )
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    manifest["lemma_order"] = ["unrelated"]
    manifest["target_lemma_order"] = ["unrelated"]
    manifest["lemmas"] = [{"name": "unrelated", "statement_header": "Lemma unrelated : True /\\ True."}]
    paths["manifest"].write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    original_compile = packet_apply._compile_candidate
    packet_apply._compile_candidate = lambda *_args, **_kwargs: None

    try:
        report = apply_partial_proof_packet(
            paths["manifest"],
            lib_file=paths["current_lib"],
            packet_path=packet_path,
            compile_check=True,
        )
    finally:
        packet_apply._compile_candidate = original_compile

    assert report["applied_count"] == 0
    assert report["remaining_goal_names"] == ["unrelated"]
    assert report["pattern_reference_goal_count"] == 1
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    pattern = manifest["partial_proof_packet_pattern_reference"]
    assert pattern["goals"][0]["lemma_name"] == "unrelated"
    assert pattern["goals"][0]["candidates"] == []
    assert pattern["goals"][0]["packet_proof_reference_pool"][0]["lemma_name"] == "proof_of_old"


def test_compile_check_disabled_falls_back_to_pattern_reference_not_solved(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    packet = build_partial_proof_packet(
        paths["solved_manual"],
        paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
        manifest=json.loads(paths["manifest"].read_text(encoding="utf-8")),
    )
    packet_path = paths["work_dir"] / "partial_proof_packet.json"
    packet_path.write_text(json.dumps(packet, indent=2), encoding="utf-8")
    original_lib = paths["current_lib"].read_text(encoding="utf-8")

    report = apply_partial_proof_packet(
        paths["manifest"],
        lib_file=paths["current_lib"],
        packet_path=packet_path,
        compile_check=False,
    )

    assert report["kind"] == "partial_proof_packet_pattern_reference_report"
    assert any(
        item["field"] == "direct_reuse_compile_check"
        for item in report["context_mismatches"]
    )
    assert paths["current_lib"].read_text(encoding="utf-8") == original_lib
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    assert [entry["name"] for entry in manifest["lemmas"]] == ["proof_of_new"]
    assert manifest["partial_proof_packet_prepass"]["applied_count"] == 0


def test_compile_failure_falls_back_to_pattern_reference_and_restores_lib(tmp_path: Path):
    paths = _write_packet_case(tmp_path)
    packet = build_partial_proof_packet(
        paths["solved_manual"],
        paths["packet_lib"],
        frozen_prefix_end_line=1,
        case_id="case",
        round_id="r1",
        source_goal_version="goal-hash",
        manifest=json.loads(paths["manifest"].read_text(encoding="utf-8")),
    )
    packet_path = paths["work_dir"] / "partial_proof_packet.json"
    packet_path.write_text(json.dumps(packet, indent=2), encoding="utf-8")
    original_lib = paths["current_lib"].read_text(encoding="utf-8")
    original_compile = packet_apply._compile_candidate

    def fail_compile(*_args, **_kwargs):
        raise SystemExit("forced compile failure")

    packet_apply._compile_candidate = fail_compile
    try:
        report = packet_apply.apply_partial_proof_packet(
            paths["manifest"],
            lib_file=paths["current_lib"],
            packet_path=packet_path,
            compile_check=True,
        )
    finally:
        packet_apply._compile_candidate = original_compile

    assert report["kind"] == "partial_proof_packet_pattern_reference_report"
    assert any(
        item["field"] == "direct_reuse_compile_gate"
        for item in report["context_mismatches"]
    )
    assert paths["current_lib"].read_text(encoding="utf-8") == original_lib
    manifest = json.loads(paths["manifest"].read_text(encoding="utf-8"))
    assert [entry["name"] for entry in manifest["lemmas"]] == ["proof_of_new"]
    assert "partial_proof_packet_prepass" in manifest
    assert manifest["partial_proof_packet_prepass"]["applied_count"] == 0
