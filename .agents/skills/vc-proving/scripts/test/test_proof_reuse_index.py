#!/usr/bin/env python3
"""Tests for proof_reuse_index.py."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SCRIPT_DIR))

from proof_reuse_index import analyze_manifest, apply_reuse, build_index


def _write_case(tmp_path: Path) -> dict[str, Path]:
    (tmp_path / "_CoqProject").write_text("-Q . MyLib\n", encoding="utf-8")
    (tmp_path / "foo_goal.v").write_text(
        "Definition old_goal := True.\n\n"
        "Definition new_goal := True.\n",
        encoding="utf-8",
    )
    solved = tmp_path / "solved_proof_manual.v"
    solved.write_text(
        "Require Import MyLib.foo_goal.\n\n"
        "Lemma proof_of_old : old_goal.\n"
        "Proof.\n"
        "  unfold old_goal.\n"
        "  exact I.\n"
        "Qed.\n",
        encoding="utf-8",
    )
    current = tmp_path / "current_proof_manual.v"
    current.write_text(
        "Require Import MyLib.foo_goal.\n\n"
        "Lemma proof_of_new : new_goal.\n"
        "Proof. Admitted.\n",
        encoding="utf-8",
    )
    lib = tmp_path / "foo_lib.v"
    lib.write_text(
        "Definition frozen_spec := True.\n"
        "Lemma helper_suffix : True.\n"
        "Proof. exact I. Qed.\n",
        encoding="utf-8",
    )
    manifest = tmp_path / "manifest.json"
    manifest.write_text(
        json.dumps(
            {
                "source_file": str(current),
                "work_dir": str(tmp_path),
                "lemma_order": ["proof_of_new"],
                "target_lemma_order": ["proof_of_new"],
                "lemmas": [
                    {
                        "name": "proof_of_new",
                        "statement_header": "Lemma proof_of_new : new_goal.",
                    }
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
    )
    return {"solved": solved, "current": current, "lib": lib, "manifest": manifest}


def test_reuses_by_goal_body_hash_and_adapts_target_symbol(tmp_path: Path):
    paths = _write_case(tmp_path)
    index = build_index(
        paths["solved"],
        lib_file=str(paths["lib"]),
        frozen_prefix_end_line=1,
    )

    report = analyze_manifest(
        paths["manifest"],
        index,
        lib_file=str(paths["lib"]),
        frozen_prefix_end_line=1,
    )
    assert report["reusable_count"] == 1
    assert report["goals"][0]["status"] == "reusable"
    assert report["goals"][0]["match_key"] == "goal_body_hash"

    output = tmp_path / "reused_proof_manual.v"
    apply_report = apply_reuse(
        paths["manifest"],
        index,
        output=output,
        report_output=tmp_path / "reuse_report.json",
        lib_file=str(paths["lib"]),
        frozen_prefix_end_line=1,
        compile_check=False,
    )
    assert apply_report["applied_count"] == 1
    reused_text = output.read_text(encoding="utf-8")
    assert "Admitted." not in reused_text
    assert "Lemma proof_of_new : new_goal." in reused_text
    assert "unfold new_goal." in reused_text
    assert "unfold old_goal." not in reused_text


def test_context_mismatch_blocks_reuse(tmp_path: Path):
    paths = _write_case(tmp_path)
    index = build_index(
        paths["solved"],
        lib_file=str(paths["lib"]),
        frozen_prefix_end_line=1,
    )
    changed_lib = tmp_path / "foo_lib_changed.v"
    changed_lib.write_text(
        "Definition frozen_spec := True.\n"
        "Lemma different_helper_suffix : True.\n"
        "Proof. exact I. Qed.\n",
        encoding="utf-8",
    )

    report = analyze_manifest(
        paths["manifest"],
        index,
        lib_file=str(changed_lib),
        frozen_prefix_end_line=1,
    )
    assert report["reusable_count"] == 0
    assert report["goals"][0]["status"] == "context_mismatch"


def test_split_manifest_records_statement_and_goal_body_hashes(tmp_path: Path):
    paths = _write_case(tmp_path)
    result = subprocess.run(
        [sys.executable, str(SCRIPT_DIR / "split_manual_goals.py"), str(paths["current"])],
        capture_output=True,
        text=True,
        check=True,
    )
    manifest_path = None
    for line in result.stdout.splitlines():
        if line.startswith("Manifest: "):
            manifest_path = Path(line.removeprefix("Manifest: "))
    assert manifest_path is not None
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    entry = manifest["lemmas"][0]
    assert entry["statement_hash"]
    assert entry["target_symbol"] == "new_goal"
    assert entry["goal_body_hash"]
    assert entry["goal_definition_module"] == "MyLib.foo_goal"
