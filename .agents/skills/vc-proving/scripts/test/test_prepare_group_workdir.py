#!/usr/bin/env python3
"""Tests for manual_goal_utils shared helpers and prepare_group_workdir."""

from __future__ import annotations

import json
import os
import stat
import tempfile
from pathlib import Path
from unittest.mock import patch

import pytest

from manual_goal_utils import (
    build_compile_cmd,
    copy_coqproject,
    copy_tutorial,
    generate_rocq_mcp_config,
    make_readonly,
    prepare_simplec_case_dependencies,
    require_import_lines,
    simplec_case_dependency_modules,
    setup_lib_copy,
)
from prepare_group_workdir import _case_deps_from_seed, prepare_group


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture()
def tmp(tmp_path):
    """Provide a tmp_path with a _CoqProject and dummy files."""
    # _CoqProject
    (tmp_path / "_CoqProject").write_text("-Q . MyLib\n", encoding="utf-8")
    # Dummy lib file
    lib = tmp_path / "foo_rel_lib.v"
    lib.write_text("Definition foo := 1.\n", encoding="utf-8")
    # Dummy source file (for resolve_coqc_flags)
    src = tmp_path / "foo_manual.v"
    src.write_text("Lemma a : True.\nProof. auto. Qed.\n", encoding="utf-8")
    return tmp_path


@pytest.fixture()
def goal_files(tmp):
    """Create 3 dummy split goal files and return lemma dicts."""
    names = [
        "proof_of_foo_entail_wit_1",
        "proof_of_foo_entail_wit_2",
        "proof_of_foo_return_wit_1",
    ]
    lemmas = []
    for i, name in enumerate(names, 1):
        f = tmp / f"goal_{i:02d}__{name}.v"
        f.write_text(
            f"Require Import MyLib.\nLemma {name} : True.\nProof. Admitted.\n",
            encoding="utf-8",
        )
        lemmas.append({
            "index": i,
            "name": name,
            "split_rocq_file": str(f),
            "statement_header": f"Lemma {name} : True.",
            "original_start_line": i * 10,
            "original_end_line": i * 10 + 5,
        })
    return lemmas


# ---------------------------------------------------------------------------
# manual_goal_utils helpers
# ---------------------------------------------------------------------------

class TestMakeReadonly:
    def test_removes_write_permission(self, tmp_path):
        f = tmp_path / "test.txt"
        f.write_text("hello")
        make_readonly(f)
        mode = f.stat().st_mode
        assert not (mode & stat.S_IWUSR)
        assert not (mode & stat.S_IWGRP)
        assert not (mode & stat.S_IWOTH)

    def test_idempotent(self, tmp_path):
        f = tmp_path / "test.txt"
        f.write_text("hello")
        make_readonly(f)
        mode1 = f.stat().st_mode
        make_readonly(f)
        mode2 = f.stat().st_mode
        assert mode1 == mode2


class TestSetupLibCopy:
    def test_readonly_copy(self, tmp):
        lib = tmp / "foo_rel_lib.v"
        work = tmp / "workdir"
        work.mkdir()
        dest = setup_lib_copy(work, lib, readonly=True)
        assert dest.exists()
        assert not dest.is_symlink()
        assert dest.read_text(encoding="utf-8") == lib.read_text(encoding="utf-8")
        assert not (dest.stat().st_mode & stat.S_IWUSR)

    def test_writable_copy(self, tmp):
        lib = tmp / "foo_rel_lib.v"
        work = tmp / "workdir"
        work.mkdir()
        dest = setup_lib_copy(work, lib, readonly=False)
        assert dest.exists()
        assert not dest.is_symlink()
        assert (dest.stat().st_mode & stat.S_IWUSR)

    def test_edits_do_not_reach_original(self, tmp):
        lib = tmp / "foo_rel_lib.v"
        work = tmp / "workdir"
        work.mkdir()
        dest = setup_lib_copy(work, lib)
        dest.write_text("edited")
        assert lib.read_text() != "edited"

    def test_replaces_existing(self, tmp):
        lib = tmp / "foo_rel_lib.v"
        work = tmp / "workdir"
        work.mkdir()
        (work / "lib").mkdir()
        (work / "lib" / lib.name).write_text("old")
        dest = setup_lib_copy(work, lib)
        assert dest.read_text(encoding="utf-8") == lib.read_text(encoding="utf-8")


class TestCopyCoqproject:
    def test_copies_readonly(self, tmp):
        work = tmp / "workdir"
        work.mkdir()
        dest = copy_coqproject(work, tmp)
        assert dest.exists()
        text = dest.read_text(encoding="utf-8")
        assert f"-Q {tmp.resolve()} MyLib" in text
        assert not (dest.stat().st_mode & stat.S_IWUSR)


class TestSimpleCCaseDependencyParsing:
    def test_normalizes_first_require_command_when_line_has_import_command(self):
        assert require_import_lines(
            "Require Import SetsClass.SetsClass. Import SetsNotation.\n"
        ) == ["Require Import SetsClass.SetsClass."]

    def test_parses_multi_module_require_import(self):
        text = (
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_goal "
            "SimpleC.EE.QCP_demos_LLM.foo_lib Coq.Lists.List.\n"
            "From SimpleC.EE.QCP_demos_LLM Require Import bar_goal bar_lib.\n"
        )
        assert simplec_case_dependency_modules(text) == [
            "SimpleC.EE.QCP_demos_LLM.foo_goal",
            "SimpleC.EE.QCP_demos_LLM.foo_lib",
            "SimpleC.EE.QCP_demos_LLM.bar_goal",
            "SimpleC.EE.QCP_demos_LLM.bar_lib",
        ]

    def test_case_deps_seed_is_copied_and_remapped(self, tmp_path):
        seed_root = tmp_path / "base" / "case_deps"
        seed_module_dir = seed_root / "QCP_demos_LLM"
        seed_module_dir.mkdir(parents=True)
        seed_file = seed_module_dir / "foo_goal.v"
        seed_file.write_text("Definition x := 1.\n", encoding="utf-8")
        seed_file.with_suffix(".vo").write_text("compiled", encoding="utf-8")
        seed = {
            "root": str(seed_root),
            "flags": ["-Q", str(seed_module_dir), "SimpleC.EE.QCP_demos_LLM"],
            "files": [str(seed_file)],
            "modules": ["SimpleC.EE.QCP_demos_LLM.foo_goal"],
            "module_map": {"SimpleC.EE.QCP_demos_LLM.foo_goal": str(seed_file)},
            "task_local_scratch_lib_module": None,
            "task_local_scratch_lib_modules": [],
            "task_local_scratch_lib_files": [],
        }
        work = tmp_path / "group"
        work.mkdir()

        copied = _case_deps_from_seed(work, seed)

        assert copied is not None
        copied_file = work / "case_deps" / "QCP_demos_LLM" / "foo_goal.v"
        assert copied_file.is_file()
        assert copied_file.with_suffix(".vo").is_file()
        assert copied["files"] == [str(copied_file.resolve())]
        assert copied["module_map"]["SimpleC.EE.QCP_demos_LLM.foo_goal"] == str(
            copied_file.resolve()
        )
        assert str((work / "case_deps" / "QCP_demos_LLM").resolve()) in copied["flags"]
        assert copied["cache_mode"] == "copied_from_base_overlay"


class TestCopyTutorial:
    def test_copies_single_file_readonly(self, tmp_path):
        tutorial = tmp_path / "tutorial.md"
        tutorial.write_text("# Tutorial\n")
        work = tmp_path / "workdir"
        work.mkdir()
        copied = copy_tutorial(work, tutorial)
        assert len(copied) == 1
        assert copied[0].exists()
        assert copied[0].read_text() == "# Tutorial\n"
        assert not (copied[0].stat().st_mode & stat.S_IWUSR)

    def test_copies_directory_of_md_files(self, tmp_path):
        src = tmp_path / "tutorials"
        src.mkdir()
        (src / "a.md").write_text("a")
        (src / "b.md").write_text("b")
        (src / "c.md").write_text("c")
        (src / "ignore.txt").write_text("ignore")  # non-md should be skipped
        work = tmp_path / "workdir"
        work.mkdir()
        copied = copy_tutorial(work, src)
        assert len(copied) == 3
        names = {p.name for p in copied}
        assert names == {"a.md", "b.md", "c.md"}
        for p in copied:
            assert not (p.stat().st_mode & stat.S_IWUSR)

    def test_missing_tutorial_returns_empty(self, tmp_path):
        work = tmp_path / "workdir"
        work.mkdir()
        copied = copy_tutorial(work, tmp_path / "nonexistent.md")
        assert copied == []


class TestGenerateRocqMcpConfig:
    @patch("shutil.which", return_value="/usr/bin/rocq-mcp")
    def test_creates_config(self, mock_which, tmp_path):
        work = tmp_path / "workdir"
        work.mkdir()
        result = generate_rocq_mcp_config(work, tmp_path)
        assert result is not None
        assert result.exists()
        content = result.read_text()
        assert "rocq-mcp" in content
        assert str(tmp_path) in content

    @patch("shutil.which", return_value=None)
    def test_returns_none_when_not_found(self, mock_which, tmp_path):
        work = tmp_path / "workdir"
        work.mkdir()
        result = generate_rocq_mcp_config(work, tmp_path)
        assert result is None


class TestBuildCompileCmd:
    def test_basic(self):
        cmd = build_compile_cmd(Path("/project"), ["-Q", ".", "MyLib"], "<goal.v>")
        assert cmd == "coqc -Q /project MyLib <goal.v>"

    def test_relative_load_paths_are_absolutized(self):
        cmd = build_compile_cmd(
            Path("/project"),
            ["-Q", "libs", "Lib", "-R", "deps", "DepLib", "-I", "include"],
            "<goal.v>",
        )
        assert cmd == (
            "coqc -Q /project/libs Lib -R /project/deps DepLib "
            "-I /project/include <goal.v>"
        )

    def test_empty_logical_names_are_shell_quoted(self):
        cmd = build_compile_cmd(
            Path("/project"),
            ["-Q", "libs", "", "-Q", "vcs", ""],
            "<goal.v>",
        )
        assert cmd == "coqc -Q /project/libs '' -Q /project/vcs '' <goal.v>"


class TestSimpleCCaseDependencies:
    def test_parses_goal_and_lib_imports(self):
        text = (
            "From SimpleC.EE.QCP_demos_LLM Require Import sortArray3_goal.\n"
            "Require Import SimpleC.EE.QCP_demos_LLM.sortArray3_lib.\n"
            "Require Import Coq.Lists.List.\n"
        )
        assert simplec_case_dependency_modules(text) == [
            "SimpleC.EE.QCP_demos_LLM.sortArray3_goal",
            "SimpleC.EE.QCP_demos_LLM.sortArray3_lib",
        ]


# ---------------------------------------------------------------------------
# prepare_group_workdir: prepare_group (adaptive single-pass)
# ---------------------------------------------------------------------------

class TestPrepareGroup:
    def test_creates_work_dir(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        assert work.is_dir()

    def test_copies_all_goal_files(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        for entry in goal_files:
            src = Path(str(entry["split_rocq_file"])).resolve()
            dest = work / src.name
            assert dest.exists()
            assert not dest.is_symlink()
            assert dest.read_text(encoding="utf-8") == src.read_text(encoding="utf-8")

    def test_does_not_copy_common_lib(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        assert not (work / "lib" / "foo_rel_lib.v").exists()
        assert not (work / "case_deps").exists()

    def test_creates_worker_helper_scratch_lib(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        helper_lib = work / "worker_helper" / "worker_helper_scratch_lib.v"
        assert helper_lib.exists()
        assert "worker_helper_scratch_lib helper lemmas go below" in helper_lib.read_text(encoding="utf-8")
        assert helper_lib.stat().st_mode & stat.S_IWUSR

    def test_worker_manual_imports_helper_lib(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        worker_manual = work / "foo_manual.v"
        text = worker_manual.read_text(encoding="utf-8")
        assert "From VCWorker Require Import worker_helper_scratch_lib." in text

    def test_agents_md_lists_all_goals(self, tmp, goal_files):
        """Adaptive agent sees every assigned goal at once."""
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        for entry in goal_files:
            name = Path(str(entry["split_rocq_file"])).name
            assert name in agents_md

    def test_agents_md_has_proof_group_instructions(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "Proof Group Notes" in agents_md
        assert "reuse within the group" in agents_md.lower()
        assert "representative" in agents_md.lower()

    def test_agents_md_renders_group_metadata(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(
            work,
            goal_files,
            tmp / "foo_rel_lib.v",
            tmp / "foo_manual.v",
            group_meta={
                "proof_group_id": "entail-shape",
                "grouping_source": "vc-checking-group-plan",
                "representative_witness": "proof_of_foo_entail_wit_1",
                "natural_language_proof_pattern": "same entailment frame",
                "shared_helper_candidates": ["helper_frame"],
                "proving_hints": ["solve representative first"],
                "grouping_confidence": "high",
            },
        )
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "entail-shape" in agents_md
        assert "same entailment frame" in agents_md
        assert "helper_frame" in agents_md

    def test_agents_md_has_strategy_report_instruction(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "proof_strategy_report.json" in agents_md

    def test_agents_md_forbids_browsing_compile_only_dependencies(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            f"-Q {tmp_path / 'libs'} ''\n"
            f"-R {tmp_path / 'deps'} DepLib\n",
            encoding="utf-8",
        )
        (tmp_path / "libs").mkdir()
        (tmp_path / "deps").mkdir()
        lib = tmp_path / "foo_rel_lib.v"
        lib.write_text("Definition foo := 1.\n", encoding="utf-8")
        src = tmp_path / "foo_manual.v"
        src.write_text("Lemma a : True.\nProof. auto. Qed.\n", encoding="utf-8")
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text("Lemma proof_of_foo : True.\nProof. Admitted.\n", encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 1,
            "original_end_line": 2,
        }]

        work = tmp_path / "group_0"
        prepare_group(work, goals, lib, src)

        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "compile-only dependencies" in agents_md
        assert str(tmp_path / "libs") in agents_md
        assert str(tmp_path / "deps") in agents_md
        assert "Do NOT inspect compile-only dependency paths" in agents_md
        assert "rg \"lemma_name\"" in agents_md
        assert f"-Q {tmp_path / 'libs'} " in agents_md
        assert "cd " not in agents_md

    def test_agents_md_has_timeout_based_stopping_policy(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "Keep proving until every assigned goal is solved" in agents_md
        assert "process timeout stops you" in agents_md
        assert "proof-obligation defect" in agents_md
        assert "attempts per goal" not in agents_md

    def test_agents_md_lib_readonly(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "Do NOT modify" in agents_md
        assert "worker_helper_scratch_lib.v" in agents_md

    def test_agents_md_admitted_fallback(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "Admitted." in agents_md

    def test_returns_group_manifest(self, tmp, goal_files):
        work = tmp / "group_0"
        result = prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        assert result["goals"] == goal_files
        assert "max_retries" not in result
        assert result["work_dir"] == str(work)
        assert "coqproject_root" in result
        assert "coqc_flags" in result

    def test_coqproject_copied(self, tmp, goal_files):
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        assert (work / "_CoqProject").exists()

    def test_no_wave_terminology(self, tmp, goal_files):
        """Adaptive AGENTS.md should not mention 'Wave 1' or 'Wave 2' anymore."""
        work = tmp / "group_0"
        prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "Wave 1" not in agents_md
        assert "Wave 2" not in agents_md

    def test_default_enables_rocq_mcp(self, tmp, goal_files):
        """Default should instruct the agent to use rocq-mcp."""
        work = tmp / "group_0"
        result = prepare_group(work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v")
        assert result["use_rocq_mcp"] is True
        assert result["worker_execution_mode"] == "rocq_mcp"
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "rocq-mcp" in agents_md

    def test_can_disable_rocq_mcp(self, tmp, goal_files):
        """use_rocq_mcp=False should leave the agent in coqc-only mode."""
        work = tmp / "group_0"
        result = prepare_group(
            work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v",
            use_rocq_mcp=False,
        )
        assert result["use_rocq_mcp"] is False
        assert result["worker_execution_mode"] == "coqc_only"
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "Show." in agents_md
        assert "Search" in agents_md

    def test_use_rocq_mcp_true_writes_config(self, tmp, goal_files):
        """use_rocq_mcp=True should mention rocq-mcp in AGENTS.md."""
        work = tmp / "group_0"
        result = prepare_group(
            work, goal_files, tmp / "foo_rel_lib.v", tmp / "foo_manual.v",
            use_rocq_mcp=True,
        )
        assert result["use_rocq_mcp"] is True
        agents_md = (work / "AGENTS.md").read_text(encoding="utf-8")
        assert "rocq-mcp" in agents_md

    def test_creates_readonly_normalized_simplec_case_dependency_overlay(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "QCP_demos_LLM"
        case_dir.mkdir(parents=True)
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_lib.\n"
            "Lemma generated_goal : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "foo__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        src = tmp_path / "foo__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "From SimpleC.EE.QCP_demos_LLM Require Import foo_goal.\n"
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_lib.\n\n"
            "Lemma proof_of_foo : True.\nProof. Admitted.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 3,
            "original_end_line": 4,
        }]

        work = tmp_path / "group_0"
        result = prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        dep_goal = work / "case_deps" / "QCP_demos_LLM" / "foo_goal.v"
        dep_lib = work / "case_deps" / "QCP_demos_LLM" / "foo_lib.v"
        assert dep_goal.exists()
        assert dep_lib.exists()
        assert dep_goal.with_suffix(".vo").exists()
        assert dep_lib.with_suffix(".vo").exists()
        assert not (dep_goal.stat().st_mode & stat.S_IWUSR)
        assert not (dep_lib.stat().st_mode & stat.S_IWUSR)
        assert "task_local_scratch_lib_marker" in dep_lib.read_text(encoding="utf-8")
        assert result["case_dependency_modules"] == [
            "SimpleC.EE.QCP_demos_LLM.foo_goal",
            "SimpleC.EE.QCP_demos_LLM.foo_lib",
        ]
        assert result["case_dependency_module_map"] == {
            "SimpleC.EE.QCP_demos_LLM.foo_goal": str(dep_goal),
            "SimpleC.EE.QCP_demos_LLM.foo_lib": str(dep_lib),
        }
        assert result["dependency_mode"] == "worker_case_dependency_overlay"
        assert (work / "worker_helper" / "worker_helper_scratch_lib.v").exists()
        coqproject = (work / "_CoqProject").read_text(encoding="utf-8")
        assert "case_deps/QCP_demos_LLM SimpleC.EE.QCP_demos_LLM" in coqproject
        assert f"-Q {work.resolve()} VCWorker" not in coqproject
        assert f"-Q {(work / 'worker_helper').resolve()} VCWorker" in coqproject
        assert "VCWorker" in coqproject
        assert "examples SimpleC.EE" not in coqproject

    def test_overlay_preserves_shared_lib_imports(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "QCP_demos_LLM"
        case_dir.mkdir(parents=True)
        (case_dir / "shared_lib.v").write_text(
            "Lemma shared_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        current_lib_text = (
            "Require Import SimpleC.EE.QCP_demos_LLM.shared_lib.\n"
            "Lemma task_local_scratch_lib_marker : True.\n"
            "Proof. exact shared_marker. Qed.\n"
        )
        (case_dir / "foo_lib.v").write_text(current_lib_text, encoding="utf-8")
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_lib.\n"
            "Lemma generated_goal : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "foo__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(current_lib_text, encoding="utf-8")
        src = tmp_path / "foo__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "From SimpleC.EE.QCP_demos_LLM Require Import foo_goal.\n"
            "Require Import SimpleC.EE.QCP_demos_LLM.shared_lib.\n"
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_lib.\n\n"
            "Lemma proof_of_foo : True.\nProof. Admitted.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 4,
            "original_end_line": 5,
        }]

        work = tmp_path / "group_0"
        result = prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        dep_shared = work / "case_deps" / "QCP_demos_LLM" / "shared_lib.v"
        dep_current = work / "case_deps" / "QCP_demos_LLM" / "foo_lib.v"
        assert dep_shared.exists()
        assert dep_current.exists()
        assert "shared_marker" in dep_shared.read_text(encoding="utf-8")
        assert "task_local_scratch_lib_marker" in dep_current.read_text(encoding="utf-8")
        assert result["case_dependency_task_local_scratch_lib_modules"] == [
            "SimpleC.EE.QCP_demos_LLM.foo_lib",
        ]
        assert result["case_dependency_task_local_scratch_lib_files"] == [
            str(dep_current),
        ]
        compiled = [path.name for path in sorted(work.rglob("*.vo"))]
        assert "shared_lib.vo" in compiled
        assert "foo_lib.vo" in compiled
        assert "foo_goal.vo" in compiled

    def test_overlay_follows_goal_import_to_task_local_scratch_lib(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "QCP_demos_LLM"
        case_dir.mkdir(parents=True)
        (case_dir / "foo_lib.v").write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_lib.\n"
            "Lemma generated_goal : True.\nProof. exact task_local_scratch_lib_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "foo__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        src = tmp_path / "foo__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "From SimpleC.EE.QCP_demos_LLM Require Import foo_goal.\n\n"
            "Lemma proof_of_foo : True.\nProof. Admitted.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 3,
            "original_end_line": 4,
        }]

        work = tmp_path / "group_0"
        result = prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        dep_goal = work / "case_deps" / "QCP_demos_LLM" / "foo_goal.v"
        dep_lib = work / "case_deps" / "QCP_demos_LLM" / "foo_lib.v"
        assert dep_goal.with_suffix(".vo").exists()
        assert dep_lib.with_suffix(".vo").exists()
        assert result["case_dependency_modules"] == [
            "SimpleC.EE.QCP_demos_LLM.foo_goal",
            "SimpleC.EE.QCP_demos_LLM.foo_lib",
        ]
        assert result["case_dependency_task_local_scratch_lib_modules"] == [
            "SimpleC.EE.QCP_demos_LLM.foo_lib",
        ]

    def test_overlay_uses_standard_scratch_name_when_lib_contents_match(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "QCP_demos_LLM"
        case_dir.mkdir(parents=True)
        same_text = "Lemma same_marker : True.\nProof. exact I. Qed.\n"
        (case_dir / "shared_lib.v").write_text(same_text, encoding="utf-8")
        (case_dir / "foo_lib.v").write_text(same_text, encoding="utf-8")
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_lib.\n"
            "Lemma generated_goal : True.\nProof. exact same_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "foo__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(same_text, encoding="utf-8")
        src = tmp_path / "foo__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "Require Import SimpleC.EE.QCP_demos_LLM.shared_lib.\n"
            "From SimpleC.EE.QCP_demos_LLM Require Import foo_goal.\n\n"
            "Lemma proof_of_foo : True.\nProof. Admitted.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 4,
            "original_end_line": 5,
        }]

        result = prepare_group(
            tmp_path / "group_0",
            goals,
            task_local_scratch_lib,
            src,
            use_rocq_mcp=False,
        )

        assert result["case_dependency_task_local_scratch_lib_modules"] == [
            "SimpleC.EE.QCP_demos_LLM.foo_lib",
        ]

    def test_overlay_copies_generated_strategy_support_imports(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "CurrentCase"
        case_dir.mkdir(parents=True)
        strategy_dir = tmp_path / "examples" / "QCP_demos_LLM"
        strategy_dir.mkdir(parents=True)
        (strategy_dir / "int_array_strategy_proof.v").write_text(
            "Lemma strategy_proof_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (strategy_dir / "int_array_strategy_goal.v").write_text(
            "Require Import SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof.\n"
            "Lemma strategy_goal_marker : True.\nProof. exact strategy_proof_marker. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "foo_lib.v").write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.CurrentCase.foo_lib.\n"
            "From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal int_array_strategy_proof.\n"
            "Lemma generated_goal : True.\nProof. exact strategy_goal_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "foo__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        src = tmp_path / "foo__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "From SimpleC.EE.CurrentCase Require Import foo_goal.\n\n"
            "Lemma proof_of_foo : True.\nProof. exact generated_goal. Qed.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 3,
            "original_end_line": 4,
        }]

        work = tmp_path / "group_0"
        result = prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        dep_strategy_goal = work / "case_deps" / "QCP_demos_LLM" / "int_array_strategy_goal.v"
        dep_strategy_proof = work / "case_deps" / "QCP_demos_LLM" / "int_array_strategy_proof.v"
        assert dep_strategy_goal.with_suffix(".vo").exists()
        assert dep_strategy_proof.with_suffix(".vo").exists()
        assert "SimpleC.EE.QCP_demos_LLM.int_array_strategy_goal" in result["case_dependency_modules"]
        assert "SimpleC.EE.QCP_demos_LLM.int_array_strategy_proof" in result["case_dependency_modules"]

    def test_overlay_copies_direct_simplec_helper_imports(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        helper_dir = tmp_path / "examples" / "Applications_human" / "typeinfer"
        helper_dir.mkdir(parents=True)
        (helper_dir / "sound_pv.v").write_text(
            "Lemma sound_pv_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "CurrentCase"
        case_dir.mkdir(parents=True)
        (case_dir / "foo_lib.v").write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.CurrentCase.foo_lib.\n"
            "Lemma generated_goal : True.\nProof. exact task_local_scratch_lib_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "foo__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        src = tmp_path / "foo__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "Require Import SimpleC.EE.Applications_human.typeinfer.sound_pv.\n"
            "From SimpleC.EE.CurrentCase Require Import foo_goal.\n\n"
            "Lemma proof_of_foo : True.\nProof. exact sound_pv_marker. Qed.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 4,
            "original_end_line": 5,
        }]

        work = tmp_path / "group_0"
        result = prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        dep_helper = work / "case_deps" / "Applications_human" / "typeinfer" / "sound_pv.v"
        assert dep_helper.with_suffix(".vo").exists()
        assert "SimpleC.EE.Applications_human.typeinfer.sound_pv" in result["case_dependency_modules"]
        assert "examples SimpleC.EE" not in (work / "_CoqProject").read_text(encoding="utf-8")

    def test_overlay_copies_case_local_bare_string_strategy_imports(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "LLM_bench" / "Engineering" / "string"
        case_dir.mkdir(parents=True)
        (case_dir / "string_strategy_goal.v").write_text(
            "Lemma string_goal_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "string_strategy_proof.v").write_text(
            "From SimpleC.EE.LLM_bench.Engineering.string Require Import string_strategy_goal.\n"
            "Lemma string_proof_marker : True.\nProof. exact string_goal_marker. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "memchr_lib.v").write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "memchr_goal.v").write_text(
            "Require Import SimpleC.EE.LLM_bench.Engineering.string.memchr_lib.\n"
            "Require Import string_strategy_goal.\n"
            "Require Import string_strategy_proof.\n"
            "Lemma generated_goal : True.\nProof. exact string_proof_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "memchr__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        src = tmp_path / "memchr__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "From SimpleC.EE.LLM_bench.Engineering.string Require Import memchr_goal.\n\n"
            "Lemma proof_of_memchr : True.\nProof. exact generated_goal. Qed.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_memchr.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_memchr",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_memchr : True.",
            "original_start_line": 3,
            "original_end_line": 4,
        }]

        work = tmp_path / "group_0"
        result = prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        bare_goal = work / "case_deps" / "bare" / "string_strategy_goal.v"
        bare_proof = work / "case_deps" / "bare" / "string_strategy_proof.v"
        namespaced_goal = (
            work / "case_deps" / "LLM_bench" / "Engineering" / "string"
            / "string_strategy_goal.v"
        )
        assert bare_goal.with_suffix(".vo").exists()
        assert bare_proof.with_suffix(".vo").exists()
        assert namespaced_goal.with_suffix(".vo").exists()
        assert "string_strategy_goal" in result["case_dependency_modules"]
        assert "string_strategy_proof" in result["case_dependency_modules"]
        assert (
            "SimpleC.EE.LLM_bench.Engineering.string.string_strategy_goal"
            in result["case_dependency_modules"]
        )
        coqproject = (work / "_CoqProject").read_text(encoding="utf-8")
        assert "case_deps/bare ''" in coqproject
        assert "examples SimpleC.EE" not in coqproject

    def test_overlay_copies_qcp_llm_bare_strategy_without_human_duplicate(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        qcp_dir = tmp_path / "examples" / "QCP_demos_LLM"
        qcp_dir.mkdir(parents=True)
        human_dir = tmp_path / "examples" / "QCP_demos_human"
        human_dir.mkdir(parents=True)
        (qcp_dir / "int_array_strategy_goal.v").write_text(
            "Lemma strategy_goal_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (qcp_dir / "int_array_strategy_proof.v").write_text(
            "From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.\n"
            "Lemma strategy_proof_marker : True.\nProof. exact strategy_goal_marker. Qed.\n",
            encoding="utf-8",
        )
        (human_dir / "int_array_strategy_goal.v").write_text(
            "Lemma human_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "LLM_bench" / "Algorithms" / "super_piano"
        case_dir.mkdir(parents=True)
        (case_dir / "super_piano_lib.v").write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "super_piano_goal.v").write_text(
            "Require Import SimpleC.EE.LLM_bench.Algorithms.super_piano.super_piano_lib.\n"
            "Require Import int_array_strategy_goal.\n"
            "Require Import int_array_strategy_proof.\n"
            "Lemma generated_goal : True.\nProof. exact strategy_proof_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "super_piano__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        src = tmp_path / "super_piano__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "From SimpleC.EE.LLM_bench.Algorithms.super_piano Require Import super_piano_goal.\n\n"
            "Lemma proof_of_super_piano : True.\nProof. exact generated_goal. Qed.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_super_piano.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_super_piano",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_super_piano : True.",
            "original_start_line": 3,
            "original_end_line": 4,
        }]

        work = tmp_path / "group_0"
        result = prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        bare_goal = work / "case_deps" / "bare" / "int_array_strategy_goal.v"
        bare_proof = work / "case_deps" / "bare" / "int_array_strategy_proof.v"
        qcp_goal = work / "case_deps" / "QCP_demos_LLM" / "int_array_strategy_goal.v"
        assert bare_goal.with_suffix(".vo").exists()
        assert bare_proof.with_suffix(".vo").exists()
        assert qcp_goal.with_suffix(".vo").exists()
        assert "human_marker" not in bare_goal.read_text(encoding="utf-8")
        assert "int_array_strategy_goal" in result["case_dependency_modules"]
        assert "SimpleC.EE.QCP_demos_LLM.int_array_strategy_goal" in result["case_dependency_modules"]

    def test_explicit_task_local_module_resolves_ambiguous_lib_mapping(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "CurrentCase"
        case_dir.mkdir(parents=True)
        same_text = "Lemma shared_marker : True.\nProof. exact I. Qed.\n"
        (case_dir / "shared_lib.v").write_text(same_text, encoding="utf-8")
        (case_dir / "foo_lib.v").write_text(same_text, encoding="utf-8")
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.CurrentCase.foo_lib.\n"
            "Lemma generated_goal : True.\nProof. exact shared_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "scratch_lib.v"
        task_local_scratch_lib.write_text(same_text, encoding="utf-8")
        src = tmp_path / "scratch_manual.v"
        src.write_text(
            "Require Import SimpleC.EE.CurrentCase.shared_lib.\n"
            "From SimpleC.EE.CurrentCase Require Import foo_goal.\n\n"
            "Lemma proof_of_foo : True.\nProof. exact generated_goal. Qed.\n",
            encoding="utf-8",
        )
        work = tmp_path / "group_0"

        result = prepare_simplec_case_dependencies(
            work_dir=work,
            source_file=src,
            lib_file=task_local_scratch_lib,
            coqproject_root=tmp_path,
            coqc_flags=["-Q", "examples", "SimpleC.EE"],
            task_local_logical_module="SimpleC.EE.CurrentCase.foo_lib",
        )

        assert result["task_local_scratch_lib_module"] == "SimpleC.EE.CurrentCase.foo_lib"
        assert result["task_local_scratch_lib_files"] == [
            str(work / "case_deps" / "CurrentCase" / "foo_lib.v")
        ]

    def test_prepare_clears_stale_case_deps(self, tmp_path):
        (tmp_path / "_CoqProject").write_text(
            "-Q examples SimpleC.EE\n",
            encoding="utf-8",
        )
        case_dir = tmp_path / "examples" / "QCP_demos_LLM"
        case_dir.mkdir(parents=True)
        (case_dir / "foo_lib.v").write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        (case_dir / "foo_goal.v").write_text(
            "Require Import SimpleC.EE.QCP_demos_LLM.foo_lib.\n"
            "Lemma generated_goal : True.\nProof. exact task_local_scratch_lib_marker. Qed.\n",
            encoding="utf-8",
        )
        task_local_scratch_lib = tmp_path / "foo__vc_proving_subagent_tmp_lib.v"
        task_local_scratch_lib.write_text(
            "Lemma task_local_scratch_lib_marker : True.\nProof. exact I. Qed.\n",
            encoding="utf-8",
        )
        src = tmp_path / "foo__vc_proving_subagent_tmp_proof_manual.v"
        src.write_text(
            "From SimpleC.EE.QCP_demos_LLM Require Import foo_goal.\n\n"
            "Lemma proof_of_foo : True.\nProof. exact generated_goal. Qed.\n",
            encoding="utf-8",
        )
        goal = tmp_path / "goal_01__proof_of_foo.v"
        goal.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
        goals = [{
            "index": 1,
            "name": "proof_of_foo",
            "split_rocq_file": str(goal),
            "statement_header": "Lemma proof_of_foo : True.",
            "original_start_line": 3,
            "original_end_line": 4,
        }]
        work = tmp_path / "group_0"
        stale = work / "case_deps" / "QCP_demos_LLM" / "stale_goal.v"
        stale.parent.mkdir(parents=True)
        stale.write_text("Lemma stale : True.\nProof. exact I. Qed.\n", encoding="utf-8")

        prepare_group(work, goals, task_local_scratch_lib, src, use_rocq_mcp=False)

        assert not stale.exists()
