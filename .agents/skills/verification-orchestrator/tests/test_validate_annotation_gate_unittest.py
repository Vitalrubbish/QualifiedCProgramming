import importlib.util
import os
import stat
import tempfile
import textwrap
import unittest
from pathlib import Path


SCRIPT_PATH = (
    Path(__file__).resolve().parents[1]
    / "scripts"
    / "validate_annotation_gate.py"
)
SPEC = importlib.util.spec_from_file_location("validate_annotation_gate", SCRIPT_PATH)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class ValidateAnnotationGateTests(unittest.TestCase):
    def write_report(self, root: Path, name: str, body: str) -> Path:
        path = root / name
        path.write_text(textwrap.dedent(body).strip() + "\n", encoding="utf-8")
        return path

    def write_fake_coqc(self, root: Path, exit_code: int) -> Path:
        path = root / "fake-coqc.sh"
        path.write_text(
            "#!/bin/sh\n"
            f"exit {exit_code}\n",
            encoding="utf-8",
        )
        path.chmod(path.stat().st_mode | stat.S_IXUSR)
        return path

    def write_coqproject(self, root: Path) -> Path:
        path = root / "_CoqProject"
        path.write_text("-Q . Tmp\n", encoding="utf-8")
        return path

    def write_scratch_lib(self, root: Path) -> Path:
        path = root / "scratch_lib.v"
        path.write_text("Definition ok := True.\n", encoding="utf-8")
        return path

    def test_gate_passes_when_reports_and_coqc_are_ok(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            subagent = self.write_report(
                root,
                "subagent.md",
                """
                ## Subagent Return Report
                - round_outcome: completed
                - annotation_checking_status: passed
                - qcp_mcp_requirement_satisfied: yes, via qcp-mcp loader fallback
                - annotation_scratch_lib_coqc_status: passed
                """,
            )
            checking = self.write_report(
                root,
                "checking.md",
                """
                ## Annotation Checking Report
                - status: passed
                - qcp_mcp_requirement_satisfied: yes
                - annotation_scratch_lib_coqc_status: passed
                - ready_for_main_symexec: yes
                """,
            )
            scratch_lib = self.write_scratch_lib(root)
            coqproject = self.write_coqproject(root)
            fake_coqc = self.write_fake_coqc(root, 0)

            result = MODULE.validate_annotation_gate(
                subagent_report=subagent,
                checking_report=checking,
                scratch_lib=scratch_lib,
                coqproject=coqproject,
                coqc_bin=str(fake_coqc),
            )

        self.assertTrue(result["ok"])
        self.assertEqual(result["errors"], [])
        self.assertTrue(result["coqc_ok"])

    def test_gate_rejects_missing_qcp_success(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            subagent = self.write_report(
                root,
                "subagent.md",
                """
                ## Subagent Return Report
                - round_outcome: completed
                - annotation_checking_status: passed
                - qcp_mcp_requirement_satisfied: no
                - annotation_scratch_lib_coqc_status: passed
                """,
            )
            checking = self.write_report(
                root,
                "checking.md",
                """
                ## Annotation Checking Report
                - status: passed
                - ready_for_main_symexec: yes
                - annotation_scratch_lib_coqc_status: passed
                """,
            )

            result = MODULE.validate_annotation_gate(
                subagent_report=subagent,
                checking_report=checking,
            )

        self.assertFalse(result["ok"])
        self.assertIn("qcp_mcp_requirement_satisfied must be truthy.", result["errors"])

    def test_gate_rejects_coqc_failure(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            subagent = self.write_report(
                root,
                "subagent.md",
                """
                ## Subagent Return Report
                - round_outcome: completed
                - annotation_checking_status: passed
                - qcp_mcp_requirement_satisfied: yes
                - annotation_scratch_lib_coqc_status: passed
                """,
            )
            checking = self.write_report(
                root,
                "checking.md",
                """
                ## Annotation Checking Report
                - status: passed
                - qcp_mcp_requirement_satisfied: yes
                - annotation_scratch_lib_coqc_status: passed
                - ready_for_main_symexec: yes
                """,
            )
            scratch_lib = self.write_scratch_lib(root)
            coqproject = self.write_coqproject(root)
            fake_coqc = self.write_fake_coqc(root, 1)

            result = MODULE.validate_annotation_gate(
                subagent_report=subagent,
                checking_report=checking,
                scratch_lib=scratch_lib,
                coqproject=coqproject,
                coqc_bin=str(fake_coqc),
            )

        self.assertFalse(result["ok"])
        self.assertIn("annotation_scratch_lib coqc gate failed.", result["errors"])


if __name__ == "__main__":
    unittest.main()
