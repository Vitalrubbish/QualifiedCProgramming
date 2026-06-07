#!/usr/bin/env python3
"""Validate that an annotation round is eligible for main-owned symexec."""

from __future__ import annotations

import argparse
import json
import re
import shlex
import subprocess
import sys
from pathlib import Path

FIELD_RE = re.compile(r"^\s*-\s+([A-Za-z0-9_]+):\s*(.*)$")
TRUE_PREFIXES = ("yes", "passed", "true")


def parse_markdown_fields(path: Path) -> dict[str, str]:
    fields: dict[str, str] = {}
    in_code_block = False
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        stripped = raw_line.strip()
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue
        match = FIELD_RE.match(raw_line)
        if match:
            key, value = match.groups()
            fields[key] = value.strip()
    return fields


def is_truthy(value: str | None) -> bool:
    if value is None:
        return False
    lowered = value.strip().lower()
    return lowered.startswith(TRUE_PREFIXES)


def parse_coqproject_args(path: Path) -> list[str]:
    args: list[str] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        args.extend(shlex.split(line))
    return args


def run_coqc_gate(
    scratch_lib: Path,
    coqproject: Path,
    *,
    coqc_bin: str = "coqc",
) -> tuple[bool, str]:
    cmd = [coqc_bin, *parse_coqproject_args(coqproject), str(scratch_lib)]
    proc = subprocess.run(
        cmd,
        cwd=str(coqproject.parent),
        capture_output=True,
        text=True,
        check=False,
    )
    output = "\n".join(part for part in (proc.stdout.strip(), proc.stderr.strip()) if part).strip()
    return proc.returncode == 0, output


def validate_annotation_gate(
    *,
    subagent_report: Path,
    checking_report: Path,
    scratch_lib: Path | None = None,
    coqproject: Path | None = None,
    coqc_bin: str = "coqc",
) -> dict[str, object]:
    subagent_fields = parse_markdown_fields(subagent_report)
    checking_fields = parse_markdown_fields(checking_report)

    errors: list[str] = []

    if subagent_fields.get("round_outcome", "").strip().lower() != "completed":
        errors.append("subagent round_outcome must be `completed`.")
    if subagent_fields.get("annotation_checking_status", "").strip().lower() != "passed":
        errors.append("subagent annotation_checking_status must be `passed`.")
    if checking_fields.get("status", "").strip().lower() != "passed":
        errors.append("annotation-checking report status must be `passed`.")
    if not is_truthy(checking_fields.get("ready_for_main_symexec")):
        errors.append("annotation-checking report ready_for_main_symexec must be truthy.")

    qcp_field = checking_fields.get("qcp_mcp_requirement_satisfied")
    if qcp_field is None:
        qcp_field = subagent_fields.get("qcp_mcp_requirement_satisfied")
    if qcp_field is None:
        errors.append("missing qcp_mcp_requirement_satisfied field.")
    elif not is_truthy(qcp_field):
        errors.append("qcp_mcp_requirement_satisfied must be truthy.")

    coqc_status = checking_fields.get("annotation_scratch_lib_coqc_status")
    if coqc_status is None:
        coqc_status = subagent_fields.get("annotation_scratch_lib_coqc_status")
    if coqc_status is None:
        errors.append("missing annotation_scratch_lib_coqc_status field.")
    elif not is_truthy(coqc_status):
        errors.append("annotation_scratch_lib_coqc_status must be truthy.")

    coqc_ran = False
    coqc_ok = None
    coqc_output = ""
    if scratch_lib is not None or coqproject is not None:
        if scratch_lib is None or coqproject is None:
            errors.append("scratch_lib and coqproject must be provided together.")
        else:
            coqc_ran = True
            coqc_ok, coqc_output = run_coqc_gate(scratch_lib, coqproject, coqc_bin=coqc_bin)
            if not coqc_ok:
                errors.append("annotation_scratch_lib coqc gate failed.")

    return {
        "ok": not errors,
        "errors": errors,
        "subagent_report": str(subagent_report),
        "checking_report": str(checking_report),
        "qcp_mcp_requirement_satisfied": qcp_field,
        "annotation_scratch_lib_coqc_status": coqc_status,
        "coqc_ran": coqc_ran,
        "coqc_ok": coqc_ok,
        "coqc_output": coqc_output,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate that an annotation round may enter main-owned symexec / goal-frozen."
    )
    parser.add_argument("--subagent-report", required=True, type=Path)
    parser.add_argument("--checking-report", required=True, type=Path)
    parser.add_argument("--annotation-scratch-lib", type=Path, default=None)
    parser.add_argument("--coqproject", type=Path, default=None)
    parser.add_argument("--coqc-bin", default="coqc")
    parser.add_argument("--json", action="store_true", help="Print machine-readable JSON.")
    args = parser.parse_args(argv)

    result = validate_annotation_gate(
        subagent_report=args.subagent_report,
        checking_report=args.checking_report,
        scratch_lib=args.annotation_scratch_lib,
        coqproject=args.coqproject,
        coqc_bin=args.coqc_bin,
    )

    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=True))
    else:
        if result["ok"]:
            print("annotation gate: PASS")
        else:
            print("annotation gate: FAIL")
            for error in result["errors"]:
                print(f"- {error}")
        if result["coqc_ran"]:
            verdict = "passed" if result["coqc_ok"] else "failed"
            print(f"annotation_scratch_lib coqc gate: {verdict}")
            if result["coqc_output"]:
                print(result["coqc_output"])
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
