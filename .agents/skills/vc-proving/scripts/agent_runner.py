#!/usr/bin/env python3
"""Run one sandboxed Codex worker in one concurrent vc-proving work directory.

The concurrent runner invokes this once per prepared group; the actual
subprocess invocation, sandbox flags, timeout handling, and Ctrl-C cleanup live
here.
"""

from __future__ import annotations

import os
import json
import signal
import shutil
import subprocess
import sys
from pathlib import Path

WORKER_MODE_ROCQ_MCP = "rocq_mcp"
WORKER_MODE_COQC_ONLY = "coqc_only"
WORKER_EXECUTION_MODES = {WORKER_MODE_ROCQ_MCP, WORKER_MODE_COQC_ONLY}
LEGACY_FALSE_VALUES = {"0", "false", "no", "off", "coqc_only"}


def normalize_worker_execution_mode(
    worker_execution_mode: str | None = None,
    *,
    use_rocq_mcp: object | None = None,
) -> str:
    """Return the canonical worker execution mode.

    ``worker_execution_mode`` is the authoritative field written to manifests.
    ``use_rocq_mcp`` is accepted only for backwards compatibility with older
    manifests and tests.
    """
    if worker_execution_mode is not None:
        mode = str(worker_execution_mode).strip()
        if mode not in WORKER_EXECUTION_MODES:
            raise ValueError(
                "unknown worker_execution_mode "
                f"{worker_execution_mode!r}; expected one of "
                + ", ".join(sorted(WORKER_EXECUTION_MODES))
            )
        return mode
    return (
        WORKER_MODE_ROCQ_MCP
        if legacy_use_rocq_mcp_enabled(use_rocq_mcp)
        else WORKER_MODE_COQC_ONLY
    )


def legacy_use_rocq_mcp_enabled(use_rocq_mcp: object | None) -> bool:
    if use_rocq_mcp is None:
        return True
    if isinstance(use_rocq_mcp, bool):
        return use_rocq_mcp
    return str(use_rocq_mcp).strip().lower() not in LEGACY_FALSE_VALUES


def worker_mode_uses_rocq_mcp(worker_execution_mode: str) -> bool:
    return normalize_worker_execution_mode(worker_execution_mode) == WORKER_MODE_ROCQ_MCP


def suppress_worker_rocq_mcp_config(work_dir: Path) -> Path | None:
    """Remove generated rocq-mcp config for a coqc-only worker run.

    Codex may read ``.codex/config.toml`` from the worker directory in addition
    to explicit CLI overrides.  When the manifest says the worker is coqc-only,
    leaving a generated rocq-mcp config in place makes the prompt/runtime mode
    drift.  The worker dir is scratch, so rename the generated config out of
    the active path and return the disabled path for diagnostics.
    """
    config_path = work_dir / ".codex" / "config.toml"
    if not config_path.is_file():
        return None
    disabled = config_path.with_name("config.toml.disabled-by-coqc-only")
    if disabled.exists():
        disabled.unlink()
    config_path.rename(disabled)
    return disabled


def build_group_prompt(
    goal_files: list[str],
    worker_manual: str | None = None,
    worker_helper_scratch_lib: str | None = None,
    proof_group_id: str | None = None,
    use_rocq_mcp: bool = True,
) -> str:
    """The prompt sent to every concurrent Codex worker."""
    if os.name == "nt":
        use_rocq_mcp = False
    goal_list = "\n".join(f"  - {f}" for f in goal_files)
    manual_line = (
        f"Put witness-proof edits in the worker-local proof manual `{worker_manual}`.\n"
        if worker_manual else
        "Put witness-proof edits in the worker-local proof manual named in AGENTS.md.\n"
    )
    helper_line = (
        f"Put reusable helper lemmas in worker_helper_scratch_lib `{worker_helper_scratch_lib}` only.\n"
        if worker_helper_scratch_lib else
        "Put reusable helper lemmas in the worker_helper_scratch_lib named in AGENTS.md only.\n"
    )
    group_line = (
        f"Solve proof group `{proof_group_id}` for the following Rocq goals:\n"
        if proof_group_id else
        "Solve the following Rocq proof group:\n"
    )
    if use_rocq_mcp:
        tooling_line = (
            "Use rocq-mcp when it is available. If any rocq-mcp call fails "
            "(including transport errors or `request_user_input is not supported in exec mode`), "
            "record the failure in proof_strategy_report.json and immediately continue "
            "with coqc/coqtop; MCP failure alone is not a proof blocker.\n"
        )
    else:
        tooling_line = (
            "rocq-mcp is disabled for this run. Use only coqc/coqtop and temporary "
            "Rocq commands such as Show, Search, Check, Print, and About for feedback.\n"
        )
    return (
        f"{group_line}"
        f"{goal_list}\n\n"
        f"{manual_line}"
        f"{helper_line}"
        f"{tooling_line}"
        f"Do not copy or modify common_case_formal_lib or goal files; use them only as compile-only dependencies.\n"
        f"Follow the Proof Group Notes and all file-boundary rules in AGENTS.md.\n"
        f"Write your results to proof_report.json and proof_strategy_report.json as instructed."
    )


def check_codex() -> str:
    """Return the path to the codex binary, or exit."""
    codex = shutil.which("codex")
    if codex is None:
        raise SystemExit("codex not found in PATH")
    return codex


def _parse_toml_scalar(value: str) -> str:
    """Parse the simple TOML scalar syntax written by manual_goal_utils."""
    value = value.strip()
    if value.startswith('"') and value.endswith('"'):
        try:
            parsed = json.loads(value)
            return str(parsed)
        except json.JSONDecodeError:
            return value[1:-1]
    return value


def _load_worker_rocq_mcp_config(work_dir: Path) -> dict[str, str] | None:
    """Load the generated worker-local rocq-mcp config, if present."""
    config_path = work_dir / ".codex" / "config.toml"
    if not config_path.is_file():
        return None

    config: dict[str, str] = {}
    in_rocq_section = False
    try:
        lines = config_path.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        print(f"WARNING: could not read {config_path}: {exc}", file=sys.stderr)
        return None

    for raw_line in lines:
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1].strip()
            in_rocq_section = section in {
                "mcp_servers.rocq-mcp",
                'mcp_servers."rocq-mcp"',
            }
            continue
        if not in_rocq_section or "=" not in line:
            continue
        key, value = line.split("=", 1)
        config[key.strip()] = _parse_toml_scalar(value.strip())

    if not config.get("command") or not config.get("cwd"):
        print(f"WARNING: incomplete rocq-mcp config in {config_path}; ignoring it",
              file=sys.stderr)
        return None
    return config


def _rocq_mcp_config_overrides(work_dir: Path, *, use_rocq_mcp: bool) -> list[str]:
    """Translate worker-local .codex/config.toml into explicit codex -c overrides."""
    if os.name == "nt":
        return []
    if not use_rocq_mcp:
        return []
    config = _load_worker_rocq_mcp_config(work_dir)
    if config is None:
        return []

    values: list[tuple[str, str]] = [
        ("command", json.dumps(config["command"])),
        ("cwd", json.dumps(config["cwd"])),
    ]
    for key in ("startup_timeout_sec", "tool_timeout_sec"):
        if key in config:
            try:
                values.append((key, str(int(config[key]))))
            except ValueError:
                print(f"WARNING: ignoring non-integer rocq-mcp {key}: {config[key]!r}",
                      file=sys.stderr)

    overrides: list[str] = []
    for key, value in values:
        overrides.extend(["-c", f"mcp_servers.rocq-mcp.{key}={value}"])
    return overrides


def run_codex_agent(
    work_dir: Path,
    prompt: str,
    timeout: int,
    *,
    codex: str | None = None,
    use_rocq_mcp: bool = True,
    worker_execution_mode: str | None = None,
) -> int:
    """Spawn one sandboxed Codex agent in *work_dir*.

    Returns the agent's exit code (or ``-1`` if it timed out / errored before
    completion). Re-raises ``KeyboardInterrupt`` after terminating the child.
    """
    if codex is None:
        codex = check_codex()
    worker_execution_mode = normalize_worker_execution_mode(
        worker_execution_mode,
        use_rocq_mcp=use_rocq_mcp,
    )
    use_rocq_mcp = worker_mode_uses_rocq_mcp(worker_execution_mode)
    if not worker_mode_uses_rocq_mcp(worker_execution_mode):
        suppress_worker_rocq_mcp_config(work_dir)
    cmd = [
        codex, "exec",
        "-C", str(work_dir),
        "--skip-git-repo-check",
        "-s", "workspace-write",
        "-c", 'sandbox_permissions=["network"]',
        "-c", "features.tool_call_mcp_elicitation=false",
        *_rocq_mcp_config_overrides(work_dir, use_rocq_mcp=use_rocq_mcp),
        "--color", "never",
        prompt,
    ]
    env = os.environ.copy()
    wrapper_dir = work_dir / "bin"
    if wrapper_dir.is_dir():
        env["PATH"] = str(wrapper_dir) + os.pathsep + env.get("PATH", "")
    proc: subprocess.Popen | None = None
    try:
        proc = subprocess.Popen(cmd, start_new_session=True, env=env)
        proc.wait(timeout=timeout)
        return proc.returncode
    except subprocess.TimeoutExpired:
        if proc is not None:
            _terminate(proc)
        print(f"Codex agent in {work_dir} timed out after {timeout}s", file=sys.stderr)
        return -1
    except KeyboardInterrupt:
        if proc is not None:
            _terminate(proc)
        raise
    except Exception as exc:
        if proc is not None:
            _terminate(proc)
        print(f"Codex agent in {work_dir} failed: {exc!r}", file=sys.stderr)
        return -1


def _terminate(proc: subprocess.Popen) -> None:
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            return
        proc.wait()
