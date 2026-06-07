#!/usr/bin/env python3
"""Build Task tool prompts for vc-proving-worker subagents from groups_manifest.json.

Reads groups_manifest.json (produced by prepare_agent_concurrent.py) and outputs
JSON with one entry per group containing a ready-to-use prompt string for the
Task tool to spawn a vc-proving-worker subagent.

Usage:
  python build_worker_prompts.py <groups_manifest.json>
"""

from __future__ import annotations

import json
import sys
from pathlib import Path


def build_prompt(work_dir: str, goals: list[str], proof_group_id: str,
                 worker_manual: str, worker_helper: str) -> str:
    goal_list = "\n".join(f"  - {g}" for g in goals)
    return (
        f"You are solving proof group {proof_group_id} in workdir {work_dir}.\n\n"
        f"Your assigned goals ({len(goals)} total):\n"
        f"{goal_list}\n\n"
        f"Instructions:\n"
        f"1. cd {work_dir} and read AGENTS.md. Follow ALL instructions in it exactly.\n"
        f"2. The worker-local proof manual is at {worker_manual} (relative to workdir). "
        f"Put all witness proofs there.\n"
        f"3. Reusable helper lemmas go into worker_helper_scratch_lib ONLY "
        f"(path: {worker_helper}).\n"
        f"4. Use the compile command from AGENTS.md to verify your work after each goal.\n"
        f"5. Write proof_report.json and proof_strategy_report.json as specified in AGENTS.md.\n"
        f"6. Do NOT modify common_case_formal_lib, task_local_scratch_lib, "
        f"case_deps/, goal_*.v, or tutorial/.\n"
        f"7. Complete all assigned goals or report concrete proof-obligation defects "
        f"with evidence.\n"
    )


def main() -> int:
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <groups_manifest.json>", file=sys.stderr)
        return 1

    manifest_path = Path(sys.argv[1]).expanduser().resolve()
    if not manifest_path.is_file():
        print(f"groups_manifest.json not found: {manifest_path}", file=sys.stderr)
        return 1

    groups = json.loads(manifest_path.read_text(encoding="utf-8"))
    if not isinstance(groups, list):
        print(f"{manifest_path} is not a JSON array", file=sys.stderr)
        return 1

    prompts: list[dict] = []
    for i, gm in enumerate(groups):
        work_dir = str(gm["work_dir"])
        goals = [str(e["name"]) for e in gm["goals"]]
        proof_group_id = str(gm.get("proof_group_id", f"group_{i:02d}"))
        worker_manual = gm.get("worker_manual_file", "proof_manual.v")
        worker_helper = gm.get("worker_helper_scratch_lib_file", "worker_helper_scratch_lib.v")

        prompts.append({
            "group_index": i,
            "proof_group_id": proof_group_id,
            "work_dir": work_dir,
            "goal_count": len(goals),
            "goals": goals,
            "worker_manual": str(Path(worker_manual).name),
            "worker_helper_scratch_lib": (
                str(Path(worker_helper).relative_to(Path(work_dir)))
                if Path(worker_helper).is_relative_to(work_dir)
                else str(Path(worker_helper).name)
            ),
            "prompt": build_prompt(work_dir, goals, proof_group_id,
                                   str(Path(worker_manual).name),
                                   str(Path(worker_helper).relative_to(Path(work_dir))
                                       if Path(worker_helper).is_relative_to(work_dir)
                                       else Path(worker_helper).name)),
        })

    print(json.dumps(prompts, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
