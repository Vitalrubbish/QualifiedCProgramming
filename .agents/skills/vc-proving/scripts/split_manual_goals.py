#!/usr/bin/env python3
"""Split a proof manual into target-goal records without editing the source."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from manual_goal_utils import (
    ensure_unique_lemma_names,
    goal_definition_hash_for_lemma,
    lemma_proof_block_hash,
    lemma_statement_hash,
    lemma_target_symbol,
    make_run_workdir,
    parse_manual_file,
    prepare_keep_dest,
    resolve_keep_dest,
    stable_text_digest,
)


def main() -> int:
    parser = argparse.ArgumentParser(description="Split a proof manual into target-goal records.")
    parser.add_argument("manual_file", help="Path to the source *_manual.v file")
    parser.add_argument(
        "--goals",
        nargs="*",
        default=None,
        help="Optional lemma names to prove in this run. Defaults to every top-level lemma.",
    )
    parser.add_argument(
        "--keep-workdir",
        nargs="?",
        const="",
        default=None,
        metavar="DEST",
        help=(
            "Keep the work directory after final verification by copying it to DEST. "
                "If DEST is omitted, defaults under the repository .tmp tree. "
                "Without this flag, the temporary work dir is deleted at step 5. "
                "The agent always runs in a fresh repository .tmp dir."
            ),
    )
    parser.add_argument("--force", action="store_true", help="Overwrite an existing keep-destination")
    args = parser.parse_args()

    manual_path = Path(args.manual_file).expanduser().resolve()
    if not manual_path.is_file():
        raise SystemExit(f"Manual VC file not found: {manual_path}")

    text = manual_path.read_text(encoding="utf-8")
    prelude, lemmas = parse_manual_file(text)
    ensure_unique_lemma_names(lemmas)
    lemma_names = [str(lemma["name"]) for lemma in lemmas]
    if args.goals is None:
        target_names = lemma_names
    else:
        missing = [name for name in args.goals if name not in set(lemma_names)]
        if missing:
            raise SystemExit(f"Target goal(s) not found in {manual_path}: {', '.join(missing)}")
        target_names = list(dict.fromkeys(args.goals))
    target_set = set(target_names)
    target_lemmas = [lemma for lemma in lemmas if str(lemma["name"]) in target_set]

    keep = args.keep_workdir is not None
    keep_dest = resolve_keep_dest(manual_path, args.keep_workdir or None) if keep else None
    if keep:
        prepare_keep_dest(keep_dest, force=args.force)
    work_dir = make_run_workdir(manual_path.stem, manual_path)

    def lemma_manifest_metadata(lemma: dict[str, object]) -> dict[str, object]:
        goal_metadata = goal_definition_hash_for_lemma(
            prelude,
            lemma,
            source_file=manual_path,
        )
        return {
            "statement_hash": lemma_statement_hash(lemma),
            "proof_block_hash": lemma_proof_block_hash(lemma),
            "target_symbol": lemma_target_symbol(lemma),
            **goal_metadata,
        }

    manifest = {
        "source_file": str(manual_path),
        "source_kind": "proof_manual",
        "case_id": str(manual_path),
        "source_goal_version": stable_text_digest(text),
        "work_dir": str(work_dir),
        "keep_dest": str(keep_dest) if keep else None,
        "goal_count": len(target_lemmas),
        "lemma_order": target_names,
        "target_lemma_order": target_names,
        "source_lemma_order": lemma_names,
        "cleanup_policy": "keep" if keep else "delete_on_success",
        "debug_keep_workdir": keep,
        "all_lemmas": [
            {
                "index": index,
                "name": str(lemma["name"]),
                "statement_header": str(lemma["header_line"]),
                "original_start_line": int(lemma["start_line"]),
                "original_end_line": int(lemma["end_line"]),
                **lemma_manifest_metadata(lemma),
            }
            for index, lemma in enumerate(lemmas, start=1)
        ],
        "lemmas": [],
    }

    for index, lemma in enumerate(target_lemmas, start=1):
        lemma_name = str(lemma["name"])
        file_name = f"goal_{index:02d}__{lemma_name}.v"
        target = work_dir / file_name
        target.write_text(prelude + str(lemma["block"]), encoding="utf-8")
        manifest["lemmas"].append(
            {
                "index": index,
                "name": lemma_name,
                "split_rocq_file": str(target),
                "statement_header": str(lemma["header_line"]),
                "original_start_line": int(lemma["start_line"]),
                "original_end_line": int(lemma["end_line"]),
                **lemma_manifest_metadata(lemma),
            }
        )

    manifest_path = work_dir / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    print(f"Split {manual_path} into {len(target_lemmas)} target goal file(s) under {work_dir}")
    print(f"Manifest: {manifest_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
