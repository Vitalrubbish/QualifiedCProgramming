#!/usr/bin/env python3
"""Group lemma goals for concurrent solving.

Provides a pluggable interface for grouping strategies. The default
strategy sorts lemma names lexicographically and splits into chunks.
When vc-checking provides a proof-pattern group plan, that explicit plan
is preferred over the fallback chunking strategy.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable

# Type alias for a grouping strategy function.
# Takes a list of lemma dicts and chunk size, returns list of groups.
GroupStrategy = Callable[[list[dict], int], list[list[dict]]]

DEFAULT_CHUNK_SIZE = 5

PLAN_GROUP_KEYS = ("proof_groups", "witness_groups", "groups")
PLAN_MEMBER_KEYS = ("members", "witnesses", "goals")
PLAN_MEMBER_NAME_KEYS = ("name", "witness", "goal", "lemma")


def group_goals(
    lemmas: list[dict],
    chunk_size: int = DEFAULT_CHUNK_SIZE,
    strategy: GroupStrategy | None = None,
) -> list[list[dict]]:
    """Group lemmas for concurrent solving.

    Parameters
    ----------
    lemmas : list[dict]
        Lemma entries from manifest.json (must have "name" key).
    chunk_size : int
        Maximum group size (default 1).
    strategy : callable, optional
        Custom grouping function. Defaults to sort_chunk_strategy.
    """
    if not lemmas:
        return []
    if strategy is None:
        strategy = sort_chunk_strategy
    return strategy(lemmas, chunk_size)


def sort_chunk_strategy(lemmas: list[dict], chunk_size: int) -> list[list[dict]]:
    """Sort lemmas by name lexicographically, then split into chunks.

    Simple and effective for structured naming like:
        entail_wit_1, entail_wit_2, ..., return_wit_1, return_wit_2, ...
    """
    sorted_lemmas = sorted(lemmas, key=lambda e: str(e["name"]))
    groups: list[list[dict]] = []
    for i in range(0, len(sorted_lemmas), chunk_size):
        groups.append(sorted_lemmas[i : i + chunk_size])
    return groups


def load_group_plan(path: Path) -> Any:
    """Load a vc-checking witness group plan from JSON."""
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise SystemExit(f"Invalid witness group plan JSON: {path}: {exc}") from exc


def fallback_group_entries(
    lemmas: list[dict],
    chunk_size: int = DEFAULT_CHUNK_SIZE,
) -> list[dict]:
    """Return structured group entries for the stable sort+chunk fallback."""
    groups = group_goals(lemmas, chunk_size=chunk_size)
    return [
        {
            "proof_group_id": f"fallback_{i:02d}",
            "grouping_source": "sort_chunk_fallback",
            "goals": group,
        }
        for i, group in enumerate(groups)
    ]


def group_entries_from_plan(lemmas: list[dict], plan: Any) -> list[dict]:
    """Return structured group entries from a vc-checking group plan.

    The plan must cover exactly the current lemma set. This makes stale or
    partial vc-checking output fail early instead of silently changing proof scope.
    Accepted shapes:
      - [{"members": ["lemma_a", "lemma_b"], ...}, ...]
      - {"groups": [...]} or {"proof_groups": [...]} or {"witness_groups": [...]}
    """
    raw_groups = _extract_raw_groups(plan)
    by_name = {str(lemma["name"]): lemma for lemma in lemmas}
    raw_aliases = _raw_witness_aliases(by_name)
    seen: set[str] = set()
    entries: list[dict] = []

    for index, raw_group in enumerate(raw_groups):
        group_id, members, meta = _parse_raw_group(raw_group, index)
        if not members:
            raise SystemExit(f"Witness group `{group_id}` has no members")
        goals: list[dict] = []
        for raw_name in members:
            name = _resolve_plan_witness_name(raw_name, by_name, raw_aliases, group_id)
            if name not in by_name:
                raise SystemExit(f"Witness group `{group_id}` references unknown witness `{name}`")
            if name in seen:
                raise SystemExit(f"Witness `{name}` appears in more than one proof group")
            seen.add(name)
            goals.append(by_name[name])
        if "representative_witness" in meta:
            representative = _resolve_plan_witness_name(
                str(meta["representative_witness"]),
                by_name,
                raw_aliases,
                group_id,
            )
            if representative not in by_name:
                raise SystemExit(
                    f"Witness group `{group_id}` references unknown representative "
                    f"witness `{representative}`"
                )
            if representative not in {str(goal["name"]) for goal in goals}:
                raise SystemExit(
                    f"Witness group `{group_id}` representative `{representative}` "
                    "is not a member of the group"
                )
            meta["representative_witness"] = representative
        entry = {
            "proof_group_id": group_id,
            "grouping_source": "vc-checking-group-plan",
            "goals": goals,
            **meta,
        }
        entries.append(entry)

    missing = sorted(set(by_name) - seen)
    if missing:
        raise SystemExit(
            "Witness group plan does not cover current witness set: "
            + ", ".join(missing)
        )
    return entries


def group_goals_from_plan(lemmas: list[dict], plan: Any) -> list[list[dict]]:
    """Compatibility helper returning only goal lists from an explicit plan."""
    return [entry["goals"] for entry in group_entries_from_plan(lemmas, plan)]


def _extract_raw_groups(plan: Any) -> list[Any]:
    if isinstance(plan, list):
        return plan
    if not isinstance(plan, dict):
        raise SystemExit("Witness group plan must be a JSON object or array")
    for key in PLAN_GROUP_KEYS:
        value = plan.get(key)
        if value is not None:
            if not isinstance(value, list):
                raise SystemExit(f"Witness group plan field `{key}` must be an array")
            return value
    raise SystemExit(
        "Witness group plan must contain one of: "
        + ", ".join(PLAN_GROUP_KEYS)
    )


def _parse_raw_group(raw_group: Any, index: int) -> tuple[str, list[str], dict]:
    if isinstance(raw_group, list):
        group_id = f"group_{index:02d}"
        return group_id, [_member_name(member, group_id) for member in raw_group], {}
    if not isinstance(raw_group, dict):
        raise SystemExit(f"Witness group #{index} must be an object or array")

    group_id = str(
        raw_group.get("proof_group_id")
        or raw_group.get("group_id")
        or raw_group.get("id")
        or f"group_{index:02d}"
    )
    raw_members = None
    for key in PLAN_MEMBER_KEYS:
        if raw_group.get(key) is not None:
            raw_members = raw_group[key]
            break
    if not isinstance(raw_members, list):
        raise SystemExit(f"Witness group `{group_id}` must contain a members array")

    meta_keys = (
        "representative_witness",
        "natural_language_proof_pattern",
        "shared_helper_candidates",
        "proving_hints",
        "grouping_confidence",
        "difficulty",
        "estimated_difficulty",
        "difficulty_score",
        "estimated_seconds",
        "expected_seconds",
    )
    meta = {key: raw_group[key] for key in meta_keys if key in raw_group}
    return group_id, [_member_name(member, group_id) for member in raw_members], meta


def _member_name(member: Any, group_id: str) -> str:
    if isinstance(member, str):
        return member
    if isinstance(member, dict):
        for key in PLAN_MEMBER_NAME_KEYS:
            value = member.get(key)
            if value is not None:
                return str(value)
    raise SystemExit(f"Witness group `{group_id}` contains a member without a witness name")


def _raw_witness_aliases(by_name: dict[str, dict]) -> dict[str, str | None]:
    """Map raw vc-checking witness names to generated lemma names.

    Symexec manual lemmas are named ``proof_of_<witness>`` while vc-checking
    reports often use the raw witness name.  Keep exact lemma names authoritative
    and only use this alias map when a plan member is not already an exact match.
    ``None`` marks an ambiguous alias.
    """
    aliases: dict[str, str | None] = {}
    for name in by_name:
        if not name.startswith("proof_of_"):
            continue
        alias = name.removeprefix("proof_of_")
        existing = aliases.get(alias)
        if existing is None and alias in aliases:
            continue
        if existing is not None and existing != name:
            aliases[alias] = None
            continue
        aliases[alias] = name
    return aliases


def _resolve_plan_witness_name(
    raw_name: str,
    by_name: dict[str, dict],
    raw_aliases: dict[str, str | None],
    group_id: str,
) -> str:
    if raw_name in by_name:
        return raw_name
    if raw_name in raw_aliases:
        resolved = raw_aliases[raw_name]
        if resolved is None:
            raise SystemExit(
                f"Witness group `{group_id}` references ambiguous raw witness `{raw_name}`"
            )
        return resolved
    return raw_name
