#!/usr/bin/env python3
"""Tests for group_goals.py."""

from __future__ import annotations

import unittest

from group_goals import (
    DEFAULT_CHUNK_SIZE,
    group_entries_from_plan,
    group_goals,
    group_goals_from_plan,
    sort_chunk_strategy,
)


def _make_lemmas(names: list[str]) -> list[dict]:
    """Create minimal lemma dicts from a list of names."""
    return [{"name": n, "index": i} for i, n in enumerate(names, 1)]


# Real lemma names from sll_merge_rel_manual.v (16 goals)
SLL_MERGE_NAMES = [
    "proof_of_sll_merge_entail_wit_1_1",
    "proof_of_sll_merge_entail_wit_1_2",
    "proof_of_sll_merge_entail_wit_2_1",
    "proof_of_sll_merge_entail_wit_2_2",
    "proof_of_sll_merge_entail_wit_2_3",
    "proof_of_sll_merge_entail_wit_2_4",
    "proof_of_sll_merge_entail_wit_3_1",
    "proof_of_sll_merge_entail_wit_3_2",
    "proof_of_sll_merge_entail_wit_4_3",
    "proof_of_sll_merge_entail_wit_4_4",
    "proof_of_sll_merge_return_wit_1",
    "proof_of_sll_merge_return_wit_2",
    "proof_of_sll_merge_return_wit_3",
    "proof_of_sll_merge_return_wit_4",
    "proof_of_sll_merge_return_wit_5",
    "proof_of_sll_merge_return_wit_6",
]

# Real lemma names from sll_multi_merge_rel_manual.v (19 goals)
SLL_MULTI_MERGE_NAMES = [
    "proof_of_sll_multi_merge_entail_wit_1",
    "proof_of_sll_multi_merge_entail_wit_2",
    "proof_of_sll_multi_merge_entail_wit_3",
    "proof_of_sll_multi_merge_entail_wit_4",
    "proof_of_sll_multi_merge_entail_wit_5",
    "proof_of_sll_multi_merge_entail_wit_6",
    "proof_of_sll_multi_merge_entail_wit_7",
    "proof_of_sll_multi_merge_entail_wit_8",
    "proof_of_sll_multi_merge_entail_wit_9",
    "proof_of_sll_multi_merge_entail_wit_10",
    "proof_of_sll_multi_merge_return_wit_1",
    "proof_of_sll_multi_merge_return_wit_2",
    "proof_of_sll_multi_merge_return_wit_3",
    "proof_of_sll_multi_merge_return_wit_4",
    "proof_of_sll_multi_merge_partial_solve_wit_1_pure",
    "proof_of_sll_multi_merge_partial_solve_wit_4_pure",
    "proof_of_sll_multi_merge_partial_solve_wit_6_pure",
    "proof_of_sll_multi_merge_partial_solve_wit_8_pure",
    "proof_of_sll_merge_derive_low_level_spec_aux_by_low_level_spec",
]


class TestGroupGoals(unittest.TestCase):
    """Tests for the group_goals() interface."""

    def test_empty(self):
        self.assertEqual(group_goals([]), [])

    def test_single_goal(self):
        lemmas = _make_lemmas(["proof_of_foo_entail_wit_1"])
        groups = group_goals(lemmas)
        self.assertEqual(len(groups), 1)
        self.assertEqual(len(groups[0]), 1)

    def test_two_goals(self):
        lemmas = _make_lemmas(["b_wit_2", "a_wit_1"])
        groups = group_goals(lemmas, chunk_size=5)
        self.assertEqual(len(groups), 1)
        # Should be sorted: a_wit_1 first (seed)
        self.assertEqual(groups[0][0]["name"], "a_wit_1")
        self.assertEqual(groups[0][1]["name"], "b_wit_2")

    def test_first_element_is_seed(self):
        """First element of each group should be the lexicographically smallest."""
        lemmas = _make_lemmas(["c", "a", "b", "e", "d", "f"])
        groups = group_goals(lemmas, chunk_size=3)
        self.assertEqual(groups[0][0]["name"], "a")
        self.assertEqual(groups[1][0]["name"], "d")

    def test_all_goals_preserved(self):
        """Every input lemma must appear in exactly one group."""
        lemmas = _make_lemmas(SLL_MERGE_NAMES)
        groups = group_goals(lemmas, chunk_size=5)
        all_names = [e["name"] for g in groups for e in g]
        self.assertEqual(sorted(all_names), sorted(SLL_MERGE_NAMES))

    def test_chunk_size_respected(self):
        lemmas = _make_lemmas(SLL_MERGE_NAMES)
        groups = group_goals(lemmas, chunk_size=5)
        for g in groups[:-1]:  # all but last must be full
            self.assertEqual(len(g), 5)
        self.assertLessEqual(len(groups[-1]), 5)

    def test_no_number_suffix(self):
        names = ["proof_of_foo_derive_spec", "proof_of_bar_derive_spec"]
        lemmas = _make_lemmas(names)
        groups = group_goals(lemmas, chunk_size=5)
        self.assertEqual(len(groups), 1)
        self.assertEqual(len(groups[0]), 2)

    def test_default_chunk_size_groups_multiple_goals(self):
        lemmas = _make_lemmas(["e", "d", "c", "b", "a", "f"])
        groups = group_goals(lemmas)
        self.assertEqual(DEFAULT_CHUNK_SIZE, 5)
        self.assertEqual([len(g) for g in groups], [5, 1])


class TestExplicitGroupPlan(unittest.TestCase):
    def test_group_plan_order_and_metadata(self):
        lemmas = _make_lemmas(["a", "b", "c"])
        plan = {
            "proof_groups": [
                {
                    "proof_group_id": "shape_a",
                    "members": ["b", "a"],
                    "representative_witness": "b",
                    "natural_language_proof_pattern": "split pure facts, then solve spatial tail",
                    "shared_helper_candidates": ["helper_ab"],
                    "proving_hints": ["start with b"],
                    "grouping_confidence": "high",
                },
                {"proof_group_id": "shape_c", "members": [{"name": "c"}]},
            ]
        }
        entries = group_entries_from_plan(lemmas, plan)
        self.assertEqual([e["proof_group_id"] for e in entries], ["shape_a", "shape_c"])
        self.assertEqual([[g["name"] for g in e["goals"]] for e in entries], [["b", "a"], ["c"]])
        self.assertEqual(entries[0]["representative_witness"], "b")
        self.assertEqual(entries[0]["grouping_source"], "vc-checking-group-plan")

    def test_group_plan_accepts_raw_witness_names(self):
        lemmas = _make_lemmas([
            "proof_of_superPiano_entail_wit_15_4",
            "proof_of_superPiano_return_wit_1",
        ])
        plan = {
            "witness_groups": [
                {
                    "proof_group_id": "entail_shape",
                    "members": ["superPiano_entail_wit_15_4"],
                    "representative_witness": "superPiano_entail_wit_15_4",
                },
                {
                    "proof_group_id": "return_shape",
                    "members": [{"witness": "superPiano_return_wit_1"}],
                    "representative_witness": "proof_of_superPiano_return_wit_1",
                },
            ]
        }

        entries = group_entries_from_plan(lemmas, plan)

        self.assertEqual(
            [[g["name"] for g in e["goals"]] for e in entries],
            [
                ["proof_of_superPiano_entail_wit_15_4"],
                ["proof_of_superPiano_return_wit_1"],
            ],
        )
        self.assertEqual(
            entries[0]["representative_witness"],
            "proof_of_superPiano_entail_wit_15_4",
        )

    def test_group_goals_from_plan_returns_goal_lists(self):
        lemmas = _make_lemmas(["a", "b"])
        groups = group_goals_from_plan(lemmas, [{"members": ["b"]}, {"members": ["a"]}])
        self.assertEqual([[g["name"] for g in group] for group in groups], [["b"], ["a"]])

    def test_group_plan_must_cover_all_witnesses(self):
        lemmas = _make_lemmas(["a", "b"])
        with self.assertRaises(SystemExit):
            group_entries_from_plan(lemmas, {"groups": [{"members": ["a"]}]})

    def test_group_plan_rejects_duplicate_witnesses(self):
        lemmas = _make_lemmas(["a", "b"])
        with self.assertRaises(SystemExit):
            group_entries_from_plan(
                lemmas,
                {"groups": [{"members": ["a"]}, {"members": ["a", "b"]}]},
            )

    def test_group_plan_rejects_unknown_witnesses(self):
        lemmas = _make_lemmas(["a", "b"])
        with self.assertRaises(SystemExit):
            group_entries_from_plan(
                lemmas,
                {"groups": [{"members": ["a", "c"]}, {"members": ["b"]}]},
            )


class TestSortChunkSllMerge(unittest.TestCase):
    """Test sort+chunk on sll_merge (16 goals)."""

    def test_entail_wit_grouped(self):
        """entail_wit goals (sorted adjacent) should land in consecutive groups."""
        lemmas = _make_lemmas(SLL_MERGE_NAMES)
        groups = group_goals(lemmas, chunk_size=5)
        # After sorting, entail_wit_* come first (10 goals), then return_wit_* (6 goals)
        # With chunk_size=5: group0=[entail 1-5], group1=[entail 6-10], group2=[return 1-5], group3=[return 6]
        entail_names = [n for n in sorted(SLL_MERGE_NAMES) if "entail_wit" in n]
        return_names = [n for n in sorted(SLL_MERGE_NAMES) if "return_wit" in n]

        # Check entail goals are in the first groups
        group0_names = [e["name"] for e in groups[0]]
        group1_names = [e["name"] for e in groups[1]]
        for name in entail_names:
            self.assertTrue(
                name in group0_names or name in group1_names,
                f"{name} not in entail groups",
            )

        # Check return goals are in the last groups
        group2_names = [e["name"] for e in groups[2]]
        group3_names = [e["name"] for e in groups[3]]
        for name in return_names:
            self.assertTrue(
                name in group2_names or name in group3_names,
                f"{name} not in return groups",
            )

    def test_group_count(self):
        lemmas = _make_lemmas(SLL_MERGE_NAMES)
        groups = group_goals(lemmas, chunk_size=5)
        # 16 goals / 5 = 4 groups (5, 5, 5, 1)
        self.assertEqual(len(groups), 4)


class TestSortChunkSllMultiMerge(unittest.TestCase):
    """Test sort+chunk on sll_multi_merge (19 goals)."""

    def test_group_count(self):
        lemmas = _make_lemmas(SLL_MULTI_MERGE_NAMES)
        groups = group_goals(lemmas, chunk_size=5)
        # 19 goals / 5 = 4 groups (5, 5, 5, 4)
        self.assertEqual(len(groups), 4)

    def test_partial_solve_grouped(self):
        """partial_solve_wit goals should land together."""
        lemmas = _make_lemmas(SLL_MULTI_MERGE_NAMES)
        groups = group_goals(lemmas, chunk_size=5)
        partial_names = {n for n in SLL_MULTI_MERGE_NAMES if "partial_solve" in n}
        # Find which groups contain partial_solve goals
        groups_with_partial = []
        for i, g in enumerate(groups):
            names_in_group = {e["name"] for e in g}
            if names_in_group & partial_names:
                groups_with_partial.append(i)
        # All 4 partial_solve goals should be in at most 1 group (they sort adjacent)
        self.assertLessEqual(len(groups_with_partial), 1)

    def test_all_goals_preserved(self):
        lemmas = _make_lemmas(SLL_MULTI_MERGE_NAMES)
        groups = group_goals(lemmas, chunk_size=5)
        all_names = [e["name"] for g in groups for e in g]
        self.assertEqual(sorted(all_names), sorted(SLL_MULTI_MERGE_NAMES))


class TestCustomStrategy(unittest.TestCase):
    """Test pluggable strategy interface."""

    def test_custom_strategy(self):
        """A custom strategy that puts each goal in its own group."""

        def one_per_group(lemmas: list[dict], chunk_size: int) -> list[list[dict]]:
            return [[e] for e in lemmas]

        lemmas = _make_lemmas(["a", "b", "c"])
        groups = group_goals(lemmas, strategy=one_per_group)
        self.assertEqual(len(groups), 3)
        for g in groups:
            self.assertEqual(len(g), 1)


if __name__ == "__main__":
    unittest.main()
