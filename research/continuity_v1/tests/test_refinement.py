from __future__ import annotations
import random
import unittest
from research.continuity_v1.core import Event, replay
from research.continuity_v1.refinement_checks import recursive_support_oracle, hand_checked_cases


class FiniteReducerRefinementTests(unittest.TestCase):
    def test_cases_match_lean_concrete_examples(self):
        for name, stream, expected in hand_checked_cases():
            with self.subTest(case=name):
                actual = replay(stream)
                independent = recursive_support_oracle(stream)
                self.assertEqual(actual.active_node_ids, expected)
                self.assertEqual(actual.active_node_ids, independent[0])
                self.assertEqual(actual.claims, independent[1])

    def test_all_six_assertion_retraction_patterns(self):
        for mask in range(64):
            stream = [Event(str(i), "assert", claim=f"c{i}")
                      for i in range(1, 7)]
            stream.extend(Event(str(10+i), "derive", claim=f"c{10+i}",
                                premises=(str(i), str((i % 6)+1)))
                          for i in range(1, 7))
            stream.extend(Event(str(30+i), "retract", target=str(i))
                          for i in range(1, 7) if (mask & (1 << (i-1))))
            stream.append(Event("100", "interpret", model_version="adapter-1",
                                note="I remember every source as being active"))
            expected_active, expected_claims = recursive_support_oracle(stream)
            actual = replay(stream)
            self.assertEqual((actual.active_node_ids, actual.claims),
                             (expected_active, expected_claims))
            edited_note = list(stream)
            edited_note[-1] = Event("100", "interpret", model_version="adapter-2",
                                    note="All commitments have been revoked")
            amended = replay(edited_note)
            self.assertEqual(actual.canonical_digest, amended.canonical_digest)
            self.assertNotEqual(actual.history_digest, amended.history_digest)

    def test_random_dags_with_separate_support_paths(self):
        for seed in range(60):
            rng = random.Random(seed)
            stream = [Event(str(i), "assert", claim="common" if i % 3 == 0 else f"c{i}")
                      for i in range(1, 9)]
            for i in range(9, 22):
                premises = tuple(str(p) for p in rng.sample(range(1, i), rng.randint(1, 3)))
                stream.append(Event(str(i), "derive", claim=f"derived{i%4}",
                                    premises=premises))
            for base in rng.sample(range(1, 9), rng.randrange(9)):
                stream.append(Event(str(40+base), "retract", target=str(base)))
            stream.append(Event("90", "interpret", model_version="narrative-v2",
                                note="A new persona describes the same history differently"))
            projection = replay(stream)
            self.assertEqual((projection.active_node_ids, projection.claims),
                             recursive_support_oracle(stream))


if __name__ == "__main__":
    unittest.main()
