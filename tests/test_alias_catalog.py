"""OLM-06 computer-assisted single-swap alias and 13-state detection audit."""
import json
import hashlib
from itertools import combinations
from pathlib import Path
import unittest
from alias_catalog import enumerate_single_swap_aliases
from latent_stars import matchings, star_covers

HERE = Path(__file__).parent


class AliasCatalogTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = enumerate_single_swap_aliases()
        cls.reference_digest = '085d61d44e72bbbe3c381bd48198a9ea34cb8fceb55df9c8a41d8e578b96b190'
        cls.edges = tuple(combinations(range(6),2))
        cls.states = tuple(matchings(tuple(range(6))))
        cls.masks = tuple(tuple(int(e in m) for e in cls.edges) for m in cls.states)

    def test_fresh_replay_matches_frozen_exact_catalog(self):
        digest = hashlib.sha256(json.dumps(self.report,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        self.assertEqual(digest, self.reference_digest)
        self.assertEqual(self.report['one_swap_alias_events'],180)
        self.assertEqual(self.report['gauge_incompatible_aliases'],0)
        self.assertEqual(self.report['heldouts_with_no_alias'],275)
        self.assertEqual(self.report['remaining_eleven_subcohorts'],5460)

    def test_all_aliases_are_genuinely_different_feature_geometries(self):
        physical_stars = {frozenset(i for i,e in enumerate(self.edges) if vertex in e)
                          for vertex in range(6)}
        for case in self.report['aliases']:
            held = case['heldout']
            kept = [i for i in range(15) if i not in held]
            original = [self.masks[i] for i in kept]
            swapped = list(original)
            pos = kept.index(case['corrupted_train_class'])
            row = list(swapped[pos]); row[case['swap_out']] = 0; row[case['swap_in']] = 1
            swapped[pos] = tuple(row)
            _, original_covers = star_covers(original)
            _, alternate_covers = star_covers(swapped)
            self.assertEqual(len(original_covers),1)
            self.assertEqual(len(alternate_covers),1)
            self.assertEqual(set(original_covers[0]),physical_stars)
            self.assertNotEqual(set(alternate_covers[0]),physical_stars)

    def test_every_alias_rejected_by_each_of_three_heldout_states(self):
        # Heldout rows are evaluation-only and never enter cover selection.
        for case in self.report['aliases']:
            held = case['heldout']
            kept = [i for i in range(15) if i not in held]
            altered = list(self.masks[i] for i in kept)
            pos = kept.index(case['corrupted_train_class'])
            row = list(altered[pos]); row[case['swap_out']] = 0; row[case['swap_in']] = 1
            altered[pos] = tuple(row)
            _, covers = star_covers(altered)
            self.assertEqual(len(covers),1)
            edge_map = {j:tuple(i for i,star in enumerate(covers[0]) if j in star) for j in range(15)}
            for omitted in held:
                abstract_edges = [edge_map[j] for j,x in enumerate(self.masks[omitted]) if x]
                self.assertNotEqual(sorted(z for a,b in abstract_edges for z in (a,b)), list(range(6)))

    def test_thirteen_distinct_states_always_detect_single_swap(self):
        # A single swap cannot complete a perfect matching when two edges are unchanged.
        full_codebook = set(self.masks)
        count = 0
        for omit_pair in combinations(range(15),2):
            original = [self.masks[i] for i in range(15) if i not in omit_pair]
            _, cover = star_covers(original)
            self.assertEqual(len(cover),1)
            for row in original:
                active = [j for j,b in enumerate(row) if b]
                inactive = [j for j,b in enumerate(row) if not b]
                for a in active:
                    for b in inactive:
                        altered = list(row); altered[a] = 0; altered[b] = 1
                        self.assertNotIn(tuple(altered),full_codebook)
                        count += 1
        self.assertEqual(count,105*13*3*12)

    def test_large_topk_margin_cannot_establish_planted_fidelity(self):
        case = self.report['aliases'][0]
        kept = [i for i in range(15) if i not in case['heldout']]
        alt = list(self.masks[i] for i in kept)
        pos = kept.index(case['corrupted_train_class'])
        r = list(alt[pos]); r[case['swap_out']] = 0; r[case['swap_in']] = 1
        alt[pos] = tuple(r)
        self.assertEqual(len(star_covers(alt)[1]),1)
        for arbitrary_margin in (1,10,1000,1000000):
            scores = [tuple(arbitrary_margin*v for v in row) for row in alt]
            self.assertTrue(all(sorted(row,reverse=True)[2]-sorted(row,reverse=True)[3]
                                ==arbitrary_margin for row in scores))
        self.assertNotEqual(alt,[self.masks[i] for i in kept])


if __name__=='__main__': unittest.main()
