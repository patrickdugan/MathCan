import unittest

from mm06_branching import exhaustive, mask_depth, partition

class BranchingControls(unittest.TestCase):
    def test_interacting_choices(self):
        def transition(stack, label):
            if label == "a":
                return [1]
            if label == "b":
                return [2]
            if label == "x" and stack == [1]:
                return [3]
            if label == "y" and stack == [2]:
                return [3]
            return None
        solutions, calls = exhaustive([0,1],[["a","b"],["x","y"]],[],3,transition)
        self.assertEqual(solutions,[["a","x"],["b","y"]])
        self.assertEqual(calls,6)

    def test_fixed_suffix_failure(self):
        def transition(stack,label):
            return [label] if label != "fail" else None
        solutions,calls = exhaustive([0,"fail"],[["a","b"]],[],"a",transition)
        self.assertEqual(solutions,[])
        self.assertEqual(calls,4)

    def test_depth_split(self):
        self.assertIn(mask_depth("example"),(2,3,4))
        self.assertIn(partition("example"),("train","dev","family_test"))

if __name__=="__main__":
    unittest.main()
