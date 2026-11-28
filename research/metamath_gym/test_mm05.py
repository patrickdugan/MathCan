import unittest
from mm05_family import family, partition

class FamilyControls(unittest.TestCase):
    def test_alpha(self):
        a = {"floating":[["wff","ph"],["wff","ps"]],"statement":["|-","ph","->","ps"],"essential":[["|-","ph"]],"distinct":[]}
        b = {"floating":[["wff","z"],["wff","w"]],"statement":["|-","w","->","z"],"essential":[["|-","w"]],"distinct":[]}
        self.assertEqual(family(a),family(b))
        self.assertEqual(partition(family(a)),partition(family(b)))
        b["essential"]=[["|-","z"]]
        self.assertNotEqual(family(a),family(b))
    def test_dv(self):
        a = {"floating":[["setvar","x"],["setvar","y"]],"statement":["|-","x","=","y"],"essential":[],"distinct":[["x","y"]]}
        b = dict(a,distinct=[])
        self.assertNotEqual(family(a),family(b))

if __name__=="__main__":
    unittest.main()
