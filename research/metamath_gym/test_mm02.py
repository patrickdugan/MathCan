import unittest
from c_differential import classify
from setmm_corpus import decode, source_prefix, strip_comments

class Controls(unittest.TestCase):
    def test_reuse(self):
        self.assertEqual(decode(["(", "x", "pair", ")", "AZCB"], [],
                                {"x": 0, "pair": 2}.__getitem__),
                         ({"x", "pair"}, 2, 3, ["x", "x", "pair"]))

    def test_cap(self):
        self.assertEqual(decode(["(", "x", "pair", ")", "AZCB"], [],
                                {"x": 0, "pair": 2}.__getitem__, cap=2)[2:], (3, None))

    def test_invalid(self):
        for chars in ("Z", "AU", "?", "C"):
            with self.subTest(chars=chars), self.assertRaises(ValueError):
                decode(["(", "x", ")", chars], [], lambda _: 0)

    def test_extended_reference(self):
        refs = ["a"+str(i) for i in range(21)]
        self.assertEqual(decode(["(", *refs, ")", "UA"], [], lambda _: 0)[3], ["a20"])

    def test_prefix_scope(self):
        start = "$"+"{"
        source = "$c wff $. "+start+" $( $p fake $) x $p wff $= ( a ) A $. y $p wff $= a $. $}"
        self.assertEqual(source_prefix(source, ["x"], {"x": ["a"]}),
                         "$c wff $. "+start+" $( $p fake $) x $p wff $= a $.\n$}\n")

    def test_inline_include_comment(self):
        src = "$c wff $. $( Begin $[ set-pred.mm $] $) x $p wff $= a $."
        self.assertEqual(strip_comments(src).split(), "$c wff $. x $p wff $= a $.".split())
        with self.assertRaises(ValueError):
            strip_comments("$[ other.mm $]")
        with self.assertRaises(ValueError):
            strip_comments("$( unfinished")

    def test_c_logs(self):
        ok = "All proofs in the database were verified"
        err = "?Error: invalid proof"
        self.assertEqual(classify(0, ok), ("accepted", False))
        self.assertEqual(classify(0, err+"\n"+ok), ("rejected", True))
        self.assertEqual(classify(1, err), ("rejected", False))
        self.assertEqual(classify(1, ok), ("inconclusive", False))
        self.assertEqual(classify(-11, err), ("inconclusive", False))
        self.assertEqual(classify(0, ""), ("inconclusive", False))

if __name__ == "__main__":
    unittest.main()
