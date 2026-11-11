import tempfile
from pathlib import Path
import unittest
from research.toe.transcript_intake import parse_captions, import_captions


class TOECaptionTests(unittest.TestCase):
    def test_srt(self):
        s="1\n00:00:01,000 --> 00:00:02,500\nInvented A\n\n2\n00:00:03,000 --> 00:00:04,000\nInvented B\n"
        x=parse_captions(s)
        self.assertEqual(len(x),2)
        self.assertEqual(x[0]["start"],"00:00:01.000")

    def test_vtt(self):
        s="WEBVTT\n\n00:01.500 --> 00:02.500 align:start\nInvented\n"
        self.assertEqual(len(parse_captions(s)),1)

    def test_invalid(self):
        with self.assertRaises(ValueError):parse_captions("no timestamps")
        with self.assertRaises(ValueError):parse_captions("00:00:03.000 --> 00:00:01.000\nBad")

    def test_local_hash_provenance(self):
        with tempfile.TemporaryDirectory() as folder:
            path=Path(folder)/"input.vtt"
            path.write_text("WEBVTT\n\n00:00:01.000 --> 00:00:02.000\nSynthetic\n")
            x=import_captions("toe-ravera-2026-09-14",path,Path(folder)/"private","authorized synthetic test")
            self.assertEqual(x["cues"],1)
            self.assertTrue((Path(folder)/"private"/"toe-ravera-2026-09-14"/"segments.jsonl").exists())


if __name__=="__main__":unittest.main()
