import unittest
from research.rh_proof_distillation.main_character_dependency_audit import (
    git_blob_sha, parse_open_fields, wrapper_graph, verify_sources, OPEN_FIELDS
)


class MainCharacterAuditTests(unittest.TestCase):
    def test_git_blob_of_empty_file(self):
        self.assertEqual(git_blob_sha(b""), "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391")

    def test_duplicate_row_contract(self):
        source = (
            "structure UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop where\n"
            "  caraianiLocalGlobalDual : Row\n"
            "  localLanglandsExists : RecTExists\n"
            "  galoisRepOfPolarizedPairLit : Row\n"
            "theorem UpperTheory.LiteratureTheorems.foo (O : OpenLiteratureStatements) := trivial\n"
        )
        fields = parse_open_fields(source)
        self.assertEqual(set(fields), set(OPEN_FIELDS))
        self.assertEqual(fields["caraianiLocalGlobalDual"], fields["galoisRepOfPolarizedPairLit"])
        with self.assertRaisesRegex(ValueError, "duplicate Row"):
            parse_open_fields(source.replace("galoisRepOfPolarizedPairLit : Row", "galoisRepOfPolarizedPairLit : Different"))

    def test_proof_body_usage_and_transitive_wrapper_edges(self):
        text = (
            "theorem UpperTheory.LiteratureTheorems.helper (O : OL) : True := True.intro\n"
            "theorem UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin (O : OL) : True := "
            "UpperTheory.LiteratureTheorems.helper O\n"
        )
        graph = wrapper_graph(text)
        self.assertEqual(graph["total_wrappers"], 2)
        self.assertEqual(graph["source_bodies_without_literal_O"], 1)
        self.assertTrue(graph["all_wrappers_reachable_from_root"])

    def test_pin_rejects_missing_repository(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaises(Exception):
                verify_sources(Path(td))


if __name__ == "__main__":
    unittest.main()
