"""documentSymbol: list of symbols declared in a document."""

import unittest

from .base import LSPTestCase


class TestDocumentSymbol(LSPTestCase):

    def test_symbols_listed_for_simple_doc(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        syms = self.server.document_symbol(uri)
        self.assertIsInstance(syms, list)
        self.assertGreater(len(syms), 0,
            "simple.lp declares symbols; documentSymbol should list them")
        names = [s.get("name") for s in syms]
        for expected in ("Nat", "zero", "succ", "double"):
            self.assertIn(expected, names,
                f"{expected!r} should appear in documentSymbol result")

    def test_symbol_kind_is_numeric(self):
        uri, _, _, _ = self.open_fixture("simple.lp")
        syms = self.server.document_symbol(uri)
        for s in syms:
            self.assertIn("kind", s)
            self.assertIsInstance(s["kind"], int)

    def test_symbols_have_locations(self):
        uri, _, _, _ = self.open_fixture("simple.lp")
        syms = self.server.document_symbol(uri)
        for s in syms:
            loc = s.get("location") or {}
            self.assertIn("uri", loc)
            self.assertIn("range", loc)
            r = loc["range"]
            self.assertGreaterEqual(r["start"]["line"], 0)

    def test_modifiers_file_lists_all_symbols(self):
        uri, _, _, _ = self.open_fixture("modifiers.lp")
        syms = self.server.document_symbol(uri)
        names = [s.get("name") for s in syms]
        for expected in ("Nat", "zero", "inj", "priv", "prot", "seq", "op"):
            self.assertIn(expected, names,
                f"{expected!r} missing from documentSymbol on modifiers.lp")


class TestHierarchicalDocumentSymbol(LSPTestCase):
    """When the client advertises [hierarchicalDocumentSymbolSupport],
    the server must return [DocumentSymbol[]] (objects with [range] +
    [selectionRange] + [children]) instead of the legacy flat
    [SymbolInformation[]] (objects with [location])."""

    advertise_hierarchical_symbols = True

    def test_inductive_has_constructors_as_children(self):
        uri, _, _, _ = self.open_fixture("inductive.lp")
        syms = self.server.document_symbol(uri)
        self.assertIsInstance(syms, list)
        # Hierarchical shape: every symbol has [range] / [selectionRange],
        # and the inductive type carries its constructors as children.
        for s in syms:
            self.assertIn("range", s,
                f"hierarchical DocumentSymbol must have [range]; got {s!r}")
            self.assertIn("selectionRange", s,
                f"hierarchical DocumentSymbol must have [selectionRange]; "
                f"got {s!r}")
            self.assertNotIn("location", s,
                f"hierarchical mode shouldn't emit legacy [location]; "
                f"got {s!r}")
        by_name = {s["name"]: s for s in syms}
        tree = by_name.get("Tree")
        self.assertIsNotNone(tree, f"expected 'Tree' in outline; got {syms}")
        children = tree.get("children", [])
        child_names = [c["name"] for c in children]
        self.assertEqual(child_names, ["leaf", "node"],
            f"Tree's constructors should appear as children in order; "
            f"got {child_names}")
        for c in children:
            self.assertEqual(c["kind"], 22,    # EnumMember
                f"constructor should have kind EnumMember (22); got {c!r}")

    def test_top_level_symbol_has_no_children(self):
        uri, _, _, _ = self.open_fixture("inductive.lp")
        syms = self.server.document_symbol(uri)
        bool_sym = next((s for s in syms if s["name"] == "Bool"), None)
        self.assertIsNotNone(bool_sym)
        self.assertEqual(bool_sym.get("children", []), [])


if __name__ == "__main__":
    unittest.main()
