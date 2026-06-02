"""Diagnostics: errors, positions, and pr/lsp's focused hint ranges."""

import unittest

from .base import LSPTestCase


class TestErrorDiagnostics(LSPTestCase):

    def test_single_error_at_correct_line(self):
        _uri, _text, _src, diags = self.open_fixture("with_error.lp")
        errs = self.errors(diags)
        self.assertEqual(len(errs), 1,
                         f"expected 1 error, got {len(errs)}")
        # Error is `symbol bad : Undefined;` on line 3 (0-based: 2).
        self.assertEqual(errs[0]["range"]["start"]["line"], 2)
        self.assertIn("Undefined", errs[0]["message"])

    def test_error_range_does_not_crash_client(self):
        _uri, _, _, diags = self.open_fixture("with_error.lp")
        for d in diags:
            r = d["range"]
            # LSP requires 0-based, non-negative positions
            self.assertGreaterEqual(r["start"]["line"], 0)
            self.assertGreaterEqual(r["start"]["character"], 0)
            self.assertGreaterEqual(r["end"]["line"], r["start"]["line"])


class TestFocusedHints(LSPTestCase):
    """pr/lsp feature: hint ranges underline symbol names / keywords,
    not the whole line."""

    MAX_HINT_WIDTH = 30  # a "focused" hint shouldn't exceed this

    def test_hints_are_narrow(self):
        _uri, _, _, diags = self.open_fixture("simple.lp")
        hints = self.hints(diags)
        self.assertGreater(len(hints), 0,
                           "simple.lp should emit OK hints")
        too_wide = []
        for h in hints:
            r = h["range"]
            if r["start"]["line"] != r["end"]["line"]:
                continue  # skip multi-line ranges
            width = r["end"]["character"] - r["start"]["character"]
            if width > self.MAX_HINT_WIDTH:
                too_wide.append((h.get("message"), width, r))
        self.assertFalse(too_wide,
            f"{len(too_wide)}/{len(hints)} hints exceed {self.MAX_HINT_WIDTH} "
            f"chars: {too_wide[:2]}")

    def test_symbol_declaration_hint_covers_name(self):
        """For `constant symbol Nat : TYPE;`, hint should underline `Nat`."""
        uri, text, src, diags = self.open_fixture("simple.lp")
        nat_line, nat_col = src.find(r"constant symbol Nat", "Nat")
        hints = self.hints(diags)
        matching = [h for h in hints
                    if h["range"]["start"]["line"] == nat_line]
        self.assertTrue(matching,
            f"no hint on line {nat_line} where Nat is declared")
        r = matching[0]["range"]
        self.assertEqual(r["start"]["character"], nat_col,
            f"hint should start at Nat (col {nat_col}), "
            f"got col {r['start']['character']}")
        self.assertEqual(
            r["end"]["character"] - r["start"]["character"], len("Nat"),
            "hint should span exactly the symbol name")

    def test_rule_hint_covers_keyword(self):
        """For `rule double zero ↪ zero`, hint should underline `rule`."""
        _uri, text, src, diags = self.open_fixture("simple.lp")
        rule_line, rule_col = src.find(r"^rule double", "rule")
        hints = self.hints(diags)
        matching = [h for h in hints
                    if h["range"]["start"]["line"] == rule_line]
        self.assertTrue(matching, f"no hint on rule line {rule_line}")
        r = matching[0]["range"]
        self.assertEqual(r["start"]["character"], rule_col)
        self.assertEqual(
            r["end"]["character"] - r["start"]["character"], len("rule"))


class TestMultipleErrors(LSPTestCase):

    def test_errors_in_multiple_places(self):
        _uri, _text, _src, diags = self.open_fixture("multiple_errors.lp")
        errs = self.errors(diags)
        # The LSP should report at least the first error; both is better.
        self.assertGreaterEqual(len(errs), 1,
                                f"expected at least 1 error, got {len(errs)}")
        # Errors should be sorted by position (ascending line).
        for a, b in zip(errs, errs[1:]):
            self.assertLessEqual(a["range"]["start"]["line"],
                                 b["range"]["start"]["line"],
                                 "errors should be in position order")


class TestTacticHintMessage(LSPTestCase):
    """Every successful tactic emits a severity-4 hint with message 'OK',
    matching upstream behaviour."""

    @classmethod
    def _has_stdlib(cls):
        from .base import _opam_stdlib
        return _opam_stdlib() is not None

    def test_hint_message_is_OK(self):
        if not self._has_stdlib():
            self.skipTest("stdlib required")
        _uri, _text, _src, diags = self.open_fixture("proof.lp")
        hints_on_tactics = [
            d for d in self.hints(diags)
            if d.get("message") and d["range"]["start"]["line"] > 0
        ]
        ok_hints = [d for d in hints_on_tactics if d["message"] == "OK"]
        self.assertGreater(len(ok_hints), 0,
            f"expected at least one 'OK' hint; "
            f"got {[d['message'] for d in hints_on_tactics]}")


if __name__ == "__main__":
    unittest.main()
