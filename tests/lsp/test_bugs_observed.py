"""Tests for two bugs observed in live Zed usage:

1. cross-file go-to-def landed on line 0 instead of the actual declaration
   line (pre-existing; fixed by pr/lsp's do_definition change, but the
   test here guards against regression)
2. go-to-def on the module name in `require open Foo.Bar` returns null
   (still broken; parser/RangeMap doesn't track module paths)

The third observed issue (`p ∨ q` rendered as `p \∨ q`) couldn't be
reproduced in the LSP output and is likely a Zed rendering artifact.
"""

import unittest

from .base import LSPTestCase, requires_stdlib
from .test_definition import _first_definition


@requires_stdlib
class TestCrossFileDefinitionLine(LSPTestCase):
    """Go-to-def must land on the actual declaration line, not fall back
    to line 0 / 1. (Pre-pr/lsp, the URI-comparison bug in do_definition
    caused every external symbol to return a line-1 fallback.)"""

    def test_stdlib_nat_lands_on_declaration(self):
        uri, _text, src, _ = self.open_fixture("imports.lp")
        line, col = src.find(r"symbol double :", r"ℕ")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d)
        self.assertTrue(d["uri"].endswith("Nat.lp"))
        got_line = d["range"]["start"]["line"]
        # ℕ is declared on source line 93 of Nat.lp (LSP line 92).
        # Anything <= 1 is the fallback bug resurfacing.
        self.assertGreater(got_line, 1,
            f"stdlib go-to-def landed on line {got_line} "
            f"(regression of the line-1 fallback bug)")

    def test_user_module_lands_on_declaration(self):
        """Cross-file go-to-def should land on the actual column of the
        declared name, not at (line,char) = (0,0)."""
        import os
        mod_a = (
            "constant symbol Nat : TYPE;\n"
            "constant symbol zero : Nat;\n"
            "constant symbol succ : Nat → Nat;\n")
        mod_b = (
            "require open test.ModA;\n"
            "symbol two : Nat ≔ succ (succ zero);\n")
        path_a = os.path.join(self.lib_root, "ModA.lp")
        with open(path_a, "w") as f:
            f.write(mod_a)
        self.addCleanup(lambda: os.remove(path_a)
                        if os.path.exists(path_a) else None)
        uri, src, _ = self.open_text("ModB.lp", mod_b)
        # `succ` is declared on line 2 (0-based) of ModA.lp at col 16.
        line, col = src.find(r"symbol two :", r"\bsucc\b")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d)
        self.assertTrue(d["uri"].endswith("ModA.lp"))
        r = d["range"]["start"]
        self.assertEqual(r["line"], 2,
            f"expected succ on line 2 of ModA.lp, got {r}")
        # The pre-fix fallback always returned char 0.
        self.assertGreater(r["character"], 0,
            f"cross-file go-to-def fell back to char 0: {r}")


@requires_stdlib
class TestRequireOpenDefinition(LSPTestCase):
    """Go-to-def on a module name in `require open` should navigate to
    that module."""

    def test_go_to_def_on_required_module(self):
        uri, _text, src, _ = self.open_fixture("imports.lp")
        # `Nat` in `require open Stdlib.Nat;`
        line, col = src.find(r"require open Stdlib\.Nat", r"\bNat")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d,
            "go-to-def on module in `require open` should resolve")
        self.assertTrue(d["uri"].endswith("Nat.lp"),
            f"should resolve to Nat.lp, got {d.get('uri')}")


if __name__ == "__main__":
    unittest.main()
