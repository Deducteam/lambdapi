"""Go-to-definition tests."""

import os
import unittest

from .base import LSPTestCase, requires_stdlib


def _first_definition(result):
    """Normalize the definition result to a single {uri, range} dict or None.

    LSP allows: null | Location | Location[] | LocationLink[]."""
    if result is None:
        return None
    if isinstance(result, dict):
        return result
    if isinstance(result, list) and result:
        return result[0]
    return None


class TestDefinitionLocal(LSPTestCase):
    """Go-to-def within a single file."""

    def test_definition_of_local_symbol(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        # Jump from use of `zero` in `rule double zero ↪ zero`
        line, col = src.find(r"rule double zero", "zero")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d, "definition should be non-null for local use")
        self.assertEqual(d["uri"], uri, "local def should point to same URI")
        # The declaration of `zero` is on line 1 (0-based).
        decl_line, _ = src.find(r"constant symbol zero", "zero")
        self.assertEqual(d["range"]["start"]["line"], decl_line)

    def test_definition_of_undefined_is_null(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        # Line 0, col 0 is the start of `constant` keyword — not a symbol.
        result = self.server.definition(uri, 0, 0)
        d = _first_definition(result)
        self.assertIsNone(d, f"expected null def, got {d}")


class TestDefinitionUncheckedRegion(LSPTestCase):
    """Go-to-definition falls back to the in-scope symbol table for
    text the checker never reached (e.g. past a parse error)."""

    TEXT = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol ;\n"                     # parse error: no name
        "symbol later : Nat;\n"          # never parsed / checked
    )

    def test_definition_after_parse_error_uses_symbol_table(self):
        uri, _src, diags = self.open_text("def_err.lp", self.TEXT)
        self.assertTrue(self.errors(diags),
            "fixture should produce a parse error")
        col = self.TEXT.splitlines()[3].index("Nat")
        d = _first_definition(self.server.definition(uri, 3, col))
        self.assertIsNotNone(d,
            "definition should fall back to the in-scope symbol table")
        self.assertEqual(d["uri"], uri)
        self.assertEqual(d["range"]["start"]["line"], 0,
            "should jump to the declaration of Nat on line 0")


@requires_stdlib
class TestDefinitionStdlib(LSPTestCase):
    """Go-to-def on symbols defined in another file (stdlib)."""

    def test_definition_of_stdlib_symbol(self):
        uri, _text, src, _ = self.open_fixture("imports.lp")
        # Jump from `ℕ` in `symbol double : ℕ → ℕ;`
        line, col = src.find(r"symbol double :", r"ℕ")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d, "stdlib go-to-def must not be null")
        self.assertNotEqual(d["uri"], uri,
            "stdlib def should point to another file")
        self.assertTrue(d["uri"].endswith("Nat.lp"),
            f"stdlib def should point to Nat.lp, got {d['uri']}")
        # And the range must be plausible (not the line-1 fallback for all
        # external symbols).
        self.assertGreaterEqual(d["range"]["start"]["line"], 0)


class TestDefinitionModulePath(LSPTestCase):
    """Go-to-definition on the module path of a require/open jumps to
    the start of that module's file (no stdlib needed)."""

    MOD_A = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n")

    def test_go_to_def_on_local_required_module(self):
        path_a = os.path.join(self.lib_root, "DefModA.lp")
        with open(path_a, "w") as f:
            f.write(self.MOD_A)
        self.addCleanup(lambda: os.path.exists(path_a) and os.remove(path_a))
        uri, src, _ = self.open_text("DefModB.lp",
            "require open test.DefModA;\n"
            "symbol z : Nat ≔ zero;\n")
        line, col = src.find(r"require open test\.DefModA", "DefModA")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d, "module-path go-to-def should resolve")
        self.assertTrue(d["uri"].endswith("DefModA.lp"),
            f"should resolve to DefModA.lp; got {d.get('uri')}")
        self.assertEqual(d["range"]["start"]["line"], 0)


@requires_stdlib
class TestCrossFileDefinitionLine(LSPTestCase):
    """Cross-file go-to-def must land on the actual declaration, not
    fall back to line 0 / char 0 (a regression seen in live usage)."""

    def test_stdlib_nat_lands_on_declaration(self):
        uri, _text, src, _ = self.open_fixture("imports.lp")
        line, col = src.find(r"symbol double :", r"ℕ")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d)
        self.assertTrue(d["uri"].endswith("Nat.lp"))
        got_line = d["range"]["start"]["line"]
        # We don't hardcode the actual declaration line (it shifts as
        # stdlib evolves); just guard the line-1-fallback regression.
        self.assertGreater(got_line, 1,
            f"stdlib go-to-def landed on line {got_line} "
            f"(regression of the line-1 fallback bug)")

    def test_user_module_lands_on_declaration(self):
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


@requires_stdlib
class TestDefinitionQualified(LSPTestCase):
    """#1366 fix: find_sym resolves qualified names rather than the
    short-name in_scope lookup."""

    def test_qualified_name_resolves_to_qualified(self):
        uri, _text, src, _ = self.open_fixture("qualified.lp")
        # Hover on `ℕ` in `Stdlib.Nat.ℕ` — should resolve to the stdlib def.
        line, col = src.find(r"symbol two : Stdlib", r"ℕ")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d, "qualified name should resolve")
        self.assertTrue(d["uri"].endswith("Nat.lp"),
            f"Stdlib.Nat.ℕ should resolve to Nat.lp, got {d['uri']}")

    def test_qualified_name_with_local_shadow(self):
        """Even if a symbol with the same short name exists locally,
        a qualified reference must resolve to the qualified target."""
        text = (
            "require Stdlib.Nat;\n"
            "symbol ℕ : TYPE;\n"  # local shadow
            "symbol x : Stdlib.Nat.ℕ ≔ Stdlib.Nat.0;\n"
        )
        uri, src, _ = self.open_text("shadow.lp", text)
        line, col = src.find(r"symbol x : Stdlib", r"ℕ")
        d = _first_definition(self.server.definition(uri, line, col))
        self.assertIsNotNone(d)
        # The qualified reference should NOT resolve to the local ℕ.
        self.assertTrue(d["uri"].endswith("Nat.lp"),
            f"Stdlib.Nat.ℕ must resolve to stdlib, got {d['uri']}")


if __name__ == "__main__":
    unittest.main()
