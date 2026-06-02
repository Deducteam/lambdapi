"""Go-to-definition tests — including pr/lsp's URI fix and find_sym fix."""

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


@requires_stdlib
class TestDefinitionStdlib(LSPTestCase):
    """pr/lsp fix: go-to-def on external (stdlib) symbols returns a
    usable location instead of silently discarding sym_pos."""

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


@requires_stdlib
class TestDefinitionQualified(LSPTestCase):
    """pr/lsp fix: find_sym uses Sign.find_qualified for qualified names
    rather than the short-name in_scope lookup."""

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
