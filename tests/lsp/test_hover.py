"""Hover tests."""

import unittest

from .base import LSPTestCase, requires_stdlib


def _hover_text(result):
    """Extract the hover markdown/text from a hover response."""
    if result is None:
        return None
    contents = result.get("contents")
    if contents is None:
        return None
    if isinstance(contents, dict):
        return contents.get("value", "")
    if isinstance(contents, list):
        return "\n".join(
            c.get("value", c) if isinstance(c, dict) else str(c)
            for c in contents)
    return str(contents)


class TestHoverBasic(LSPTestCase):
    """Hover works on uses of a symbol (the RangeMap tracks uses)."""

    def test_hover_on_use_of_symbol(self):
        uri, _text, src, _diags = self.open_fixture("simple.lp")
        # Use of `zero` in `rule double zero ↪ zero;` — its type is Nat.
        line, col = src.find(r"rule double zero", "zero")
        result = self.server.hover(uri, line, col)
        text = _hover_text(result)
        self.assertIsNotNone(text, "hover on use of zero should not be null")
        # In either plain or rich mode, the type string "Nat" should appear.
        self.assertIn("Nat", text)

    def test_hover_off_symbol_returns_null(self):
        uri, _text, _src, _diags = self.open_fixture("simple.lp")
        # Hover in a blank / non-identifier column.
        result = self.server.hover(uri, 0, 0)
        text = _hover_text(result)
        if text is not None:
            self.assertNotIn("symbol", text.lower())


class TestHoverPlainString(LSPTestCase):
    """Upstream-compatible hover: [contents] is a plain string carrying
    the type of the hovered symbol. Guards against accidental markdown
    divergence that VSCode/Emacs clients haven't had to handle."""

    def test_contents_is_plain_string(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"rule double zero", "zero")
        result = self.server.hover(uri, line, col)
        self.assertIsNotNone(result)
        contents = result.get("contents")
        self.assertIsInstance(contents, str,
            f"contents must be a plain string; "
            f"got {type(contents).__name__}: {contents!r}")


class TestHoverStdlib(LSPTestCase):

    @requires_stdlib
    def test_hover_on_stdlib_symbol(self):
        uri, _text, src, _ = self.open_fixture("imports.lp")
        line, col = src.find(r"symbol double :", r"ℕ")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text,
            "hover on stdlib type should return content, got null")


if __name__ == "__main__":
    unittest.main()
