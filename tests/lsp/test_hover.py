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

    def test_hover_on_blank_position_returns_null(self):
        uri, _text, _src, _diags = self.open_fixture("simple.lp")
        # Col 8 of "constant symbol Nat : TYPE;" is the space between
        # `constant` and `symbol` — no token there.
        result = self.server.hover(uri, 0, 8)
        self.assertIsNone(result,
            f"hover on whitespace should be null; got {result!r}")


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


class TestHoverTacticKeyword(LSPTestCase):
    """Inside a proof, hovering a tactic keyword shows the tactic's
    documentation; outside a proof, tactic names are not special."""

    PROOF = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol triv : Nat → Nat ≔\n"
        "begin\n"
        "  assume n;\n"
        "  refine n;\n"
        "end;\n"
    )

    def test_hover_on_tactic_keyword_in_proof(self):
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 is "  refine n;" — cols 2..7 are `refine`.
        text = _hover_text(self.server.hover(uri, 5, 3))
        self.assertIsNotNone(text,
            "hover on a tactic keyword inside a proof should document it")
        self.assertIn("goal", text,
            f"tactic documentation should describe the tactic; got {text!r}")

    def test_hover_on_hypothesis_in_proof(self):
        """After `assume n`, hovering the use of `n` should show its
        type (hypotheses are proof-local: not symbols, not in the
        identifier RangeMap)."""
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 is "  refine n;" — col 9 is `n`.
        text = _hover_text(self.server.hover(uri, 5, 9))
        self.assertIsNotNone(text,
            "hover on a hypothesis should show its type")
        self.assertIn("Nat", text,
            f"hypothesis `n` has type Nat; got {text!r}")


class TestHoverSameLineTactics(LSPTestCase):
    """Hypothesis hovers work in every tactic of a line, not just the
    first. Goal snapshots are anchored at each tactic's keyword and
    record the state after it; when the tactic under the cursor closes
    the proof, the fallback must step back to the snapshot before that
    tactic — not to the start of the line, which with several tactics
    on one line lands before the hypothesis was introduced."""

    PROOF = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol triv : Nat → Nat ≔\n"
        "begin\n"
        "  assume n; refine n;\n"
        "end;\n"
    )

    def test_hover_on_hypothesis_in_second_tactic(self):
        uri, src, _ = self.open_text("sameline.lp", self.PROOF)
        # `n` in `refine n;` — the second tactic on the line, and the
        # one that finishes the proof. (`refine` itself contains an
        # `n`; the hypothesis use is the one followed by `;`.)
        line, col = src.find(r"refine n", "n;")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text,
            "hover on a hypothesis used in the second tactic of a line "
            "should show its type")
        self.assertIn("Nat", text,
            f"hypothesis `n` has type Nat; got {text!r}")

    def test_hover_on_hypothesis_in_first_tactic(self):
        uri, src, _ = self.open_text("sameline2.lp", self.PROOF)
        # `n` in `assume n;` — introduced by the tactic under the
        # cursor (`assume` contains no `n`, so plain `n` finds it).
        line, col = src.find(r"assume n", "n")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text,
            "hover on a hypothesis named in `assume` should show its type")
        self.assertIn("Nat", text,
            f"hypothesis `n` has type Nat; got {text!r}")


class TestHoverSubgoalClosingTactic(LSPTestCase):
    """Hypothesis hovers resolve in the tactic's pre-application state.
    Goal snapshots record the state *after* each tactic, so when the
    tactic under the cursor closes the current subgoal while a sibling
    goal remains, the snapshot at the cursor is the *next* goal's
    context — which lacks the subproof-local hypotheses the tactic's
    own arguments refer to."""

    PROOF = (
        "constant symbol A : TYPE;\n"
        "constant symbol B : TYPE;\n"
        "constant symbol P : TYPE;\n"
        "constant symbol mk : (A → A) → (B → B) → P;\n"
        "symbol thm : P ≔\n"
        "begin\n"
        "  apply mk\n"
        "  { assume ha; refine ha }\n"
        "  { assume hb; refine hb };\n"
        "end;\n"
    )

    def test_hover_on_argument_of_subgoal_closing_tactic(self):
        """`ha` in `refine ha`: the refine closes the first subgoal and
        the second (`B → B`) is still open, with no `ha` in context."""
        uri, src, _ = self.open_text("subgoal.lp", self.PROOF)
        line, col = src.find(r"refine ha", "ha")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text,
            "hover on a hypothesis used by a subgoal-closing tactic "
            "should show its type from the pre-application state")
        self.assertIn("A", text,
            f"hypothesis `ha` has type A; got {text!r}")

    def test_hover_on_argument_of_proof_closing_tactic(self):
        """`hb` in `refine hb`: the refine finishes the whole proof, so
        the post-state has no goals at all."""
        uri, src, _ = self.open_text("subgoal2.lp", self.PROOF)
        line, col = src.find(r"refine hb", "hb")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text,
            "hover on a hypothesis used by the proof-closing tactic "
            "should show its type")
        self.assertIn("B", text,
            f"hypothesis `hb` has type B; got {text!r}")

    def test_hover_on_binder_of_assume(self):
        """`ha` in `assume ha`: the name only exists in the tactic's
        post-state, which must remain a fallback."""
        uri, src, _ = self.open_text("subgoal3.lp", self.PROOF)
        line, col = src.find(r"assume ha", "ha")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text,
            "hover on the hypothesis bound by `assume` should show its type")
        self.assertIn("A", text,
            f"hypothesis `ha` has type A; got {text!r}")


class TestHoverMidEdit(LSPTestCase):
    """Tactic docs and hypothesis hovers survive a mid-word edit that
    breaks the parse (served from the last successfully parsed nodes)."""

    def test_tactic_hover_survives_broken_parse(self):
        proof = TestHoverTacticKeyword.PROOF
        uri, _src, _ = self.open_text("hovmid.lp", proof)
        broken = proof.replace("  refine n;\n", "  re\n  refine n;\n")
        self.server.did_change(uri, broken, 2)
        self.server.drain_notifications(timeout=5.0)
        # `assume` on line 4 sits before the edit point, so its stale
        # position is exact.
        text = _hover_text(self.server.hover(uri, 4, 3))
        self.assertIsNotNone(text,
            "tactic hover should survive a broken parse")
        self.assertIn("goal", text,
            f"expected the `assume` documentation; got {text!r}")

    def test_hypothesis_hover_survives_broken_parse(self):
        proof = TestHoverTacticKeyword.PROOF
        uri, _src, _ = self.open_text("hovmid2.lp", proof)
        # Mid-word edit after the refine line: earlier lines (and the
        # goal snapshots recorded for them) keep their positions.
        broken = proof.replace("end;\n", "  re\nend;\n")
        self.server.did_change(uri, broken, 2)
        self.server.drain_notifications(timeout=5.0)
        # `n` in the unshifted `refine n;` line (line 5, col 9).
        text = _hover_text(self.server.hover(uri, 5, 9))
        self.assertIsNotNone(text,
            "hypothesis hover should survive a broken parse")
        self.assertIn("Nat", text,
            f"hypothesis `n` has type Nat; got {text!r}")


class TestHoverCommandKeywords(LSPTestCase):
    """Command keywords and symbol modifiers are documented on hover,
    anywhere in a document."""

    def test_hover_on_symbol_command(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"constant symbol Nat", "symbol")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text, "hover on `symbol` should document it")
        self.assertIn("Declares or defines", text)

    def test_hover_on_constant_modifier(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"constant symbol Nat", "constant")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text, "hover on `constant` should document it")
        self.assertIn("modifier", text)

    def test_hover_on_rule_command(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"^rule double", "rule")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text, "hover on `rule` should document it")
        self.assertIn("rewriting", text)

    def test_hover_on_settings_query(self):
        text_lp = (
            "constant symbol Nat : TYPE;\n"
            "flag \"print_implicits\" on;\n"
        )
        uri, src, _ = self.open_text("settings.lp", text_lp)
        line, col = src.find(r"^flag", "flag")
        text = _hover_text(self.server.hover(uri, line, col))
        self.assertIsNotNone(text, "hover on `flag` should document it")
        self.assertIn("Sets a flag", text)


class TestHoverUncheckedRegion(LSPTestCase):
    """Hover falls back to the in-scope symbol table for text the
    checker never reached (e.g. past a parse error), where the
    RangeMap has no entries."""

    TEXT = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol ;\n"                     # parse error: no name
        "symbol later : Nat;\n"          # never parsed / checked
    )

    def test_hover_after_parse_error_uses_symbol_table(self):
        uri, _src, diags = self.open_text("hov_err.lp", self.TEXT)
        self.assertTrue(self.errors(diags),
            "fixture should produce a parse error")
        # `Nat` on the last line is past the error: not in the RangeMap,
        # but in scope from the checked prefix.
        col = self.TEXT.splitlines()[3].index("Nat")
        text = _hover_text(self.server.hover(uri, 3, col))
        self.assertIsNotNone(text,
            "hover should fall back to the in-scope symbol table")
        self.assertIn("TYPE", text)


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
