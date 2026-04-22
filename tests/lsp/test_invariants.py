"""Invariant tests: properties that should always hold.

These tests are written to find bugs, not confirm known behavior. Each test
asserts a property that should hold across many inputs; a failure likely
indicates a real defect.
"""

import re
import unittest

from .base import LSPTestCase, requires_stdlib


def _valid_range(r):
    """Return (ok, reason) for a well-formed LSP range."""
    s, e = r.get("start") or {}, r.get("end") or {}
    sl, sc = s.get("line", -1), s.get("character", -1)
    el, ec = e.get("line", -1), e.get("character", -1)
    if sl < 0 or sc < 0 or el < 0 or ec < 0:
        return False, f"negative coordinate in {r}"
    if (sl, sc) > (el, ec):
        return False, f"start > end in {r}"
    return True, ""


def _range_within_text(r, text):
    lines = text.split("\n")
    el = r["end"]["line"]
    if el >= len(lines):
        return False, f"end line {el} past file ({len(lines)} lines)"
    # Allow end.character == len(line) (LSP permits this).
    if r["end"]["character"] > len(lines[el]) + 1:
        return False, (
            f"end.char {r['end']['character']} past line len "
            f"{len(lines[el])}")
    return True, ""


def _all_identifier_positions(src):
    """Yield (line, col) for every Unicode/ASCII identifier-like token."""
    ident = re.compile(r"[A-Za-z_ℕ\u03b1-\u03c9][A-Za-z0-9_\u03b1-\u03c9]*")
    for lineno, line in enumerate(src.lines):
        for m in ident.finditer(line):
            yield lineno, m.start()


class TestRangeValidity(LSPTestCase):
    """Every LSP range we ever receive must be well-formed."""

    def _check_all_ranges(self, payloads, text, label):
        """[payloads] is a list of dicts that may contain "range" keys."""
        bad = []
        def walk(obj, path):
            if isinstance(obj, dict):
                if "range" in obj and isinstance(obj["range"], dict):
                    ok, why = _valid_range(obj["range"])
                    if not ok:
                        bad.append((path + ".range", why))
                    else:
                        ok, why = _range_within_text(obj["range"], text)
                        if not ok:
                            bad.append((path + ".range", why))
                for k, v in obj.items():
                    walk(v, f"{path}.{k}")
            elif isinstance(obj, list):
                for i, v in enumerate(obj):
                    walk(v, f"{path}[{i}]")
        for i, p in enumerate(payloads):
            walk(p, f"{label}[{i}]")
        self.assertFalse(bad,
            f"malformed ranges: {bad[:5]}{' ...' if len(bad) > 5 else ''}")

    def test_diagnostics_have_valid_ranges(self):
        _uri, text, _, diags = self.open_fixture("simple.lp")
        self._check_all_ranges(diags, text, "simple.lp")
        _uri, text, _, diags = self.open_fixture("with_error.lp")
        self._check_all_ranges(diags, text, "with_error.lp")
        _uri, text, _, diags = self.open_fixture("multiple_errors.lp")
        self._check_all_ranges(diags, text, "multiple_errors.lp")
        _uri, text, _, diags = self.open_fixture("modifiers.lp")
        self._check_all_ranges(diags, text, "modifiers.lp")

    def test_hover_ranges_valid_on_every_identifier(self):
        """Hover on every identifier-like position; any returned range
        must be well-formed. Bugs in position synthesis show up here."""
        uri, text, src, _ = self.open_fixture("simple.lp")
        responses = []
        for line, col in _all_identifier_positions(src):
            r = self.server.hover(uri, line, col)
            if r is not None and "range" in r:
                responses.append(r)
        self._check_all_ranges(responses, text, "hover responses")

    def test_document_symbol_ranges_valid(self):
        uri, text, _, _ = self.open_fixture("modifiers.lp")
        syms = self.server.document_symbol(uri) or []
        # mk_syminfo wraps the range inside "location", so flatten.
        flat = [{"range": s.get("location", {}).get("range")}
                for s in syms if s.get("location")]
        self._check_all_ranges(flat, text, "documentSymbol")


class TestIncrementalConsistency(LSPTestCase):
    """Re-introducing identical source should produce identical diagnostics."""

    def test_reintroduced_error_matches_original(self):
        uri, error_text, _, diags0 = self.open_fixture("with_error.lp")
        errs0 = self.errors(diags0)
        self.assertEqual(len(errs0), 1)
        r0 = errs0[0]["range"]

        # Fix: remove the bad line.
        clean = error_text.replace(
            "symbol bad : Undefined;\n", "")
        self.server.did_change(uri, clean, 2)
        self.server.drain_notifications(timeout=5.0)

        # Re-introduce the exact same text.
        self.server.did_change(uri, error_text, 3)
        new_diags = self.server.extract_diagnostics(
            self.server.drain_notifications(timeout=5.0), uri=uri)
        errs1 = self.errors(new_diags)
        self.assertEqual(len(errs1), 1,
            f"after reintroducing error, expected 1, got {len(errs1)}")
        r1 = errs1[0]["range"]
        self.assertEqual((r0["start"], r0["end"]), (r1["start"], r1["end"]),
            "re-introduced identical error should have identical range")


class TestDocumentSymbolCompleteness(LSPTestCase):
    """Every `symbol X` declaration in the source should appear in
    documentSymbol (modulo the ones without sym_pos, e.g. ghost)."""

    def test_all_declared_symbols_listed(self):
        uri, text, _src, _ = self.open_fixture("simple.lp")
        # Names declared via `constant symbol X` / `symbol X`.
        decl = re.findall(r"(?:^|\s)symbol\s+(\w+)", text, re.M)
        syms = self.server.document_symbol(uri) or []
        names = {s.get("name") for s in syms}
        missing = [d for d in decl if d not in names]
        self.assertFalse(missing,
            f"declared but missing from documentSymbol: {missing}; "
            f"got {sorted(names)}")

    def test_modifiers_file_completeness(self):
        uri, text, _, _ = self.open_fixture("modifiers.lp")
        decl = re.findall(r"(?:^|\s)symbol\s+(\w+)", text, re.M)
        syms = self.server.document_symbol(uri) or []
        names = {s.get("name") for s in syms}
        missing = [d for d in decl if d not in names]
        self.assertFalse(missing,
            f"modifiers.lp: missing {missing}; got {sorted(names)}")


@requires_stdlib
class TestGoalsContinuity(LSPTestCase):
    """Throughout an in-progress proof, proof/goals must return goals."""

    def test_goals_nonempty_at_every_line_mid_proof(self):
        uri, text, src, _ = self.open_fixture("proof.lp")
        # Find the begin/end lines for the second (multi-tactic) proof.
        begin_line = None
        end_line = None
        for i, line in enumerate(src.lines):
            if "eq_sym_nat" in line:
                # Next `begin` after this is our target.
                for j in range(i, len(src.lines)):
                    if src.lines[j].strip() == "begin":
                        begin_line = j
                        break
                break
        self.assertIsNotNone(begin_line)
        for j in range(begin_line + 1, len(src.lines)):
            if src.lines[j].strip() == "end;":
                end_line = j
                break
        self.assertIsNotNone(end_line)

        # Each non-blank, non-`end` line between begin and end should
        # report at least one goal.
        empty_lines = []
        for line in range(begin_line + 1, end_line):
            stripped = src.lines[line].strip()
            if not stripped or stripped.startswith("(*"):
                continue
            result = self.server.goals(uri, line=line, character=0)
            goals = (result or {}).get("goals") or []
            if not goals:
                empty_lines.append(line)
        self.assertFalse(empty_lines,
            f"mid-proof lines with no goals: {empty_lines}")


class TestSequentialStability(LSPTestCase):
    """Repeated identical requests should return identical results.

    If any stateful (Timed) side-effect leaks, we'll see drift."""

    def test_repeated_hover_stable(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"symbol zero : Nat", "Nat")
        first = self.server.hover(uri, line, col)
        for _ in range(5):
            again = self.server.hover(uri, line, col)
            self.assertEqual(again, first,
                "hover result drifted between identical calls")

    def test_repeated_definition_stable(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"rule double zero", "zero")
        first = self.server.definition(uri, line, col)
        for _ in range(5):
            again = self.server.definition(uri, line, col)
            self.assertEqual(again, first,
                "definition result drifted between identical calls")


class TestNonStandardMode(LSPTestCase):
    """When standard_lsp is OFF, diagnostics carry embedded goal_info.

    This is the mode the Zed extension and lp-goals rely on; it's
    completely untested otherwise."""

    standard_lsp = False

    @requires_stdlib
    def test_diagnostics_embed_goal_info_in_proofs(self):
        _uri, _text, _src, diags = self.open_fixture("proof.lp")
        # At least one diagnostic inside a proof should carry goal_info.
        with_goals = [d for d in diags if "goal_info" in d]
        self.assertGreater(len(with_goals), 0,
            "non-standard mode should embed goal_info on proof diagnostics")

    def test_simple_file_still_works(self):
        _uri, _text, _src, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags)


class TestBoundaryPositions(LSPTestCase):
    """Hovering / jumping at boundary positions must not hang or crash."""

    def test_hover_past_end_of_line(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        # First line: "constant symbol Nat : TYPE;" — hover way past it.
        result = self.server.hover(uri, 0, 1000)
        # Must return (null or well-formed); must not hang.
        if result is not None and "range" in result:
            ok, why = _valid_range(result["range"])
            self.assertTrue(ok, f"bad range: {why}")

    def test_hover_past_last_line(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        result = self.server.hover(uri, 10000, 0)
        if result is not None and "range" in result:
            ok, why = _valid_range(result["range"])
            self.assertTrue(ok, f"bad range: {why}")

    def test_definition_past_end_of_line(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        # Must return null / not crash.
        self.server.definition(uri, 0, 1000)
        self.server.definition(uri, 10000, 0)

    def test_hover_at_exact_line_end(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        for lineno, line in enumerate(src.lines):
            if not line:
                continue
            result = self.server.hover(uri, lineno, len(line))
            if result is not None and "range" in result:
                ok, why = _valid_range(result["range"])
                self.assertTrue(ok, f"line {lineno}: {why}")


class TestErrorRecovery(LSPTestCase):
    """Server must remain responsive after errors — no hangs, no crashes."""

    def test_hover_on_error_bearing_symbol(self):
        uri, _text, src, diags = self.open_fixture("with_error.lp")
        # There's an error on `symbol bad : Undefined;`. Hover on each
        # identifier in that line should either null-out or return a
        # well-formed response.
        err_line, _ = src.find(r"symbol bad : Undefined", "bad")
        for col in range(len(src.lines[err_line])):
            result = self.server.hover(uri, err_line, col)
            if result is not None and "range" in result:
                ok, why = _valid_range(result["range"])
                self.assertTrue(ok,
                    f"col {col} on error line: {why}")

    def test_rapid_didChange_converges(self):
        """Rapid-fire changes should still leave us with consistent diags."""
        uri, text, _src, _ = self.open_fixture("simple.lp")
        clean = text
        broken = text + "\nsymbol bad : Undefined;\n"
        # Flip-flop many times, no reads in between.
        for v in range(2, 10):
            self.server.did_change(uri, broken if v % 2 == 0 else clean, v)
        # Final state (v=9, odd) is broken -> wait, the loop above:
        # v=2: broken; v=3: clean; ... v=9: clean. So final is clean.
        final_diags = self.server.extract_diagnostics(
            self.server.drain_notifications(timeout=5.0), uri=uri)
        # We expect the final state to match: no errors (clean was last).
        self.assertNoErrors(final_diags,
            "after rapid-fire flips ending clean, errors remain")


class TestSymPosAbsent(LSPTestCase):
    """Symbols without sym_pos (ghost symbols) must not crash go-to-def."""

    def test_definition_on_unif_rule_symbol(self):
        """Hover on a built-in/ghost symbol should return null, not crash."""
        text = (
            "constant symbol Nat : TYPE;\n"
            "constant symbol zero : Nat;\n"
            # Implicit uses of ghost equivs can appear during unification;
            # we can't easily force a ghost in user source, but we CAN
            # exercise the null-handling path by asking for a def on a
            # non-symbol position.
            "symbol x : Nat ≔ zero;\n"
        )
        uri, src, _ = self.open_text("ghostprobe.lp", text)
        # Position on the `≔` character — not a symbol identifier.
        line, _ = src.find(r"symbol x")
        col = src.lines[line].index("≔")
        # Must return (null / empty / well-formed) without hanging.
        result = self.server.definition(uri, line, col)
        if result is not None and isinstance(result, dict) and "range" in result:
            ok, why = _valid_range(result["range"])
            self.assertTrue(ok, f"bad range: {why}")


if __name__ == "__main__":
    unittest.main()
