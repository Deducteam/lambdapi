"""Incremental checking: didChange, position shifting, debouncing."""

import unittest

from .base import LSPTestCase
from .source import SourceFile


def _publishes(notifs, uri):
    return [n for n in notifs
            if n.get("method") == "textDocument/publishDiagnostics"
            and n.get("params", {}).get("uri") == uri]


class TestIncrementalEdit(LSPTestCase):

    def test_edit_clean_file_stays_clean(self):
        uri, text, _src, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags)
        # Insert a blank line at the top.
        new_text = "\n" + text
        self.server.did_change(uri, new_text, 2)
        notifs = self.server.drain_notifications(timeout=5.0)
        new_diags = self.server.extract_diagnostics(notifs, uri=uri)
        self.assertNoErrors(new_diags, "after inserting blank line")

    def test_edit_introduces_error(self):
        uri, text, _src, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags)
        new_text = text + "\nsymbol bad : Undefined;\n"
        self.server.did_change(uri, new_text, 2)
        notifs = self.server.drain_notifications(timeout=5.0)
        new_diags = self.server.extract_diagnostics(notifs, uri=uri)
        errs = self.errors(new_diags)
        self.assertGreater(len(errs), 0,
            "error introduced by edit should produce a diagnostic")
        self.assertIn("Undefined", errs[0]["message"])

    def test_edit_fixes_error(self):
        uri, text, _src, diags = self.open_fixture("with_error.lp")
        self.assertGreater(len(self.errors(diags)), 0)
        # Replace the body with a clean version.
        new_text = (
            "constant symbol Nat : TYPE;\n"
            "constant symbol zero : Nat;\n"
        )
        self.server.did_change(uri, new_text, 2)
        notifs = self.server.drain_notifications(timeout=5.0)
        new_diags = self.server.extract_diagnostics(notifs, uri=uri)
        self.assertNoErrors(new_diags,
            "errors should clear after fixing the source")


class TestPositionShifting(LSPTestCase):
    """When content is inserted above existing code, positions must shift
    correctly — both for diagnostic ranges and goals."""

    def test_diagnostic_position_shifts_on_insert(self):
        uri, text, _src, diags = self.open_fixture("with_error.lp")
        err_line = self.errors(diags)[0]["range"]["start"]["line"]
        # Insert two blank lines above.
        new_text = "\n\n" + text
        self.server.did_change(uri, new_text, 2)
        notifs = self.server.drain_notifications(timeout=5.0)
        new_errs = self.errors(
            self.server.extract_diagnostics(notifs, uri=uri))
        self.assertGreater(len(new_errs), 0)
        self.assertEqual(new_errs[0]["range"]["start"]["line"],
                         err_line + 2,
            "error line should shift by +2 after inserting 2 lines")

    def test_column_shifts_when_line_gets_leading_whitespace(self):
        """Inserting whitespace at the start of a line should shift the
        diagnostic's column, not just its line number."""
        uri, text, _src, diags = self.open_fixture("with_error.lp")
        orig_err = self.errors(diags)[0]
        # Insert 4 spaces at the start of the error line.
        lines = text.split("\n")
        err_line = orig_err["range"]["start"]["line"]
        lines[err_line] = "    " + lines[err_line]
        new_text = "\n".join(lines)
        self.server.did_change(uri, new_text, 2)
        notifs = self.server.drain_notifications(timeout=5.0)
        new_errs = self.errors(
            self.server.extract_diagnostics(notifs, uri=uri))
        self.assertGreater(len(new_errs), 0)
        self.assertEqual(
            new_errs[0]["range"]["start"]["character"],
            orig_err["range"]["start"]["character"] + 4,
            "column should shift by +4 after inserting whitespace")


class TestDebounce(LSPTestCase):
    """Rapid-fire didChanges should coalesce: only the trailing change
    triggers a re-check, and the final published diagnostics must
    reflect that trailing text."""

    def test_rapid_changes_coalesce_diagnostics(self):
        uri, text, _src, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags)
        # Drain anything from open.
        self.server.drain_notifications(timeout=0.3)
        # Fire many didChanges in tight succession; each is a complete
        # text replace under full-document sync. The final one
        # introduces an undefined name so we can verify it's the one
        # the server actually checked.
        N = 12
        for v in range(2, N + 1):
            tail = "" if v < N else "\nsymbol bad : Undefined;\n"
            self.server.did_change(uri, text + f"// rev {v}\n" + tail, v)
        notifs = self.server.drain_notifications(timeout=5.0)
        publishes = _publishes(notifs, uri)
        # The debounce design promises: when a later didChange is already
        # queued, we skip the current re-check. If we blast 11 changes
        # back-to-back, at most a handful should actually publish — we
        # pick a concrete cap rather than the permissive "less than N-1"
        # so a regression that silently reduces coalescing surfaces.
        self.assertLessEqual(len(publishes), 3,
            f"rapid edits should coalesce to <=3 publishes; "
            f"got {len(publishes)} for {N - 1} changes")
        # The trailing change must be reflected in the final state.
        final = publishes[-1]["params"]["diagnostics"]
        msgs = " ".join(d.get("message", "") for d in final)
        self.assertIn("Undefined", msgs,
            f"final diagnostics must mirror the last sent text; "
            f"got {msgs[:120]!r}")


if __name__ == "__main__":
    unittest.main()
