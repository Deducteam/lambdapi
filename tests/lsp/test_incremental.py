"""Incremental checking: didChange and position shifting."""

import unittest

from .base import LSPTestCase


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


if __name__ == "__main__":
    unittest.main()
