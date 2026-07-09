"""Position finder: locate (line, character) for a pattern in source text.

Tests need stable positions even when a fixture gains a leading line. Use
this helper to search for a distinctive pattern in the source and return
the 0-based (line, character) for a substring within the match.

Example:

    src = SourceFile(text)
    # Line-based: find the word "foo" on the line that contains "symbol foo"
    line, col = src.find(r"symbol foo", "foo")
"""

import re


class SourceFile:
    def __init__(self, text):
        self.text = text
        self.lines = text.split("\n")

    def find(self, line_pattern, token=None):
        """Find [token] on the first line matching [line_pattern].

        If [token] is None, returns the start of [line_pattern]'s match.
        Both arguments are treated as regexes.
        """
        line_re = re.compile(line_pattern)
        for lineno, line in enumerate(self.lines):
            m = line_re.search(line)
            if not m:
                continue
            if token is None:
                return lineno, m.start()
            t = re.search(token, line[m.start():])
            if not t:
                continue
            return lineno, m.start() + t.start()
        raise AssertionError(
            f"pattern {line_pattern!r} / token {token!r} not found")

    def line_of(self, pattern):
        """Return the 0-based line number of the first line matching [pattern]."""
        line_re = re.compile(pattern)
        for lineno, line in enumerate(self.lines):
            if line_re.search(line):
                return lineno
        raise AssertionError(f"pattern {pattern!r} not found")
