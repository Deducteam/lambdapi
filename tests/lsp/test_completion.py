"""Completion tests: symbols, proof-context tactic keywords, hypotheses,
and lazy detail via completionItem/resolve."""

import unittest

from .base import LSPTestCase


def _completion_request(srv, uri, line, character):
    return srv.request("textDocument/completion", {
        "textDocument": {"uri": uri},
        "position": {"line": line, "character": character},
    })


class TestCompletion(LSPTestCase):

    def test_in_scope_symbols_listed(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        items = r.get("items", [])
        labels = [i["label"] for i in items]
        for expected in ("Nat", "zero", "succ", "double"):
            self.assertIn(expected, labels,
                f"{expected!r} should appear in completion list")

    def test_symbol_items_omit_detail_but_carry_resolve_data(self):
        """Symbol detail is computed on [completionItem/resolve], not in
        the initial response. The initial response carries a [data] field
        pointing back at the symbol so resolve can look it up."""
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        by_label = {i["label"]: i for i in r.get("items", [])}
        succ = by_label.get("succ")
        self.assertIsNotNone(succ)
        self.assertNotIn("detail", succ,
            f"detail should be attached lazily via resolve; got {succ!r}")
        data = succ.get("data")
        self.assertIsInstance(data, dict,
            f"symbol item needs a [data] field for resolve; got {succ!r}")
        self.assertEqual(data.get("kind"), "symbol")
        self.assertEqual(data.get("name"), "succ")
        self.assertIn("path", data)

    def test_resolve_attaches_type_detail(self):
        """completionItem/resolve on a symbol item returns the same item
        with [detail] populated."""
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 5, 0)
        succ = next(i for i in r.get("items", []) if i["label"] == "succ")
        resolved = self.server.resolve_completion(succ)
        self.assertIsNotNone(resolved)
        self.assertIn("Nat", resolved.get("detail", ""),
            f"resolved detail should mention Nat; got {resolved!r}")

    def test_no_tactic_completions_outside_proof(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _completion_request(self.server, uri, 0, 0)
        labels = [i["label"] for i in r.get("items", [])]
        self.assertNotIn("refine", labels)
        self.assertNotIn("rewrite", labels)


class TestCompletionInProof(LSPTestCase):
    """Inside a begin..end block, tactic keywords + hypotheses appear."""

    PROOF = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol triv : Nat \u2192 Nat \u2254\n"
        "begin\n"
        "  assume n;\n"
        "  refine n;\n"
        "end;\n"
    )

    def test_tactic_completions_in_proof(self):
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 is "  refine n;" — cursor at col 0 is inside the proof.
        r = _completion_request(self.server, uri, 5, 0)
        labels = [i["label"] for i in r.get("items", [])]
        for kw in ("refine", "reflexivity", "apply", "assume",
                   "eval", "fail"):
            self.assertIn(kw, labels,
                f"{kw!r} should be offered inside a proof; got {labels[:8]}")

    def test_hypothesis_completions_in_proof(self):
        """After `assume n`, the hypothesis `n` should appear as a
        completion with CompletionItemKind.Variable (6) and its type."""
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        # Line 5 (`  refine n;`), col 0: after `assume n;` on line 4.
        r = _completion_request(self.server, uri, 5, 0)
        by_label = {i["label"]: i for i in r.get("items", [])}
        self.assertIn("n", by_label,
            f"hypothesis 'n' should appear; got {sorted(by_label)[:20]}")
        n_item = by_label["n"]
        self.assertEqual(n_item["kind"], 6,
            f"hypothesis kind should be Variable (6); got {n_item['kind']}")
        self.assertIn("Nat", n_item.get("detail", ""),
            f"hypothesis detail should carry its type; got {n_item!r}")


class TestSnippetSupport(LSPTestCase):
    """Tactic completions carry TextMate-style [insertText] /
    [insertTextFormat=2] when the client advertises snippetSupport,
    and omit them otherwise."""

    advertise_snippet_support = True

    PROOF = TestCompletionInProof.PROOF

    def test_tactic_with_arg_emits_snippet(self):
        uri, _src, _ = self.open_text("prf.lp", self.PROOF)
        r = _completion_request(self.server, uri, 5, 0)
        apply_item = next(i for i in r.get("items", [])
                          if i["label"] == "apply")
        self.assertEqual(apply_item.get("insertTextFormat"), 2,
            f"snippet format expected; got {apply_item!r}")
        self.assertIn("${1:", apply_item.get("insertText", ""),
            f"insertText should contain a tab-stop; got {apply_item!r}")


class TestNoSnippetSupport(LSPTestCase):
    """With snippetSupport off, tactic items have no [insertText]."""

    advertise_snippet_support = False

    def test_tactic_lacks_insertText(self):
        uri, _src, _ = self.open_text("prf.lp", TestCompletionInProof.PROOF)
        r = _completion_request(self.server, uri, 5, 0)
        apply_item = next(i for i in r.get("items", [])
                          if i["label"] == "apply")
        self.assertNotIn("insertText", apply_item,
            f"expected no insertText without snippetSupport; got {apply_item!r}")
        self.assertNotIn("insertTextFormat", apply_item)


if __name__ == "__main__":
    unittest.main()
