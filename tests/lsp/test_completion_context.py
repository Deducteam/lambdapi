"""Context-aware completion: module paths, qualified names, argument
keywords. Keyword membership comes from the parser's follow set at
the cursor; the partial-token contexts (paths, qualified names, flag
names) are detected lexically from the line before the cursor, so
they also work while the text does not parse."""

import unittest

from .base import LSPTestCase, requires_stdlib


def _complete(srv, uri, line, character, context=None):
    params = {"textDocument": {"uri": uri},
              "position": {"line": line, "character": character}}
    if context is not None:
        params["context"] = context
    return srv.request("textDocument/completion", params)


def _labels(r):
    return {i["label"] for i in (r or {}).get("items", [])}


class TestRequirePathCompletion(LSPTestCase):
    """After `require`/`open`, complete module paths from the library
    mappings, replacing the typed partial path via a textEdit."""

    def test_require_offers_local_modules(self):
        uri, _src, _ = self.open_text("req1.lp", "require test.\n")
        r = _complete(self.server, uri, 0, 13)
        by_label = {i["label"]: i for i in r.get("items", [])}
        self.assertIn("test.simple", by_label,
            f"local module should be offered; got "
            f"{sorted(by_label)[:10]}")
        item = by_label["test.simple"]
        self.assertEqual(item.get("kind"), 9)      # Module
        te = item.get("textEdit")
        self.assertIsNotNone(te, "path items need a textEdit: '.' is "
            "not a word character, a label would insert after the dot")
        self.assertEqual(te["newText"], "test.simple")
        self.assertEqual(te["range"]["start"],
                         {"line": 0, "character": 8})
        self.assertEqual(te["range"]["end"],
                         {"line": 0, "character": 13})

    def test_require_open_offers_paths_only(self):
        uri, _src, _ = self.open_text("req2.lp", "require open test.\n")
        labels = _labels(_complete(self.server, uri, 0, 18))
        self.assertIn("test.simple", labels)
        self.assertNotIn("symbol", labels,
            "a path position should not offer command keywords")

    def test_open_offers_paths(self):
        uri, _src, _ = self.open_text("req3.lp", "open test.\n")
        self.assertIn("test.simple",
                      _labels(_complete(self.server, uri, 0, 10)))

    def test_partial_path_filters(self):
        uri, _src, _ = self.open_text("req4.lp", "require test.sim\n")
        labels = _labels(_complete(self.server, uri, 0, 16))
        self.assertIn("test.simple", labels)
        self.assertNotIn("test.proof", labels,
            "candidates should be filtered by the typed prefix")

    @requires_stdlib
    def test_require_offers_stdlib(self):
        uri, _src, _ = self.open_text("req5.lp", "require Stdlib.\n")
        self.assertIn("Stdlib.Nat",
                      _labels(_complete(self.server, uri, 0, 15)))

    def test_indented_require_offers_paths(self):
        uri, _src, _ = self.open_text("req6.lp", "  require test.\n")
        self.assertIn("test.simple",
                      _labels(_complete(self.server, uri, 0, 15)))

    def test_second_path_on_the_same_require(self):
        uri, _src, _ = self.open_text("req7.lp",
            "require test.simple test.\n")
        self.assertIn("test.inductive",
                      _labels(_complete(self.server, uri, 0, 25)))

    def test_no_paths_after_as(self):
        """`require M as <cursor>` expects a fresh alias name, not a
        module path."""
        uri, _src, _ = self.open_text("req8.lp",
            "require test.simple as \n")
        self.assertNotIn("test.simple",
                         _labels(_complete(self.server, uri, 0, 23)))

    def test_private_require_offers_paths(self):
        uri, _src, _ = self.open_text("req9.lp", "private open test.\n")
        self.assertIn("test.simple",
                      _labels(_complete(self.server, uri, 0, 18)))


class TestQualifiedCompletion(LSPTestCase):
    """After `M.` in term position, complete the non-private symbols
    of the (required) module M, resolving `require as` aliases, plus
    the next segments of loaded module paths."""

    def test_qualified_offers_module_symbols(self):
        uri, _src, _ = self.open_text("qual1.lp",
            "require test.simple;\n"
            "symbol z : test.simple.\n")
        r = _complete(self.server, uri, 1, 23)
        labels = _labels(r)
        for name in ("Nat", "zero", "succ", "double"):
            self.assertIn(name, labels,
                f"{name!r} of test.simple should be offered; "
                f"got {sorted(labels)[:10]}")

    def test_qualified_resolve_attaches_type(self):
        uri, _src, _ = self.open_text("qual2.lp",
            "require test.simple;\n"
            "symbol z : test.simple.\n")
        r = _complete(self.server, uri, 1, 23)
        item = next(i for i in r.get("items", [])
                    if i["label"] == "succ")
        resolved = self.server.resolve_completion(item)
        self.assertIn("Nat", resolved.get("detail", ""),
            f"resolved detail should carry the type; got {resolved!r}")

    def test_alias_resolves(self):
        uri, _src, _ = self.open_text("qual3.lp",
            "require test.simple as S;\n"
            "symbol z : S.\n")
        self.assertIn("Nat", _labels(_complete(self.server, uri, 1, 13)))

    def test_private_symbols_excluded(self):
        uri, _src, _ = self.open_text("qual4.lp",
            "require test.modifiers;\n"
            "symbol z : test.modifiers.\n")
        labels = _labels(_complete(self.server, uri, 1, 26))
        self.assertIn("inj", labels)
        self.assertNotIn("priv", labels,
            "private symbols must not be offered outside their module")

    def test_qualified_in_tactic_argument(self):
        uri, _src, _ = self.open_text("qual6.lp",
            "require test.simple;\n"
            "symbol z : test.simple.Nat ≔\n"
            "begin\n"
            "  apply test.simple.\n"
            "end;\n")
        labels = _labels(_complete(self.server, uri, 3, 20))
        self.assertIn("zero", labels,
            "qualified completion should work in tactic arguments")

    def test_intermediate_segment_offered(self):
        """`test.` in term position: `test` is not itself a module,
        but loaded paths extend it — offer the next segment."""
        uri, _src, _ = self.open_text("qual5.lp",
            "require test.simple;\n"
            "symbol z : test.\n")
        r = _complete(self.server, uri, 1, 16)
        by_label = {i["label"]: i for i in r.get("items", [])}
        self.assertIn("simple", by_label,
            f"next path segment should be offered; "
            f"got {sorted(by_label)[:10]}")
        self.assertEqual(by_label["simple"].get("kind"), 9)  # Module


class TestDotTrigger(LSPTestCase):
    """A "."-triggered request outside the dot-aware contexts must
    return no items (e.g. after a number), while normal invocation at
    the same position still completes."""

    def test_dot_trigger_outside_context_is_quiet(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _complete(self.server, uri, 5, 0,
                      context={"triggerKind": 2, "triggerCharacter": "."})
        self.assertEqual(r.get("items"), [],
            "dot-trigger outside path/qualified contexts must be quiet")

    def test_invoked_at_same_position_completes(self):
        uri, _text, _src, _ = self.open_fixture("simple.lp")
        r = _complete(self.server, uri, 5, 0,
                      context={"triggerKind": 1})
        self.assertIn("double", _labels(r))


class TestArgumentContexts(LSPTestCase):
    """Focused completions in argument positions: notation kinds,
    associativity sides, flag names and switches; hypotheses ranked
    first in hypothesis-taking tactic arguments."""

    def test_notation_arguments(self):
        uri, _src, _ = self.open_text("arg1.lp",
            "constant symbol Nat : TYPE;\nnotation Nat \n")
        labels = _labels(_complete(self.server, uri, 1, 13))
        for kw in ("infix", "prefix", "postfix", "quantifier"):
            self.assertIn(kw, labels,
                f"{kw!r} should be offered after `notation <id>`")
        self.assertNotIn("Nat", labels,
            "the notation-argument list should not offer symbols")

    def test_associativity_sides(self):
        uri, _src, _ = self.open_text("arg2.lp",
            "constant symbol Nat : TYPE;\nnotation Nat infix \n")
        labels = _labels(_complete(self.server, uri, 1, 19))
        self.assertIn("left", labels)
        self.assertIn("right", labels)
        self.assertNotIn("infix", labels)

    def test_flag_names(self):
        uri, _src, _ = self.open_text("arg3.lp", 'flag "\n')
        labels = _labels(_complete(self.server, uri, 0, 6))
        self.assertIn("print_implicits", labels,
            f"registered flags should be offered; got {sorted(labels)}")
        self.assertIn("eta_equality", labels)

    def test_flag_switch(self):
        uri, _src, _ = self.open_text("arg4.lp",
            'flag "print_implicits" \n')
        labels = _labels(_complete(self.server, uri, 0, 23))
        self.assertEqual(labels, {"on", "off"},
            f"after the flag string, only on/off; got {sorted(labels)}")

    def test_hypotheses_ranked_first_in_tactic_args(self):
        proof = (
            "constant symbol Nat : TYPE;\n"
            "symbol triv : Nat → Nat ≔\n"
            "begin\n"
            "  assume n;\n"
            "  apply n;\n"
            "end;\n"
        )
        uri, _src, _ = self.open_text("arg5.lp", proof)
        # Cursor after "  apply " (line 4, col 8).
        r = _complete(self.server, uri, 4, 8)
        n_item = next(i for i in r.get("items", [])
                      if i["label"] == "n")
        self.assertTrue(n_item.get("sortText", "").startswith("0"),
            f"hypothesis should rank first after `apply`; got {n_item!r}")

    def test_no_keywords_in_tactic_args(self):
        """The argument of a tactic is a term position: offering
        `have` (or any keyword) after `apply ` would be invalid."""
        proof = (
            "constant symbol Nat : TYPE;\n"
            "symbol triv : Nat → Nat ≔\n"
            "begin\n"
            "  assume n;\n"
            "  apply n;\n"
            "end;\n"
        )
        uri, _src, _ = self.open_text("arg6.lp", proof)
        labels = _labels(_complete(self.server, uri, 4, 8))
        for kw in ("have", "apply", "admitted", "print"):
            self.assertNotIn(kw, labels,
                f"{kw!r} is not valid in a tactic argument")
        self.assertIn("n", labels)
        self.assertIn("triv", labels,
            "in-scope symbols are valid tactic arguments")


class TestProofRegion(LSPTestCase):
    """Being inside the command of a theorem is not being inside its
    proof: tactics belong strictly between `begin` and `end`."""

    THM = (
        "constant symbol Nat : TYPE;\n"
        "constant symbol zero : Nat;\n"
        "symbol triv : Nat → Nat ≔\n"
        "begin\n"
        "  assume n;\n"
        "  refine n;\n"
        "end;\n"
    )

    def test_no_tactics_on_the_statement_line(self):
        uri, _src, _ = self.open_text("region1.lp", self.THM)
        # Line 2 is the statement (`symbol triv : Nat → Nat ≔`).
        labels = _labels(_complete(self.server, uri, 2, 24))
        self.assertNotIn("refine", labels,
            "the statement is not a proof position")
        self.assertIn("zero", labels)

    def test_tactics_inside_the_script(self):
        uri, _src, _ = self.open_text("region2.lp", self.THM)
        labels = _labels(_complete(self.server, uri, 5, 2))
        self.assertIn("refine", labels)

    def test_new_line_above_a_proof_gets_keywords(self):
        """Typing a new declaration above an existing proof: the doc
        no longer parses and the stale node's span covers the cursor
        line, but that line is before `begin` — command keywords, not
        tactics."""
        uri, _src, _ = self.open_text("region3.lp", self.THM)
        broken = self.THM.replace("symbol triv", "co\nsymbol triv", 1)
        self.server.did_change(uri, broken, 2)
        self.server.drain_notifications(timeout=5.0)
        # Line 2 is the fresh "co" line.
        labels = _labels(_complete(self.server, uri, 2, 2))
        self.assertIn("constant", labels,
            "command keywords should be offered above the proof")
        self.assertNotIn("refine", labels,
            "tactics must not leak out of the proof script")


class TestModifierContext(LSPTestCase):
    """After modifiers, only further modifiers and the declarations
    they qualify are valid."""

    def test_symbol_offered_after_modifier(self):
        uri, _src, _ = self.open_text("mod1.lp",
            "constant symbol Nat : TYPE;\nconstant \n")
        r = _complete(self.server, uri, 1, 9)
        by_label = {i["label"]: i for i in r.get("items", [])}
        self.assertIn("symbol", by_label,
            f"symbol should follow a modifier; got "
            f"{sorted(by_label)[:10]}")
        self.assertTrue(
            by_label["symbol"]["sortText"].startswith("0"),
            "symbol should rank first after a modifier")
        self.assertIn("injective", by_label)
        self.assertNotIn("constant", by_label,
            "already-typed modifiers are not repeated")
        self.assertNotIn("rule", by_label,
            "rule cannot follow a modifier")
        self.assertNotIn("Nat", by_label,
            "a modifier position does not take terms")

    def test_private_offers_open_not_require(self):
        uri, _src, _ = self.open_text("mod2.lp", "private \n")
        labels = _labels(_complete(self.server, uri, 0, 8))
        for kw in ("symbol", "open", "protected"):
            self.assertIn(kw, labels,
                f"{kw!r} can follow `private`")
        # `private` comes after `require`, not before:
        # `require private open M;` vs `private open M;`.
        self.assertNotIn("require", labels,
            "`private require` does not parse")

    def test_associative_offers_sides_and_symbol(self):
        uri, _src, _ = self.open_text("mod3.lp",
            "commutative associative \n")
        labels = _labels(_complete(self.server, uri, 0, 24))
        for kw in ("left", "right", "symbol"):
            self.assertIn(kw, labels,
                f"{kw!r} can follow `associative`")


class TestGrammarFollowSets(LSPTestCase):
    """Keyword completions come from the parser's follow sets: what
    the grammar accepts at the cursor, nothing else."""

    def test_require_offers_open_private_and_paths(self):
        uri, _src, _ = self.open_text("fol1.lp", "require \n")
        labels = _labels(_complete(self.server, uri, 0, 8))
        for kw in ("open", "private"):
            self.assertIn(kw, labels, f"{kw!r} can follow `require`")
        self.assertIn("test.simple", labels,
            "module paths complete after `require`")
        self.assertNotIn("symbol", labels,
            "`require symbol` does not parse")

    def test_require_path_offers_as(self):
        uri, _src, _ = self.open_text("fol2.lp",
            "require test.simple \n")
        labels = _labels(_complete(self.server, uri, 0, 20))
        self.assertIn("as", labels,
            "`require M as N;` aliases the module")
        self.assertIn("test.inductive", labels,
            "`require` takes several paths")
        self.assertNotIn("open", labels,
            "`open` only comes right after `require`")

    def test_require_alias_position_is_quiet(self):
        """`require M as <cursor>` wants a fresh name: no keywords,
        no symbols."""
        uri, _src, _ = self.open_text("fol3.lp",
            "require test.simple as \n")
        self.assertEqual(_labels(_complete(self.server, uri, 0, 23)),
                         set())

    def test_require_private_offers_only_open(self):
        uri, _src, _ = self.open_text("fol4.lp", "require private \n")
        labels = _labels(_complete(self.server, uri, 0, 16))
        self.assertIn("open", labels)
        self.assertNotIn("test.simple", labels,
            "`require private` must be followed by `open`, not a path")

    def test_notation_offers_kinds(self):
        uri, _src, _ = self.open_text("fol5.lp",
            "constant symbol Nat : TYPE;\n"
            "notation Nat \n")
        labels = _labels(_complete(self.server, uri, 1, 13))
        for kw in ("infix", "prefix", "postfix", "quantifier"):
            self.assertIn(kw, labels, f"{kw!r} can follow `notation f`")
        self.assertNotIn("Nat", labels,
            "a notation kind position does not take terms")

    def test_infix_offers_sides(self):
        uri, _src, _ = self.open_text("fol6.lp",
            "constant symbol Nat : TYPE;\n"
            "notation Nat infix \n")
        labels = _labels(_complete(self.server, uri, 1, 19))
        for kw in ("left", "right"):
            self.assertIn(kw, labels, f"{kw!r} can follow `infix`")

    def test_flag_string_offers_switch(self):
        uri, _src, _ = self.open_text("fol7.lp",
            'flag "eta_equality" \n')
        labels = _labels(_complete(self.server, uri, 0, 20))
        self.assertIn("on", labels)
        self.assertIn("off", labels)

    def test_simplify_offers_rule(self):
        uri, _src, _ = self.open_text("fol8.lp",
            "constant symbol P : TYPE;\n"
            "constant symbol p : P;\n"
            "symbol thm : P ≔\n"
            "begin\n"
            "  simplify \n"
            "  refine p;\n"
            "end;\n")
        labels = _labels(_complete(self.server, uri, 4, 11))
        self.assertIn("rule", labels,
            "`simplify rule off` disables rewrite rules")
        self.assertIn("p", labels,
            "`simplify f` takes a symbol")
        self.assertNotIn("apply", labels,
            "a tactic cannot follow `simplify` without a separator")

    def test_statement_type_offers_begin(self):
        uri, _src, _ = self.open_text("fol9.lp",
            "constant symbol P : TYPE;\n"
            "symbol thm : P \n")
        labels = _labels(_complete(self.server, uri, 1, 15))
        self.assertIn("begin", labels,
            "a proof can start after the statement's type")
        self.assertIn("P", labels,
            "the type may also continue with more term")
        self.assertNotIn("symbol", labels,
            "a command cannot start before the previous one ends")

    def test_left_offers_associative(self):
        uri, _src, _ = self.open_text("fol10.lp", "left \n")
        labels = _labels(_complete(self.server, uri, 0, 5))
        self.assertEqual(labels, {"associative"},
            "`left` must be followed by `associative`")


if __name__ == "__main__":
    unittest.main()
