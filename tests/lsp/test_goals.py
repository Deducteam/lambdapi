"""proof/goals: the custom request that backs lp-goals / Zed's goal panel."""

import unittest

from .base import LSPTestCase, requires_stdlib


@requires_stdlib
class TestGoals(LSPTestCase):

    def test_goals_outside_proof_is_empty(self):
        uri, _text, src, _ = self.open_fixture("proof.lp")
        # Above any proof.
        result = self.server.goals(uri, line=0, character=0)
        goals = (result or {}).get("goals") or []
        self.assertEqual(goals, [],
            f"outside any proof, expected no goals; got {goals}")

    def test_goals_inside_proof(self):
        uri, _text, src, _ = self.open_fixture("proof.lp")
        # Line after `begin` in zero_eq_zero; should have a goal.
        begin_line, _ = src.find(r"^\s*reflexivity;", "reflexivity")
        result = self.server.goals(uri, line=begin_line, character=0)
        goals = (result or {}).get("goals") or []
        self.assertGreater(len(goals), 0,
            f"inside proof, expected >=1 goal; got {goals}")

    def test_goals_after_tactic(self):
        uri, _text, src, _ = self.open_fixture("proof.lp")
        # After `assume x y h;` in eq_sym_nat there are still 1 goal,
        # with 3 hypotheses in context.
        line, _ = src.find(r"^\s*symmetry;", "symmetry")
        result = self.server.goals(uri, line=line, character=0)
        goals = (result or {}).get("goals") or []
        self.assertGreater(len(goals), 0,
            "proof in progress should have >=1 goal")
        # If hypotheses are exposed, they should include `h`.
        hyps = goals[0].get("hyps") or goals[0].get("hypotheses") or []
        if hyps:
            names = [h.get("name", h.get("hname", "")) for h in hyps]
            self.assertIn("h", names,
                f"expected `h` in hypotheses after `assume ... h`; got {names}")


class TestGoalsUriHandling(LSPTestCase):
    """goals request should behave sensibly on unknown URIs."""

    def test_goals_on_unopened_doc_does_not_crash(self):
        # This must return quickly and not hang.
        try:
            self.server.goals("file:///not-opened.lp", line=0, character=0)
        except Exception:
            pass  # An error response is OK; a hang is not.
        # Server should still handle subsequent requests.
        uri, _, _, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags)


if __name__ == "__main__":
    unittest.main()
