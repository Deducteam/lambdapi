require open tests.OK.FOL tests.OK.HOL tests.OK.Eq tests.OK.FunExt
  tests.OK.Impred;

// --------------------------------------------------------------------------
// Shared setup
// --------------------------------------------------------------------------

symbol a : τ ι;
symbol b : τ ι;
symbol c : τ ι;

symbol f : τ (ι ⤳ ι);
symbol g : τ (ι ⤳ ι);
symbol h : τ (ι ⤳ ι ⤳ ι);
symbol w : τ (ι ⤳ ι ⤳ ι);

symbol q : τ (ι ⤳ ι ⤳ o);
symbol wrap : τ o → τ o;

symbol eq_point x : π (f x = g x);

symbol eq_lambda : π ((λ x, f x) = (λ x, g x)) ≔
  funExt (λ x, f x) (λ x, g x) eq_point;

// --------------------------------------------------------------------------
// Ordinary rewriting and occurrence selection
// --------------------------------------------------------------------------

symbol target_one_binder :
  π ((∀ (λ x, q (g x) b)) = ⊤);

// The redex f x depends on the quantified variable, so its equality must
// be lifted before rewriting inside the quantifier.
symbol test_rewrite_under_one_binder :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite eq_point;
  refine target_one_binder
end;

symbol eq_redex x :
  π (w (f x) (g x) = g x);

symbol target_redex_function :
  π ((∀ (λ x, q (g x) b)) = ⊤);

// Instantiate the lemma inside a compound redex, then lift its equality
// over the variable on which both sides depend.
symbol test_rewrite_under_redex_function :
  π ((∀ (λ x, q (w (f x) (g x)) b)) = ⊤) ≔
begin
  rewrite eq_redex;
  refine target_redex_function
end;

symbol target_preserve_context :
  π ((∀ (λ x, q (g x) x)) = ⊤);

// The same bound variable also occurs outside the redex. Rewriting must
// preserve that occurrence in the surrounding context.
symbol test_rewrite_under_binder_preserve_context :
  π ((∀ (λ x, q (w (f x) (g x)) x)) = ⊤) ≔
begin
  rewrite eq_redex;
  refine target_preserve_context
end;

symbol eq_two_binders x y :
  π (w (f x) (g y) = h x y);

symbol target_two_binders :
  π ((∀ (λ x, ∀ (λ y, q (h x y) b))) = ⊤);

// The redex depends on two nested binders. Lift over both in the correct
// order, keeping the arguments of h in their original positions.
symbol test_rewrite_under_two_binders :
  π ((∀ (λ x, ∀ (λ y, q (w (f x) (g y)) b))) = ⊤) ≔
begin
  rewrite eq_two_binders;
  refine target_two_binders
end;

symbol target_inner_binder_only :
  π ((∀ (λ x, ∀ (λ y, q x (g y)))) = ⊤);

// Only the inner variable occurs in the redex. The outer binder remains
// part of the context but must not be included in equality lifting.
symbol test_rewrite_under_inner_binder_only :
  π ((∀ (λ x, ∀ (λ y, q x (f y)))) = ⊤) ≔
begin
  rewrite eq_point;
  refine target_inner_binder_only
end;

// The first occurrence fixes both the lemma instance and the original
// bound variable. Rewrite its repetitions, leaving other binders, compound
// arguments and closed instances unchanged.
symbol eq_occurrences u v : π (w u v = h u v);

symbol target_first_occurrences :
  π (((∀ (λ x, q (h a x) (h a x)))
        ∧ ((∀ (λ y, q (w a y) b))
        ∧ ((∀ (λ z, q (w a (f z)) b))
        ∧ (q (w a c) b ∧ q (w b c) b)))) = ⊤);

symbol test_rewrite_alpha_equivalent_first_occurrences :
  π (((∀ (λ x, q (w a x) (w a x)))
        ∧ ((∀ (λ y, q (w a y) b))
        ∧ ((∀ (λ z, q (w a (f z)) b))
        ∧ (q (w a c) b ∧ q (w b c) b)))) = ⊤) ≔
begin
  rewrite eq_occurrences;
  refine target_first_occurrences
end;

// --------------------------------------------------------------------------
// Application selectors beneath goal binders
// --------------------------------------------------------------------------

symbol test_rewrite_application_selector :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[f _] eq_point;
  refine target_one_binder
end;

// The identifier directly names the binder-dependent redex.
symbol test_rewrite_application_id_selector :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[id in q id b] eq_point;
  refine target_one_binder
end;

// The as selector additionally constrains the identifier's value to f _.
symbol test_rewrite_application_as_selector :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[f _ as id in q id b] eq_point;
  refine target_one_binder
end;

// --------------------------------------------------------------------------
// Literal lambda patterns and wildcard scope
// --------------------------------------------------------------------------

symbol test_rewrite_named_binder_pattern :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[in (λ y, q (f y) b)] eq_point;
  refine target_one_binder
end;

symbol test_rewrite_binder_redex_pattern :
  π ((∀ (λ x, q ((λ y, f y) x) b)) = ⊤) ≔
begin
  rewrite .[(λ z, f z)] eq_lambda;
  refine target_one_binder
end;

symbol target_dependent_wildcard :
  π ((∀ (λ x, q (g x) x)) = ⊤);

// The selector wildcard matches the local bound variable in the context.
// Retain its scope while rewriting the separate occurrence f y.
symbol test_rewrite_dependent_wildcard :
  π ((∀ (λ x, q (f x) x)) = ⊤) ≔
begin
  rewrite .[in (λ y, q (f y) _)] eq_point;
  refine target_dependent_wildcard
end;

// An anonymous pattern binder and a wildcard in its body must also
// select the lambda whose body depends on its bound variable.
symbol test_rewrite_anonymous_binder_pattern :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[in (λ _, q (f _) b)] eq_point;
  refine target_one_binder
end;

// --------------------------------------------------------------------------
// Contextual patterns and reconstruction
// --------------------------------------------------------------------------

symbol test_rewrite_contextual_binder_pattern :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

symbol test_rewrite_contextual_binder_region :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[in y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

symbol target_contextual_region :
  π ((∀ (λ x, q (w (g x) (g x)) b)) = ⊤);

// The selected region contains the redex below its root. Rewrite inside
// that region without replacing the whole compound term.
symbol test_rewrite_contextual_binder_region_nested :
  π ((∀ (λ x, q (w (f x) (g x)) b)) = ⊤) ≔
begin
  rewrite .[in y in (λ x, q y b)] eq_point;
  refine target_contextual_region
end;

symbol test_rewrite_contextual_binder_explicit :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[f _ in y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

// The explicit selector must find a proper subterm of the selected
// compound region and preserve the rest of that region.
symbol test_rewrite_contextual_binder_explicit_nested :
  π ((∀ (λ x, q (w (f x) (g x)) b)) = ⊤) ≔
begin
  rewrite .[f _ in y in (λ x, q y b)] eq_point;
  refine target_contextual_region
end;

symbol test_rewrite_contextual_binder_as :
  π ((∀ (λ x, q (f x) b)) = ⊤) ≔
begin
  rewrite .[f _ as y in (λ x, q y b)] eq_point;
  refine target_one_binder
end;

symbol target_repeated_context :
  π ((∀ (λ x, q (g x) (g x))) = ⊤);

// Both uses of the contextual identifier refer to the same original
// binder, so both named occurrences must be rewritten.
symbol test_rewrite_repeated_context :
  π ((∀ (λ x, q (f x) (f x))) = ⊤) ≔
begin
  rewrite .[y in (λ x, q y y)] eq_point;
  refine target_repeated_context
end;

// A contextual identifier can name a redex depending on two binders
// opened while matching the surrounding pattern.
symbol test_rewrite_contextual_two_binders :
  π ((∀ (λ x, ∀ (λ y, q (w (f x) (g y)) b))) = ⊤) ≔
begin
  rewrite .[z in (λ x, ∀ (λ y, q z b))] eq_two_binders;
  refine target_two_binders
end;

constant symbol p_nested : τ ι → τ ι → Prop;
constant symbol q_outer : τ ι → Prop;

symbol not_all_exists_not (r : τ ι → Prop) :
  π ((¬ (∀ r)) = (`∃ x : τ ι, ¬ (r x)));

// The selected term has its own quantifiers but does not depend on a.
// Preserve those internal binders and the surrounding context when
// instantiating the lemma and rebuilding the goal.
opaque symbol contextual_rewrite_nested_quantifier :
  π ((`∀ a : τ ι, (q_outer a) ∨
        ((¬ (`∀ b : τ ι, `∃ c : τ ι, p_nested c b)) ∧ (q_outer a))) =
     (`∀ a : τ ι, (q_outer a) ∨
        ((`∃ b : τ ι, ¬ (`∃ c : τ ι, p_nested c b)) ∧ (q_outer a)))) ≔
begin
  rewrite .[x in ∀ (λ a, (q_outer a) ∨ (x ∧ (q_outer a)))]
    not_all_exists_not;
  reflexivity
end;

// --------------------------------------------------------------------------
// Selected regions with outer and inner binders
// --------------------------------------------------------------------------

symbol target_region_outer_and_inner :
  π ((∀ (λ y, wrap (∀ (λ x, q (h x y) b)))) = ⊤);

// The selected wrap region lies under y and contains a binder for x.
// The redex depends on both; preserve the outer frame while finding x.
symbol test_rewrite_region_outer_and_inner :
  π ((∀ (λ y, wrap (∀ (λ x, q (w (f x) (g y)) b)))) = ⊤) ≔
begin
  rewrite .[in wrap _] eq_two_binders;
  refine target_region_outer_and_inner
end;

// The identifier-selected region has the same outer/inner binder split.
// Carry both frames through the search and reinsertion of the context.
symbol test_rewrite_id_region_outer_and_inner :
  π ((∀ (λ y, wrap (∀ (λ x, q (w (f x) (g y)) b)))) = ⊤) ≔
begin
  rewrite .[in body in wrap body] eq_two_binders;
  refine target_region_outer_and_inner
end;

// --------------------------------------------------------------------------
// Let patterns and rewriting in let bodies
// --------------------------------------------------------------------------

symbol target_under_let_body :
  π ((let x ≔ a in q (g x) b) = ⊤);

symbol test_rewrite_under_let_body :
  π ((let x ≔ a in q (f x) b) = ⊤) ≔
begin
  rewrite eq_point;
  refine target_under_let_body
end;

symbol target_let_pattern : π ((q (g b) b) = ⊤);

symbol test_rewrite_let_pattern :
  π ((let y : τ ι ≔ f b in q y b) = ⊤) ≔
begin
  rewrite .[in (let y : τ ι ≔ f b in q y b)] eq_point;
  refine target_let_pattern
end;
