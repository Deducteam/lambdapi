symbol const T : TYPE
symbol const U : TYPE

definition fst : T ⇒ U ⇒ T ≔ λ x _, x
definition snd : T ⇒ U ⇒ U ≔ λ _ x, x

theorem trivial : T ⇒ T ⇒ T ⇒ T
proof
  intro _ _ x
  refine x
qed
