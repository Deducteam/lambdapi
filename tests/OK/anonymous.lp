constant symbol T : TYPE
constant symbol U : TYPE

definition fst : T → U → T ≔ λ x _, x
definition snd : T → U → U ≔ λ _ x, x

theorem trivial : T → T → T → T
proof
  assume _ _ x
  refine x
qed
