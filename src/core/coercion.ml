open Common
open Term

let coerce : sym =
  let id = Pos.none "coerce" in
  Sign.add_symbol Ghost.sign Public Defin Eager false id None mk_Kind []

let apply a b t : term = add_args (mk_Symb coerce) [a; b; t]

let _ =
  (* Add the rule [coerce $A $A $t ↪ $t] (but we don't have access to
     the parser here) *)
  let rule =
    let a = mk_Patt (Some 0, "A", [||])
    and t = mk_Patt (Some 1, "t", [||]) in
    let lhs = [a; a; t] and arities = [|0; 0|] in
    { lhs; rhs=t; arity=3; arities; vars_nb=2; xvars_nb = 0; rule_pos = None }
  in
  Sign.add_rule Ghost.sign (coerce, rule)
