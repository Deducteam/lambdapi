open Common
open Term

let coerce : sym =
  let id = Pos.none "coerce" in
  Sign.add_symbol Ghost.sign Public Defin Eager false id mk_Kind []

let apply a b t : term = add_args (mk_Symb coerce) [a; b; t]

let _ =
  (* Add the rule [coerce $A $A $t ↪ $t] (but we don't have access to
     the parser here) *)
  let rule =
    let lhs =
      [ mk_Patt (Some 0, "A", [||])
      ; mk_Patt (Some 0, "A", [||])
      ; mk_Patt (Some 1, "t", [||]) ]
    in
    let vars = [|new_tevar "A"; new_tevar "t"|] in
    let rhs = _TEnv (_TE_Vari vars.(1)) [||] in
    let rhs = Bindlib.(bind_mvar vars rhs |> unbox) in
    let arity = 3 in
    let arities = [|0; 0|] in
    { lhs; rhs; arity; arities; vars; xvars_nb = 0; rule_pos = None }
  in
  Sign.add_rule Ghost.sign coerce rule
