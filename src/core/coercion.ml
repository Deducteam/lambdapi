open Common
open Term

let coerce : sym =
  let id = Pos.none "#c" in
  Sign.add_symbol Ghost.sign Public Defin Eager false id mk_Kind []

let is_coercion : sym -> bool = (==) coerce

(** [apply t a b] creates the coercion of [t] from [a] to [b]. *)
let apply : term -> term -> term -> term = fun t a b ->
  add_args (mk_Symb coerce) [a; t; b]

(** [has_coercions t] is true if term [t] contains the symbol
    [Coercions.coerce]. *)
let has_coercions : term -> bool = fun t ->
  let exception Found in
  let do_symb s = if is_coercion s then raise Found in
  try LibTerm.iter ~do_symb t; false with Found -> true

let _ =
  (* Add the rule [coerce $a $t $a --> $t] (but we don't have access to
     the parser here) *)
  let rule =
    let lhs =
      [ mk_Patt (Some 0, "a", [||])
      ; mk_Patt (Some 1, "_", [||])
      ; mk_Patt (Some 0, "a", [||]) ]
    in
    let vars = [|new_tevar "x"; new_tevar "y"|] in
    let rhs = _TEnv (_TE_Vari vars.(1)) [||] in
    let rhs = Bindlib.(bind_mvar vars rhs |> unbox) in
    let arity = 3 in
    let arities = [|0; 0|] in
    { lhs; rhs; arity; arities; vars; xvars_nb = 0; rule_pos = None }
  in
  Sign.add_rule Ghost.sign coerce rule
