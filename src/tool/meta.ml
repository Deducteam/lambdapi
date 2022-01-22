open Core
open Timed
open Lplib
open Extra

let rewrite_with (sign : Sign.t) (rules : (Term.sym * Term.rule) list) :
    Term.term -> Term.term =
  let exec t =
    (* Remove rules and definitions from {b!all} signatures *)
    let strip_sym _ s =
      s.Term.sym_rules := [];
      s.Term.sym_def := None;
      Tree.update_dtree s
    in
    Common.Path.Map.iter
      (fun _ s -> StrMap.iter strip_sym !(s.Sign.sign_symbols))
      Timed.(!Sign.loaded);
    (* Add a set of custom rules *)
    List.iter (fun (s, r) -> Sign.add_rule sign s r) rules;
    Eval.snf [] t
  in
  pure_apply exec
