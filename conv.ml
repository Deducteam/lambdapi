open Extra
open Console
open Terms
open Eq
open Eval

(* Representation of equality constraints. *)
type constrs = (term * term) list

(* If [constraints] is set to [None], then typechecking is in regular mode. If
   it is set to [Some(l)] then it is in constraint mode, which means that when
   equality fails, an equality constraint is added to [constrs] instead of the
   equality function giving up. *)
let constraints = ref None

(* NOTE: constraint mode is only used when type-cheching the left-hand side of
   reduction rules (see function [infer_with_constrs] for mode switching). *)

(* [add_constraint a b] adds an equality constraint between [a] and [b] if the
   program is in regular mode. In this case it returns [true].  If the program
   is in regular mode, then [false] is returned immediately. *)
let add_constraint : term -> term -> bool = fun a b ->
  match !constraints with
  | None    -> false
  | Some(l) ->
      if !debug then log "cnst" "adding constraint [%a == %a]." pp a pp b;
      constraints := Some((a, b)::l); true

let eq_modulo : term -> term -> bool = fun a b ->
  if !debug then log "equa" "%a == %a" pp a pp b;
  let rec eq_modulo l =
    match l with
    | []                   -> true
    | (a,b)::l when eq a b -> eq_modulo l
    | (a,b)::l             ->
        let (a,sa) = whnf_stk a [] in
        let (b,sb) = whnf_stk b [] in
        let rec sync acc la lb =
          match (la, lb) with
          | ([]   , []   ) -> (a, b, List.rev acc)
          | (a::la, b::lb) -> sync ((a,b)::acc) la lb
          | (la   , []   ) -> (add_args a (List.rev la), b, acc)
          | ([]   , lb   ) -> (a, add_args b (List.rev lb), acc)
        in
        let (a,b,l) = sync l (List.rev sa) (List.rev sb) in
        let a = unfold a in
        let b = unfold b in
        match (a, b) with
        | (_            , _            ) when eq a b -> eq_modulo l
        | (Appl(_,_,_)  , Appl(_,_,_)  ) -> eq_modulo ((a,b)::l)
        | (Abst(_,aa,ba), Abst(_,ab,bb)) ->
            let x = mkfree (Bindlib.new_var mkfree "_eq_modulo_") in
            eq_modulo ((aa,ab)::(Bindlib.subst ba x, Bindlib.subst bb x)::l)
        | (Prod(_,aa,ba), Prod(_,ab,bb)) ->
            let x = mkfree (Bindlib.new_var mkfree "_eq_modulo_") in
            eq_modulo ((aa,ab)::(Bindlib.subst ba x, Bindlib.subst bb x)::l)
        | (a            , b            ) -> add_constraint a b && eq_modulo l
  in
  let res = eq_modulo [(a,b)] in
  if !debug then log "equa" (r_or_g res "%a == %a") pp a pp b; res  
