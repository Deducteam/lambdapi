open Extra
open Console
open Terms
open Print
open Eq

let rec whnf_stk : term -> term list -> term * term list = fun t stk ->
  let t = unfold t in
  match (t, stk) with
  (* Push argument to the stack. *)
  | (Appl(_,f,u) , stk    ) -> whnf_stk f (u :: stk)
  (* Beta reduction. *)
  | (Abst(_,_,f) , u::stk ) -> whnf_stk (Bindlib.subst f u) stk
  (* Try to rewrite. *)
  | (Symb(Def(s)), stk    ) ->
      begin
        match match_rules s stk with
        | []          ->
            (* No rule applies. *)
            (t, stk)
        | (t,stk)::rs ->
            (* At least one rule applies. *)
            if !debug_eval && rs <> [] then
              wrn "%i rules apply...\n%!" (List.length rs);
            (* Just use the first one. *)
            whnf_stk t stk
      end
  (* In head normal form. *)
  | (_           , _      ) -> (t, stk)

(* [match_rules s stk] tries to apply the reduction rules of symbol [s]  using
   the stack [stk]. The possible abstract machine states (see [eval_stk]) with
   which to continue are returned. *)
and match_rules : def -> term list -> (term * term list) list = fun s stk ->
  let nb_args = List.length stk in
  let rec eval_args n stk =
    match (n, stk) with
    | (0, stk   ) -> stk
    | (_, []    ) -> assert false
    | (n, u::stk) -> let (u,s) = whnf_stk u [] in
                     add_args u s :: eval_args (n-1) stk
  in
  let max_req acc r = if r.arity <= nb_args then max r.arity acc else acc in
  let n = List.fold_left max_req 0 !(s.def_rules) in
  let stk = eval_args n stk in
  let match_rule acc r =
    (* First check that we have enough arguments. *)
    if r.arity > nb_args then acc else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let new_pvar _ = PVar(ref None) in
    let uvars = Array.init (Bindlib.mbinder_arity r.lhs) new_pvar in
    let lhs = Bindlib.msubst r.lhs uvars in
    if !debug_eval then log "eval" "RULE trying rule [%a]" pp_rule (s,r);
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args lhs stk =
      match (lhs, stk) with
      | ([]    , stk   ) ->
          (Bindlib.msubst r.rhs (Array.map unfold uvars), stk) :: acc
      | (t::lhs, v::stk) ->
          if eq ~rewrite:true t v then match_args lhs stk else acc
      | (_     , _     ) -> assert false
    in
    match_args lhs stk
  in
  List.fold_left match_rule [] !(s.def_rules)

(* [eval t] returns a weak head normal form of [t].  Note that some  arguments
   are evaluated if they might be used to allow the application of a rewriting
   rule. As their evaluation is kept, so this function does more normalisation
   that the usual weak head normalisation. *)
let eval : term -> term = fun t ->
  if !debug_eval then log "eval" "evaluating %a" pp t;
  let (u, stk) = whnf_stk t [] in
  let u = add_args u stk in
  if !debug_eval then log "eval" "produced %a" pp u; u
