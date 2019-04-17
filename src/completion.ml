(** Completion procedure for closed equations *)

open Terms
open Basics
open Extra
open Timed

(** [lpo ord] computes the lexicographic path ordering corresponding to
    the strict total order [ord] on the set of all function symbols. *)
let rec lpo : sym Ord.cmp -> term Ord.cmp = fun ord t1 t2 ->
  let f, args = get_args t1 in
  let f = get_symb f in
  if List.exists (fun x -> lpo ord x t2 >= 0) args then 1
  else
    let g, args' = get_args t2 in
    let g = get_symb g in
    match ord f g with
    | 1 ->
        if List.for_all (fun x -> lpo ord t1 x > 0) args' then 1
        else -1
    | 0 ->
        if List.for_all (fun x -> lpo ord t1 x > 0) args' then
          Ord.ord_lex (lpo ord) args args'
        else -1
    | _ -> -1

(** [to_rule (lhs, rhs)] tranlates the pair [(lhs, rhs)] of closed terms into
    a rule. *)
let to_rule : term * term -> sym * rule = fun (lhs, rhs) ->
  let (s, args) = get_args lhs in
  let s = get_symb s in
  let vs = Bindlib.new_mvar te_mkfree [||] in
  let rhs = Bindlib.unbox (Bindlib.bind_mvar vs (lift rhs)) in
  s, { lhs = args ; rhs = rhs ; arity = List.length args ; vars = [||] }

(** [completion eqs ord] returns a pair of time points [(t1, t2)] where t1
    corresponds to the used-defined rewrite system and t2 to the convergent
    rewrite system obtained using the completion procedure. *)
let completion : (term * term) list -> sym Ord.cmp -> Time.t * Time.t
  = fun eqs ord ->
  let t1 = Time.save () in
  let lpo = lpo ord in
  (* [symbs] is used to store all the symbols appearing in the equations. *)
  let symbs = ref [] in
  (* [reset_sym t] erases all the rules defined for all the symbols in
     [symbs]. Note that these rules can be retrieved using [t1]. *)
  let reset_sym t =
    match t with
    | Symb (s, _) when not (List.mem s !symbs) ->
        s.sym_rules := [];
        symbs := s :: !symbs
    | _                                        -> () in
  List.iter
    (fun (t1, t2) -> Basics.iter reset_sym t1; Basics.iter reset_sym t2) eqs;
  let add_rule (s, r) =
    s.sym_rules := r :: !(s.sym_rules) in
  (* [orient (t1, t2)] orients the equation [t1 = t2] using LPO. *)
  let orient (t1, t2) =
    match lpo t1 t2 with
    | 0            -> ()
    | k when k > 0 -> add_rule (to_rule (t1, t2))
    | _            -> add_rule (to_rule (t2, t1)) in
  List.iter orient eqs;
  let completion_aux : unit -> bool = fun () ->
    let b = ref false in
    (* [to_add] is used to store the new rules that need to be added. *)
    let to_add = ref [] in
    (* [find_cp s] applies the following procedure to all the rules of head
       symbol [s]. *)
    let find_cp s =
      (* Intuitively, [f acc rs' r] corresponds to a sequence of Deduce,
         Simplify, and Orient (or Delete) steps in the Knuth-Bendix
         completion algorithm. Here, we attempts to deal with the critical
         pairs between [r] and the other rules. Since only closed equations
         are considered here, a critical pair between the rules (l1, r1) and
         (l2, r2) is of the form (r1, r2') or (r1', r2) where ri' is a reduct
         of ri. Note that [acc @ rs'] is the list of rules of head symbol [s]
         other than [r]. *)
      let f acc rs' r =
        s.sym_rules := acc @ rs';
        let (lhs, rhs) = to_terms (s, r) in
        let lhs' = Eval.snf lhs in
        let rhs' = Eval.snf rhs in
        if eq lhs lhs' then acc
        else begin
          match lpo lhs' rhs' with
          | 0            -> acc
          | k when k > 0 ->
              to_add := to_rule (lhs', rhs') :: !to_add;
              b := true;
              r :: acc
          | _            ->
              to_add := to_rule (rhs', lhs') :: !to_add;
              b := true;
              r :: acc
        end
      in
      let rec aux acc f rs =
        match rs with
        | []       -> ()
        | r :: rs' -> let acc = f acc rs' r in aux acc f rs' in
      aux [] f !(s.sym_rules) in
    List.iter find_cp !symbs;
    List.iter add_rule !to_add;
    !b in
  let b = ref true in
  while !b do b := completion_aux () done;
  let t2 = Time.save () in
  t1, t2
