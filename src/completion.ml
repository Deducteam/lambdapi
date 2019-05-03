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
  match f with
  | None   -> if t1 == t2 then 0 else -1
  | Some f ->
      if List.exists (fun x -> lpo ord x t2 >= 0) args then 1
      else
        let g, args' = get_args t2 in
        let g = get_symb g in
        match g with
        | None   -> 1
        | Some g ->
            match ord f g with
            | k when k > 0 ->
                if List.for_all (fun x -> lpo ord t1 x > 0) args' then 1
                else -1
            | 0            ->
                if List.for_all (fun x -> lpo ord t1 x > 0) args' then
                  Ord.ord_lex (lpo ord) args args'
                else -1
            | _            -> -1

(** [to_rule (lhs, rhs)] tranlates the pair [(lhs, rhs)] of closed terms into
    a rule. *)
let to_rule : term * term -> sym * rule = fun (lhs, rhs) ->
  let (s, args) = get_args lhs in
  let s = get_symb s in
  match s with
  | None   -> assert false
  | Some s ->
      let vs = Bindlib.new_mvar te_mkfree [||] in
      let rhs = Bindlib.unbox (Bindlib.bind_mvar vs (lift rhs)) in
      s, { lhs = args ; rhs = rhs ; arity = List.length args ; vars = [||] }

(** [find_deps eqs] returns a pair [(symbs, deps)], where [symbs] is a list of
    (names of) new symbols and [deps] is a list of pairs of symbols. (s, t)
    is added into [deps] iff there is a equation (l, r) in [eqs] such that
    (l = s and t is a proper subterm of r) or (r = s and t is a proper subterm
    of l). In this case, we also add s and t into [symbs]. *)
let find_deps : (term * term) list -> string list * (string * string) list
  = fun eqs ->
  let deps = ref [] in
  let symbs = ref [] in
  let add_symb name =
    if not (List.mem name !symbs) then symbs := name :: !symbs in
  let add_dep dep =
    if not (List.mem dep !deps) then deps := dep :: !deps in
  let find_dep_aux (t1, t2) =
    match get_symb t1 with
    | Some sym ->
        if is_new_symb sym then
          let check_root t =
            let g, _ = get_args t in
            match get_symb g with
            | Some sym' when is_new_symb sym' ->
                add_dep (sym.sym_name, sym'.sym_name);
                add_symb sym.sym_name;
                add_symb sym'.sym_name;
            | _                           -> () in
          let _, args = get_args t2 in
          List.iter (Basics.iter check_root) args
    | None     -> () in
  List.iter
    (fun (t1, t2) -> find_dep_aux (t1, t2); find_dep_aux (t2, t1)) eqs;
  (!symbs, !deps)

module StrMap = Map.Make(struct
  type t = string
  let compare = compare
end)

exception Not_DAG

(** [topo_sort symbs edges] computes a topological sort on the directed graph
    [(symbs, edges)]. *)
let topo_sort : string list -> (string * string) list -> int StrMap.t
  = fun symbs edges ->
  let n = List.length symbs in
  let i = ref (-1) in
  let name_map =
    List.fold_left
      (fun map s -> incr i; StrMap.add s !i map) StrMap.empty symbs in
  let adj = Array.make_matrix n n 0 in
  let incoming = Array.make n 0 in
  List.iter
    (fun (s1, s2) ->
      let i1 = StrMap.find s1 name_map in
      let i2 = StrMap.find s2 name_map in
      adj.(i1).(i2) <- 1 + adj.(i1).(i2);
      incoming.(i2) <- 1 + incoming.(i2)) edges;
  let no_incoming = ref [] in
  let remove_edge (i, j) =
    if adj.(i).(j) <> 0 then begin
      adj.(i).(j) <- 0;
      incoming.(j) <- incoming.(j) - 1;
      if incoming.(j) = 0 then no_incoming := j :: !no_incoming
    end
  in
  Array.iteri
    (fun i incoming ->
      if incoming = 0 then no_incoming := i :: !no_incoming) incoming;
  let ord = ref 0 in
  let ord_array = Array.make n (-1) in
  while !no_incoming <> [] do
    let s = List.hd !no_incoming in
    ord_array.(s) <- !ord;
    incr ord;
    no_incoming := List.tl !no_incoming;
    for i = 0 to n-1 do
      remove_edge (s, i)
    done;
  done;
  if Array.exists (fun x -> x > 0) incoming then raise Not_DAG
  else
    List.fold_left
      (fun map s ->
        let i = StrMap.find s name_map in
        StrMap.add s (ord_array.(i)) map) StrMap.empty symbs

(** [ord_from_eqs eqs s1 s2] computes the order induced by the equations
    [eqs]. We first use [find_deps] to find the dependency between the new
    symbols (symbols introduced for checking SR) and compute its corresponding
    DAG. The order obtained satisfies the following property:
    1. New symbols are always larger than the orginal ones.
    2. If [s1] and [s2] are not new symbols, then we use the usual
       lexicographic order.
    3. If [s1] and [s2] are new symbols, then if the topological order is well
       defined then we compare their positions in this latter one. Otherwise,
       we use the usual lexicographic order. *)
let ord_from_eqs : (term * term) list -> sym Ord.cmp = fun eqs ->
  let symbs, deps = find_deps eqs in
  try
    let ord = topo_sort symbs deps in
    fun s1 s2 ->
      match (is_new_symb s1, is_new_symb s2) with
      | true, true   ->
          if s1 == s2 then 0
          else begin
            try
              StrMap.find s2.sym_name ord - StrMap.find s1.sym_name ord
            with _ -> Pervasives.compare s1.sym_name s2.sym_name
          end
      | true, false  -> 1
      | false, true  -> -1
      | false, false -> Pervasives.compare s1.sym_name s2.sym_name
  with Not_DAG ->
    fun s1 s2 -> Pervasives.compare s1.sym_name s2.sym_name

(** [completion eqs ord] returns the convergent rewrite system obtained from
    the completion procedure on the set of equations [eqs] using the LPO
    [lpo ord]. *)
let completion : (term * term) list -> sym Ord.cmp -> (sym * rule list) list
  = fun eqs ord ->
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
  let add_rule (s, r) = s.sym_rules := r :: !(s.sym_rules) in
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
        s.sym_rules := r :: !(s.sym_rules);
        if eq lhs lhs' then ()
        else begin
          match lpo lhs' rhs' with
          | 0            -> ()
          | k when k > 0 ->
              to_add := to_rule (lhs', rhs') :: !to_add;
              b := true;
          | _            ->
              to_add := to_rule (rhs', lhs') :: !to_add;
              b := true;
        end
      in
      let rec aux acc f rs =
        match rs with
        | []       -> ()
        | r :: rs' -> f acc rs' r; aux (r :: acc) f rs' in
      aux [] f !(s.sym_rules) in
    List.iter find_cp !symbs;
    List.iter add_rule !to_add;
    !b in
  let b = ref true in
  while !b do b := completion_aux () done;
  List.map (fun s -> (s, !(s.sym_rules))) !symbs
