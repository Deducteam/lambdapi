(** Compute the inverse image of a term wrt an injective function. *)

open Term
open Timed
open Common
open Print
open Lplib.Extra

(** Logging function for unification. *)
let log_inv = Logger.make 'v' "invr" "inverse"
let log_inv = log_inv.pp

(** [cache f s] is equivalent to [f s] but [f s] is computed only once unless
   the rules of [s] are changed. *)
let cache : (sym -> 'a) -> (sym -> 'a) = fun f ->
  let cache = ref [] in
  fun s ->
  let srs = !(s.sym_rules) in
  try let rs, x = List.assq s !cache in
      if rs == srs then x else raise Not_found
  with Not_found -> let x = f s in cache := (s, (srs, x))::!cache; x

(** [const_graph s] returns the list of pairs [(s0,s1)] such that [s]
   has a rule of the form [s (s0 ...) ↪ s1 ...]. *)
let const_graph : sym -> (sym * sym) list = fun s ->
  if Logger.log_enabled () then log_inv "check rules of %a" pp_sym s;
  let add s0 s1 l =
    if Logger.log_enabled () then
      log_inv (yel "%a %a ↪ %a") pp_sym s pp_sym s0 pp_sym s1;
    (s0,s1)::l
  in
  let f l rule =
    match rule.lhs with
    | [l1] ->
        begin
          match get_args l1 with
          | Symb s0, _ ->
              let n = Bindlib.mbinder_arity rule.rhs in
              let r = Bindlib.msubst rule.rhs (Array.make n TE_None) in
              begin
                match get_args r with
                | Symb s1, _ -> add s0 s1 l
                | _ -> l
              end
          | _ -> l
        end
    | _ -> l
  in
  List.fold_left f [] !(s.sym_rules)

(** cached version of [const_rules]. *)
let const_graph : sym -> (sym * sym) list = cache const_graph

(** [inverse_const s s'] returns [s0] if [s] has a rule of the form [s (s0
   ...) ↪ s' ...].
@raise [Not_found] otherwise. *)
let inverse_const : sym -> sym -> sym = fun s s' ->
  fst (List.find (fun (_,s1) -> s1 == s') (const_graph s))

(** [prod_graph s] returns the list of tuples [(s0,s1,s2,b)] such that [s] has
   a rule of the form [s (s0 _ _) ↪ Π x:s1 _, s2 r] with [b=true] iff [x]
   occurs in [r]. *)
let prod_graph : sym -> (sym * sym * sym * bool) list = fun s ->
  if Logger.log_enabled () then log_inv "check rules of %a" pp_sym s;
  let add (s0,s1,s2,b) l =
    if Logger.log_enabled () then
      if b then log_inv (yel "%a (%a _ _) ↪ Π x:%a _, %a _[x]")
                  pp_sym s pp_sym s0 pp_sym s1 pp_sym s2
      else log_inv (yel "%a (%a _ _) ↪ %a _ → %a _")
             pp_sym s pp_sym s0 pp_sym s1 pp_sym s2;
    (s0,s1,s2,b)::l
  in
  let f l rule =
    match rule.lhs with
    | [l1] ->
    begin
      match get_args l1 with
      | Symb s0, [_;_] ->
        let n = Bindlib.mbinder_arity rule.rhs in
        let r = Bindlib.msubst rule.rhs (Array.make n TE_None) in
        begin
        match r with
        | Prod(a,b) ->
          begin
          match get_args a with
          | Symb s1, [_] ->
            begin
            match get_args (Bindlib.subst b mk_Kind) with
            | Symb(s2), [_] -> add (s0,s1,s2,Bindlib.binder_occur b) l
            | _ -> l
            end
          | _ -> l
          end
        | _ -> l
        end
      | _ -> l
    end
    | _ -> l
  in
  List.fold_left f [] !(s.sym_rules)

(** cached version of [prod_graph]. *)
let prod_graph : sym -> (sym * sym * sym * bool) list = cache prod_graph

(** [inverse_prod s s'] returns [(s0,s1,s2,b)] if [s] has a rule of the form
   [s (s0 _ _) ↪ Π x:s1 _, s2 r] with [b=true] iff [x] occurs in [r], and
   either [s1] has a rule of the form [s1 (s3 ...) ↪ s' ...] or [s1 == s'].
@raise [Not_found] otherwise. *)
let inverse_prod : sym -> sym -> sym * sym * sym * bool = fun s s' ->
  match prod_graph s with
  | [] -> raise Not_found
  | [x] -> x
  | graph ->
  let f (_,s1,_,_) =
    try let _ = inverse_const s1 s' in true with Not_found -> false in
  try List.find f graph
  with Not_found -> List.find (fun (_,s1,_,_) -> s1 == s') graph

(** [inverse s v] tries to compute a term [u] such that [s(u)] reduces to [v].
@raise [Not_found] otherwise. *)
let rec inverse : sym -> term -> term = fun s v ->
  if Logger.log_enabled () then log_inv "compute %a⁻¹(%a)" pp_sym s pp_term v;
  match get_args v with
  | Symb s', [t] when s' == s -> t
  | Symb s', ts -> add_args (mk_Symb (inverse_const s s')) ts
  | Prod(a,b), _ ->
      let s0,s1,s2,occ =
        match get_args a with
        | Symb s', _ -> inverse_prod s s'
        | _ -> raise Not_found
      in
      let t1 = inverse s1 a in
      let t2 =
        let x, b = Bindlib.unbind b in
        let b = inverse s2 b in
        if occ then
          Bindlib.unbox (_Abst (lift a) (Bindlib.bind_var x (lift b)))
        else b
      in
      add_args (mk_Symb s0) [t1;t2]
  | _ -> raise Not_found

let inverse : sym -> term -> term = fun s v ->
  let t = inverse s v in
  if Eval.eq_modulo [] (mk_Appl(mk_Symb s,t)) v then t
  else raise Not_found
