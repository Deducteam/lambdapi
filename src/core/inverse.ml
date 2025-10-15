(** Compute the inverse image of a term wrt an injective function. *)

open Term
open Timed
open Common
open Print
open Lplib

(** Logging function for unification. *)
let log = Logger.make 'v' "invr" "inverse"
let log = log.pp

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
  if Logger.log_enabled () then log "check rules of %a" sym s;
  let add s0 s1 l =
    if Logger.log_enabled () then
      log (Color.yel "%a %a ↪ %a") sym s sym s0 sym s1;
    (s0,s1)::l
  in
  let f l rule =
    match rule.lhs with
    | [l1] ->
        begin
          match get_args l1 with
          | Symb s0, _ ->
              begin
                match get_args rule.rhs with
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
  if Logger.log_enabled () then log "check rules of %a" sym s;
  let add (s0,s1,s2,b) l =
    if Logger.log_enabled () then
      if b then log (Color.yel "%a (%a _ _) ↪ Π x:%a _, %a _[x]")
                  sym s sym s0 sym s1 sym s2
      else log (Color.yel "%a (%a _ _) ↪ %a _ → %a _")
             sym s sym s0 sym s1 sym s2;
    (s0,s1,s2,b)::l
  in
  let f l rule =
    match rule.lhs with
    | [l1] ->
    begin
      match get_args l1 with
      | Symb s0, [_;_] ->
        begin
        match rule.rhs with
        | Prod(a,b) ->
          begin
          match get_args a with
          | Symb s1, [_] ->
            begin
            match get_args (subst b mk_Kind) with
            | Symb(s2), [_] -> add (s0,s1,s2,binder_occur b) l
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

(** [inverse s v] tries to compute a term [u] such that [s(u)] reduces to [v].
@raise [Not_found] otherwise. *)
let rec inverse : sym -> term -> term = fun s v ->
  if Logger.log_enabled () then log "compute %a⁻¹(%a)" sym s term v;
  match get_args v with
  | Symb s', [t] when s' == s -> t
  | Symb s', ts -> add_args (mk_Symb (inverse_const s s')) ts
  | Prod(a,b), _ ->
      let x, b = unbind b in
      let f (s0,s1,s2,occ) =
        try
          let t1 = inverse s1 a in
          let t2 = inverse s2 b in
          let t2 = if occ then mk_Abst (a, bind_var x t2) else t2 in
          Some (add_args (mk_Symb s0) [t1;t2])
        with Not_found -> None
      in
      begin
        match List.find_map f (prod_graph s) with
        | None -> raise Not_found
        | Some t -> t
      end
  | _ -> raise Not_found

let inverse : sym -> term -> term = fun s v ->
  let t = inverse s v in let v' = mk_Appl(mk_Symb s,t) in
  if Eval.eq_modulo [] v' v then t
  else (if Logger.log_enabled() then log "%a ≢ %a" term v' term v;
        raise Not_found)
