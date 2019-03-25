open Terms
open Print
open Basics

module Eset = Set.Make(
  struct
    type t = (term * term) 
    let compare = Pervasives.compare
  end)

exception No_relation

(** [find_relation t] calculates a pair of {!type:term} [A] and {!type:Eset.t}
    [E] such that t:A[E] holds and raises the exception [No_relation] if
    such a pair does not exist. Note that such a pair is unique if it exists
    **)
let find_relation : term -> (term * Eset.t) = fun t ->
  let t = unfold t in
  match t with
  | Symb (s, _) -> (!s.sym_type, Eset.empty)
  | Appl (_, _) ->
      (* Check if t is of the form ft₁...tn” *)
      let rec appl_aux : term list -> term -> (sym * term list) = fun acc t ->
        match t with 
        | Appl (t1, t2) -> appl_aux (t2 :: acc) t1
        | Symb (s, _)   -> (s, acc)
        | _             -> raise No_relation in 
      let (s, ts) = appl_aux [] t in
      let rs = List.map find_relation ts in
      let rec cal_relation t tlist rs es = match tlist with
        | []       -> (t, es)
        | t1 :: ts -> begin
            match t with
            | Prod (a, b) ->
                let t' = Bindlib.subst b t1 in
                let (a1, e1) :: rs' = rs in
                let es' = Eset.add (a1, a) (Eset.union es e1) in
                cal_relation t' ts rs' es'
            | _           -> raise No_relation 
            end
      in
      cal_relation s.sym_type ts rs Eset.empty
  | _           -> raise No_relation
