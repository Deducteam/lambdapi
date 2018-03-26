(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console
open Eval

let prod x t u = Prod(t, Bindlib.unbox (Bindlib.bind_var x (lift u)))

type constr = ctxt * term * term

let pp_constr : out_channel -> constr -> unit = fun oc (c,t,u) ->
  Printf.fprintf oc "%a ⊢ %a ~ %a" pp_ctxt c pp t pp u

type problem = constr list

let pp_problem : out_channel -> problem -> unit = fun oc p ->
  if p = [] then output_string oc "∅"
  else List.pp pp_constr ", " oc p

(** [unbind_tbinder c t f] returns the triple [(x,u,c')] where [(x,u)] is the
    result of unbinding [f] and [c'] the extension of [c] with [x] mapped
    to [t]. *)
let unbind_tbinder (c:ctxt) (t:term) (f:tbinder) : tvar * term * ctxt =
  let (x,u) = Bindlib.unbind mkfree f in
  let c = if Bindlib.binder_occur f then add_tvar x t c else c in
  x,u,c

let unbind_tbinder2 (c:ctxt) (t:term) (f:tbinder) (g:tbinder)
    : tvar * term * term * ctxt =
  let (x,u,v) = Bindlib.unbind2 mkfree f g in
  let c =
    if Bindlib.binder_occur f || Bindlib.binder_occur g
    then add_tvar x t c else c in
  x,u,v,c

exception Exit

let distinct_vars a =
  let acc = ref [] in
  let fn t =
    match t with
    | Vari v ->
       if List.exists (Bindlib.eq_vars v) !acc then raise Exit
       else acc := v::!acc
    | _ -> raise Exit
  in
  let res = try Array.iter fn a; true with Exit -> false in
  acc := []; res

type error =
  | E_not_a_sort of term
  | E_not_a_product of term
  | E_not_convertible of term * term
  | E_not_typable of term

exception Error of error

let rec infer : problem -> ctxt -> term -> problem * term =
  fun p c t ->
  if !debug_type then log "INFR" "%a; %a ⊢ %a : ?" pp_problem p pp_ctxt c pp t;
  let p, typ_t =
    match unfold t with
    (* Sort *)
    | Type        -> p, Kind
    (* Variable *)
    | Vari(x)     ->
       begin try p, find_tvar x c with Not_found -> assert false end
    (* Symbol *)
    | Symb(s)     -> p, s.sym_type
    (* Product *)
    | Prod(t,f) ->
       begin
        let p = check p c t Type in
        let x,u,c = unbind_tbinder c t f in
        let p, typ_u = infer p c u in
        match whnf typ_u with
        | Type | Kind -> p, typ_u
        | _ -> raise (Error (E_not_a_sort typ_u))
       end
    (* Abstraction *)
    | Abst(t,f) ->
       begin
        let p = check p c t Type in
        let x,u,c = unbind_tbinder c t f in
        let p, typ_u = infer p c u in
        p, prod x t typ_u
       end
    (* Application *)
    | Appl(t,u) ->
       begin
        let p, typ_u = infer p c u in
        let p, typ_t = infer p c t in
        match whnf typ_t with
        | Prod(a,f) -> add_constr c a typ_u p, Bindlib.subst f u
        | _ -> raise (Error (E_not_a_product typ_t))
       end
    (* Metavariable *)
    | Meta(m, ts) ->
       (* The type of [Meta(m,ts)] is the same as [add_args v ts]
         where [v] is some fresh variable with the same type as [m]. *)
       begin
        let v = Bindlib.new_var mkfree (meta_name m) in
        let c = add_tvar v m.meta_type c in
        infer p c (add_args (Vari v) (Array.to_list ts))
       end
    (* No rule apply. *)
    | Kind        -> raise (Error (E_not_typable t))
    | Patt(_,_,_) -> assert false
    | TEnv(_,_)   -> assert false
  in
  if !debug_type then
    log "INFR" (gre "%a; %a ⊢ %a : %a") pp_problem p pp_ctxt c pp t pp typ_t;
  p, typ_t

and check : problem -> ctxt -> term -> term -> problem =
  fun p c t u ->
    let p, typ_t = infer p c t in
    add_constr c typ_t u p

and add_constr : ctxt -> term -> term -> problem -> problem =
  fun c t1 t2 p ->
    let t1 = whnf t1 and t2 = whnf t2 in
    let h1, ts1 = get_args t1 and h2, ts2 = get_args t2 in
    let n1 = List.length ts1 and n2 = List.length ts2 in
    match h1, h2 with
    | Type, Type
    | Kind, Kind ->
       if ts1 = [] then
         if ts2 = [] then p
         else raise (Error (E_not_typable t2))
       else raise (Error (E_not_typable t1))

    | Vari x, Vari y ->
       if Bindlib.eq_vars x y && n1 = n2 then add_constr2 c ts1 ts2 p
       else raise (Error (E_not_convertible (t1,t2)))

    | Prod(a,f), Prod(b,g) ->
       if ts1=[] then
         if ts2=[] then
           let p = add_constr c a b p in
           let x,u,v,c = unbind_tbinder2 c a f g in
           add_constr c u v p
         else raise (Error (E_not_typable t2))
       else raise (Error (E_not_typable t1))

    | Abst(a,f), Abst(b,g) ->
       (* [ts1] and [ts2] are empty since [t1] and [t2] are in whnf. *)
       let p = add_constr c a b p in
       let x,u,v,c = unbind_tbinder2 c a f g in
       add_constr c u v p

    | Symb(s1), Symb(s2) when s1.sym_rules = [] && s2.sym_rules = [] ->
       if s1 == s2 && n1 = n2 then add_constr2 c ts1 ts2 p
       else raise (Error (E_not_convertible (t1,t2)))

    | Symb(s1), Symb(s2) when s1==s2 && n1 = 0 && n2 = 0 -> p

    | Meta(m1,a1), Meta(m2,a2) when m1==m2 && a1==a2 && n1 = 0 && n2 = 0 -> p

    | Meta(m,a), _ when n1 = 0 && distinct_vars a
(*FIXME:&& not (occurs m t2) *) ->
       let get_var = function Vari v -> v | _ -> assert false in
       let b = Array.map get_var a in
       Unif.set_meta m (Bindlib.unbox (Bindlib.bind_mvar b (lift t2)));
       p

    | Meta(_,_), _
    | _, Meta(_,_)
    | Symb(_), _
    | _, Symb(_) -> (c,t1,t2)::p

    | _, _ -> raise (Error (E_not_convertible (t1,t2)))

and add_constr2 : ctxt -> term list -> term list -> problem -> problem =
  fun c ts1 ts2 p ->
    let fn p a b = add_constr c a b p in
    List.fold_left2 fn p ts1 ts2

let has_type : ctxt -> term -> term -> bool = fun c t u ->
  let p = check [] c t u in
  p = []

let sort_type : ctxt -> term -> bool = fun c t ->
  let p, typ_t = infer [] c t in
  match typ_t with
  | Type | Kind -> p = []
  | _ -> false

let infer : ctxt -> term -> term option = fun c t ->
  let p, typ_t = infer [] c t in
  if p = [] then Some typ_t else None
