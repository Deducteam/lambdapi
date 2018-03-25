(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console

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

type error =
  | E_not_a_sort of term
  | E_not_a_product of term
  | E_not_convertible of term * term

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
    | Symb(s)     -> p, symbol_type s
    (* Product *)
    | Prod(t,f) ->
       begin
        let p = check p c t Type in
        let x,u,c = unbind_tbinder c t f in
        let p, typ_u = infer p c u in
        match typ_u with
        | Type | Kind -> p, typ_u
        | _ -> raise (Error (E_not_a_sort typ_u))
       end
    (* Abstraction *)
    | Abst(t,f) ->
       begin
        let p = check p c t Type in
        let x,u,c = unbind_tbinder c t f in
        let p, typ_u = infer p c u in
        p, prod x t u
       end
    (* Application *)
    | Appl(t,u) ->
       begin
        let p, typ_u = infer p c u in
        let p, typ_t = infer p c t in
        match typ_t with
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
    | Kind        -> assert false
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
  fun c t u p ->
    match t, u with
    | Symb(Sym(s1)), Symb(Sym(s2)) when s1 == s2 -> p
    | Symb(Def(s1)), Symb(Def(s2)) when s1 == s2 -> p
    | Meta(m1,a1), Meta(m2,a2) when m1==m2 && a1==a2 -> p
    | Type, Type
    | Kind, Kind -> p
    | Vari x, Vari y ->
       if Bindlib.eq_vars x y then p
       else raise (Error (E_not_convertible (t,u)))
    | Prod(a,f), Prod(b,g)
    | Abst(a,f), Abst(b,g) ->
       let p = add_constr c a b p in
       let x,u,v,c = unbind_tbinder2 c a f g in
       add_constr c u v p
    | Patt _, _
    | _, Patt _
    | TEnv _, _
    | _, TEnv _ -> assert false
    | _, _ -> raise (Error (E_not_convertible (t,u)))

let infer : ctxt -> term -> term option = fun c t ->
  let p, typ_t = infer [] c t in
  if p = [] then Some typ_t else None

