(** Type-checking and inference. *)

open Terms
open Print
open Extra
open Console

let prod x t u =
  let u = Bindlib.unbox (Bindlib.bind_var x (lift u)) in 
  Prod({closed=false}(*FIXME*), t, u)
    
type constr = ctxt * term * term

let pp_constr : out_channel -> constr -> unit = fun oc (c,t,u) ->
  Printf.fprintf oc "%a ⊢ %a ~ %a" pp_ctxt c pp t pp u
    
type problem = constr list

let pp_problem : out_channel -> problem -> unit = fun oc p ->
  if p = [] then output_string oc "∅"
  else List.pp pp_constr ", " oc p

exception Not_typable
  
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
    | Prod(_,t,f) ->
       begin
	 let p = check p c t Type in
	 let (x,u) = Bindlib.unbind mkfree f in
	 let c = if Bindlib.binder_occur f then add_tvar x t c else c in
	 let p, typ_u = infer p c u in
	 match typ_u with
	 | Type | Kind -> p, typ_u
	 | _ -> err "[%a] is not a sort...\n" pp typ_u; raise Not_typable
       end
    (* Abstraction *)
    | Abst(_,t,f) ->
       begin
	 let p = check p c t Type in
         let (x,u) = Bindlib.unbind mkfree f in
	 let c = if Bindlib.binder_occur f then add_tvar x t c else c in
	 let p, typ_u = infer p c u in
	 p, prod x t u
       end
    (* Application *)
    | Appl(_,t,u) ->
       begin
	 let p, typ_u = infer p c u in
	 let p, typ_t = infer p c t in
	 match typ_t with
	 | Prod(_,a,f) -> add_constr c a typ_u p, Bindlib.subst f u
	 | _ -> err "[%a] is not a product...\n" pp typ_t; raise Not_typable
       end
    (* Metavariable *)
    | Meta(m, ts) ->
       (* The type of [Meta(m,ts)] is the same as [addd_args v ts]
	  where [v] is some fresh variable with the same type as [m]. *)
       begin
	 let v = Bindlib.new_var mkfree (name_of_meta m) in
	 let c = add_tvar v m.meta_type c in
	 infer p c (add_args (Vari v) (Array.to_list ts))
       end
    (* No rule apply. *)
    | Kind        -> assert false
    | ITag(_)     -> assert false
    | Wild        -> assert false
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
    (c,t,u)::p
      
let infer : ctxt -> term -> term option = fun c t ->
  try
    let p, typ_t = infer [] c t in
    if p = [] then Some typ_t else None
  with Not_typable -> None
    
