(** Type-checking and inference. *)

open Terms

let prod x t u =
  let u = Bindlib.unbox (Bindlib.bind_var x (lift u)) in 
  Prod(false (*FIXME*), t, u)
    
type constr = ctxt * term * term

let pp_constr : out_channel -> constr -> unit = fun oc (c,t,u) ->
  Printf.fprintf oc "%a ⊢ %a ~ %a" pp_ctxt c pp t pp u in
    
type problem = constr list

let pp_problem : out_channel -> problem -> unit = fun oc p ->
  if p = [] then output_string oc "∅"
  else List.pp pp_constr ", " oc p
  
let rec infer : Sign.t -> problem -> ctxt -> term -> problem * term =
  fun s p c t ->
  if !debug_type then log "INFR" "%a; %a ⊢ %a : ?" pp_problem p pp_ctxt c pp t;
  let p, typ_t =
    match unfold t with
    (* Sort *)
    | Type        -> p, Kind
    (* Variable *)
    | Vari(x)     -> try p, find_tvar x c with Not_found -> assert false
    (* Symbol *)
    | Symb(s)     -> p, symbol_type s
    (* Product *)
    | Prod(_,t,f) ->
       begin
	 let p = check s p c t Type in
	 let (x,u) = Bindlib.unbind mkfree f in
	 let c = if Bindlib.binder_occur u then add_tvar x t c else c in
	 let p, typ_u = infer s p c u in
	 match typ_u with
	 | Type | Kind -> p, typ_u
	 | _ -> err "[%a] is not a sort...\n" pp tux
       end
    (* Abstraction *)
    | Abst(_,t,f) ->
       begin
	 let p = check s p c t Type in
         let (x,u) = Bindlib.unbind mkfree f in
	 let c = if Bindlib.binder_occur f then add_tvar x t c else c in
	 let p, typ_u = infer s p c u in
	 p, prod x t u
       end
    (* Application *)
    | Appl(_,t,u) ->
       begin
	 let p, typ_u = infer s p c u in
	 let p, typ_t = infer s p c t in
	 match typ_t with
	 | Prod(_,a,f) -> (c,a,typ_u)::p, Bindlib.subst f u
	 | _ -> err "[%a] is not a product...\n" typ_t
       end
    (* Metavariable *)
    | Meta(m, ts) ->
       (* The type of [Meta(m,ts)] is the same as [addd_args v ts]
	  where [v] is some fresh variable with the same type as [m]. *)
       begin
	 let v = Bindlib.new_var mkfree (name_of_meta m) in
	 let c = add_tvar v m.meta_type c in
	 infer s p c (add_args (Vari v) (Array.to_list ts))
       end
    (* No rule apply. *)
    | Kind        -> assert false
    | ITag(_)     -> assert false
    | Wild        -> assert false
  in
  if !debug_type then
    log "INFR" (r_or_g res "%a; %a ⊢ %a : %a")
      pp_problem p pp_ctxt c pp t pp typ_t;
  p, typ_t

and check : Sign.t -> problem -> ctxt -> term -> term -> problem =
  fun s p c t u ->
    let p, typ_t = infer s p c t in
    (c,typ_t,u)::p
      
