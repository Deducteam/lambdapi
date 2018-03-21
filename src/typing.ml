(** Type-checking and inference. *)

open Console
open Terms
open Print
open Eval
open Unif

(** [to_prod r e xo] instantiates the metavariable [r] (with [e] as an
    environment) using a product type formed with fresh metavariables.
    The argument [xo] is used to name the bound variable. Note that the binder
    (the body) is constant if [xo] is equal to [None]. *)
let to_prod r e xo =
  let ra = new_meta Type 0 in
  let rb = new_meta Type 0 in
  (* We use dummy values for the context and type since they are not
     used in the current type-checking algorithm. *)
  let le = Array.map lift e in
  let a = _Meta ra le in
  let fn =
    match xo with
    | None    -> fun _ -> _Meta rb le
    | Some(_) -> fun x -> _Meta rb (Array.append le [|Bindlib.box_of_var x|])
  in
  let x = match xo with Some(x) -> x | None -> "_" in
  let p = Bindlib.unbox (_Prod a x fn) in
  if not (instantiate r e p) then assert false (* cannot fail *)

(** [infer sign ctx t] tries to infer a type for the term [t] in context [ctx]
    and with the signature [sign]. If the function is not able to infer a type
    then [None] is returned. Otherwise, [Some a] is returned, where [a] is the
    (fully evaluated) infered type. *)
let rec infer : Sign.t -> ctxt -> term -> term option = fun sign ctx t ->
  let env = List.map (fun (x,_) -> Bindlib.box_of_var x) ctx in
  let a = Bindlib.unbox(_Meta (new_meta Type 0) (Array.of_list env)) in
  if has_type sign ctx t a then Some(whnf a) else None

(** [has_type sign ctx t a] tests whether the term [t] has type [a] in context
    [ctx] and with the signature [sign]. Note that inference can be  performed
    using an [a] that is a metavariable. *)
and has_type : Sign.t -> ctxt -> term -> term -> bool = fun sign ctx t c ->
  if !debug_type then log "TYPE" "%a ⊢ %a : %a%!" pp_ctxt ctx pp t pp c;
  let res =
    match unfold t with
    (* Sort *)
    | Type      ->
        unify c Kind
    (* Variable *)
    | Vari(x)   ->
        let cx = try find_tvar x ctx with Not_found -> assert false in
        unify_modulo cx c
    (* Symbol *)
    | Symb(s)   ->
        unify_modulo (symbol_type s) c
    (* Product *)
    | Prod(a,b) ->
        begin
          let (x,bx) = Bindlib.unbind mkfree b in
          let uses_x = Bindlib.binder_occur b in
          has_type sign (if uses_x then add_tvar x a ctx else ctx) bx c &&
          has_type sign ctx a Type &&
          match whnf c with
          | Type -> true | Kind -> true
          | c    -> err "[%a] is not a sort...\n" pp c; false
        end
    (* Abstraction *)
    | Abst(a,t) ->
        begin
          let (x,tx) = Bindlib.unbind mkfree t in
          let c = whnf c in
          begin
            match c with
            | Meta(r,e) -> to_prod r e (Some(Bindlib.binder_name t))
            | _         -> ()
          end;
          match unfold c with
          | Prod(c,b) ->
              let bx = Bindlib.subst b (mkfree x) in
              let ctx_x = add_tvar x a ctx in
              unify_modulo a c &&
              has_type sign ctx_x tx bx &&
              has_type sign ctx a Type &&
              begin
                match infer sign ctx_x bx with
                | Some(Type) -> true
                | Some(Kind) -> true
                | Some(a)    -> wrn "BUG3 ([%a] not a sort)\n" pp a; false
                | None       -> wrn "BUG3 (cannot infer sort)\n"; false
              end
          | c         ->
              err "Product type expected, found [%a]...\n" pp c;
              assert(unfold c == c); false
        end
    (* Application *)
    | Appl(t,u) ->
        begin
          match infer sign ctx t with
          | None    -> wrn "Cannot infer the type of [%a]\n%!" pp t; false
          | Some(a) ->
              begin
                begin
                  match a with
                  | Meta(r,e) -> to_prod r e None
                  | _         -> ()
                end;
                match unfold a with
                | Prod(a,b) ->
                    unify_modulo (Bindlib.subst b u) c
                    && has_type sign ctx u a
                | a         ->
                    err "Product expected for [%a], found [%a]...\n%!"
                      pp t pp a;
                    assert(unfold c == c); false
              end
        end
    (* No rule apply. *)
    | Kind      -> assert false
    | ITag(_)   -> assert false
    | Meta(_,_) -> assert false
    | Wild      -> assert false
  in
  if !debug_type then
    log "TYPE" (r_or_g res "%a ⊢ %a : %a") pp_ctxt ctx pp t pp c;
  res

(** [infer sign ctx t] is a wrapper function for the [infer] function  defined
    earlier. It is mainly used to obtain fine-grained logs. *)
let infer : Sign.t -> ctxt -> term -> term option = fun sign ctx t ->
  if !debug then log "infr" "%a ⊢ %a : ?" pp_ctxt ctx pp t;
  let res = infer sign ctx t in
  if !debug then
    begin
      match res with
      | Some(a) -> log "infr" (gre "%a ⊢ %a : %a") pp_ctxt ctx pp t pp a
      | None    -> err "Cannot infer the type of [%a]\n" pp t
    end;
  res

(** [has_type sign ctx t a] is a wrapper function for the [has_type]  function
    defined earlier. It is mainly used to obtain fine-grained logs. *)
let has_type : Sign.t -> ctxt -> term -> term -> bool = fun sign ctx t c ->
  if !debug then log "type" "%a ⊢ %a : %a" pp_ctxt ctx pp t pp c;
  let res = has_type sign ctx t c in
  if !debug then log "type" (r_or_g res "%a ⊢ %a : %a") pp_ctxt ctx pp t pp c;
  res

(** [sort_type sign a] infers the sort of the type [a]. The result type may be
    be [Type] or [Kind]. If [a] is not well-sorted type then the program fails
    gracefully. *)
let sort_type : Sign.t -> term -> term = fun sign a ->
  match infer sign empty_ctxt a with
  | Some(Kind) -> Kind
  | Some(Type) -> Type
  | Some(s)    -> fatal "[%a] has type [%a] (not a sort)...\n" pp a pp s
  | None       -> fatal "cannot infer the sort of [%a]...\n" pp a
