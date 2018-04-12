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

(** [infer ctx t] tries to infer a type for the term [t] in context
    [ctx]. If the function is not able to infer a type then [None] is
    returned. Otherwise, [Some a] is returned, where [a] is the (fully
    evaluated) infered type. *)
let rec infer : Ctxt.t -> term -> term option = fun ctx t ->
  let vs = List.map (fun (x,_) -> _Vari x) ctx in
  let m = new_meta Type 0 in
  let a = Bindlib.unbox(_Meta m (Array.of_list vs)) in
  if has_type ctx t a then Some(whnf a) else None

(** [has_type ctx t a] tests whether the term [t] has type [a] in
    context [ctx]. Note that inference can be performed using an [a]
    that is a metavariable. *)
and has_type : Ctxt.t -> term -> term -> bool = fun ctx t typ ->
  if !debug_type then log "type" "%a ⊢ %a : %a%!" Ctxt.pp ctx pp t pp typ;
  let res =
    match unfold t with
    | Type        ->
        unify typ Kind

    | Vari(x)     ->
        let typ_x = try Ctxt.find x ctx with Not_found -> assert false in
        unify_modulo typ_x typ

    | Symb(s)     ->
        unify_modulo !(s.sym_type) typ

    | Prod(a,b)   ->
        begin
          let (x,bx) = Bindlib.unbind mkfree b in
          let uses_x = Bindlib.binder_occur b in
          has_type (if uses_x then Ctxt.add x a ctx else ctx) bx typ &&
          has_type ctx a Type &&
          match whnf typ with
          | Type -> true | Kind -> true
          | typ    -> err "[%a] is not a sort...\n" pp typ; false
        end

    | Abst(a,t)   ->
        begin
          let (x,tx) = Bindlib.unbind mkfree t in
          let typ = whnf typ in
          begin
            match typ with
            | Meta(r,e) -> to_prod r e (Some(Bindlib.binder_name t))
            | _         -> ()
          end;
          match unfold typ with
          | Prod(c,b) ->
              let bx = Bindlib.subst b (mkfree x) in
              let ctx_x = Ctxt.add x a ctx in
              unify_modulo a c &&
              has_type ctx_x tx bx &&
              has_type ctx a Type &&
              begin
                match infer ctx_x bx with
                | Some(Type) -> true
                | Some(Kind) -> true
                | Some(a)    -> wrn "BUG3 ([%a] not a sort)\n" pp a; false
                | None       -> wrn "BUG3 (cannot infer sort)\n"; false
              end
          | typ         ->
              err "Product type expected, found [%a]...\n" pp typ;
              assert(unfold typ == typ); false
        end

    | Appl(t,u)   ->
        begin
          match infer ctx t with
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
                    unify_modulo (Bindlib.subst b u) typ
                    && has_type ctx u a
                | a         ->
                    err "Product expected for [%a], found [%a]...\n%!"
                      pp t pp a;
                    assert(unfold typ == typ); false
              end
        end

    | Meta(m,e)   ->
        let v = Bindlib.new_var mkfree (meta_name m) in
        let ctx = Ctxt.add v m.meta_type ctx in
        has_type ctx (add_args (Vari(v)) (Array.to_list e)) typ

    | Kind
    | Patt(_,_,_)
    | TEnv(_,_)   -> assert false
  in
  if !debug_type then
    log "type" (r_or_g res "%a ⊢ %a : %a") Ctxt.pp ctx pp t pp typ;
  res

(** [infer ctx t] is a wrapper function for the [infer] function  defined
    earlier. It is mainly used to obtain fine-grained logs. *)
let infer : Ctxt.t -> term -> term option = fun ctx t ->
  if !debug then log "infr" "%a ⊢ %a" Ctxt.pp ctx pp t;
  let res = infer ctx t in
  if !debug then
    begin
      match res with
      | Some(a) -> log "infr" (gre "%a ⊢ %a : %a") Ctxt.pp ctx pp t pp a
      | None    -> err "Cannot infer the type of [%a]\n" pp t
    end;
  res

(** [has_type ctx t a] is a wrapper function for the [has_type]  function
    defined earlier. It is mainly used to obtain fine-grained logs. *)
let has_type : Ctxt.t -> term -> term -> bool = fun ctx t c ->
  if !debug then log "type" "%a ⊢ %a : %a" Ctxt.pp ctx pp t pp c;
  let res = has_type ctx t c in
  if !debug then log "type" (r_or_g res "%a ⊢ %a : %a") Ctxt.pp ctx pp t pp c;
  res

(** [sort_type a] infers the sort of the type [a]. The result type may be
    be [Type] or [Kind]. If [a] is not well-sorted type then the program fails
    gracefully. *)
let sort_type : Ctxt.t -> term -> term = fun c a ->
  match infer c a with
  | Some(Kind) -> Kind
  | Some(Type) -> Type
  | Some(s)    -> fatal "[%a] has type [%a] (not a sort)...\n" pp a pp s
  | None       -> fatal "cannot infer the sort of [%a]...\n" pp a
