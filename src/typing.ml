(** Type-checking and inference *)

open Timed
open Console
open Terms
open Print

(** Logging function for typing. *)
let log_type = new_logger 't' "type" "debugging information for typing"
let log_type = log_type.logger

(** [make_prod_domain ctx] builds a metavariable intended as a domain type for
    a product. It has access to the variables of the context [ctx]. *)
let make_prod_domain : Ctxt.t -> term = fun ctx ->
  Ctxt.make_meta ctx (Meta(fresh_meta Type 0, [||]))

(** [make_prod_codomain ctx a] builds a metavariable intended as the  codomain
    type for a product of domain type [a].  It has access to the variables  of
    the context [ctx] and a fresh variables corresponding to the argument. *)
let make_prod_codomain : Ctxt.t -> term -> tbinder = fun ctx a ->
  let x = Bindlib.new_var mkfree "x" in
  let b = Ctxt.make_meta ((x,a)::ctx) (Meta(fresh_meta Type 0, [||])) in
  Bindlib.unbox (Bindlib.bind_var x (lift b))

(** Type of a list of convertibility constraints. *)
type conv_constrs = (term * term) list

(** [infer ctx t] returns a couple [(a, constrs)] where [a] is an infered type
    for [t] in the (well-formed) context [ctx], under the condition that every
    unification constraint in [constrs] is satisfied. The function cannot fail
    and the returned type can be assume to be well-sorted (at least if all the
    constraints are satisifed). *)
let infer : Ctxt.t -> term -> term * conv_constrs = fun ctx t ->
  if !log_enabled then log_type "infer [%a]" pp t;
  let constrs = Pervasives.ref [] in (* Accumulated constraints. *)
  let conv a b =
    if not (Terms.eq a b) then Pervasives.(constrs := (a,b) :: !constrs)
  in
  let rec infer ctx t =
    match unfold t with
    | Patt(_,_,_) -> assert false (* Forbidden case. *)
    | TEnv(_,_)   -> assert false (* Forbidden case. *)
    | Kind        -> assert false (* Forbidden case. *)
    | Wild        -> assert false (* Forbidden case. *)
    | TRef(_)     -> assert false (* Forbidden case. *)

    (* ───────────────────
        ctx ⊢ Type ⇒ Kind  *)
    | Type        -> Kind

    (* ─────────────────────────────────
        ctx ⊢ Vari(x) ⇒ Ctxt.find x ctx  *)
    | Vari(x)     -> (try Ctxt.find x ctx with Not_found -> assert false)

    (* ───────────────────────────────
        ctx ⊢ Symb(s) ⇒ !(s.sym_type)  *)
    | Symb(s,_)   -> Timed.(!(s.sym_type))

    (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ b<x> ⇒ s
       ─────────────────────────────────────────
                  ctx ⊢ Prod(a,b) ⇒ s            *)
    | Prod(a,b)   ->
        (* We ensure that [a] is of type [Type]. *)
        check ctx a Type;
        (* We infer the type of the body, first extending the context. *)
        let (x,b) = Bindlib.unbind b in
        let s = infer (Ctxt.add x a ctx) b in
        (* We check that [s] is a sort. *)
        let s =
          match unfold s with
          | Type | Kind -> s
          | s           -> conv s Type; Type
        in s

    (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ t<x> ⇒ b<x>
       ────────────────────────────────────────────
               ctx ⊢ Abst(a,t) ⇒ Prod(a,b)          *)
    | Abst(a,t)   ->
        (* We ensure that [a] is of type [Type]. *)
        check ctx a Type;
        (* We infer the type of the body, first extending the context. *)
        let (x,t) = Bindlib.unbind t in
        let b = infer (Ctxt.add x a ctx) t in
        (* We build the product type by binding [x] in [b]. *)
        Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))

    (*  ctx ⊢ t ⇒ Prod(a,b)    ctx ⊢ u ⇐ a
       ────────────────────────────────────
           ctx ⊢ Appl(t,u) ⇒ subst b u      *)
    | Appl(t,u)   ->
        (* We first infer a product type for [t]. *)
        let (a,b) =
          let c = Eval.whnf (infer ctx t) in
          match c with
          | Prod(a,b) -> (a,b)
          | _         ->
              let a = make_prod_domain ctx in
              let b = make_prod_codomain ctx a in
              conv c (Prod(a,b)); (a,b)
        in
        (* We then check the type of [u] against the domain type. *)
        check ctx u a;
        (* We produce the returned type. *)
        Bindlib.subst b u

    (*  ctx ⊢ term_of_meta m e ⇒ a
       ─────────────────────────────
           ctx ⊢ Meta(m,e) ⇒ a      *)
    | Meta(m,e)   -> infer ctx (term_of_meta m e)
  and check ctx t c =
    (*  ctx ⊢ t ⇒ a    a ~ c
       ──────────────────────
            ctx ⊢ t ⇐ c       *)
    conv (infer ctx t) c
  in
  let a = infer ctx t in
  let constrs = Pervasives.(!constrs) in
  if !log_enabled then
    begin
      log_type (gre "infer [%a] yields [%a]") pp t pp a;
      let fn (a,b) = log_type "  assuming [%a] ~ [%a]" pp a pp b in
      List.iter fn constrs;
    end;
  (a, constrs)

(** [check ctx t c] returns a list of unification constraints [constrs] which
    must be satisfied for [t] to have type [c] in the context [ctx]. Note that
    [ctx] and [c] are respectively assumed to be well-formed and  well-sorted,
    and that the function cannot fail. *)
let check : Ctxt.t -> term -> term -> conv_constrs = fun ctx t c ->
  if !log_enabled then log_type "check [%a] [%a]" pp t pp c;
  let (a, constrs) = infer ctx t in
  let constrs = if Terms.eq a c then constrs else (a,c) :: constrs in
  log_type (gre "check [%a] [%a] OK") pp t pp c; constrs
