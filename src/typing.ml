(** Type-checking and inference *)

open Console
open Terms
open Print

(** Configuration of the type-checking / inference functions. *)
type config =
  { conv_fun : term -> term -> unit (** Convertibility check. *) }

(** [infer cfg ctx t] returns a type for the term [t] in the context [ctx]. In
    the process, the [cfg.conv_fun] function is used as a convertibility test.
    Note that we require [ctx] to be well-formed (with well-sorted types), and
    that the returned type is always well-sorted. *)
let rec infer : config -> Ctxt.t -> term -> term = fun cfg ctx t ->
  match unfold t with
  | Patt(_,_,_) -> assert false (* Forbidden case. *)
  | TEnv(_,_)   -> assert false (* Forbidden case. *)
  | Kind        -> assert false (* Forbidden case. *)
  | Type        ->
      (* -------------------
          ctx ⊢ Type ⇒ Kind  *)
      Kind
  | Vari(x)     ->
      (* ---------------------------------
          ctx ⊢ Vari(x) ⇒ Ctxt.find x ctx  *)
      begin
        try Ctxt.find x ctx with Not_found -> assert false
        (* Every free variable must be in the context. *)
      end
  | Symb(s)     ->
      (* -------------------------------
          ctx ⊢ Symb(s) ⇒ !(s.sym_type)  *)
      !(s.sym_type)
  | Prod(a,b)   ->
      (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ b<x> ⇒ s
         -----------------------------------------
                    ctx ⊢ Prod(a,b) ⇒ s            *)
      begin
        (* We ensure that [a] is well-sorted. *)
        check cfg ctx a Type;
        (* We infer the type of the body, first extending the context. *)
        let (x,b) = Bindlib.unbind b in
        let s = infer cfg (Ctxt.add x a ctx) b in
        (* We check that [s] is a sort. *)
        match unfold s with
        | Type | Kind -> s
        | Meta(_,_)   -> assert false (* FIXME is [Meta(_,_)] possible? *)
        | _           -> fatal_no_pos "Sort expected, [%a] infered." pp s
      end
  | Abst(a,t)   ->
      (*  ctx ⊢ a ⇐ Type    ctx, x : a ⊢ t<x> ⇒ b<x>
         --------------------------------------------
                 ctx ⊢ Abst(a,t) ⇒ Prod(a,b)          *)
      begin
        (* We ensure that [a] is well-sorted. *)
        check cfg ctx a Type;
        (* We infer the type of the body, first extending the context. *)
        let (x,t) = Bindlib.unbind t in
        let b = infer cfg (Ctxt.add x a ctx) t in
        (* We build the product type by binding [x] in [b]. *)
        Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))
      end
  | Appl(t,u)   ->
      (*  ctx ⊢ t ⇒ Prod(a,b)    ctx ⊢ u ⇐ a
         ------------------------------------
             ctx ⊢ Appl(t,u) ⇒ subst b u      *)
      begin
        (* We first infer a product type for [t]. *)
        let (a,b) =
          match Eval.whnf (infer cfg ctx t) with
          | Prod(a,b) -> (a,b)
          | Meta(_,_) -> assert false (* FIXME is [Meta(_,_)] possible? *)
          | a         -> fatal_no_pos "Product expected, [%a] infered." pp a
        in
        (* We then check the type of [u] against the domain type. *)
        check cfg ctx u a;
        (* We produce the redurned type. *)
        Bindlib.subst b u
      end
  | Meta(m,e)   ->
      (*  ctx ⊢ term_of_meta m e ⇒ a
         ----------------------------
             ctx ⊢ Meta(m,e) ⇒ a      *)
      infer cfg ctx (term_of_meta m e)

(** [check cfg ctx t c] checks that the term [t] has type [c] (which should be
    well-sorted) in context [ctx]. In the process, the [cfg.conv_fun] function
    is used as a convertibility test. Note that [ctx] must be well-formed.  In
    particuler, it should contain only well-sorted types. *)
and check : config -> Ctxt.t -> term -> term -> unit = fun cfg ctx t c ->
  match unfold t with
  | Patt(_,_,_) -> assert false (* Forbidden case. *)
  | TEnv(_,_)   -> assert false (* Forbidden case. *)
  | Kind        -> assert false (* Forbidden case. *)
  | Type        ->
      (* -------------------
          ctx ⊢ Type ⇐ Kind  *)
      begin
        match unfold c with
        | Kind -> ()
        | _    -> fatal_no_pos "[Kind] expected, [%a] given." pp c
      end
  | Abst(a,t)   ->
      (*  c → Prod(a',b)    a ~ a'    ctx, x : A ⊢ t<x> ⇐ b<x>
         ------------------------------------------------------
                          ctx ⊢ Abst(a,t) ⇐ c                   *)
      begin
        (* We (hopefully) evaluate [c] to a product. *)
        let (a',b) =
          match Eval.whnf c with
          | Prod(d,b) -> (d,b)
          | Meta(_,_) -> assert false (* FIXME is [Meta(_,_)] possible? *)
          | _         -> fatal_no_pos "Product expected, [%a] given." pp c
        in
        (* We check domain type compatibility. *)
        cfg.conv_fun a a';
        (* We type-check the body with the codomain. *)
        let (x,t) = Bindlib.unbind t in
        check cfg (Ctxt.add x a ctx) t (Bindlib.subst b (Vari(x)))
      end
  | t           ->
      (*  ctx ⊢ t ⇒ a
         -------------
          ctx ⊢ t ⇐ a  *)
      let a = infer cfg ctx t in
      if not (Terms.eq a c) then cfg.conv_fun a c

(* NOTE the following functions are wrapper for the above. They write debuging
   data to the log. *)

(** [infer cfg ctx t] returns a type for the term [t] in the context [ctx]. In
    the process, the [cfg.conv_fun] function is used as a convertibility test.
    Note that we require [ctx] to be well-formed (with well-sorted types), and
    that the returned type is always well-sorted.  This function writes to the
    debuging log. *)
let infer : config -> Ctxt.t -> term -> term = fun cfg ctx t ->
  if !debug_type then
    begin
      log "type" "infer [%a]" pp t;
      try
        let a = infer cfg ctx t in
        log "type" (gre "infer [%a] : [%a]") pp t pp a; a
      with e ->
        log "type" (red "infer [%a] failed.") pp t;
        raise e
    end
  else infer cfg ctx t
 
(** [check cfg ctx t c] checks that the term [t] has type [c] (which should be
    well-sorted) in context [ctx]. In the process, the [cfg.conv_fun] function
    is used as a convertibility test. Note that [ctx] must be well-formed.  In
    particuler, it should contain only well-sorted types. This function writes
    to the debuging log. *)
let check : config -> Ctxt.t -> term -> term -> unit = fun cfg ctx t c ->
  if !debug_type then
    begin
      log "type" "check [%a] : [%a]" pp t pp c;
      try
        check cfg ctx t c;
        log "type" (gre "check [%a] : [%a]") pp t pp c;
      with e ->
        log "type" (red "check [%a] : [%a]") pp t pp c;
        raise e
    end
  else check cfg ctx t c
