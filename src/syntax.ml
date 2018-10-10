(** Parser-level abstract syntax. *)

open Extra
open Timed
open Console
open Files
open Pos

(** Representation of a (located) identifier. *)
type ident = strloc

(** Representation of a possibly qualified (and located) identifier. *)
type qident = (module_path * string) Pos.loc

(** Parser-level (located) term representation. *)
type p_term = p_term_aux Pos.loc
and p_term_aux =
  | P_Type
  (** TYPE constant. *)
  | P_Vari of qident
  (** Variable (empty module path) or symbol (arbitrary module path). *)
  | P_Wild
  (** Wildcard (place-holder for terms). *)
  | P_Meta of strloc * p_term array
  (** Meta-variable with the given environment. *)
  | P_Patt of strloc * p_term array
  (** Higher-order pattern (used for rules LHS / RHS). *)
  | P_Appl of p_term * p_term
  (** Application. *)
  | P_Impl of p_term * p_term
  (** Implication. *)
  | P_Abst of p_arg list * p_term
  (** Abstraction over several variables. *)
  | P_Prod of p_arg list * p_term
  (** Product over several variables. *)
  | P_LLet of strloc * p_arg list * p_term * p_term
  (** Local let. *)
  | P_NLit of int
  (** Natural number literal. *)

(** Synonym of [p_term] for semantic hints. *)
and p_type = p_term

(** Synonym of [p_term] for semantic hints. *)
and p_patt = p_term

(** Parser-level representation of a function argument. *)
and p_arg = ident * p_type option

(** Representation of a symbol tag. *)
type symtag =
  | Sym_const
  (** The symbol is constant. *)
  | Sym_inj
  (** The symbol is injective. *)

(** Parser-level rewriting rule representation. *)
type p_rule = (p_patt * p_term) Pos.loc

(** Rewrite pattern specification. *)
type p_rw_patt =
  | P_rw_Term           of p_term
  | P_rw_InTerm         of p_term
  | P_rw_InIdInTerm     of ident * p_term
  | P_rw_IdInTerm       of ident * p_term
  | P_rw_TermInIdInTerm of p_term * ident * p_term
  | P_rw_TermAsIdInTerm of p_term * ident * p_term

(** Parser-level representation of a proof tactic. *)
type p_tactic_aux =
  | P_tac_refine  of p_term
  (** Refine the current goal using the given term. *)
  | P_tac_intro   of ident list
  (** Eliminate quantifiers using the given names for hypotheses. *)
  | P_tac_apply   of p_term
  (** Apply the given term to the current goal. *)
  | P_tac_simpl
  (** Normalize in the focused goal. *)
  | P_tac_rewrite of p_rw_patt loc option * p_term
  (** Apply rewriting using the given lemma and pattern. *)
  | P_tac_refl
  (** Apply reflexivity of equality. *)
  | P_tac_sym
  (** Apply symmetry of equality. *)
  | P_tac_focus   of int
  (** Focus on the given goal. *)
  | P_tac_print
  (** Print the current goal. *)
  | P_tac_proofterm
  (** Print the current proof term (possibly containing open goals). *)
type p_tactic = p_tactic_aux Pos.loc

(** Parser-level representation of a proof terminator. *)
type p_proof_end =
  | P_proof_QED
  (** The proof is done and fully checked. *)
  | P_proof_admit
  (** Give up current state and admit the theorem. *)
  | P_proof_abort
  (** Abort the proof (theorem not admitted). *)

(** Parser-level representation of an assertion. *)
type p_assertion =
  | P_assert_typing of p_term * p_type
  (** The given term should have the given type. *)
  | P_assert_conv   of p_term * p_term
  (** The two given terms should be convertible. *)

(** Parser-level representation of a configuration command. *)
type p_config =
  | P_config_verbose of int
  (** Sets the verbosity level. *)
  | P_config_debug   of bool * string
  (** Toggles logging functions described by string according to boolean. *)
  | P_config_builtin of string * qident
  (** Sets the configuration for a builtin syntax (e.g., nat literals). *)

type require_mode =
  | P_require_default
  (** Just require the module. *)
  | P_require_open
  (** Require the module and open it. *)
  | P_require_as of ident
  (** Require the module and aliases it with the given indentifier. *)

(** Parser-level representation of a single command. *)
type p_cmd =
  | P_require    of module_path * require_mode
  (** Require statement. *)
  | P_open       of module_path
  (** Open statement. *)
  | P_symbol     of symtag list * ident * p_type
  (** Symbol declaration. *)
  | P_rules      of p_rule list
  (** Rewriting rule declarations. *)
  | P_definition of bool * ident * p_arg list * p_type option * p_term
  (** Definition of a symbol (unfoldable). *)
  | P_theorem    of ident * p_type * p_tactic list * p_proof_end
  (** Theorem with its proof. *)
  | P_assert     of bool * p_assertion
  (** Assertion (must fail if boolean is [true]). *)
  | P_set        of p_config
  (** Set the configuration (debug, logging, ...). *)
  | P_infer      of p_term * Eval.config
  (** Type inference command. *)
  | P_normalize  of p_term * Eval.config
  (** Normalisation command. *)

(** Top level AST returned by the parser. *)
type ast = p_cmd Pos.loc list

(** [get_args t] decomposes [t] into a head term and a list of arguments. Note
    that in the returned pair [(h,args)], [h] is never a [P_Appl] node. *)
let get_args : p_term -> p_term * (Pos.popt * p_term) list = fun t ->
  let rec get_args acc t =
    match t.elt with
    | P_Appl(u,v) -> get_args ((t.pos,v)::acc) u
    | _           -> (t, acc)
  in get_args [] t

(** [add_args t args] builds the application of the term [t] to the  arguments
    [args]. When [args] is empty, the returned value is exactly [t]. Note that
    this function is the inverse of [get_args] (in some sense). *)
let add_args : p_term -> (Pos.popt * p_term) list -> p_term =
  List.fold_left (fun t (p,u) -> Pos.make p (P_Appl(t,u)))

(** Representation of a reduction rule, with its context. *)
type old_p_rule = ((strloc * p_term option) list * p_term * p_term) Pos.loc

(** [translate_old_rule r] transforms the legacy representation of a rule into
    the new representation. This function will be removed soon. *)
let translate_old_rule : old_p_rule -> p_rule = fun r ->
  let (ctx, lhs, rhs) = r.elt in
  (** Check for (deprecated) annotations in the context. *)
  let get_var (x,ao) =
    let fn a = wrn a.pos "Ignored type annotation." in
    (if !verbose > 1 then Option.iter fn ao); x
  in
  let ctx = List.map get_var ctx in
  (** Find the minimum number of arguments a variable is applied to. *)
  let is_pat_var env x =
    not (List.mem x env) && List.exists (fun y -> y.elt = x) ctx
  in
  let arity = Hashtbl.create 7 in
  let rec compute_arities env t =
    let (h, args) = get_args t in
    let nb_args = List.length args in
    begin
      match h.elt with
      | P_Appl(_,_)           -> assert false (* Cannot happen. *)
      | P_Vari({elt = (p,x)}) ->
          if p = [] && is_pat_var env x then
            begin
              try
                let n = Hashtbl.find arity x in
                if nb_args < n then Hashtbl.replace arity x nb_args
              with Not_found -> Hashtbl.add arity x nb_args
            end
      | P_Wild          -> ()
      | P_Type          -> ()
      | P_Prod(_,_)     -> fatal h.pos "Product in legacy pattern."
      | P_Meta(_,_)     -> fatal h.pos "Metaviable in legacy pattern."
      | P_Abst(xs,t)    ->
          begin
            match xs with
            | [(_, Some(a))] -> fatal a.pos "Annotation in legacy pattern."
            | [(x, None   )] -> compute_arities (x.elt::env) t
            | _              -> fatal h.pos "Invalid legacy pattern lambda."
          end
      | P_Patt(_,_)     -> fatal h.pos "Pattern in legacy rule."
      | P_Impl(_,_)     -> fatal h.pos "Implication in legacy rule."
      | P_LLet(_,_,_,_) -> fatal h.pos "Implication in legacy rule."
      | P_NLit(_)       -> fatal h.pos "Nat literal in legacy rule."
    end;
    List.iter (fun (_,t) -> compute_arities env t) args
  in
  compute_arities [] lhs;
  (** Check that all context variables occur in the LHS. *)
  let check_here x =
    try ignore (Hashtbl.find arity x.elt) with Not_found ->
      fatal x.pos "Variable [%s] does not occur in the LHS." x.elt
  in
  List.iter check_here ctx;
  (** Actually process the LHS and RHS. *)
  let rec build env t =
    let (h, lts) = get_args t in
    match h.elt with
    | P_Vari({elt = ([],x)}) when is_pat_var env x ->
       let lts = List.map (fun (p,t) -> p,build env t) lts in
       let n =
         try Hashtbl.find arity x with Not_found ->
           assert false (* Unreachable. *)
       in
       let (lts1, lts2) = List.cut lts n in
       let ts1 = Array.of_list (List.map snd lts1) in
       add_args (Pos.make t.pos (P_Patt(Pos.make h.pos x, ts1))) lts2
    | _                                            ->
    match t.elt with
    | P_Vari(_)
    | P_Type
    | P_Wild          -> t
    | P_Prod(xs,b)    ->
        let (x,a) =
          match xs with
          | [(x, Some(a))] -> (x, build env a)
          | _              -> assert false (* Unreachable. *)
        in
        Pos.make t.pos (P_Prod([(x, Some(a))], build (x.elt::env) b))
    | P_Abst(xs,u)    ->
        let (x,a) =
          match xs with
          | [(x, ao)] -> (x, Option.map (build env) ao)
          | _         -> assert false (* Unreachable. *)
        in
        Pos.make t.pos (P_Abst([(x,a)], build (x.elt::env) u))
    | P_Appl(t1,t2)   -> Pos.make t.pos (P_Appl(build env t1, build env t2))
    | P_Meta(_,_)     -> fatal t.pos "Invalid legacy rule syntax."
    | P_Patt(_,_)     -> fatal h.pos "Pattern in legacy rule."
    | P_Impl(_,_)     -> fatal h.pos "Implication in legacy rule."
    | P_LLet(_,_,_,_) -> fatal h.pos "Implication in legacy rule."
    | P_NLit(_)       -> fatal h.pos "Nat literal in legacy rule."
  in
  (* NOTE the computation order is important for setting arities properly. *)
  let lhs = build [] lhs in
  let rhs = build [] rhs in
  Pos.make r.pos (lhs, rhs)
