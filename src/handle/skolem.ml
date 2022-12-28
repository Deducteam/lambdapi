open Common
open Core
open Term

let log = Logger.make 'a' "sklm" "skolemization"
let log = log.pp

type fol_config = {
  symb_P : sym;  (** Encoding of propositions. *)
  symb_T : sym;  (** Encoding of types. *)
  symb_or : sym;  (** Disjunction(∨) symbol. *)
  symb_and : sym;  (** Conjunction(∧) symbol. *)
  symb_imp : sym;  (** Implication(⇒) symbol. *)
  symb_bot : sym;  (** Bot(⊥) symbol. *)
  symb_top : sym;  (** Top(⊤) symbol. *)
  symb_not : sym;  (** Not(¬) symbol. *)
  symb_ex : sym;  (** Exists(∃) symbol. *)
  symb_all : sym;  (** Forall(∀) symbol. *)
}
(** Builtin configuration for propositional logic. *)

(** [get_fol_config ss pos] build the configuration using [ss]. *)
let get_fol_config : Sig_state.t -> Pos.popt -> fol_config =
 fun ss pos ->
  let builtin = Builtin.get ss pos in
  {
    symb_P = builtin "P";
    symb_T = builtin "T";
    symb_or = builtin "or";
    symb_and = builtin "and";
    symb_imp = builtin "imp";
    symb_bot = builtin "bot";
    symb_top = builtin "top";
    symb_not = builtin "not";
    symb_ex = builtin "ex";
    symb_all = builtin "all";
  }

let add_ctxt : ctxt -> tvar -> term -> ctxt =
 fun c var typ -> c @ [ (var, typ, None) ]

(**Skolemization*)

(*[new_skolem ss ctx cpt ex_typ] is called when existantial quantifier ("∃y")
  occurs. [ex_typ] is the type of quantificated variable "y". In order to
  eliminate ∃ quantifier, we need to extend signature state [ss] with a skolem
  term, represented by a fresh symbol that will later replace the binded
  variable ("y"). Such skolem term may either be a skolem function or a skolem
  constant : The type of a skolem term depends on registered variables in
  [ctx] For example, if a set of variables x1:a1, x2:a2,..., xn:an were
  previously introduced by an universal quantifier, A skolem term "skt" will
  take as arguments x1, ..., xn, and must therefore be typed as follows : skt
  (x1, x2, ..., xn) : a1 -> a2 -> ... -> an -> ex_typ. A skolem term is a
  constant if skolemized term is not in the scope of any universal quantifier,
  namely, [ctx] is empty. For the sake of clarity, we use a counter [cpt] for
  naming the generated symbol. OUT : Updated signature state [upt_sig] is
  returned, as well as introduced symbol [symb_skt] and updated counter*)
let new_skolem : Sig_state.t -> ctxt -> int -> term -> Sig_state.t * sym * int
  = fun ss ctx ctr ex_typ ->
  let skt_name =
    if ctx == [] then "c" ^ string_of_int ctr else "f" ^ string_of_int ctr
  in
  let skt, _ = Ctxt.to_prod ctx ex_typ in
  let upt_sig, symb_skt =
    Sig_state.add_symbol ss Public Const Eager true (Pos.none skt_name) skt []
      None
  in
  if Logger.log_enabled () then log "New symbol %a" Print.sym symb_skt;
  (upt_sig, symb_skt, ctr + 1)

(*[Subst_app ctx tb s] builds [f_appl], the application of a symbol [symb_skt]
  and a list of variables extracted from context [ctx]. Then, the binded
  variable in [tb] is substituted by [f_appl]*)
(*Assumes type of [symb_skt] correspond to variables's types as they are
  listed in context [ctx] *)
let subst_app : ctxt -> tbinder -> sym -> term =
 fun ctx tb symb_skt ->
  (*args_list : [tvar list], are context's variables*)
  let args_list = List.map (fun (v, _, _) -> mk_Vari v) ctx in
  (*[add_args] build the application of [f_term] to the list of variables
    [args_list].*)
  let f_appl = add_args (mk_Symb symb_skt) args_list in
  Bindlib.subst tb f_appl

type quant = {
  symb : sym;  (** The symbol that stand for the quantifier. *)
  dom : term;  (** The domain of the quantification. *)
  var : tvar;  (** The variable bound by the quantification. *)
  typ : term;
      (** The type of the quantified variable {b NOTE} It should always be
          [T dom] where [T] is the builtin that interprets type codes. *)
}
(** A structure to represent quantifiers in a FOF. *)

(* add_quant ql symb_all symb_P Vari(x) type_a add in a list a representation
   of the universal quantification of x:type_a on top of the list ql, and
   return the list.*)
let add_quant : quant list -> sym -> term -> tvar -> term -> quant list =
 fun qlist q d v t -> { symb = q; dom = d; var = v; typ = t } :: qlist

(* [mk_quant t q] builds an application of the quantifier q on the proposition
   f.*)
let mk_quant : term -> quant -> term =
 fun f q ->
  let tb = bind q.var lift f in
  add_args (mk_Symb q.symb) [ q.dom; mk_Abst (q.typ, tb) ]

(** [nnf_term cfg t] computes the negation normal form of a first order
    formula. *)
let nnf_of : fol_config -> term -> term =
 fun cfg t ->
  let rec nnf_prop t =
    match get_args t with
    | Symb s, [ t1; t2 ] when s == cfg.symb_and ->
        add_args (mk_Symb s) [ nnf_prop t1; nnf_prop t2 ]
    | Symb s, [ t1; t2 ] when s == cfg.symb_or ->
        add_args (mk_Symb s) [ nnf_prop t1; nnf_prop t2 ]
    | Symb s, [ t1; t2 ] when s == cfg.symb_imp ->
        add_args (mk_Symb cfg.symb_or) [ neg t1; nnf_prop t2 ]
    | Symb s, [ t ] when s == cfg.symb_not -> neg t
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_all ->
        let var, p = Bindlib.unbind tb in
        let nnf_tb = bind var lift (nnf_prop p) in
        add_args (mk_Symb cfg.symb_all) [ a; mk_Abst (x, nnf_tb) ]
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_ex ->
        let var, p = Bindlib.unbind tb in
        let nnf_tb = bind var lift (nnf_prop p) in
        add_args (mk_Symb cfg.symb_ex) [ a; mk_Abst (x, nnf_tb) ]
    | Symb _, _ | Abst (_, _), _ -> t
    | _, _ -> t
  and neg t =
    match get_args t with
    | Symb s, [] when s == cfg.symb_bot -> mk_Symb cfg.symb_top
    | Symb s, [] when s == cfg.symb_top -> mk_Symb cfg.symb_bot
    | Symb s, [ t1; t2 ] when s == cfg.symb_and ->
        add_args (mk_Symb cfg.symb_or) [ neg t1; neg t2 ]
    | Symb s, [ t1; t2 ] when s == cfg.symb_or ->
        add_args (mk_Symb cfg.symb_and) [ neg t1; neg t2 ]
    | Symb s, [ _; _ ] when s == cfg.symb_imp -> neg (nnf_prop t)
    | Symb s, [ nt ] when s == cfg.symb_not -> nnf_prop nt
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_all ->
        let var, p = Bindlib.unbind tb in
        let neg_tb = bind var lift (neg p) in
        add_args (mk_Symb cfg.symb_ex) [ a; mk_Abst (x, neg_tb) ]
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_ex ->
        let var, p = Bindlib.unbind tb in
        let nnf_tb = bind var lift (neg p) in
        add_args (mk_Symb cfg.symb_all) [ a; mk_Abst (x, nnf_tb) ]
    | _, _ -> add_args (mk_Symb cfg.symb_not) [ t ]
  in
  nnf_prop t

exception PrenexFormulaNotNnf of term

let prenex_of cfg t =
  let rec prenex t =
    match get_args t with
    | Symb s, [ t1; t2 ] when s == cfg.symb_and ->
        let qlist1, sub1 = prenex t1 in
        let qlist2, sub2 = prenex t2 in
        let t = add_args (mk_Symb s) [ sub1; sub2 ] in
        let qlist = qlist1 @ qlist2 in
        (qlist, t)
    | Symb s, [ t1; t2 ] when s == cfg.symb_or ->
        let qlist1, sub1 = prenex t1 in
        let qlist2, sub2 = prenex t2 in
        let t = add_args (mk_Symb s) [ sub1; sub2 ] in
        let qlist = qlist1 @ qlist2 in
        (qlist, t)
    | Symb s, [ _; _ ] when s == cfg.symb_imp ->
      raise @@ PrenexFormulaNotNnf t
    | Symb s, [ nt ] when s == cfg.symb_not ->
        let res =
          match nt with
          | Vari _ -> ([], t)
          | Symb _ -> ([], t)
          | _ -> raise @@ PrenexFormulaNotNnf t
        in
        res
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_all ->
        let var, f = Bindlib.unbind tb in
        let qlist, sf = prenex f in
        let qlist = add_quant qlist s a var x in
        (qlist, sf)
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_ex ->
        let var, f = Bindlib.unbind tb in
        let qlist, sf = prenex f in
        let qlist = add_quant qlist s a var x in
        (qlist, sf)
    | _, _ -> ([], t)
  in
  let qlist, f = prenex t in
  List.fold_left mk_quant f (List.rev qlist)

(** [handle ss pos t] returns a skolemized form of term [t] (at position
    [pos]).  A term is skolemized when it has no existential quantifiers: to
    this end, for each existential quantifier in [t], signature state [ss] is
    extended with a new symbol in order to substitute the variable bound by
    the said quantifier.
    @raise NotProp when the argument [t] is not an encoded proposition. *)
let handle : Sig_state.t -> Pos.popt -> term -> term =
 fun ss pos t ->
  (*Gets user-defined symbol identifiers mapped using "builtin" command.*)
  let cfg = get_fol_config ss pos in
  let t = nnf_of cfg t in
  let t =
    try prenex_of cfg t
    with PrenexFormulaNotNnf _ ->
      assert false (* [t] is put into nnf before *)
  in
  let rec skolemisation ss ctx ctr t =
    match get_args t with
    | Symb s, [ _; Abst (y, tb) ] when s == cfg.symb_ex ->
        (* When existential quantification occurs, quantified variable is
           substituted by a fresh symbol*)
        let maj_ss, nv_sym, maj_ctr = new_skolem ss ctx ctr y in
        let maj_term = subst_app ctx tb nv_sym in
        skolemisation maj_ss ctx maj_ctr maj_term
    | Symb s, [ a; Abst (x, tb) ] when s == cfg.symb_all ->
        (* When universal quantification occurs, quantified variable is added
           to context*)
        let var, f = Bindlib.unbind tb in
        let maj_ctx = add_ctxt ctx var a in
        let maj_f = skolemisation ss maj_ctx ctr f in
        let maj_tb = bind var lift maj_f in
        (*Reconstruct a term of form ∀ x : P, t', with t' skolemized*)
        add_args (mk_Symb s) [ a; mk_Abst (x, maj_tb) ]
    | _ -> t
  in
  let skl_of_t = skolemisation ss [] 0 t in
  if Logger.log_enabled () then
    log "Skolemized form of %a is %a" Print.term t Print.term skl_of_t;
  skl_of_t
