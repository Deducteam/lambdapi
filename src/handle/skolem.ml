open Common
open Core open Term

(** Logging function for the skolem tactic. *)
let log_sklm = Logger.make '!' "sklm" "the skolemization tactic"
let log_sklm = log_sklm.pp

(** Builtin configuration for propositional logic. *)
type config =
  { symb_ex  : sym (** Exists(∃) symbol. *)
  ; symb_all : sym (** Forall(∀) symbol. *) 
  ; symb_P   : sym (** Encoding of propositions. *)}

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  { symb_ex  = builtin "ex"
  ; symb_all = builtin "all" 
  ; symb_P   = builtin "P"}

(*Context of skolemization allow to record introduced variables and their types when
universal quantifiers occurs.*)
let empty_context = []
let add_ctxt : ctxt->tvar->term->ctxt = 
  fun c var typ ->
    c @ [(var, typ, None)]


(**Skolemization*)

(*[new_skolem ss ctx cpt ex_typ] is called when existantial quantifier ("∃y") occurs.
[ex_typ] is the type of quantificated variable "y".
In order to eliminate ∃ quantifier, we need to extend signature state [ss] with a skolem term, 
represented by a fresh symbol that will later replace the binded variable ("y").
Such skolem term may either be a skolem function or a skolem constant :
The type of a skolem term depends on registered variables in [ctx]
For example, if a set of variables x1:a1, x2:a2,..., xn:an were previously introduced by an 
universal quantifier, A skolem term "skt" will take as arguments x1, ..., xn, and must therefore be
typed as follows : skt (x1, x2, ..., xn) : a1 -> a2 -> ... -> an -> ex_typ. 
A skolem term is a constant if skolemized term is not in the scope of any universal quantifier, 
namely,  [ctx] is empty.
For the sake of clarity, we use a counter [cpt] for naming the generated symbol.
OUT : Updated signature state [upt_sig] is returned, as well as introduced symbol [symb_skt] and updated counter*)
  let new_skolem : Sig_state.t -> ctxt -> int -> term -> Sig_state.t * sym * int =
    fun ss ctx ctr ex_typ ->
      let skt_name = if (ctx == []) then ("c"^(string_of_int (ctr))) else ("f"^(string_of_int (ctr))) in
      let skt, _ = Ctxt.to_prod ctx ex_typ in
      let upt_sig, symb_skt = Sig_state.add_symbol ss Public Const Eager true (Pos.none skt_name) skt []
      None   
      in
      if Logger.log_enabled () then
        log_sklm "New symbol %a" Print.sym symb_skt;
      upt_sig, symb_skt,(ctr + 1) 



(*[Subst_app ctx tb s] builds [f_appl], the application of a symbol [symb_skt] 
and a list of variables extracted from context [ctx]. Then, the binded
variable in [tb] is substituted by [f_appl]*)
(*Assumes type of [symb_skt] correspond to variables's types as they are 
listed in context [ctx] *)
let subst_app : ctxt -> tbinder -> sym -> term =
  fun ctx tb symb_skt ->
    (*args_list : [tvar list], are context's variables*)
    let args_list = List.map (fun (v, _, _) -> mk_Vari v) ctx in
    (*[add_args] build the application of [f_term] to the list
    of variables [args_list].*)
    let f_appl=  add_args (mk_Symb symb_skt) args_list in
  Bindlib.subst tb f_appl 


(**Main fonction : 
[skolemisation ss pos t] return a skolemized form of term [t].
(ie existential quantifications in [t] are removed)
To this end, for each existential quantifiers in [t], signature state [ss] is 
extended with new symbol [symb_skt] in order to substitute the variable binded 
by the said quantifier*)
let handle : Sig_state.t -> Pos.popt -> term -> term = fun ss pos t ->
    (*Gets user-defined symbol identifiers mapped using "builtin" command.*)
    let cfg = get_config ss pos in 
    let rec skolemisation ss ctx ctr t =  
        match get_args t with
        | Symb(s), [_;Abst(y, tb)] when s == cfg.symb_ex -> 
          (* When existential quantification occurs, quantified variable
          is substituted by a fresh symbol*)
            let maj_ss, nv_sym, maj_ctr = new_skolem ss ctx ctr y in 
            let maj_term = subst_app ctx tb nv_sym in
            skolemisation maj_ss ctx maj_ctr maj_term
        | Symb(s), [a;Abst(x, tb)] when s == cfg.symb_all -> 
          (* When universal quantification occurs, quantified variable
          is added to context*)
            let var, f = Bindlib.unbind tb in
            let maj_ctx = add_ctxt ctx var a in
            let maj_f = skolemisation ss maj_ctx ctr f in
            let maj_tb = bind var lift maj_f in
            (*Reconstruct a term of form ∀ x : P, t', 
            with t' skolemized*)
            add_args (mk_Symb s) [a ; mk_Abst (x, maj_tb)] 
        | _  -> t 
    in
    let skl_of_t = skolemisation ss empty_context 0 t in
    if Logger.log_enabled () then
      log_sklm "Skolemized form of %a is %a" Print.term t Print.term skl_of_t ;
    skl_of_t

