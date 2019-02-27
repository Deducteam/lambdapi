(** Translation of lambdapi goals to why3 goals in propositional case *)

open Terms
open Extra

(* a type to present the list of why3 constants and lambdapi terms *)
type cnst_table = (term * Why3.Term.lsymbol) list

(* number of axioms proved whith the Why3 tactic *)
let nbr_axioms : int ref = ref 0

(** [get_newname ()] generates a new axiom name. *)
let get_newname () : string =
    nbr_axioms := !nbr_axioms + 1;
    "Why3axiom_" ^ (string_of_int !nbr_axioms)

(* builtins configuration for propositional logic *)
type prop_config =
  { symb_P     : sym * pp_hint (** Encoding of propositions.        *)
  ; symb_T     : sym * pp_hint (** Encoding of types.               *)
  ; symb_or    : sym * pp_hint (** Disjunction(∨) symbol.           *)
  ; symb_and   : sym * pp_hint (** Conjunction(∧) symbol.           *)
  ; symb_imp   : sym * pp_hint (** Implication(⇒) symbol.           *)
  ; symb_bot   : sym * pp_hint (** Bot(⊥) symbol.                   *)
  ; symb_not   : sym * pp_hint (** Not(¬) symbol.                   *) }

(** [get_prop_config builtins] set the builtins configuration using
    [builtins] *)
let get_prop_config : Proof.builtins -> prop_config = fun builtins ->
  let find_sym key =
    try StrMap.find key builtins with Not_found ->
     Console.fatal_no_pos "Builtin symbol [%s] undefined." key
  in
  { symb_P     = find_sym "P"
  ; symb_T     = find_sym "T"
  ; symb_or    = find_sym "or"
  ; symb_and   = find_sym "and"
  ; symb_imp   = find_sym "imp"
  ; symb_bot   = find_sym "bot"
  ; symb_not   = find_sym "not" }

(** [t_goal buitltins sp (hs,g)] translate and try to prove the lambdapi goal
    [g] with hypothesis [hs] using a prover named [sp] in Why3.*)
let rec t_goal : Proof.builtins -> string -> (Env.env * term) -> bool =
    fun builtins sp (hs, g) ->
    let cfg = get_prop_config builtins in
    match Basics.get_args g with
    | (symbol, [t]) when Basics.is_symb (fst cfg.symb_P) symbol ->
        let (l_prop, hypothesis) =
            List.fold_left
            (fun (l_prop', l_hyp) (s, (_, h)) ->
            let hyp = get_proposition cfg (Bindlib.unbox h) in (* FIX types *)
            let (l', y3t) = t_prop cfg l_prop' [] hyp in
            (l', (s, y3t)::l_hyp))
            ([], []) hs in
        let (l_prop, formula) = t_prop cfg l_prop [] t in
        List.iter (fun (x, _) -> Console.out 1 "%a\n" Print.pp x) l_prop;
        let symbols = List.map (fun (_, x) -> x) l_prop in
        let tsk = Why3task.declare_symbols symbols in
        let tsk = Why3task.declare_axioms hypothesis tsk in
        let tsk = Why3task.add_goal tsk formula in
        let result = Why3prover.result (Why3prover.prover sp) tsk in
        Why3prover.answer result.pr_answer
    | _                                                         ->
        failwith "Goal can't be translated"

(** [get_proposition cfg pt] return the term [t] if [pt] is of the form [P t]
    by using the config [cfg] *)
and get_proposition : prop_config -> term -> term =
    fun cfg pt ->
    match Basics.get_args pt with
    | (symbol, [t]) when Basics.is_symb (fst cfg.symb_P) symbol ->
        t
    | _                                                         ->
        failwith "Proposition can't be translated"

(** [t_prop cfg l_prop ctxt p] translate the term [p] into Why3 terms with a
    context [ctxt] and a config [cfg]. *)
and t_prop :
    prop_config -> cnst_table -> Ctxt.t -> term ->
    cnst_table * Why3.Term.term =
    fun cfg l_prop ctxt p ->
    let (s, args) = Basics.get_args p in
    (match s with
    | symbol when Basics.is_symb (fst cfg.symb_and) symbol  ->
        let (l_prop, t1) = t_prop cfg l_prop ctxt (List.nth args 0) in
        let (l_prop, t2) = t_prop cfg l_prop ctxt (List.nth args 1) in
        l_prop, Why3.Term.t_and t1 t2
    | symbol when Basics.is_symb (fst cfg.symb_or) symbol  ->
        let (l_prop, t1) = t_prop cfg l_prop ctxt (List.nth args 0) in
        let (l_prop, t2) = t_prop cfg l_prop ctxt (List.nth args 1) in
        l_prop, Why3.Term.t_or t1 t2
    | symbol when Basics.is_symb (fst cfg.symb_imp) symbol  ->
        let (l_prop, t1) = t_prop cfg l_prop ctxt (List.nth args 0) in
        let (l_prop, t2) = t_prop cfg l_prop ctxt (List.nth args 1) in
        l_prop, Why3.Term.t_implies t1 t2
    | symbol when Basics.is_symb (fst cfg.symb_not) symbol  ->
        let (l_prop, t) = t_prop cfg l_prop ctxt (List.nth args 0) in
        l_prop, Why3.Term.t_not t
    | Symb(_, _)                        ->
        (* if the term [p] is in the list [l_prop] *)
        if List.exists (fun (lp_t, _) -> Basics.eq lp_t p) l_prop then
            (* then find it and return it *)
            let lp_eq = fun (lp_t, _) -> Basics.eq lp_t p in
            let (_, ct) = List.find lp_eq l_prop in
                (l_prop, Why3.Term.ps_app ct [])
            else
            (* or generate a new constant in why3 *)
                let new_symbol = Why3.Ident.id_fresh "P" in
                let sym = Why3.Term.create_psymbol new_symbol [] in
                let new_predicate = Why3.Term.ps_app sym [] in
                (* add the new symbol to the list and return it *)
                (p, sym)::l_prop, new_predicate
    | _                                     ->
        failwith "Proposition can't be translated ");