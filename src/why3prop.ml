(** Translation of lambdapi goals to why3 goals in propositional case *)

open Terms
open Extra

exception NoGoalTranslation

(* a map from lambdapi terms to Why3 constants *)
type cnst_table = (term * Why3.Term.lsymbol) list

(* a map from labels to Why3 terms. *)
type ctxt_labels = (string * Why3.Term.term) list

(** [get_newname ()] generates a new axiom name. *)
let get_newname : unit -> string =
    (* number of axioms proved whith the Why3 tactic *)
    let nbr_axioms : int ref = ref 0 in fun () ->
    nbr_axioms := !nbr_axioms + 1;
    "Why3axiom_" ^ (string_of_int !nbr_axioms)

(* builtins configuration for propositional logic *)
type prop_config =
  { symb_P     : sym (** Encoding of propositions.        *)
  ; symb_T     : sym (** Encoding of types.               *)
  ; symb_or    : sym (** Disjunction(∨) symbol.           *)
  ; symb_and   : sym (** Conjunction(∧) symbol.           *)
  ; symb_imp   : sym (** Implication(⇒) symbol.           *)
  ; symb_bot   : sym (** Bot(⊥) symbol.                   *)
  ; symb_not   : sym (** Not(¬) symbol.                   *) }

(** [get_prop_config pos builtins] set the builtins configuration using
    [builtins] *)
let get_prop_config :
    Pos.popt -> sym StrMap.t -> prop_config = fun pos builtins ->
    let find_sym key =
        try StrMap.find key builtins with Not_found ->
        Console.fatal pos "Builtin symbol [%s] undefined." key
    in
    { symb_P     = find_sym "P"
    ; symb_T     = find_sym "T"
    ; symb_or    = find_sym "or"
    ; symb_and   = find_sym "and"
    ; symb_imp   = find_sym "imp"
    ; symb_bot   = find_sym "bot"
    ; symb_not   = find_sym "not" }

(** [translate pos builtins (hs, g)] translate from lambdapi to Why3 goal [g]
    using the hypothesis [hs]. The function output the translation of the
    hypothesis and the goal to Why3 and return also a list of all Why3
    constants used during the translation. *)
let rec translate : Pos.popt -> sym StrMap.t -> (Env.env * term) ->
    cnst_table * ctxt_labels * Why3.Term.term =
    fun pos builtins  (hs, g) ->
    let cfg = get_prop_config pos builtins in
    let (l_prop, hypothesis) =
        List.fold_left (translate_context cfg) ([], []) hs in
    try
        let (l_prop, formula) = t_goal cfg l_prop g in
        (l_prop, hypothesis, formula)
    with NoGoalTranslation ->
        Console.fatal pos "The term [%a] is not of the form [P _]"
        Print.pp g

(** [translate_context cfg (l_constants, l_hypothesis) (hyp_name, (_, hyp))]
    translate the context [hyp] with the label [hyp_name] and add it in
    [l_hypothesis] with the why3 constants [l_constants]. *)
and translate_context :
    prop_config ->
    cnst_table * ctxt_labels ->
    string * (tvar * tbox) ->
    cnst_table * ctxt_labels =
    fun cfg (l_constants, l_hypothesis) (hyp_name, (_, hyp)) ->
    try
        let (new_why3_l, hyp') = t_goal cfg l_constants (Bindlib.unbox hyp) in
            (new_why3_l, (hyp_name, hyp')::l_hypothesis)
    with NoGoalTranslation ->
            (l_constants, l_hypothesis)

(** [t_goal cfg l_prop trm] translate the lambdapi term [trm] to Why3 term
    using the configuration [cfg] and the list of Why3 constants in [l_prop].
    *)
and t_goal : prop_config -> cnst_table -> term ->
    cnst_table * Why3.Term.term =
    fun cfg l_prop trm ->
    match Basics.get_args trm with
    | (symbol, [t]) when Basics.is_symb cfg.symb_P symbol ->
        t_prop cfg l_prop [] t
    | _                                                         ->
        raise NoGoalTranslation

(** [t_prop cfg l_prop ctxt p] translate the term [p] into Why3 terms with a
    context [ctxt] and a config [cfg]. *)
and t_prop :
    prop_config -> cnst_table -> Ctxt.t -> term ->
    cnst_table * Why3.Term.term =
    fun cfg l_prop ctxt p ->
    match Basics.get_args p with
    | symbol, [t1; t2] when Basics.is_symb cfg.symb_and symbol  ->
        let (l_prop, t1) = t_prop cfg l_prop ctxt t1 in
        let (l_prop, t2) = t_prop cfg l_prop ctxt t2 in
        l_prop, Why3.Term.t_and t1 t2
    | symbol, [t1; t2] when Basics.is_symb cfg.symb_or symbol  ->
        let (l_prop, t1) = t_prop cfg l_prop ctxt t1 in
        let (l_prop, t2) = t_prop cfg l_prop ctxt t2 in
        l_prop, Why3.Term.t_or t1 t2
    | symbol, [t1; t2] when Basics.is_symb cfg.symb_imp symbol  ->
        let (l_prop, t1) = t_prop cfg l_prop ctxt t1 in
        let (l_prop, t2) = t_prop cfg l_prop ctxt t2 in
        l_prop, Why3.Term.t_implies t1 t2
    | symbol, [t] when Basics.is_symb cfg.symb_not symbol  ->
        let (l_prop, t) = t_prop cfg l_prop ctxt t in
        l_prop, Why3.Term.t_not t
    | _                                                     ->
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