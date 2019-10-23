(** Calling a prover using Why3. *)

open Terms
open Extra
open Timed
open Scope

exception NoGoalTranslation

(* A map from lambdapi terms to Why3 constants. *)
type cnst_table = (term * Why3.Term.lsymbol) list

(** [get_newname ()] generates a new axiom name. *)
let get_newname : unit -> string =
  (* Number of axioms proved whith the Why3 tactic. *)
  let nbr_axioms : int ref = ref 0 in fun () ->
  nbr_axioms := !nbr_axioms + 1;
  "Why3axiom_" ^ (string_of_int !nbr_axioms)

(* Builtins configuration for propositional logic. *)
type prop_config =
  { symb_P     : sym (** Encoding of propositions.        *)
  ; symb_T     : sym (** Encoding of types.               *)
  ; symb_or    : sym (** Disjunction(∨) symbol.           *)
  ; symb_and   : sym (** Conjunction(∧) symbol.           *)
  ; symb_imp   : sym (** Implication(⇒) symbol.           *)
  ; symb_bot   : sym (** Bot(⊥) symbol.                   *)
  ; symb_top   : sym (** Top(⊤) symbol.                   *)
  ; symb_not   : sym (** Not(¬) symbol.                   *) }

(** [get_prop_config pos builtins] set the builtins configuration using
  [builtins]. *)
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
  ; symb_top   = find_sym "top"
  ; symb_not   = find_sym "not" }

(** [translate pos builtins (hs, g)] translates from lambdapi to Why3 goal [g]
  using the hypothesis [hs]. The function return
  [constants_table, hypothesis, formula] where :
  - [constants_table] maps abstracted Lambdapi terms to Why3 constants.
  - [hypothesis] maps abstracted labels to Why3 terms (presentation of
  [hs]).
  - [formula] Why3 term representing the goal [g].  *)
let rec translate : Pos.popt -> sym StrMap.t -> (Env.env * term) ->
  cnst_table * Why3.Term.term StrMap.t * Why3.Term.term =
  fun pos builtins (hs, g) ->
  let cfg = get_prop_config pos builtins in
  let (constants_table, hypothesis) =
    List.fold_left (translate_hyp cfg) ([], StrMap.empty) hs in
  try
    let (constants_table, formula) =
    translate_goal cfg constants_table g in
    (constants_table, hypothesis, formula)
  with NoGoalTranslation ->
    Console.fatal pos "The term [%a] is not of the form [P _]"
    Print.pp g

(** [translate_hyp cfg (l_constants, l_hypothesis) (hyp_name, (_, hyp))]
  translate the context [hyp] with the label [hyp_name] and add it in
  [l_hypothesis] with the why3 constants [l_constants]. *)
and translate_hyp :
  prop_config ->
  cnst_table * Why3.Term.term StrMap.t ->
  string * (tvar * tbox) ->
  cnst_table * Why3.Term.term StrMap.t =
  fun cfg (l_constants, l_hypothesis) (hyp_name, (_, hyp)) ->
  try
    let (new_why3_l, hyp') =
      translate_goal cfg l_constants (Bindlib.unbox hyp)
    in
      (new_why3_l, StrMap.add hyp_name hyp' l_hypothesis)
  with NoGoalTranslation ->
    (l_constants, l_hypothesis)

(** [translate_goal cfg constants_table trm] translate the lambdapi term [trm]
  to Why3 term using the configuration [cfg] and the list of Why3 constants in
  [constants_table]. *)
and translate_goal : prop_config -> cnst_table -> term ->
  cnst_table * Why3.Term.term =
  fun cfg constants_table trm ->
  match Basics.get_args trm with
  | (symbol, [t]) when Basics.is_symb cfg.symb_P symbol ->
    translate_prop cfg constants_table [] t
  | _                                                   ->
    raise NoGoalTranslation

(** [translate_prop cfg constants_table ctxt p] translate the term [p] into
  Why3 terms with a context [ctxt] and a config [cfg]. *)
and translate_prop :
  prop_config -> cnst_table -> Ctxt.t -> term ->
  cnst_table * Why3.Term.term =
  fun cfg constants_table ctxt p ->
  match Basics.get_args p with
  | symbol, [t1; t2] when Basics.is_symb cfg.symb_and symbol  ->
    let (constants_table, t1) =
      translate_prop cfg constants_table ctxt t1 in
    let (constants_table, t2) =
      translate_prop cfg constants_table ctxt t2 in
      constants_table, Why3.Term.t_and t1 t2
  | symbol, [t1; t2] when Basics.is_symb cfg.symb_or symbol  ->
    let (constants_table, t1) =
      translate_prop cfg constants_table ctxt t1 in
    let (constants_table, t2) =
      translate_prop cfg constants_table ctxt t2 in
      constants_table, Why3.Term.t_or t1 t2
  | symbol, [t1; t2] when Basics.is_symb cfg.symb_imp symbol  ->
    let (constants_table, t1) =
      translate_prop cfg constants_table ctxt t1 in
    let (constants_table, t2) =
      translate_prop cfg constants_table ctxt t2 in
      constants_table, Why3.Term.t_implies t1 t2
  | symbol, [t] when Basics.is_symb cfg.symb_not symbol  ->
    let (constants_table, t) =
      translate_prop cfg constants_table ctxt t in
      constants_table, Why3.Term.t_not t
  | symbol, [] when Basics.is_symb cfg.symb_bot symbol   ->
    constants_table, Why3.Term.t_false
  | symbol, [] when Basics.is_symb cfg.symb_top symbol   ->
    constants_table, Why3.Term.t_true
  | _                                                     ->
    (* If the term [p] is in the list [constants_table]. *)
    try
      (* Then find it and return it. *)
      let (_, ct) =
        List.find (fun x -> Basics.eq (fst x) p) constants_table in
        (constants_table, Why3.Term.ps_app ct [])
    with Not_found ->
    (* Or generate a new constant in why3. *)
      let new_symbol = Why3.Ident.id_fresh "P" in
      let sym = Why3.Term.create_psymbol new_symbol [] in
      let new_predicate = Why3.Term.ps_app sym [] in
      (* add the new symbol to the list and return it *)
      (p, sym)::constants_table, new_predicate

(** [add_goal tsk f] add a goal with [f] formula in the task [tsk]. *)
let add_goal : Why3.Task.task -> Why3.Term.term -> Why3.Task.task =
  fun tsk f ->
  let new_goal = Why3.Ident.id_fresh "lambdapi_goal" in
  let goal = Why3.Decl.create_prsymbol new_goal in
  Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal f

(** [add_hypothesis tsk (axiom_name, axiom_term)] add the axiom [axiom_term]
  named [axiom_name] to the Why3 task [tsk]. *)
let add_hypothesis :
  string -> Why3.Term.term -> Why3.Task.task ->  Why3.Task.task =
  fun axiom_name axiom_term tsk ->
  let new_axiom = Why3.Ident.id_fresh axiom_name in
  let axiom = Why3.Decl.create_prsymbol new_axiom in
  Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom axiom_term

(** [create constants_table hypothesis goal] Add all the symbols of
  [constants_table] in a new task and declare [hypothesis] as axioms and
  [goal] as a Why3 goal. *)
let create :
  cnst_table -> Why3.Term.term StrMap.t -> Why3.Term.term
  -> Why3.Task.task =
  fun constants_table hypothesis goal ->
    let symbols = List.map (fun (_, x) -> x) constants_table in
    (* Add the declaration of every symbol. *)
    let tsk = List.fold_left Why3.Task.add_param_decl None symbols in
    let tsk = StrMap.fold add_hypothesis hypothesis tsk in
    add_goal tsk goal

(** [!default_prover] contains the name of the current prover (can be changed
  by using the set prover <name> command). *)
let default_prover : string ref = ref "Alt-Ergo"

(** [prover_timeout] is the time limit (in seconds) of a prover while finding
  finding a proof. *)
let prover_timeout : int ref = ref 10

(** [why3_config] read the config file of Why3 that is installed in the
  machine. the default path is [~/.why3.conf]. More information could be found
  in http://why3.lri.fr/api/Whyconf.html . *)
let why3_config : Why3.Whyconf.config = Why3.Whyconf.read_config None

(** [why3_main] get only the main section of the Why3 config. *)
let why3_main : Why3.Whyconf.main =
  (* Filter the configuration to get only the main information. *)
  let m = Why3.Whyconf.get_main why3_config in
  (* Load all plugins (TPTP, DIMACS, ...) and return the new config. *)
  Why3.Whyconf.load_plugins m; m

(** [prover pos provername] search and return the prover called [prover_name].
  *)
let prover : Pos.popt -> string -> Why3.Whyconf.config_prover =
  fun pos prover_name ->
  (* Filter the set of why3 provers. *)
  let fp = Why3.Whyconf.parse_filter_prover prover_name in
  (* Get the set of provers. *)
  let provers = Why3.Whyconf.filter_provers why3_config fp in
  (* Display a message if we did not find a matching prover. *)
  if Why3.Whyconf.Mprover.is_empty provers then
    Console.fatal pos  "[%s] not installed or not configured"
    prover_name
  else
  (* Return the prover configuration. *)
    snd (Why3.Whyconf.Mprover.max_binding provers)

(** [why3_env] build an empty environment. *)
let why3_env : Why3.Env.env ref = ref (Why3.Env.create_env [])

(* [init_env ()] init the environment. *)
let init_env () =
  why3_env := Why3.Env.create_env (Why3.Whyconf.loadpath why3_main)

(** [prover_driver pos cp] load the config prover [cp] in the current
  enironment and return the driver of the prover. *)
let prover_driver :
  Pos.popt -> Why3.Whyconf.config_prover -> Why3.Driver.driver =
  fun pos cp ->
  try
    Why3.Whyconf.load_driver why3_main !why3_env cp.Why3.Whyconf.driver []
  with e ->
    Console.fatal pos "Failed to load driver for %s: %a"
    cp.prover.prover_name
    Why3.Exn_printer.exn_printer e

let handle prover_name ss tac ps g =
  (* Get the goal to prove. *)
  let (hypotheses, trm) = Proof.Goal.get_type g in
  (* Get the default or the indicated name of the prover. *)
  let prover_name = Option.get prover_name Timed.(!default_prover) in
  (* Translate from lambdapi to why3 terms. *)
  let (constants_table, hyps, why3term) =
    translate tac.Pos.pos ps.Proof.proof_builtins (hypotheses, trm)
  in
  (* Create a new task that contains symbols, axioms and the goal. *)
  let tsk = create constants_table hyps why3term in
  (* Call the prover named [prover_name] and get the result. *)
  let prover_result =
    let prv = (prover tac.pos prover_name) in
    let limit =
      { Why3.Call_provers.empty_limit with limit_time = !prover_timeout }
    in
    Why3.Call_provers.wait_on_call (
      Why3.Driver.prove_task
        ~limit:limit
        ~command:prv.Why3.Whyconf.command (prover_driver tac.pos prv) tsk
        )
    in
  (* Check that the prover succeeded to prove the goal. *)
  if not (Why3.Call_provers.Valid = prover_result.pr_answer) then
    Console.fatal tac.pos "%s did not found a proof@." prover_name;
  (* Create a new axiom that represents the proved goal. *)
  let why3_axiom = Pos.make tac.pos (get_newname ()) in
  (* Get the meta type of the current goal (with quantified context) *)
  let trm = Timed.(!((Proof.Goal.get_meta g).meta_type)) in
  (* Add the axiom to the current signature. *)
  let a = Sign.add_symbol ss.signature Const why3_axiom trm [] in
  (* Tell the user that the goal is proved (verbose 2). *)
  Console.out 2 "%s proved the current goal@." prover_name;
  (* Return the variable terms of each item in the context. *)
  let terms = List.rev_map (fun (_, (x, _)) -> Vari x) hypotheses in
  (* Apply the instance of the axiom with context. *)
  Basics.add_args (symb a) terms

(* Initilizing Why3 environment. *)
let _ = init_env ()