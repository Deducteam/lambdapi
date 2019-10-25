(** Calling a prover using Why3. *)

open Terms
open Extra
open Timed
open Scope

(** [default_prover] contains the name of the current prover. Note that it can
    be changed by using the "set prover <name>" command. *)
let default_prover : string ref = ref "Alt-Ergo"

(** [prover_timeout] is the current time limit (in seconds) that is left for a
    prover to find a proof. It can be changed with "set prover <int>". *)
let prover_timeout : int ref = ref 2

(** [why3_config] is the Why3 configuration read the configuration file (it is
    usually located at ["~/.why3.conf"]). For more information, visit the Why3
    documentation at http://why3.lri.fr/api/Whyconf.html. *)
let why3_config : Why3.Whyconf.config = Why3.Whyconf.read_config None

(** [why3_main] is the main section of the Why3 configuration. *)
let why3_main : Why3.Whyconf.main =
  (* Filter the configuration to get only the main information. *)
  let m = Why3.Whyconf.get_main why3_config in
  (* Load all plugins (TPTP, DIMACS, ...) and return the new config. *)
  Why3.Whyconf.load_plugins m; m

(** [why3_env] is the initialized Why3 environment. *)
let why3_env : Why3.Env.env =
  Why3.Env.create_env (Why3.Whyconf.loadpath why3_main)

(** Builtins configuration for propositional logic. *)
type config =
  { symb_P   : sym (** Encoding of propositions. *)
  ; symb_T   : sym (** Encoding of types.        *)
  ; symb_or  : sym (** Disjunction(∨) symbol.    *)
  ; symb_and : sym (** Conjunction(∧) symbol.    *)
  ; symb_imp : sym (** Implication(⇒) symbol.    *)
  ; symb_bot : sym (** Bot(⊥) symbol.            *)
  ; symb_top : sym (** Top(⊤) symbol.            *)
  ; symb_not : sym (** Not(¬) symbol.            *) }

(** [get_config pos builtins] build the configuration using [builtins]. *)
let get_config : Pos.popt -> sym StrMap.t -> config = fun pos builtins ->
  { symb_P   = Sign.builtin pos builtins "P"
  ; symb_T   = Sign.builtin pos builtins "T"
  ; symb_or  = Sign.builtin pos builtins "or"
  ; symb_and = Sign.builtin pos builtins "and"
  ; symb_imp = Sign.builtin pos builtins "imp"
  ; symb_bot = Sign.builtin pos builtins "bot"
  ; symb_top = Sign.builtin pos builtins "top"
  ; symb_not = Sign.builtin pos builtins "not" }

(** A map from lambdapi terms to Why3 constants. *)
type cnst_table = (term * Why3.Term.lsymbol) list

(** [new_axiom_name ()] generates a fresh axiom name. *)
let new_axiom_name : unit -> string =
  let counter = ref 0 in
  fun _ -> incr counter; "Why3axiom_" ^ (string_of_int !counter)

(** [translate_term cfg tbl t] translates the given lambdapi term [t] into the
    correspondig Why3 term, using the configuration [cfg] and constants in the
    association list [tbl]. *)
let translate_term : config -> cnst_table -> term ->
                       (cnst_table * Why3.Term.term) option = fun cfg tbl t ->
  let rec translate_prop tbl t =
    match Basics.get_args t with
    | (Symb(s,_), [t1; t2]) when s == cfg.symb_and ->
        let (tbl, t1) = translate_prop tbl t1 in
        let (tbl, t2) = translate_prop tbl t2 in
        (tbl, Why3.Term.t_and t1 t2)
    | (Symb(s,_), [t1; t2]) when s == cfg.symb_or  ->
        let (tbl, t1) = translate_prop tbl t1 in
        let (tbl, t2) = translate_prop tbl t2 in
        (tbl, Why3.Term.t_or t1 t2)
    | (Symb(s,_), [t1; t2]) when s == cfg.symb_imp ->
        let (tbl, t1) = translate_prop tbl t1 in
        let (tbl, t2) = translate_prop tbl t2 in
        (tbl, Why3.Term.t_implies t1 t2)
    | (Symb(s,_), [t]     ) when s == cfg.symb_not ->
        let (tbl, t) = translate_prop tbl t in
        (tbl, Why3.Term.t_not t)
    | (Symb(s,_), []      ) when s == cfg.symb_bot ->
        (tbl, Why3.Term.t_false)
    | (Symb(s,_), []      ) when s == cfg.symb_top ->
        (tbl, Why3.Term.t_true)
    | (_        , _       )                        ->
        (* If the term [p] is mapped in [tbl] then use it. *)
        try (tbl, Why3.Term.ps_app (List.assoc_eq Basics.eq t tbl) [])
        with Not_found ->
          (* Otherwise generate a new constant in why3. *)
          let sym = Why3.Term.create_psymbol (Why3.Ident.id_fresh "P") [] in
          ((t, sym)::tbl, Why3.Term.ps_app sym [])
  in
  match Basics.get_args t with
  | (Symb(s,_), [t]) when s == cfg.symb_P -> Some (translate_prop tbl t)
  | _                                     -> None

(** [encode pos builtins (hs, g)] translates the goal [g] from lambdapi to
  Why3 using the hypothesis [hs]. The function return a task that contains the
  encoded version of lambdapi constants, hypothesis and the formula in Why3.
  *)
let encode : Pos.popt -> sym StrMap.t -> (Env.env * term) ->
                  Why3.Task.task = fun pos builtins (hs, g) ->
  let cfg = get_config pos builtins in
  let (constants, hypothesis) =
    (* [translate_hyp (tbl, map) (name, (_, hyp))] translate the context [hyp]
       with the label [name] and add it in [tbl] with the why3 constants. *)
    let translate_hyp (tbl, map) (name, (_, hyp)) =
      match translate_term cfg tbl (Bindlib.unbox hyp) with
      | Some(tbl, why3_hyp) -> (tbl, StrMap.add name why3_hyp map)
      | None                -> (tbl, map)
    in
    List.fold_left translate_hyp ([], StrMap.empty) hs
  in
  match translate_term cfg constants g with
  | Some(tbl, why3_term) ->
    (* Add the declaration of every constant in a task. *)
    let fn tsk (_,t) = Why3.Task.add_param_decl tsk t in
    let tsk = List.fold_left fn None tbl in
    (* Add the declaration of every hypothesis in the task. *)
    let fn name t tsk =
      let axiom = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh name) in
      Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom t
    in
    let tsk = StrMap.fold fn hypothesis tsk in
    (* Add the goal itself. *)
    let goal = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "main_goal") in
    (* Return the task that contains the encoded lambdapi formula in Why3. *)
    Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal why3_term
  | None                 ->
      Console.fatal pos "The term [%a] is not of the form [P _]" Print.pp g

(** [prover pos prv] search and return the prover called [prv]. *)
let prover : Pos.popt -> string -> Why3.Whyconf.config_prover = fun pos prv ->
  (* Filter the set of why3 provers. *)
  let fp = Why3.Whyconf.parse_filter_prover prv in
  (* Get the set of provers. *)
  let provers = Why3.Whyconf.filter_provers why3_config fp in
  (* Display a message if we did not find a matching prover. *)
  if Why3.Whyconf.Mprover.is_empty provers then
    Console.fatal pos "[%s] not installed or not configured" prv;
  (* Return the prover configuration. *)
  snd (Why3.Whyconf.Mprover.max_binding provers)

(** [handle prover_name ss tac ps g] FIXME *)
let handle prover_name ss tac ps g =
  (* Get the goal to prove. *)
  let (hypotheses, trm) = Proof.Goal.get_type g in
  (* Get the default or the indicated name of the prover. *)
  let prover_name = Option.get prover_name Timed.(!default_prover) in
  (* Encode the goal in Why3. *)
  let tsk = encode tac.Pos.pos ps.Proof.proof_builtins (hypotheses, trm) in
  (* Call the prover named [prover_name] and get the result. *)
  let prover_result =
    let prv = prover tac.pos prover_name in
    let limit_time = !prover_timeout in
    let limit = {Why3.Call_provers.empty_limit with limit_time} in
    let command = prv.Why3.Whyconf.command in
    (* Load the config prover [prv] in current environment, return the driver
       of the prover. *)
    let driver =
      try Why3.Whyconf.(load_driver why3_main why3_env prv.driver [])
      with e ->
        Console.fatal tac.pos "Failed to load driver for %s: %a"
          prv.prover.prover_name Why3.Exn_printer.exn_printer e
    in
    Why3.Call_provers.wait_on_call
      (Why3.Driver.prove_task ~limit ~command driver tsk)
  in
  (* Check that the prover succeeded to prove the goal. *)
  if not (Why3.Call_provers.Valid = prover_result.pr_answer) then
    Console.fatal tac.pos "%s did not found a proof@." prover_name;
  (* Create a new axiom that represents the proved goal. *)
  let why3_axiom = Pos.make tac.pos (new_axiom_name ()) in
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
