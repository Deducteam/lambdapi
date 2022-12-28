(** Implementation of the why3 tactic. *)

open Lplib open Extra
open Timed
open Common open Error
open Core open Term open Print

(** Logging function for external prover calling with Why3. *)
let log_why3 = Logger.make 'y' "why3" "why3 provers"
let log_why3 = log_why3.pp

(** [default_prover] contains the name of the current prover. Note that it can
    be changed by using the "set prover <string>" command. *)
let default_prover : string ref = ref "Alt-Ergo"

(** [timeout] is the current time limit (in seconds) for a Why3 prover to find
    a proof. It can be changed with "set prover <int>". *)
let timeout : int ref = ref 2

(** [why3_config] is the Why3 configuration read from the configuration file
   (["~/.why3.conf"] usually). For more information, visit the Why3
   documentation at http://why3.lri.fr/api/Whyconf.html. *)
let why3_config : Why3.Whyconf.config =
  let cfg = Why3.Whyconf.init_config None in
  let provers = Why3.Whyconf.get_provers cfg in
  Console.out 2 "provers available for why3:";
  let prover p _ = Console.out 2 "%a" Why3.Whyconf.print_prover p in
  Why3.Whyconf.Mprover.iter prover provers;
  cfg

(** [why3_main] is the main section of the Why3 configuration. *)
let why3_main : Why3.Whyconf.main = Why3.Whyconf.get_main why3_config
let why3_libdir : string = Why3.Whyconf.libdir why3_main
let why3_datadir : string = Why3.Whyconf.datadir why3_main

(** [why3_env] is the initialized Why3 environment. *)
let why3_env : Why3.Env.env =
  Why3.Env.create_env (Why3.Whyconf.loadpath why3_main)

(** Builtin configuration for propositional logic. *)
type config =
  { symb_P   : sym (** Encoding of propositions. *)
  ; symb_T   : sym (** Encoding of types. *)
  ; symb_or  : sym (** Disjunction(∨) symbol. *)
  ; symb_and : sym (** Conjunction(∧) symbol. *)
  ; symb_imp : sym (** Implication(⇒) symbol. *)
  ; symb_bot : sym (** Bot(⊥) symbol. *)
  ; symb_top : sym (** Top(⊤) symbol. *)
  ; symb_not : sym (** Not(¬) symbol. *)
  ; symb_ex  : sym (** Exists(∃) symbol. *)
  ; symb_all : sym (** Forall(∀) symbol. *) }

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  { symb_P   = builtin "P"
  ; symb_T   = builtin "T"
  ; symb_or  = builtin "or"
  ; symb_and = builtin "and"
  ; symb_imp = builtin "imp"
  ; symb_bot = builtin "bot"
  ; symb_top = builtin "top"
  ; symb_not = builtin "not"
  ; symb_ex  = builtin "ex"
  ; symb_all = builtin "all" }

(** A map from lambdapi terms to Why3 constants. *)
type cnst_table = (term * Why3.Term.lsymbol) list

(** Table of declared types, these types may be variables or constants. *)
module TyTable : sig
  type t

  val empty : t

  val ty_of_term : t -> term -> t * Why3.Ty.ty
  (** [ty_of_term tbl te] fetches the type associated to term [te] in
      table [tbl] if it exists, or it creates such a type and return
      the created type and the new table. *)

  (** {b FIXME} the translation of types {!ty_of_term} is correct on
      non empty types only. *)

  val fold_left :
    do_var:('a -> term -> Why3.Ty.tvsymbol -> 'a) ->
    do_sym:('a -> term -> Why3.Ty.tysymbol -> 'a) -> 'a -> t -> 'a
  (** [fold_left ~do_var ~do_sym init tbl] folds over the table [tbl]
      with initial value [init] using [do_var] to operate on type
      variables and [do_sym] to operate on type symbols. *)
end = struct
  (* The module is created to hide the type [sym_or_var] *)
  type sym_or_var = TySym of Why3.Ty.tysymbol | TyVar of Why3.Ty.tvsymbol

  type t = (term * sym_or_var) list

  let empty = []

  let ty_of_term tbl te =
    match List.assoc_eq (Eval.eq_modulo []) te tbl with
    | TySym s -> (tbl, Why3.Ty.ty_app s [])
    | TyVar v -> (tbl, Why3.Ty.ty_var v)
    | exception Not_found -> (
        (* FIXME generate a new goal to ensure that types translated as
           fresh constants are inhabited. *)
        match get_args te with
        | Symb s, [] ->
          let id = Why3.Ident.id_fresh s.sym_name in
          let sym = Why3.(Ty.create_tysymbol id [] Ty.NoDef) in
          ((te,TySym sym)::tbl, Why3.Ty.ty_app sym [])
        | Vari x, [] ->
          let sym = Why3.Ty.tv_of_string (Bindlib.name_of x) in
          ((te,TyVar sym)::tbl, Why3.Ty.ty_var sym)
        | _ ->
          let id = Why3.Ident.id_fresh "ty" in
          let sym = Why3.(Ty.create_tysymbol id [] Ty.NoDef) in
          ((te,TySym sym)::tbl, Why3.Ty.ty_app sym []))

  let fold_left ~do_var ~do_sym acc tbl =
    let f acc (t,s_or_v) =
      match s_or_v with
      | TySym s -> do_sym acc t s
      | TyVar v -> do_var acc t v
    in
    List.fold_left f acc tbl
end

(** [new_axiom_name ()] generates a fresh axiom name. *)
let new_axiom_name : unit -> string =
  let counter = ref 0 in
  fun _ -> incr counter; "Why3axiom_" ^ (string_of_int !counter)

(** [translate_term cfg tbl t] translates the given lambdapi term [t] into the
    correspondig Why3 term, using the configuration [cfg] and constants in the
    association list [tbl]. *)
let translate_term : config -> cnst_table -> TyTable.t -> term ->
                       (cnst_table * TyTable.t * Why3.Term.term) option =
  fun cfg tbl ty_tbl t ->
  let rec translate_prop tbl ty_tbl t =
    match get_args t with
    | Symb(s), [t1; t2] when s == cfg.symb_and ->
        let (tbl, ty_tbl, t1) = translate_prop tbl ty_tbl t1 in
        let (tbl, ty_tbl, t2) = translate_prop tbl ty_tbl t2 in
        (tbl, ty_tbl, Why3.Term.t_and t1 t2)
    | Symb(s), [t1; t2] when s == cfg.symb_or  ->
        let (tbl, ty_tbl, t1) = translate_prop tbl ty_tbl t1 in
        let (tbl, ty_tbl, t2) = translate_prop tbl ty_tbl t2 in
        (tbl, ty_tbl, Why3.Term.t_or t1 t2)
    | Symb(s), [t1; t2] when s == cfg.symb_imp ->
        let (tbl, ty_tbl, t1) = translate_prop tbl ty_tbl t1 in
        let (tbl, ty_tbl, t2) = translate_prop tbl ty_tbl t2 in
        (tbl, ty_tbl, Why3.Term.t_implies t1 t2)
    | Symb(s), [t] when s == cfg.symb_not ->
        let (tbl, ty_tbl, t) = translate_prop tbl ty_tbl t in
        (tbl, ty_tbl, Why3.Term.t_not t)
    | Symb(s), [] when s == cfg.symb_bot ->
        (tbl, ty_tbl, Why3.Term.t_false)
    | Symb(s), [] when s == cfg.symb_top ->
        (tbl, ty_tbl, Why3.Term.t_true)
    | Symb(s), [a;Abst(_,t)] when s == cfg.symb_ex || s == cfg.symb_all ->
        let (ty_tbl, ty) = TyTable.ty_of_term ty_tbl a in
        let x, t = Bindlib.unbind t in
        let (tbl, ty_tbl ,t) = translate_prop tbl ty_tbl t in
        let tquant =
          let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
          let vid = Why3.(Term.create_vsymbol id) ty in
          let close =
            if s == cfg.symb_ex then Why3.Term.t_exists_close
            else Why3.Term.t_forall_close
           (* Other cases excluded by pattern matching *)
          in
          close [vid] [] t
        in
        (tbl, ty_tbl, tquant)
    | _ ->
        (* If the term [p] is mapped in [tbl] then use it. *)
        try
          let sym = List.assoc_eq (Eval.eq_modulo []) t tbl in
          (tbl, ty_tbl, Why3.Term.ps_app sym [])
        with Not_found ->
          (* Otherwise generate a new constant in why3. *)
          let sym = Why3.Term.create_psymbol (Why3.Ident.id_fresh "P") [] in
          ((t, sym)::tbl, ty_tbl, Why3.Term.ps_app sym [])
  in
  match get_args t with
  | (Symb(s), [t]) when s == cfg.symb_P -> Some (translate_prop tbl ty_tbl t)
  | _ -> None

(** [encode ss pos hs g] translates the hypotheses [hs] and the goal [g]
    into Why3 terms, to construct a Why3 task. *)
let encode : Sig_state.t -> Pos.popt -> Env.env -> term -> Why3.Task.task =
  fun ss pos hs g ->
  let cfg = get_config ss pos in
  let (constants, types, hypothesis) =
    let translate_hyp (tbl,ty_tbl, map) (name, (_, hyp, _)) =
      match translate_term cfg tbl ty_tbl (Bindlib.unbox hyp) with
      | Some(tbl, ty_tbl, why3_hyp) ->
        (tbl, ty_tbl, StrMap.add name why3_hyp map)
      | None -> (tbl, ty_tbl , map)
    in
    List.fold_left translate_hyp ([], TyTable.empty, StrMap.empty) hs
  in
  (* Translate the goal term. *)
  let (tbl, ty_tbl, why3_term) =
    match translate_term cfg constants types g with
    | Some(tbl, ty_tbl, why3_term) -> (tbl, ty_tbl, why3_term)
    | None                         ->
        fatal pos "The goal [%a] is not of the form [P _]" term g
  in
  (* Add the declaration of every constant in a task. *)
  let fn tsk (_,t) = Why3.Task.add_param_decl tsk t in
  let tsk = List.fold_left fn None tbl in
  (* Same for types. *)
  let tsk =
    let do_sym tsk _ tys = Why3.Task.add_ty_decl tsk tys in
    let do_var tsk _ _ = tsk in
    TyTable.fold_left ~do_var ~do_sym tsk ty_tbl
  in
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

(** [run_task tsk pos prover_name] Run the task [tsk] with the specified
    prover named [prover_name] and return the answer of the prover. *)
let run_task : Why3.Task.task -> Pos.popt -> string -> bool =
  fun tsk pos prover_name ->
  (* Filter the set of why3 provers. *)
  let filter = Why3.Whyconf.parse_filter_prover prover_name in
  let provers = Why3.Whyconf.filter_provers why3_config filter in
  (* Fail if we did not find a matching prover. *)
  if Why3.Whyconf.Mprover.is_empty provers then
    begin
      fatal_msg "prover \"%s\" not found.@." prover_name;
      let provers = Why3.Whyconf.get_provers why3_config in
      let _ =
        if Why3.Whyconf.Mprover.is_empty provers then
          fatal_msg "There are no available Why3 provers.@."
        else
          let fn p _ = fatal_msg " - %a@." Why3.Whyconf.print_prover p in
          fatal_msg "The available Why3 provers are:@.";
          Why3.Whyconf.Mprover.iter fn provers
      in
      fatal_msg "Why3 configuration read from \"%s\".@."
        (Why3.Whyconf.get_conf_file why3_config);
      fatal_msg "Your prover might not be installed or detected, ";
      fatal pos "remember to run [why3 config detect]."
    end;
  (* Return the prover configuration and load the driver. *)
  let prover = snd (Why3.Whyconf.Mprover.max_binding provers) in
  let driver =
    try Why3.Whyconf.(load_driver why3_main why3_env prover)
    with e -> fatal pos "Failed to load driver for \"%s\": %a"
                prover.prover.prover_name Why3.Exn_printer.exn_printer e
  in
  (* Actually run the prover. *)
  let command = prover.Why3.Whyconf.command
  and limit = {Why3.Call_provers.empty_limit with limit_time = !timeout} in
  let call =
    Why3.Driver.prove_task ~command ~libdir:why3_libdir ~datadir:why3_datadir
        ~limit driver tsk in
  Why3.Call_provers.((wait_on_call call).pr_answer = Valid)

(** [handle ss pos prover_name g] runs the Why3 prover corresponding
    to the name [prover_name] (if given or a default one otherwise)
    on the goal [g].
    If the prover succeeded to prove the goal, then this is reflected by a new
    axiom that is added to signature [ss]. *)
let handle :
  Sig_state.t -> Pos.popt -> string option -> Proof.goal_typ -> term =
  fun ss pos prover_name {goal_meta = m; goal_hyps = hyps; goal_type = trm} ->
  (* Get the name of the prover. *)
  let prover_name = Option.get !default_prover prover_name in
  if Logger.log_enabled () then
    log_why3 "running with prover \"%s\"" prover_name;
  (* Encode the goal in Why3. *)
  let tsk = encode ss pos hyps trm in
  (* Run the task with the prover named [prover_name]. *)
  if not (run_task tsk pos prover_name) then
    fatal pos "\"%s\" did not find a proof" prover_name;
  (* Create a new axiom name that represents the proved goal. *)
  let axiom_name = new_axiom_name () in
  (* Add the axiom to the current signature. *)
  let a =
    Sign.add_symbol ss.signature Public Defin Eager true
      (Pos.make pos axiom_name) !(m.meta_type) []
  in
  if Logger.log_enabled () then
    log_why3 "axiom %a created" uid axiom_name;
  (* Return the variable terms of each item in the context. *)
  let terms = List.rev_map (fun (_, (x, _, _)) -> mk_Vari x) hyps in
  (* Apply the instance of the axiom with context. *)
  add_args (mk_Symb a) terms
