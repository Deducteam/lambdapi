(** Implementation of the why3 tactic. *)

open Lplib
open Timed
open Common open Error
open Core open Term open Print
open Fol
open Proof

(** Logging function for external prover calling with Why3. *)
let log = Logger.make 'y' "why3" "why3 provers"
let log = log.pp

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

(** [why3_env] is the initialized Why3 environment. *)
let why3_env : Why3.Env.env =
  Why3.Env.create_env (Why3.Whyconf.loadpath why3_main)

(** Data used to translate Lambdapi terms to Why3. *)
type lp2y_map =
  { tsym : (term * Why3.Ty.tysymbol) list
  (* Types not in the Why3 language are abstracted by new type symbols. *)
  ; lsym : (term * Why3.Term.lsymbol) list
  (* Terms not in the Why3 language are abstracted by new symbols. *)
  ; etys : (term Bindlib.var * (Why3.Term.lsymbol * bool)) list
  (* Mapping of environment variables.
     [true] is used for propositional variables. *)
  ; vtys : (term Bindlib.var * Why3.Term.vsymbol) list
  (* Mapping of quantified variables. *)
  }

let lp2y_empty_map = { tsym = []; lsym = []; etys = []; vtys = [] }

let lp2y_map ppf m =
  let open Debug.D in
  Base.out ppf "{tsym=%a; lsym=%a; etys=%a; vtys=%a}"
    (list (pair term Why3.Pretty.print_ts)) m.tsym
    (list (pair term Why3.Pretty.print_ls)) m.lsym
    (list (pair var (pair Why3.Pretty.print_ls bool))) m.etys
    (list (pair var Why3.Pretty.print_vs)) m.vtys

(* [translate_type m t] returns [(m',a)] where [a] is the Why3 type
   corresponding to the Lambdapi term [t], with the subterms equivalent to
   those in the domain of [m.tsym] replaced by their images, and the subterms
   not in the language of Why3 replaced by new type constants added in
   [m']. *)
let rec translate_type m t =
  match get_args t with
  | Symb s, ts ->
      let m, ts = translate_types m ts in
      let id = Why3.Ident.id_fresh s.sym_name in
      let s = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
      m, Why3.Ty.ty_app s ts
  | Vari x, [] ->
      m, Why3.Ty.ty_var (Why3.Ty.tv_of_string (Bindlib.name_of x))
  | _ ->
      try m, Why3.Ty.ty_app (List.assoc_eq (Eval.eq_modulo []) t m.tsym) []
      with Not_found ->
        let id = Why3.Ident.id_fresh "ty" in
        let sym = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
        {m with tsym = (t,sym)::m.tsym}, Why3.Ty.ty_app sym []

and translate_types m ts =
  List.fold_right
    (fun t (m,ts) -> let m,t = translate_type m t in m, t::ts)
    ts (m,[])

(** [translate_prop cfg m t] returns [(m',u)] where [u] is the Why3
    proposition corresponding to the Lambdapi term [t], with the subterms
    equivalent to those in the domain of [m.lsym] and [m.tsym] replaced by
    their images, and the subterms not in the language of Why3 replaced by new
    symbols added in [m']. *)
let rec translate_prop :
          config -> lp2y_map -> term -> lp2y_map * Why3.Term.term =
  let default m t =
    try
      let sym = List.assoc_eq (Eval.eq_modulo []) t m.lsym in
      (m, Why3.Term.ps_app sym [])
    with Not_found ->
      let sym = Why3.Term.create_psymbol (Why3.Ident.id_fresh "X") [] in
      ({m with lsym = (t,sym)::m.lsym}, Why3.Term.ps_app sym [])
  in
  fun cfg m t ->
  log "translate_prop %a %a" lp2y_map m term t;
  match get_args t with
  | Symb s, [t1;t2] when s == cfg.symb_and ->
      let (m,t1) = translate_prop cfg m t1 in
      let (m,t2) = translate_prop cfg m t2 in
      (m, Why3.Term.t_and t1 t2)
  | Symb s, [t1;t2] when s == cfg.symb_or  ->
      let (m,t1) = translate_prop cfg m t1 in
      let (m, t2) = translate_prop cfg m t2 in
      (m, Why3.Term.t_or t1 t2)
  | Symb s, [t1;t2] when s == cfg.symb_imp ->
      let (m,t1) = translate_prop cfg m t1 in
      let (m,t2) = translate_prop cfg m t2 in
      (m, Why3.Term.t_implies t1 t2)
  | Symb s, [t] when s == cfg.symb_not ->
      let (m,t) = translate_prop cfg m t in
      (m, Why3.Term.t_not t)
  | Symb s, [] when s == cfg.symb_bot ->
      (m, Why3.Term.t_false)
  | Symb s, [] when s == cfg.symb_top ->
      (m, Why3.Term.t_true)
  | Symb s, [a;Abst(_,t)] when s == cfg.symb_ex ->
      let (m,a) = translate_type m a
      and x,t = Bindlib.unbind t in
      let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
      let v = Why3.Term.create_vsymbol id a in
      let m = {m with vtys = (x,v)::m.vtys} in
      let (m,t) = translate_prop cfg m t in
      (m, Why3.Term.t_exists_close [v] [] t)
  | Symb s, [a;Abst(_,t)] when s == cfg.symb_all ->
      let (m,a) = translate_type m a
      and x,t = Bindlib.unbind t in
      let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
      let v = Why3.Term.create_vsymbol id a in
      let m = {m with vtys = (x,v)::m.vtys} in
      let (m,t) = translate_prop cfg m t in
      (m, Why3.Term.t_forall_close [v] [] t)
  | Vari x, [] ->
      begin
        match List.assoc_eq_opt Bindlib.eq_vars x m.etys with
        | Some(s, true) -> (m, Why3.Term.ps_app s [])
        | _ -> default m t
      end
  | _ -> default m t

(** [translate_goal ss pos env g] translates the hypotheses [env] and the goal
    [g] into a Why3 task. *)
let translate_goal :
      Sig_state.t -> Pos.popt -> Env.env -> term -> Why3.Task.task =
  fun ss pos env g ->
  let cfg = get_config ss pos in
  (* Translate assumptions. *)
  let translate_hyp (name,(x,a,_)) (m,hyps) =
    let a = Bindlib.unbox a in
    log "translate_hyp %a %a %s : %a"
      lp2y_map m Debug.D.(list (pair string Why3.Pretty.print_term)) hyps
      name term a;
    match get_args a with
    | Symb s, [t] when s == cfg.symb_P -> (* proposition *)
        let m,t = translate_prop cfg m t in
        m, (name,t)::hyps
    | Symb s, [t] when s == cfg.symb_T -> (* object *)
        let m,t = translate_type m t in
        let id = Why3.Ident.id_fresh name in
        let f = Why3.Term.create_fsymbol id [] t in
        {m with etys = (x,(f,false))::m.etys}, hyps
    | Symb s, [] when s == cfg.symb_Prop -> (* propositional variable *)
        let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
        let f = Why3.Term.create_psymbol id [] in
        {m with etys = (x,(f,true))::m.etys}, hyps
    | _ -> m, hyps
  in
  let m, hyps = List.fold_right translate_hyp env (lp2y_empty_map, []) in
  log "after translate_hyp: %a %a" lp2y_map m
    Debug.D.(list (pair string Why3.Pretty.print_term)) hyps;
  (* Translate the goal. *)
  let m, g =
    match get_args g with
    | Symb s, [t] when s == cfg.symb_P -> translate_prop cfg m t
    | _ -> fatal pos "The goal is not of the form [%a _]" sym cfg.symb_P
  in
  log "after translate goal: %a %a" lp2y_map m Why3.Pretty.print_term g;
  (* Build the task. *)
  let tsk = None in
  (* Add the declarations of abstracted types. *)
  let add_tsym_decl tsk (_,tsym) = Why3.Task.add_ty_decl tsk tsym in
  let tsk = List.fold_left add_tsym_decl tsk m.tsym in
  log "add abstracted types:\n%a" Why3.Pretty.print_task tsk;
  (* Add the declarations of abstracted terms. *)
  let add_lsym_decl tsk (_,lsym) = Why3.Task.add_param_decl tsk lsym in
  let tsk = List.fold_left add_lsym_decl tsk m.lsym in
  log "add abstracted terms:\n%a" Why3.Pretty.print_task tsk;
  (* Add the declarations of the environment symbols. *)
  let add_ovar_decl tsk (_,(s,_)) = Why3.Task.add_param_decl tsk s in
  let tsk = List.fold_left add_ovar_decl tsk m.etys in
  log "add environment symbols:\n%a" Why3.Pretty.print_task tsk;
  (* Add the declarations of assumptions. *)
  let add_hyp_decl tsk (name,prop) =
    let axiom = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh name) in
    Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom prop
  in
  let tsk = List.fold_left add_hyp_decl tsk hyps in
  log "add hyps:\n%a" Why3.Pretty.print_task tsk;
  (* Add the goal itself. *)
  let goal = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "G") in
  let tsk = Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal g in
  log "add goal:\n%a" Why3.Pretty.print_task tsk;
  tsk

(** [run tsk pos prover_name] sends [tsk] to [prover_name]. *)
let run : Why3.Task.task -> Pos.popt -> string -> bool =
  fun tsk pos prover_name ->
  (* Filter the set of why3 provers. *)
  let filter = Why3.Whyconf.parse_filter_prover prover_name in
  let provers = Why3.Whyconf.filter_provers why3_config filter in
  (* Fail if we did not find a matching prover. *)
  if Why3.Whyconf.Mprover.is_empty provers then
    begin
      fatal_msg "Your prover might not be installed or detected.\n";
      fatal_msg "Remember to run \"why3 config detect\" \
                 after installing a prover.";
      fatal_msg "Why3 configuration read from \"%s\".\n"
        (Why3.Whyconf.get_conf_file why3_config);
      let provers = Why3.Whyconf.get_provers why3_config in
      if Why3.Whyconf.Mprover.is_empty provers then
        fatal_msg "There are no available provers.@."
      else
        begin
          fatal_msg "The available provers are:@.";
          let f p _ = fatal_msg " - %a@." Why3.Whyconf.print_prover p in
          Why3.Whyconf.Mprover.iter f provers
        end;
      fatal pos "prover \"%s\" not found.@." prover_name;
    end;
  (* Return the prover configuration and load the driver. *)
  let prover = snd (Why3.Whyconf.Mprover.max_binding provers) in
  let driver =
    try Why3.Driver.load_driver_for_prover why3_main why3_env prover
    with e -> fatal pos "Failed to load driver for \"%s\": %a"
                prover.prover.prover_name Why3.Exn_printer.exn_printer e
  in
  (* Actually run the prover. *)
  let command = prover.Why3.Whyconf.command
  and limit = {Why3.Call_provers.empty_limit
              with limit_time = float_of_int!timeout} in
  let call =
    Why3.Driver.prove_task ~command ~config:why3_main ~limit driver tsk in
  Why3.Call_provers.((wait_on_call call).pr_answer = Valid)

(** [handle ss pos prover_name gt] runs the Why3 prover corresponding to
    [prover_name] (if given or a default one otherwise) on the goal type [gt],
    and fails if no proof is found. *)
let handle :
  Sig_state.t -> Pos.popt -> string option -> goal_typ -> unit =
  fun ss pos prover_name
      ({goal_meta = _; goal_hyps = hyps; goal_type = t} as gt) ->
  let g = Typ gt in
  if Logger.log_enabled () then log "%a%a" Goal.hyps g Goal.pp g;
  (* Get the name of the prover. *)
  let prover_name = Option.get !default_prover prover_name in
  if Logger.log_enabled () then log "running with prover \"%s\"" prover_name;
  (* Encode the goal in Why3. *)
  let tsk = translate_goal ss pos hyps t in
  (* Run the task with the prover named [prover_name]. *)
  if not (run tsk pos prover_name) then
    fatal pos "\"%s\" did not find a proof" prover_name
