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
type l2y =
  { s2ts : (sym * Why3.Ty.tysymbol) list
  (* Mapping of type symbols. *)
  ; v2tv : (tvar * Why3.Ty.tvsymbol) list
  (* Mapping of type variables. *)
  ; t2ts : (term * Why3.Ty.tysymbol) list
  (* Mapping of non-Why3 subtypes. *)
  ; v2ls : (tvar * (Why3.Term.lsymbol * bool)) list
  (* Mapping of environment variables.
     [true] is used for propositional variables. *)
  ; v2vs : (tvar * Why3.Term.vsymbol) list
  (* Mapping of quantified variables. *)
  ; t2ls : (term * Why3.Term.lsymbol) list
  (* Mapping of non-Why3 subterms. *)
  }

let empty_l2y = {s2ts=[]; v2tv=[]; t2ts=[]; v2ls=[]; v2vs=[]; t2ls=[]}

let l2y ppf m =
  let open Debug.D in
  Base.out ppf "{s2ts=%a; v2tv=%a; t2ts=%a; v2ls=%a; v2vs=%a; t2ls=%a}"
    (list (pair sym Why3.Pretty.print_ts)) m.s2ts
    (list (pair var Why3.Pretty.print_tv)) m.v2tv
    (list (pair term Why3.Pretty.print_ts)) m.t2ts
    (list (pair var (pair Why3.Pretty.print_ls bool))) m.v2ls
    (list (pair var Why3.Pretty.print_vs)) m.v2vs
    (list (pair term Why3.Pretty.print_ls)) m.t2ls

(* [translate_type m t] returns [(m',a)] where [a] is the Why3 type
   corresponding to the Lambdapi term [t], with the subterms equivalent to
   those in the domain of [m.t2ts] replaced by their images, and the subterms
   not in the language of Why3 replaced by new type constants added in
   [m']. Raises [Exit] if [t] cannot be translated. *)
let rec translate_type m t =
  match get_args t with
  | Symb s, ts ->
      let m, ts = translate_types m ts in
      let m, s =
        match List.assoc_opt s m.s2ts with
        | Some s' -> m, s'
        | None ->
            let id = Why3.Ident.id_fresh s.sym_name in
            let s' = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
            {m with s2ts=(s,s')::m.s2ts}, s'
      in
      m, Why3.Ty.ty_app s ts
  | Vari x, [] ->
      begin
        match List.assoc_eq_opt Bindlib.eq_vars x m.v2tv with
        | Some tv -> m, Why3.Ty.ty_var tv
        | None -> raise Exit
      end
  | _ ->
      raise Exit
      (*try m, Why3.Ty.ty_app (List.assoc_eq (Eval.eq_modulo []) t m.t2ts) []
      with Not_found ->
        let id = Why3.Ident.id_fresh "T" in
        let s = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
        {m with t2ts = (t,s)::m.t2ts}, Why3.Ty.ty_app s []*)

and translate_types m ts =
  List.fold_right
    (fun t (m,ts) -> let m,t = translate_type m t in m, t::ts)
    ts (m,[])

(** [translate_prop cfg m t] returns [(m',u)] where [u] is the Why3
    proposition corresponding to the Lambdapi term [t], with the subterms
    equivalent to those in the domain of [m.t2ls] and [m.t2ts] replaced by
    their images, and the subterms not in the language of Why3 replaced by new
    symbols added in [m']. Raises [Exit] if [t] cannot be translated. *)
let rec translate_prop :
          config -> l2y -> term -> l2y * Why3.Term.term =
  let default m t =
    try
      let sym = List.assoc_eq (Eval.eq_modulo []) t m.t2ls in
      (m, Why3.Term.ps_app sym [])
    with Not_found ->
      let sym = Why3.Term.create_psymbol (Why3.Ident.id_fresh "X") [] in
      ({m with t2ls = (t,sym)::m.t2ls}, Why3.Term.ps_app sym [])
  in
  fun cfg m t ->
  (*if Logger.log_enabled() then log "translate_prop %a %a" l2y m term t;*)
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
      let m,a = translate_type m a
      and x,t = Bindlib.unbind t in
      let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
      let v = Why3.Term.create_vsymbol id a in
      let m = {m with v2vs = (x,v)::m.v2vs} in
      let (m,t) = translate_prop cfg m t in
      (m, Why3.Term.t_exists_close [v] [] t)
  | Symb s, [a;Abst(_,t)] when s == cfg.symb_all ->
      let m,a = translate_type m a
      and x,t = Bindlib.unbind t in
      let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
      let v = Why3.Term.create_vsymbol id a in
      let m = {m with v2vs = (x,v)::m.v2vs} in
      let (m,t) = translate_prop cfg m t in
      (m, Why3.Term.t_forall_close [v] [] t)
  | Vari x, [] ->
      begin
        match List.assoc_eq_opt Bindlib.eq_vars x m.v2ls with
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
    (*if Logger.log_enabled() then log "translate_hyp %a %a %s : %a"
      l2y m Debug.D.(list (pair string Why3.Pretty.print_term)) hyps
      name term a;*)
    match get_args a with
    | Symb s, [] when s == cfg.symb_Set -> (* type variable *)
        let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
        let tv = Why3.Ty.create_tvsymbol id in
        {m with v2tv = (x,tv)::m.v2tv}, hyps
    | Symb s, [t] when s == cfg.symb_T -> (* object *)
        let m,t = translate_type m t in
        let id = Why3.Ident.id_fresh name in
        let f = Why3.Term.create_fsymbol id [] t in
        {m with v2ls = (x,(f,false))::m.v2ls}, hyps
    | Symb s, [] when s == cfg.symb_Prop -> (* propositional variable *)
        let id = Why3.Ident.id_fresh (Bindlib.name_of x) in
        let f = Why3.Term.create_psymbol id [] in
        {m with v2ls = (x,(f,true))::m.v2ls}, hyps
    | Symb s, [t] when s == cfg.symb_P -> (* proposition *)
        let m,t = translate_prop cfg m t in
        m, (name,t)::hyps
    | _ -> m, hyps
  in
  let translate_hyp b m = try translate_hyp b m with Exit -> m in
  let m, hyps = List.fold_right translate_hyp env (empty_l2y, []) in
  if Logger.log_enabled() then log "hyps: %a"
    Debug.D.(list (pair string Why3.Pretty.print_term)) hyps;
  (* Translate the goal. *)
  let m, g =
    match get_args g with
    | Symb s, [t] when s == cfg.symb_P ->
        begin
          try translate_prop cfg m t
          with Exit -> fatal pos "The goal cannot be translated to Why3."
        end
    | _ -> fatal pos "The goal is not of the form [%a _]." sym cfg.symb_P
  in
  if Logger.log_enabled() then log "goal: %a" Why3.Pretty.print_term g;
  if Logger.log_enabled() then log "map: %a" l2y m;
  (* Build the task. *)
  let tsk = None in
  (* Add the declarations of type symbols. *)
  let add_s2ts_decl tsk (_,tsym) = Why3.Task.add_ty_decl tsk tsym in
  let tsk = List.fold_left add_s2ts_decl tsk m.s2ts in
  let add_t2ts_decl tsk (_,tsym) = Why3.Task.add_ty_decl tsk tsym in
  let tsk = List.fold_left add_t2ts_decl tsk m.t2ts in
  (* Add the declarations of term symbols. *)
  let add_ovar_decl tsk (_,(lsym,_)) = Why3.Task.add_param_decl tsk lsym in
  let tsk = List.fold_left add_ovar_decl tsk m.v2ls in
  let add_t2ls_decl tsk (_,lsym) = Why3.Task.add_param_decl tsk lsym in
  let tsk = List.fold_left add_t2ls_decl tsk m.t2ls in
  (* Add the declarations of assumptions. *)
  let add_hyp_decl tsk (name,prop) =
    let axiom = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh name) in
    Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom prop
  in
  let tsk = List.fold_left add_hyp_decl tsk hyps in
  (* Add the goal. *)
  let goal = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "G") in
  let tsk = Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal g in
  if Logger.log_enabled() then log "%a" Why3.Pretty.print_task tsk;
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
  if Logger.log_enabled() then log "%a%a" Goal.hyps g Goal.pp g;
  (* Encode the goal in Why3. *)
  let tsk = translate_goal ss pos hyps t in
  (* Get the name of the prover. *)
  let prover_name = Option.get !default_prover prover_name in
  if Logger.log_enabled() then log "running with prover \"%s\"" prover_name;
  (* Run the task with the prover named [prover_name]. *)
  if not (run tsk pos prover_name) then
    fatal pos "\"%s\" did not find a proof" prover_name
