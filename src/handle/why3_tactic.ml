(** Implementation of the why3 tactic. *)

open Lplib open Extra
open Timed
open Common open Error
open Core open Term open Print
open Fol

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

(** Type for maps from Lambdapi terms to Why3 constants. *)
type cnst_table = (term * Why3.Term.lsymbol) list

(** Type for maps from Lambdapi terms to Why3 type constants. *)
type ty_table = (term * Why3.Ty.tysymbol) list

let id_user n = Why3.Ident.id_user n Why3.Loc.dummy_position

let tysymbol s = Why3.Ty.create_tysymbol (id_user s.sym_name) [] Why3.Ty.NoDef

let tvsymbol x = Why3.Ty.tv_of_string (Bindlib.name_of x)

let vsymbol x = Why3.Term.create_vsymbol (id_user (Bindlib.name_of x))

let rec tys_of_terms tbl ts =
  let tbl, ts =
    List.fold_right
      (fun t (tbl,ts) -> let tbl, t = ty_of_term tbl t in tbl, t::ts)
      ts (tbl,[])
  in
  tbl, ts

and ty_of_term tbl te =
  match get_args te with
  | Symb s, ts ->
      let tbl, ts = tys_of_terms tbl ts in
      tbl, Why3.Ty.ty_app (tysymbol s) ts
  | Vari x, [] ->
      tbl, Why3.Ty.ty_var (tvsymbol x)
  | _ ->
      match List.assoc_eq (Eval.eq_modulo []) te tbl with
      | sym -> tbl, Why3.Ty.ty_app sym []
      | exception Not_found ->
          let id = Why3.Ident.id_fresh "ty" in
          let sym = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
          (te,sym)::tbl, Why3.Ty.ty_app sym []

type vtyp_table = (term Bindlib.var * Why3.Ty.ty) list

(** [translate_term cfg tbl t] translates the given lambdapi term [t] into the
    correspondig Why3 term, using the configuration [cfg] and constants in the
    association list [tbl]. *)
let translate_term :
      config -> cnst_table -> ty_table -> vtyp_table -> term
      -> (cnst_table * ty_table * Why3.Term.term) option =
  fun cfg tbl ty_tbl vtyps t ->
  let rec translate_prop tbl ty_tbl vtyps t =
    match get_args t with
    | Symb(s), [t1; t2] when s == cfg.symb_and ->
        let (tbl, ty_tbl, t1) = translate_prop tbl ty_tbl vtyps t1 in
        let (tbl, ty_tbl, t2) = translate_prop tbl ty_tbl vtyps t2 in
        (tbl, ty_tbl, Why3.Term.t_and t1 t2)
    | Symb(s), [t1; t2] when s == cfg.symb_or  ->
        let (tbl, ty_tbl, t1) = translate_prop tbl ty_tbl vtyps t1 in
        let (tbl, ty_tbl, t2) = translate_prop tbl ty_tbl vtyps t2 in
        (tbl, ty_tbl, Why3.Term.t_or t1 t2)
    | Symb(s), [t1; t2] when s == cfg.symb_imp ->
        let (tbl, ty_tbl, t1) = translate_prop tbl ty_tbl vtyps t1 in
        let (tbl, ty_tbl, t2) = translate_prop tbl ty_tbl vtyps t2 in
        (tbl, ty_tbl, Why3.Term.t_implies t1 t2)
    | Symb(s), [t] when s == cfg.symb_not ->
        let (tbl, ty_tbl, t) = translate_prop tbl ty_tbl vtyps t in
        (tbl, ty_tbl, Why3.Term.t_not t)
    | Symb(s), [] when s == cfg.symb_bot ->
        (tbl, ty_tbl, Why3.Term.t_false)
    | Symb(s), [] when s == cfg.symb_top ->
        (tbl, ty_tbl, Why3.Term.t_true)
    | Vari x, [] ->
        let ty = try List.assoc x vtyps with Not_found -> assert false in
        (tbl, ty_tbl, Why3.Term.t_var (vsymbol x ty))
    | Symb(s), [a;Abst(_,t)] when s == cfg.symb_ex ->
        let (ty_tbl, ty) = ty_of_term ty_tbl a
        and x, t = Bindlib.unbind t in
        let vtyps = (x, ty) :: vtyps in
        let (tbl, ty_tbl, t) = translate_prop tbl ty_tbl vtyps t in
        (tbl, ty_tbl, Why3.Term.t_exists_close [vsymbol x ty] [] t)
    | Symb(s), [a;Abst(_,t)] when s == cfg.symb_all ->
        let (ty_tbl, ty) = ty_of_term ty_tbl a
        and x, t = Bindlib.unbind t in
        let vtyps = (x, ty) :: vtyps in
        let (tbl, ty_tbl, t) = translate_prop tbl ty_tbl vtyps t in
        (tbl, ty_tbl, Why3.Term.t_forall_close [vsymbol x ty] [] t)
    | _ ->
        (* If the term [t] is mapped in [tbl] then use it. *)
        try
          let sym = List.assoc_eq (Eval.eq_modulo []) t tbl in
          (tbl, ty_tbl, Why3.Term.ps_app sym [])
        with Not_found ->
          (* Otherwise generate a new constant in why3. *)
          let sym = Why3.Term.create_psymbol (Why3.Ident.id_fresh "P") [] in
          ((t, sym)::tbl, ty_tbl, Why3.Term.ps_app sym [])
  in
  match get_args t with
  | (Symb(s), [t]) when s == cfg.symb_P ->
      Some (translate_prop tbl ty_tbl vtyps t)
  | _ -> None

(** [encode ss pos hs g] translates the hypotheses [hs] and the goal [g]
    into Why3 terms, to construct a Why3 task. *)
let encode : Sig_state.t -> Pos.popt -> Env.env -> term -> Why3.Task.task =
  fun ss pos hs g ->
  let cfg = get_config ss pos in
  let (constants, types, hypothesis) =
    let translate_hyp (tbl,ty_tbl,map) (name, (_, hyp, _)) =
      match translate_term cfg tbl ty_tbl [] (Bindlib.unbox hyp) with
      | Some(tbl, ty_tbl, why3_hyp) ->
        (tbl, ty_tbl, StrMap.add name why3_hyp map)
      | None -> (tbl, ty_tbl , map)
    in
    List.fold_left translate_hyp ([], [], StrMap.empty) hs
  in
  (* Translate the goal term. *)
  let (tbl, ty_tbl, why3_term) =
    match translate_term cfg constants types [] g with
    | Some(tbl, ty_tbl, why3_term) -> (tbl, ty_tbl, why3_term)
    | None                         ->
        fatal pos "The goal [%a] is not of the form [P _]" term g
  in
  let tsk = None in
  log "%a" Why3.Pretty.print_task tsk;
  (* Add the declaration of every constant in a task. *)
  let fn tsk (_,t) = Why3.Task.add_param_decl tsk t in
  let tsk = List.fold_left fn tsk tbl in
  log "%a" Why3.Pretty.print_task tsk;
  (* Add the declarations of every type in a task. *)
  let decl_sym tsk (_,sym) = Why3.Task.add_ty_decl tsk sym in
  let tsk = List.fold_left decl_sym tsk ty_tbl in
  log "%a" Why3.Pretty.print_task tsk;
  (* Add the declaration of every hypothesis in the task. *)
  let fn name t tsk =
    let axiom = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh name) in
    Why3.Task.add_prop_decl tsk Why3.Decl.Paxiom axiom t
  in
  let tsk = StrMap.fold fn hypothesis tsk in
  log "%a" Why3.Pretty.print_task tsk;
  (* Add the goal itself. *)
  let goal = Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "main_goal") in
  (* Return the task that contains the encoded lambdapi formula in Why3. *)
  let tsk = Why3.Task.add_prop_decl tsk Why3.Decl.Pgoal goal why3_term in
  log "%a" Why3.Pretty.print_task tsk;
  tsk

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
    try Why3.Driver.(load_driver_for_prover why3_main why3_env prover)
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
  Sig_state.t -> Pos.popt -> string option -> Proof.goal_typ -> unit =
  fun ss pos prover_name {goal_meta = _; goal_hyps = hyps; goal_type = trm} ->
  (* Get the name of the prover. *)
  let prover_name = Option.get !default_prover prover_name in
  if Logger.log_enabled () then
    log "running with prover \"%s\"" prover_name;
  (* Encode the goal in Why3. *)
  let tsk = encode ss pos hyps trm in
  (* Run the task with the prover named [prover_name]. *)
  if not (run_task tsk pos prover_name) then
    fatal pos "\"%s\" did not find a proof" prover_name
