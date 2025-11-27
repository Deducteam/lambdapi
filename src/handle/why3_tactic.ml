(** Implementation of the why3 tactic. *)

open Lplib
open Timed
open Common open Error
open Core open Term open Print
open Fol
open Goal

(** Logging function for external prover calling with Why3. *)
let log = Logger.make 'y' "why3" "why3 tactic"
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

(** Data type used to record how Lambdapi symbols, variables and terms are
    mapped to Why3 symbols or variables. *)
type l2y =
  { s2ts : (sym * Why3.Ty.tysymbol) list
  (* Mapping of type symbols. *)
  ; t2ts : (term * Why3.Ty.tysymbol) list
  (* Mapping of non-Why3 subtypes. *)
  ; v2tv : (var * Why3.Ty.tvsymbol) list
  (* Mapping of type variables. *)
  ; s2ls : (sym * (Why3.Term.lsymbol * bool)) list
  (* Mapping of function symbols. [true] is for predicates. *)
  ; v2ls : (var * (Why3.Term.lsymbol * bool)) list
  (* Mapping of environment variables. [true] is for predicates. *)
  ; t2ls : (term * Why3.Term.lsymbol) list
  (* Mapping of non-Why3 subterms. *)
  ; v2vs : (var * Why3.Term.vsymbol) list
  (* Mapping of object variables. *)
  }

let empty_l2y =
  {s2ts=[]; v2tv=[]; t2ts=[]; s2ls=[]; v2ls=[]; v2vs=[]; t2ls=[]}

let l2y ppf m =
  let open Debug.D in
  Base.out ppf
    "{s2ts=%a; v2tv=%a; t2ts=%a; s2ls=%a; v2ls=%a; v2vs=%a; t2ls=%a}"
    (list (pair sym Why3.Pretty.print_ts)) m.s2ts
    (list (pair var Why3.Pretty.print_tv)) m.v2tv
    (list (pair term Why3.Pretty.print_ts)) m.t2ts
    (list (pair sym (pair Why3.Pretty.print_ls bool))) m.s2ls
    (list (pair var (pair Why3.Pretty.print_ls bool))) m.v2ls
    (list (pair var Why3.Pretty.print_vs)) m.v2vs
    (list (pair term Why3.Pretty.print_ls)) m.t2ls

(** Translation functions below raise Exit if a term cannot be
    translated. They return an update l2y map as well because mappings are
    done while translating terms. *)

(** [translate_set m t] tries to translate a Lambdapi term [t:Set] to a Why3
    type. *)
let rec translate_set m t =
  if Logger.log_enabled() then log "translate_set %a [%a]" l2y m term t;
  match get_args t with
  | Symb s, ts ->
      let m, ts = translate_sets m ts in
      let m, s =
        match List.assoc_opt s m.s2ts with
        | Some s' -> m, s'
        | None ->
            let id = Why3.Ident.id_fresh s.sym_name in
            let s' = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
            if Logger.log_enabled() then
              log "add tysymbol %a" Why3.Pretty.print_ts s';
            {m with s2ts=(s,s')::m.s2ts}, s'
      in
      m, Why3.Ty.ty_app s ts
  | Vari x, [] ->
      begin
        match List.assoc_eq_opt eq_vars x m.v2tv with
        | Some tv -> m, Why3.Ty.ty_var tv
        | None -> raise Exit
      end
  | _ -> raise Exit
      (*try m, Why3.Ty.ty_app (List.assoc_eq (Eval.eq_modulo []) t m.t2ts) []
      with Not_found ->
        let id = Why3.Ident.id_fresh "T" in
        let s = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
        {m with t2ts = (t,s)::m.t2ts}, Why3.Ty.ty_app s []*)

and translate_sets m ts =
  List.fold_right
    (fun t (m,ts) -> let m,t = translate_set m t in m, t::ts)
    ts (m,[])

(** [translate_type m t] tries to translate a Lambdapi term [t:TYPE] of the
    form [P _] to a Why3 type. *)
let translate_type cfg m t =
  if Logger.log_enabled() then log "translate_type %a [%a]" l2y m term t;
  match get_args t with
  | Symb s, [t] when s == cfg.symb_T -> translate_set m t
  | _ -> raise Exit

(*let translate_types cfg m ts =
  List.fold_right
    (fun t (m,ts) -> let m,t = translate_type cfg m t in m, t::ts)
    ts (m,[])*)

(** [translate_pred_type cfg m t] tries to translate a Lambdapi term [t] of
    the form [T a1 → .. → T an → Prop] to a Why3 type. *)
let translate_pred_type cfg =
  let rec aux acc m t =
    if Logger.log_enabled() then
      log "translate_pred_type %a [%a]" l2y m term t;
    match unfold t with
    | Symb s -> if s == cfg.symb_Prop then m, List.rev acc else raise Exit
    | Prod(a,b) ->
        let m,a = translate_type cfg m a in
        let _,b = unbind b in
        aux (a::acc) m b
    | _ -> raise Exit
  in aux []

(** [translate_fun_type cfg m t] tries to translate a Lambdapi term [t] of the
    form [T a1 → .. → T an → T a] to a Why3 type. *)
let translate_fun_type cfg =
  let rec aux acc m t =
    if Logger.log_enabled() then
      log "translate_fun_type %a [%a]" l2y m term t;
    match unfold t with
    | Prod(a,b) ->
        let m,a = translate_type cfg m a in
        let _,b = unbind b in
        aux (a::acc) m b
    | _ ->
        let m,a = translate_type cfg m t in
        m, List.rev acc, a
  in aux []

(** [translate_term cfg m t] tries to translate a Lambdapi term [t:T _] to a
    Why3 term. *)
let rec translate_term cfg m t =
  if Logger.log_enabled() then log "translate_term %a [%a]" l2y m term t;
  match get_args t with
  | Symb s, ts ->
      begin
        match List.assoc_eq_opt (==) s m.s2ls with
        | Some(_, true) -> assert false
        | Some(s, false) ->
            let m, ts = translate_terms cfg m ts in
            m, Why3.Term.t_app_infer s ts
        | None ->
            let m, tys, a = translate_fun_type cfg m !(s.sym_type) in
            let id = Why3.Ident.id_fresh s.sym_name in
            let f = Why3.Term.create_fsymbol id tys a in
            if Logger.log_enabled() then
              log "add psymbol %a : %a → %a" Why3.Pretty.print_ls f
                (Debug.D.list Why3.Pretty.print_ty) tys
                Why3.Pretty.print_ty a;
            let m = {m with s2ls = (s,(f,false))::m.s2ls} in
            let m, ts = translate_terms cfg m ts in
            m, Why3.Term.t_app_infer f ts
      end
  | Vari x, ts ->
      begin
        match List.assoc_eq_opt eq_vars x m.v2vs with
        | Some v ->
            if ts = [] then m, Why3.Term.t_var v else raise Exit
        | None ->
            match List.assoc_eq_opt eq_vars x m.v2ls with
            | Some(_, true) -> assert false
            | Some(s, false) ->
                let m, ts = translate_terms cfg m ts in
                m, Why3.Term.t_app_infer s ts
            | None -> assert false
      end
  | _ -> raise Exit

and translate_terms cfg m ts =
  List.fold_right
    (fun t (m,ts) -> let m,t = translate_term cfg m t in m, t::ts)
    ts (m,[])

(** [translate_prop cfg m t] tries to translation a Lambdapi term [t:Prop] to
    a Why3 proposition. *)
let rec translate_prop : config -> l2y -> term -> l2y * Why3.Term.term =
  let default m t =
    try
      let sym = List.assoc_eq (Eval.eq_modulo []) t m.t2ls in
      m, Why3.Term.ps_app sym []
    with Not_found ->
      let sym = Why3.Term.create_psymbol (Why3.Ident.id_fresh "X") [] in
      if Logger.log_enabled() then
        log "abstract [%a] as psymbol %a" term t Why3.Pretty.print_ls sym;
      {m with t2ls = (t,sym)::m.t2ls}, Why3.Term.ps_app sym []
  in
  fun cfg m t ->
  if Logger.log_enabled() then log "translate_prop %a [%a]" l2y m term t;
  match get_args t with
  | Symb s, [t1;t2] when s == cfg.symb_and ->
      let m, t1 = translate_prop cfg m t1 in
      let m, t2 = translate_prop cfg m t2 in
      m, Why3.Term.t_and t1 t2
  | Symb s, [t1;t2] when s == cfg.symb_or ->
      let m, t1 = translate_prop cfg m t1 in
      let m, t2 = translate_prop cfg m t2 in
      m, Why3.Term.t_or t1 t2
  | Symb s, [t1;t2] when s == cfg.symb_imp ->
      let m, t1 = translate_prop cfg m t1 in
      let m, t2 = translate_prop cfg m t2 in
      m, Why3.Term.t_implies t1 t2
  | Symb s, [t1;t2] when s == cfg.symb_eqv ->
      let m, t1 = translate_prop cfg m t1 in
      let m, t2 = translate_prop cfg m t2 in
      m, Why3.Term.t_iff t1 t2
  | Symb s, [t] when s == cfg.symb_not ->
      let m, t = translate_prop cfg m t in
      m, Why3.Term.t_not t
  | Symb s, [] when s == cfg.symb_bot ->
      m, Why3.Term.t_false
  | Symb s, [] when s == cfg.symb_top ->
      m, Why3.Term.t_true
  | Symb s, [a;Abst(_,t)] when s == cfg.symb_ex ->
      let m,a = translate_set m a
      and x,t = unbind t in
      let id = Why3.Ident.id_fresh (base_name x) in
      let v = Why3.Term.create_vsymbol id a in
      if Logger.log_enabled() then
        log "add vsymbol %a" Why3.Pretty.print_vs v;
      let m = {m with v2vs = (x,v)::m.v2vs} in
      let m,t = translate_prop cfg m t in
      (* remove x from m.v2vs ? *)
      m, Why3.Term.t_exists_close [v] [] t
  | Symb s, [a;Abst(_,t)] when s == cfg.symb_all ->
      let m,a = translate_set m a
      and x,t = unbind t in
      let id = Why3.Ident.id_fresh (base_name x) in
      let v = Why3.Term.create_vsymbol id a in
      if Logger.log_enabled() then
        log "add vsymbol %a" Why3.Pretty.print_vs v;
      let m = {m with v2vs = (x,v)::m.v2vs} in
      let m,t = translate_prop cfg m t in
      (* remove x from m.v2vs ? *)
      m, Why3.Term.t_forall_close [v] [] t
  | Vari x, ts ->
      begin
        match List.assoc_eq_opt eq_vars x m.v2ls with
        | Some(_, false) -> assert false
        | Some(s, true) ->
            begin
              try
                let m, ts = translate_terms cfg m ts in
                m, Why3.Term.ps_app s ts
              with Exit -> default m t
            end
        | None -> default m t
      end
  | Symb s, ts ->
      begin
        match List.assoc_eq_opt (==) s m.s2ls with
        | Some(_, false) -> assert false
        | Some(s, true) ->
            begin
              try
                let m, ts = translate_terms cfg m ts in
                m, Why3.Term.ps_app s ts
              with Exit -> default m t
            end
        | None ->
            begin
              try
                let m, tys = translate_pred_type cfg m !(s.sym_type) in
                let id = Why3.Ident.id_fresh s.sym_name in
                let f = Why3.Term.create_psymbol id tys in
                if Logger.log_enabled() then
                  log "add psymbol %a : %a" Why3.Pretty.print_ls f
                    (Debug.D.list Why3.Pretty.print_ty) tys;
                let m = {m with s2ls = (s,(f,true))::m.s2ls} in
                let m, ts = translate_terms cfg m ts in
                m, Why3.Term.ps_app f ts
              with Exit -> default m t
            end
      end
  | _ -> default m t

(** [translate_goal ss pos env g] translates the hypotheses [env] and the goal
    [g] into a Why3 task. *)
let translate_goal :
      Sig_state.t -> Pos.popt -> Env.env -> term -> Why3.Task.task =
  fun ss pos env g ->
  let cfg = get_config ss pos in
  (* Translate environment. *)
  let translate_env_elt (name,(x,a,_)) (m,hyps) =
    (*if Logger.log_enabled() then log "translate_env_elt %a %a %s : %a"
      l2y m Debug.D.(list (pair string Why3.Pretty.print_term)) hyps
      name term a;*)
    match get_args a with
    | Symb s, [] when s == cfg.symb_Set -> (* type variable *)
        let id = Why3.Ident.id_fresh name in
        let tv = Why3.Ty.create_tvsymbol id in
        if Logger.log_enabled() then
          log "add tvsymbol %a" Why3.Pretty.print_tv tv;
        {m with v2tv = (x,tv)::m.v2tv}, hyps
    | Symb s, [t] when s == cfg.symb_T -> (* object *)
        let m,t = translate_set m t in
        let id = Why3.Ident.id_fresh name in
        let f = Why3.Term.create_fsymbol id [] t in
        if Logger.log_enabled() then
          log "add fsymbol %a" Why3.Pretty.print_ls f;
        {m with v2ls = (x,(f,false))::m.v2ls}, hyps
    | Symb s, [t] when s == cfg.symb_P -> (* assumption *)
        let m,t = translate_prop cfg m t in
        m, (name,t)::hyps
    | _ -> (* predicate symbol *)
        let m, tys = translate_pred_type cfg m a in
        let id = Why3.Ident.id_fresh name in
        let f = Why3.Term.create_psymbol id tys in
        if Logger.log_enabled() then
          log "add psymbol %a" Why3.Pretty.print_ls f;
        {m with v2ls = (x,(f,true))::m.v2ls}, hyps
  in
  let translate_env_elt b m = try translate_env_elt b m with Exit -> m in
  let m, hyps = List.fold_right translate_env_elt env (empty_l2y, []) in
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
  if Logger.log_enabled() then log "%a" Why3.Pretty.print_task tsk;
  (* Add the declarations of term symbols. *)
  let add_s2ls_decl tsk (_,(lsym,_)) = Why3.Task.add_param_decl tsk lsym in
  let tsk = List.fold_left add_s2ls_decl tsk m.s2ls in
  let add_v2ls_decl tsk (_,(lsym,_)) = Why3.Task.add_param_decl tsk lsym in
  let tsk = List.fold_left add_v2ls_decl tsk m.v2ls in
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
  and limits = {Why3.Call_provers.empty_limits
              with limit_time = float_of_int !timeout} in
  let call =
    Why3.Driver.prove_task ~command ~config:why3_main ~limits driver tsk in
  Why3.Call_provers.((wait_on_call call).pr_answer = Valid)

(** [handle ss pos prover_name gt] runs the Why3 prover corresponding to
    [prover_name] (if given or a default one otherwise) on the goal type [gt],
    and fails if no proof is found. *)
let handle :
  Sig_state.t -> Pos.popt -> string option -> goal_typ -> unit =
  fun ss pos prover_name
      ({goal_meta = _; goal_hyps = hyps; goal_type = t} as gt) ->
  let g = Typ gt in
  if Logger.log_enabled() then log "%a" Goal.pp g;
  (* Encode the goal in Why3. *)
  let tsk = translate_goal ss pos hyps t in
  (* Get the name of the prover. *)
  let prover_name = Option.get !default_prover prover_name in
  if Logger.log_enabled() then log "running with prover \"%s\"" prover_name;
  (* Run the task with the prover named [prover_name]. *)
  if not (run tsk pos prover_name) then
    fatal pos "\"%s\" did not find a proof" prover_name
