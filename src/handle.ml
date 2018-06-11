(** Toplevel commands. *)

open Console
open Terms
open Print
open Cmd
open Pos
open Sign
open Extra
open Files

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj : bool ref = ref false

(** [handle_symdecl definable x a] extends the current signature with
    [definable] a symbol named [x] and type [a]. If [a] does not have
    sort [Type] or [Kind], then the program fails gracefully. *)
let handle_symdecl : bool -> strloc -> term -> unit =
  fun definable x a ->
    fail_if_in_proof();
    (* We check that [s] is not already used. *)
    let sign = current_sign() in
    if Sign.mem sign x.elt then fatal "%S already exists." x.elt;
    (* We check that [a] is typable by a sort. *)
    ignore (Solve.sort_type Ctxt.empty a);
    (*FIXME: check that [a] contains no uninstantiated metavariables.*)
    ignore (Sign.add_symbol sign definable x a)

(** [handle_rule r] checks that the rule [r] preserves typing, while
    adding it to the corresponding symbol. The program fails
    gracefully when an error occurs. *)
let handle_rule : sym * rule -> unit = fun (s,r) ->
  fail_if_in_proof();
  if s.sym_const || !(s.sym_def) <> None then
    fatal "%a cannot be (re)defined." pp_symbol s;
  Sr.check_rule (s, r);
  Sign.add_rule (current_sign()) s r

(** [handle_symdef opaque x ao t] checks that [t] is of type [a] if
    [ao = Some a]. Then, it does the same as [handle_symdecl (not
    definable) x ao]. Moreover, it adds the rule [x --> t] if [not
    opaque]. In case of error, the program fails gracefully. *)
let handle_symdef : bool -> strloc -> term option -> term -> unit
  = fun opaque x ao t ->
  fail_if_in_proof();
  (* We check that [s] is not already used. *)
  let sign = current_sign() in
  if Sign.mem sign x.elt then fatal "%S already exists." x.elt;
  (* We check that [t] has type [a] if [ao = Some a], and that [t] has
     some type [a] otherwise. *)
  let a =
    match ao with
    | Some(a) ->
       begin
         ignore (Solve.sort_type Ctxt.empty a);
         if Solve.has_type Ctxt.empty t a then a
         else fatal "[%a] does not have type [%a]." pp t pp a
       end
    | None    ->
       match Solve.infer Ctxt.empty t with
       | Some(a) -> a
       | None    -> fatal "Cannot infer the type of [%a]." pp t
  in
  (*FIXME: check that [t] and [a] have no uninstantiated metas.*)
  let s = Sign.add_symbol sign Parser.definable x a in
  if not opaque then s.sym_def := Some(t)

(** [handle_infer t] attempts to infer the type of [t]. In case
    of error, the program fails gracefully. *)
let handle_infer : term -> Eval.config -> unit = fun t c ->
  match Solve.infer (Ctxt.of_env (focus_goal_hyps())) t with
  | Some(a) -> out 3 "(infr) %a : %a\n" pp t pp (Eval.eval c a)
  | None    -> fatal "Cannot infer the type of [%a]." pp t

(** [handle_eval t] evaluates the term [t]. *)
let handle_eval : term -> Eval.config -> unit = fun t c ->
  match Solve.infer (Ctxt.of_env (focus_goal_hyps())) t with
  | Some(_) -> out 3 "(eval) %a\n" pp (Eval.eval c t)
  | None    -> fatal "Cannot infer the type of [%a]." pp t

(** [handle_test test] runs the test [test]. When the test does not
    succeed, the program may fail gracefully or continue its exection
    depending on the value of [test.is_assert]. *)
let handle_test : test -> unit = fun test ->
  let pp_test : test pp = fun oc test ->
    if test.must_fail then Format.pp_print_string oc "¬(";
    begin
      match test.test_type with
      | Convert(t,u) -> Format.fprintf oc "%a == %a" pp t pp u
      | HasType(t,a) -> Format.fprintf oc "%a :: %a" pp t pp a
    end;
    if test.must_fail then Format.pp_print_string oc ")"
  in
  let result =
    match test.test_type with
    | Convert(t,u) -> Eval.eq_modulo t u
    | HasType(t,a) ->
       let ctx = Ctxt.of_env (focus_goal_hyps()) in
       ignore (Solve.sort_type ctx a);
       try Solve.has_type ctx t a with _ -> false
  in
  let success = result = not test.must_fail in
  match (success, test.is_assert) with
  | (true , true ) -> ()
  | (true , false) -> out 3 "(check) OK\n"
  | (false, true ) -> fatal "Assertion [%a] failed." pp_test test
  | (false, false) -> wrn "A check failed: [%a]\n" pp_test test

(** [handle_start_proof s a] starts a proof of [a] named [s]. *)
let handle_start_proof (s:strloc) (a:term) : unit =
  (* We check that we are not already in a proof. *)
  fail_if_in_proof();
  (* We check that [s] is not already used. *)
  let sign = current_sign() in
  if Sign.mem sign s.elt then fatal "[%s] already exists." s.elt;
  (* We check that [a] is typable by a sort. *)
  ignore (Solve.sort_type Ctxt.empty a);
  (* We start the proof mode. *)
  let m = add_user_meta s.elt a 0 in
  let g = { g_meta = m; g_hyps = []; g_type = a } in
  let t = { t_proof = m; t_goals = [g]; t_focus = g } in
  theorem := Some t

(** [handle_print_focus()] prints the focused goal. *)
let handle_print_focus() : unit =
  let thm = current_theorem () in
  out 2 "%a" pp_goal thm.t_focus

(** If [t] is a product term [x1:t1->..->xn:tn->u], [env_of_prod n t]
    returns the environment [xn:tn;..;x1:t1] and the type [u]. *)
let env_of_prod (n:int) (t:term) : env * term =
  let rec aux n t acc =
    if !debug_tac then log "env_of_prod" "%i %a" n pp t;
    match n, t with
    | 0, _ -> acc, t
    | _, Prod(a,b) ->
       let (v,b) = Bindlib.unbind b in
       aux (n-1) b ((Bindlib.name_of v,(v,lift a))::acc)
    | _, _ -> assert false
  in assert(n>=0); aux n t []

let goal_of_meta (m:meta) : goal =
  if !debug_tac then log "goal_of_prod" "%a" pp_meta m;
  let env, typ = env_of_prod m.meta_arity !(m.meta_type) in
  { g_meta = m; g_hyps = env; g_type = typ }

(** [handle_refine t] instantiates the focus goal by [t]. *)
let handle_refine (new_metas:meta list) (t:term) : unit =
  let thm = current_theorem() in
  let g = thm.t_focus in
  let m = g.g_meta in
  (* We check that [m] does not occur in [t]. *)
  if occurs m t then fatal "Invalid refinement.";
  (* Check that [t] has the correct type. *)
  let bt = lift t in
  let abst u (_,(x,a)) = _Abst a x u in
  let u = Bindlib.unbox (List.fold_left abst bt g.g_hyps) in
  if not (Solve.has_type (Ctxt.of_env g.g_hyps) u !(m.meta_type)) then
    fatal "Typing error.";
  (* We update the list of new metavariables because some
     metavariables may haven been instantiated by type checking. *)
  let new_metas = List.filter unset new_metas in
  (* Instantiation. *)
  if !debug_tac then log "refine" "[%a]" pp u;
  let vs = Array.of_list (List.map var_of_name g.g_hyps) in
  m.meta_value := Some (Bindlib.unbox (Bindlib.bind_mvar vs bt));
  (* New subgoals and new focus *)
  let fn goals m = goal_of_meta m :: goals in
  let goals = List.fold_left fn (remove_goal g thm.t_goals) new_metas in
  theorem :=
    match goals with
    | [] -> out 3 "Proof finished!\n"; None
    | g::_ -> Some { thm with t_goals = goals; t_focus = g }

(** [handle_intro s] applies the [intro] tactic. *)
let handle_intro (s:strloc) : unit =
  let thm = current_theorem() in
  let g = thm.t_focus in
  (* We check that [s] is not already used. *)
  if List.mem_assoc s.elt g.g_hyps then fatal "[%s] already used." s.elt;
  fatal "Not yet implemented..."

(** [handle_simpl] normalize the focused goal. *)
let handle_simpl () : unit =
  let thm = current_theorem() in
  let g = thm.t_focus in
  let g' = {g with g_type = Eval.snf g.g_type} in
  theorem :=
    Some {thm with
      t_goals = replace_goal g g' thm.t_goals;
      t_focus = g'}

(** [handle_require path] compiles the signature corresponding to  [path],
    if necessary, so that it becomes available for further commands. *)
let rec handle_require : Files.module_path -> unit = fun path ->
  let sign = current_sign() in
  if not (PathMap.mem path !(sign.deps)) then
    sign.deps := PathMap.add path [] !(sign.deps);
  compile false path

(** [handle_cmd cmd] interprets the parser-level command [cmd]. Note that this
    function may raise the [Fatal] exceptions. *)
and handle_cmd : Parser.p_cmd loc -> unit = fun cmd ->
  let cmd, new_metas = Scope.scope_cmd cmd in
  try
    begin
      match cmd.elt with
      | SymDecl(b,n,a)  -> handle_symdecl b n a
      | Rules(rs)       -> List.iter handle_rule rs
      | SymDef(b,n,a,t) -> handle_symdef b n a t
      | Require(path)   -> handle_require path
      | Debug(v,s)      -> set_debug v s
      | Verb(n)         -> verbose := n
      | Infer(t,c)      -> handle_infer t c
      | Eval(t,c)       -> handle_eval t c
      | Test(test)      -> handle_test test
      | StartProof(s,a) -> handle_start_proof s a
      | PrintFocus      -> handle_print_focus()
      | Refine(t)       -> handle_refine new_metas t
      | Simpl           -> handle_simpl()
      (* Legacy commands. *)
      | Other(c)        -> if !debug then wrn "Unknown command %S at %a.\n"
                             c.elt Pos.print c.pos
    end;
    if !debug_unif then log "unif" "after the command: %a" print_meta_stats ()
  with
  | Fatal(m) -> fatal "[%a] error while handling a command.\n%s\n"
                  Pos.print cmd.pos m
  | e        -> let e = Printexc.to_string e in
                fatal "[%a] uncaught exception [%s].\n" Pos.print cmd.pos e

(** [compile force path] compiles the file corresponding to [path],
    when it is necessary (the corresponding object file does not
    exist, must be updated, or [force] is [true]).  In that case, the
    produced signature is stored in the corresponding object file. *)
and compile : bool -> Files.module_path -> unit =
  fun force path ->
  let base = String.concat "/" path in
  let src = base ^ Files.src_extension in
  let obj = base ^ Files.obj_extension in
  if not (Sys.file_exists src) then fatal "File [%s] not found.\n" src;
  if List.mem path !loading then
    begin
      err "Circular dependencies detected in [%s].\n" src;
      err "Dependency stack for module [%a]:\n" Files.pp_path path;
      List.iter (err "  - [%a]\n" Files.pp_path) !loading;
      fatal "Build aborted.\n"
    end;
  if PathMap.mem path !loaded then
    out 2 "Already loaded [%s]\n%!" src
  else if force || Files.more_recent src obj then
    begin
      let forced = if force then " (forced)" else "" in
      out 2 "Loading [%s]%s\n%!" src forced;
      loading := path :: !loading;
      let sign = Sign.create path in
      loaded := PathMap.add path sign !loaded;
      List.iter handle_cmd (Parser.parse_file src);
      if !gen_obj then Sign.write sign obj;
      loading := List.tl !loading;
      out 1 "Checked [%s]\n%!" src;
    end
  else
    begin
      out 2 "Loading [%s]\n%!" src;
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> compile false mp) !(sign.deps);
      loaded := PathMap.add path sign !loaded;
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj;
    end

(** Interface to PLOF. *)

module Pure :
  sig
    type command = Parser.p_cmd loc
    type state

    type result =
      | OK    of state
      | Error of string

    val initial_state : state

    val handle_command : state -> command -> result
  end =
  struct
    open Timed

    type command = Parser.p_cmd loc

    type state = Time.t

    type result =
      | OK    of state
      | Error of string

    let initial_state : state = Time.save ()

    let handle_command : state -> command -> result = fun t cmd ->
      Time.rollback t;
      try handle_cmd cmd; OK(Time.save ()) with Fatal(m) -> Error(m)
  end
