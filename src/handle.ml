(** Toplevel commands. *)

open Console
open Terms
open Print
open Cmd
open Pos
open Sign
open Extra
open Infer2
open Files

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj : bool ref = ref false

(** [handle_symdecl b n a] extends the current signature with a
    symbol named [n] and type [a]. If [a] does not have sort [Type] or
    [Kind], then the program fails gracefully. [b] indicates whether
    this symbol can have rules. *)
let handle_symdecl : bool -> strloc -> term -> unit =
  fun b n a ->
    ignore (sort_type Ctxt.empty a);
    let sign = current_sign() in
    ignore (Sign.new_symbol sign b n a)

(** [check_def_type x None t] infers the type of [t] and returns
    it. [check_def_type x (Some a) t] checks that [a] has a sort as
    type and that [t] has type [a], and it returns [a]. In case of
    error (typing or sorting), the program fails gracefully. *)
let check_def_type : strloc -> term option -> term -> term =
  fun x ao t ->
    match ao with
    | None ->
       begin
         match infer Ctxt.empty t with
         | None -> fatal "Unable to infer the type of [%a]\n" pp t
         | Some a -> a
       end
    | Some a ->
       begin
         ignore (sort_type Ctxt.empty a);
         if not (has_type Ctxt.empty t a) then
           fatal "Cannot type the definition of %s %a\n" x.elt Pos.print x.pos
         else a
       end

(** [handle_rule r] checks that the rule [r] preserves typing, while
    adding it to the corresponding symbol. The program fails
    gracefully when an error occurs. *)
let handle_rule : rspec -> unit = fun r ->
  Sr2.check_rule r;
  Sign.add_rule (current_sign()) r.rspec_symbol r.rspec_rule

(** [handle_opaque x ao t] checks the definition of [x] and adds
    [x] in the current signature. *)
let handle_opaque : strloc -> term option -> term -> unit =
  fun x ao t ->
    let a = check_def_type x ao t in
    ignore (Sign.new_symbol (current_sign()) true x a)

(** [handle_defin x ao t] does the same as [handle_opaque x ao t] and
    add the rule [x --> t]. *)
let handle_defin : strloc -> term option -> term -> unit =
  fun x ao t ->
    let a = check_def_type x ao t in
    let sign = current_sign() in
    let s = Sign.new_symbol sign true x a in
    let rule =
      let rhs =
        let t = Bindlib.box t in
         Bindlib.mvbind te_mkfree [||] (fun _ -> t)
      in
      {arity = 0; lhs = []; rhs = Bindlib.unbox rhs}
    in
    Sign.add_rule (current_sign()) s rule

(** [handle_infer t] attempts to infer the type of [t]. In case
    of error, the program fails gracefully. *)
let handle_infer : term -> Eval.config -> unit = fun t c ->
  match infer Ctxt.empty t with
  | Some(a) -> out 3 "(infr) %a : %a\n" pp t pp (Eval.eval c a)
  | None    -> fatal "%a : unable to infer\n%!" pp t

(** [handle_eval t] evaluates the term [t]. *)
let handle_eval : term -> Eval.config -> unit = fun t c ->
  match infer Ctxt.empty t with
  | Some(_) -> out 3 "(eval) %a\n" pp (Eval.eval c t)
  | None    -> fatal "unable to infer the type of [%a]\n" pp t

(** [handle_test test] runs the test [test]. When the test does not
    succeed, the program may fail gracefully or continue its exection
    depending on the value of [test.is_assert]. *)
let handle_test : test -> unit = fun test ->
  let pp_test : out_channel -> test -> unit = fun oc test ->
    if test.must_fail then output_string oc "¬(";
    begin
      match test.test_type with
      | Convert(t,u) -> Printf.fprintf oc "%a == %a" pp t pp u
      | HasType(t,a) -> Printf.fprintf oc "%a :: %a" pp t pp a
    end;
    if test.must_fail then output_string oc ")"
  in
  let result =
    match test.test_type with
    | Convert(t,u) -> Eval.eq_modulo t u
    | HasType(t,a) -> ignore (sort_type Ctxt.empty a);
                      try has_type Ctxt.empty t a with _ -> false
  in
  let success = result = not test.must_fail in
  match (success, test.is_assert) with
  | (true , true ) -> ()
  | (true , false) -> out 3 "(check) OK\n"
  | (false, true ) -> fatal "Assertion failed: [%a]\n" pp_test test
  | (false, false) -> wrn "A check failed: [%a]\n" pp_test test

(** [handle_start_proof s a] starts a proof of [a] named [s]. *)
let handle_start_proof (s:strloc) (a:term) : unit =
  (* We check that we are not already in a proof. *)
  if !current_state.s_theorem <> None then fatal "already in proof";
  (* We check that [s] is not already used. *)
  let sign = current_sign() in
  if Sign.mem sign s.elt then fatal "[%s] already exists\n" s.elt;
  (* We check that [a] is typable by a sort. *)
  ignore (sort_type Ctxt.empty a);
  (* We start the proof mode. *)
  let m = add_meta s.elt a 0 in
  let goal =
    { g_meta = m
    ; g_hyps = []
    ; g_type = a }
  in
  let thm =
    { t_proof = m
    ; t_open_goals = [goal]
    ; t_focus = goal }
  in
  current_state := { !current_state with s_theorem = Some thm }

(** [handle_print_focus()] prints the focused goal. *)
let handle_print_focus() : unit =
  let thm = current_theorem() in pp_goal stdout thm.t_focus

(** [handle_refine t] instantiates the focus goal by [t]. *)
let handle_refine (t:term) : unit =
  let thm = current_theorem() in
  let g = thm.t_focus in
  let m = g.g_meta in
  (* We check that [m] does not occur in [t]. *)
  if occurs m t then fatal "invalid refinement\n";
  (* Check that [t] has the correct type. *)
  let bt = lift t in
  let abst u (_,(x,a)) =
    Bindlib.box_apply2 (fun a f -> Abst(a,f))
      a
      (Bindlib.bind_var x u) in
  let u = Bindlib.unbox (List.fold_left abst bt g.g_hyps) in
  if not (Infer2.has_type Ctxt.empty u m.meta_type) then
    fatal "invalid refinement\n";
  (* Instantiation. *)
  let vs = Array.of_list (List.map (fun (_,(x,_)) -> x) g.g_hyps) in
  m.meta_value := Some (Bindlib.unbox (Bindlib.bind_mvar vs bt))

(** [handle_intro s] applies the [intro] tactic. *)
let handle_intro (s:strloc) : unit =
  let thm = current_theorem() in
  let g = thm.t_focus in
  (* We check that [s] is not already used. *)
  if List.mem_assoc s.elt g.g_hyps then fatal "[%s] already used\n" s.elt;
  fatal "not yet implemented\n"

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
  let cmd = Scope.scope_cmd cmd in
  let handle_symdef o = if o then handle_opaque else handle_defin in
  try
    match cmd.elt with
    | SymDecl(b,n,a)  -> handle_symdecl b n a
    | Rules(rs)       -> List.iter handle_rule rs
    | SymDef(o,n,a,t) -> handle_symdef o n a t
    | Require(path)   -> handle_require path
    | Debug(v,s)      -> set_debug v s
    | Verb(n)         -> verbose := n
    | Infer(t,c)      -> handle_infer t c
    | Eval(t,c)       -> handle_eval t c
    | Test(test)      -> handle_test test
    | StartProof(s,a) -> handle_start_proof s a
    | PrintFocus      -> handle_print_focus()
    | Refine(t)       -> handle_refine t
    (* Legacy commands. *)
    | Other(c)        -> if !debug then wrn "Unknown command %S at %a.\n"
                           c.elt Pos.print c.pos
  with
  | Fatal -> raise Fatal
  | e     -> fatal "Uncaught exception on a command at %a\n%s\n%!"
               Pos.print cmd.pos (Printexc.to_string e)

(** [handle_cmds cmds] interprets the commands of [cmds] in order. The
    program fails gracefully in case of error. *)
and handle_cmds : Parser.p_cmd loc list -> unit = fun cmds ->
  List.iter (fun cmd -> try handle_cmd cmd with Fatal -> exit 1) cmds

(** [compile force path] compiles the file corresponding to [path],
    when it is necessary (the corresponding object file does not
    exist, must be updated, or [force] is [true]).  In that case, the
    produced signature is stored in the corresponding object file. *)
and compile : bool -> Files.module_path -> unit =
  fun force path ->
  let base = String.concat "/" path in
  let src = base ^ Files.src_extension in
  let obj = base ^ Files.obj_extension in
  if not (Sys.file_exists src) then fatal "File not found: %s\n" src;
  if List.mem path !(!current_state.s_loading) then
    begin
      err "Circular dependencies detected for %a...\n" Files.pp_path path;
      err "Dependency stack:\n";
      List.iter (err "  - %a\n" Files.pp_path) !(!current_state.s_loading);
      fatal "Build aborted\n"
    end;
  if PathMap.mem path !(!current_state.s_loaded) then
    out 2 "Already loaded [%s]\n%!" src
  else if force || Files.more_recent src obj then
    begin
      let forced = if force then " (forced)" else "" in
      out 2 "Loading [%s]%s\n%!" src forced;
      !current_state.s_loading := path :: !(!current_state.s_loading);
      let sign = Sign.create path in
      !current_state.s_loaded
        := PathMap.add path sign !(!current_state.s_loaded);
      handle_cmds (Parser.parse_file src);
      if !gen_obj then Sign.write sign obj;
      !current_state.s_loading := List.tl !(!current_state.s_loading);
      out 1 "Checked [%s]\n%!" src;
    end
  else
    begin
      out 2 "Loading [%s]\n%!" src;
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> compile false mp) !(sign.deps);
      !current_state.s_loaded
        := PathMap.add path sign !(!current_state.s_loaded);
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj;
    end

module Pure :
  sig
    type command
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
      try handle_cmd cmd; OK(Time.save ()) with Fatal -> Error ""
  end
