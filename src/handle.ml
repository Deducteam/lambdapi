(** Toplevel commands. *)

open Extra
open Timed
open Console
open Terms
open Parser
open Print
open Pos
open Sign
open Files

(** Logging function for tactics. *)
let log_tact = new_logger 'i' "tact" "debugging information for tactics"
let log_tact = log_tact.logger

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Pervasives.ref false

(** [too_long] indicates the duration after which a warning should be given to
    indicate commands that take too long to execute. *)
let too_long = Pervasives.ref infinity

(** [use_legacy_parser] indicates whether the legacy (Menhir) parser should be
    used. It is faster, but only supports the legacy syntax. *)
let use_legacy_parser = Pervasives.ref false

(** [parse_file fname] parses file [fname] using the right parser. *)
let parse_file : string -> p_cmd Pos.loc list = fun fname ->
  if Pervasives.(!use_legacy_parser) then Legacy_parser.parse_file fname
  else parse_file fname

(** [handle_symdecl mode x a] extends the current signature with a new  symbol
    named [x] and with type [a].  If [a] does not have sort [Type] or [Kind],
    then the program fails gracefully. *)
let handle_symdecl : sym_mode -> strloc -> term -> unit = fun mode x a ->
  (* We check that [s] is not already used. *)
  let sign = current_sign () in
  if Sign.mem sign x.elt then
    fatal x.pos "Symbol [%s] already exists." x.elt;
  (* We check that [a] is typable by a sort. *)
  Solve.sort_type Ctxt.empty a;
  (*FIXME: check that [a] contains no uninstantiated metavariables.*)
  ignore (Sign.add_symbol sign mode x a)

(** [handle_rule r] checks that the rule [r] preserves typing, while
    adding it to the corresponding symbol. The program fails
    gracefully when an error occurs. *)
let handle_rule : sym * pp_hint * rule Pos.loc -> unit = fun (s,h,r) ->
  if s.sym_mode = Const || !(s.sym_def) <> None then
    fatal_no_pos "Symbol [%s] cannot be (re)defined." s.sym_name;
  Sr.check_rule (s,h,r);
  Sign.add_rule (current_sign ()) s h r.elt

(** [handle_symdef opaque x ao t] checks that [t] is of type [a] if
    [ao = Some a]. Then, it does the same as [handle_symdecl (not
    definable) x ao]. Moreover, it adds the rule [x --> t] if [not
    opaque]. In case of error, the program fails gracefully. *)
let handle_symdef : bool -> strloc -> term option -> term -> unit
  = fun opaque x ao t ->
  (* We check that [s] is not already used. *)
  let sign = current_sign() in
  if Sign.mem sign x.elt then
    fatal x.pos "Symbol [%s] already exists." x.elt;
  (* We check that [t] has type [a] if [ao = Some a], and that [t] has
     some type [a] otherwise. *)
  let a =
    match ao with
    | Some(a) ->
       begin
         Solve.sort_type Ctxt.empty a;
         if Solve.check Ctxt.empty t a then a
         else fatal_no_pos "[%a] does not have type [%a]." pp t pp a
       end
    | None    ->
       match Solve.infer Ctxt.empty t with
       | Some(a) -> a
       | None    -> fatal_no_pos "Cannot infer the type of [%a]." pp t
  in
  (*FIXME: check that [t] and [a] have no uninstantiated metas.*)
  let s = Sign.add_symbol sign Defin x a in
  if not opaque then s.sym_def := Some(t)

(** [handle_infer t] attempts to infer the type of [t]. In case
    of error, the program fails gracefully. *)
let handle_infer : term -> Eval.config -> unit = fun t c ->
  match Solve.infer [] t with
  | Some(a) -> out 3 "(infr) %a : %a\n" pp t pp (Eval.eval c a)
  | None    -> fatal_no_pos "Cannot infer the type of [%a]." pp t

(** [handle_eval t] evaluates the term [t]. *)
let handle_eval : term -> Eval.config -> unit = fun t c ->
  match Solve.infer (Ctxt.of_env []) t with
  | Some(_) -> out 3 "(eval) %a\n" pp (Eval.eval c t)
  | None    -> fatal_no_pos "Cannot infer the type of [%a]." pp t

(** Type of the tests that can be made in a file. *)
type test_type =
  | Convert of term * term (** Convertibility test. *)
  | HasType of term * term (** Type-checking. *)

type test =
  { is_assert : bool (** Should the program fail if the test fails? *)
  ; must_fail : bool (** Is this test supposed to fail? *)
  ; test_type : test_type  (** The test itself. *) }

(** [handle_test pos test] runs the test [test]. When the test does not
    succeed, the program may fail gracefully or continue its exection
    depending on the value of [test.is_assert]. *)
let handle_test : Pos.popt -> test -> unit = fun pos test ->
  let result =
    match test.test_type with
    | Convert(t,u) -> Eval.eq_modulo t u
    | HasType(t,a) ->
        Solve.sort_type Ctxt.empty a;
        try Solve.check Ctxt.empty t a with _ -> false
  in
  let success = result = not test.must_fail in
  match (success, test.is_assert) with
  | (true , true ) -> ()
  | (true , false) -> out 3 "(check) OK\n"
  | (false, true ) -> fatal pos "Assertion failed."
  | (false, false) -> wrn pos "Check failed."

(** If [t] is a product term [x1:t1->..->xn:tn->u], [env_of_prod n t]
    returns the environment [xn:tn;..;x1:t1] and the type [u]. *)
let env_of_prod (n:int) (t:term) : Env.t * term =
  let rec aux n t acc =
    log_tact "env_of_prod %i [%a]" n pp t;
    match n, t with
    | 0, _ -> acc, t
    | _, Prod(a,b) ->
       let (v,b) = Bindlib.unbind b in
       aux (n-1) b ((Bindlib.name_of v,(v,lift a))::acc)
    | _, _ -> assert false
  in assert(n>=0); aux n t []

(** [handle_require path] compiles the signature corresponding to  [path],
    if necessary, so that it becomes available for further commands. *)
let rec handle_require : Files.module_path -> unit = fun path ->
  let sign = current_sign() in
  if not (PathMap.mem path !(sign.deps)) then
    sign.deps := PathMap.add path [] !(sign.deps);
  compile false path

(** [handle_cmd cmd] interprets the parser-level command [cmd]. Note that this
    function may raise the [Fatal] exceptions. *)
and handle_cmd : p_cmd loc -> unit = fun cmd ->
  let scope_basic = Scope.scope_term StrMap.empty [] in
  let handle () =
    match cmd.elt with
    | P_Require(path)       -> handle_require path
    | P_SymDecl(m,x,a)      -> handle_symdecl m x (scope_basic a)
    | P_SymDef(b,x,ao,t)    ->
        let t = scope_basic t in
        let ao = Option.map scope_basic ao in
        handle_symdef b x ao t
    | P_Rules(rs)           ->
        let rs = List.map Scope.scope_rule rs in
        List.iter handle_rule rs
    | P_OldRules(rs)        ->
        let rs = List.map Scope.translate_old_rule rs in
        handle_cmd {cmd with elt = P_Rules rs}
    | P_Infer(t,cfg)        -> handle_infer (scope_basic t) cfg
    | P_Eval(t,cfg)         -> handle_eval  (scope_basic t) cfg
    | P_TestType(ia,mf,t,a) ->
        let test_type = HasType(scope_basic t, scope_basic a) in
        handle_test cmd.pos {is_assert = ia; must_fail = mf; test_type}
    | P_TestConv(ia,mf,t,u) ->
        let test_type = Convert(scope_basic t, scope_basic u) in
        handle_test cmd.pos {is_assert = ia; must_fail = mf; test_type}
    | P_Other               ->
        if !log_enabled then wrn cmd.pos "Ignored command."
  in
  try
    let (tm, ()) = time handle () in
    if Pervasives.(tm >= !too_long) then
      wrn cmd.pos "It took %.2f seconds to handle the command." tm
  with
  | Timeout                as e -> raise e
  | Fatal(Some(Some(_)),_) as e -> raise e
  | Fatal(None         ,_) as e -> raise e
  | Fatal(Some(None)   ,m)      -> fatal cmd.pos "Error on command.\n%s" m
  | e                           -> let e = Printexc.to_string e in
                                   fatal cmd.pos "Uncaught exception [%s]." e

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
and compile : bool -> Files.module_path -> unit =
  fun force path ->
  let base = String.concat "/" path in
  let src = base ^ Files.src_extension in
  let obj = base ^ Files.obj_extension in
  if not (Sys.file_exists src) then fatal_no_pos "File [%s] not found." src;
  if List.mem path !loading then
    begin
      fatal_msg "Circular dependencies detected in [%s].\n" src;
      fatal_msg "Dependency stack for module [%a]:\n" Files.pp_path path;
      List.iter (fatal_msg "  - [%a]\n" Files.pp_path) !loading;
      fatal_no_pos "Build aborted."
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
      List.iter handle_cmd (parse_file src);
      if Pervasives.(!gen_obj) then Sign.write sign obj;
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
