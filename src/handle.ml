(** Toplevel commands. *)

open Console
open Terms
open Print
open Cmd
open Pos
open Sign

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj : bool ref = ref false

(** [handle_symdecl sign b n a] extends the signature [sign] with a
    symbol named [n] and type [a]. If [a] does not have sort [Type] or
    [Kind], then the program fails gracefully. [b] indicates whether
    this symbol can have rules. *)
let handle_symdecl : Sign.t -> bool -> strloc -> term -> unit =
  fun sign b n a ->
  ignore (Infer2.sort_type empty_ctxt a);
  ignore (Sign.new_symbol sign b n a)

(** [check_def_type x None t] infers the type of [t] and returns
    it. [check_def_type x (Some a) t] checks that [a] has a sort as
    type and that [t] has type [a], and it returns [a]. In case of
    error (typing or sorting), the program fails gracefully. *)
let check_def_type : Sign.t -> strloc -> term option -> term -> term =
  fun sign x ao t ->
    match ao with
    | None ->
       begin
         match Infer2.infer empty_ctxt t with
         | None -> fatal "Unable to infer the type of [%a]\n" pp t
         | Some a -> a
       end
    | Some a ->
       begin
         ignore (Infer2.sort_type empty_ctxt a);
         if not (Infer2.has_type empty_ctxt t a) then
           fatal "Cannot type the definition of %s %a\n" x.elt Pos.print x.pos
         else a
       end

(** [handle_opaque sign x ao t] checks the definition of [x] and adds
    [x] in the signature. *)
let handle_opaque : Sign.t -> strloc -> term option -> term -> unit =
  fun sign x ao t ->
    let a = check_def_type sign x ao t in
    ignore (Sign.new_symbol sign true x a)

(** [handle_defin sign x ao t] does the same as [handle_opaque sign x ao
    t] and add the rule [x --> t]. *)
let handle_defin : Sign.t -> strloc -> term option -> term -> unit =
  fun sign x ao t ->
    let a = check_def_type sign x ao t in
    let s = Sign.new_symbol sign true x a in
    let rule =
      let rhs =
        let t = Bindlib.box t in
         Bindlib.mvbind te_mkfree [||] (fun _ -> t)
      in
      {arity = 0; lhs = []; rhs = Bindlib.unbox rhs}
    in
    Sign.add_rule sign s rule

(** [handle_rules sign rs] checks that the rules of [rs] are well-typed, while
    adding them to the corresponding symbol. The program fails gracefully when
    an error occurs. *)
let handle_rules : Sign.t -> Sr.rspec list -> unit = fun sign rs ->
  let open Sr in
  List.iter check_rule rs;
  List.iter (fun s -> Sign.add_rule sign s.rspec_symbol s.rspec_rule) rs

(** [handle_infer sign t] attempts to infer the type of [t] in [sign]. In case
    of error, the program fails gracefully. *)
let handle_infer : Sign.t -> term -> Eval.config -> unit = fun sign t c ->
  match Infer2.infer empty_ctxt t with
  | Some(a) -> out 3 "(infr) %a : %a\n" pp t pp (Eval.eval c a)
  | None    -> fatal "%a : unable to infer\n%!" pp t

(** [handle_eval sign t] evaluates the term [t]. *)
let handle_eval : Sign.t -> term -> Eval.config -> unit = fun sign t c ->
  (* FIXME check typing? *)
  out 3 "(eval) %a\n" pp (Eval.eval c t)

(** [handle_test sign test] runs the test [test] in the state [sign]. When
    the test does not succeed, the program may fail gracefully or continue its
    exection depending on the value of [test.is_assert]. *)
let handle_test : Sign.t -> test -> unit = fun sign test ->
  match (test.contents, test.is_assert, test.must_fail) with
  | (Convert(t,u), false, false) ->
      if Eval.eq_modulo t u then out 3 "(conv) OK\n"
      else fatal "cannot convert %a and %a...\n" pp t pp u
  | (HasType(t,a), false, false) ->
      ignore (Infer2.sort_type empty_ctxt a);
      if not (Infer2.has_type empty_ctxt t a) then
        fatal "%a does not have type %a...\n" pp t pp a;
      out 3 "(chck) OK\n"
  | (_           , _    , _    ) ->
      (* TODO *)
      wrn "Test not implemented...\n"

(** [handle_import sign path] compiles the signature corresponding to  [path],
    if necessary, so that it becomes available for further commands. *)
let rec handle_import : Sign.t -> Files.module_path -> unit = fun sign path ->
  let open Sign in
  if path = sign.path then fatal "Cannot require the current module...\n%!";
  if not (Hashtbl.mem sign.deps path) then Hashtbl.add sign.deps path [];
  compile sign false path

(** [handle_cmds sign cmds] interprets the commands of [cmds] in order, in the
    state [sign]. The program fails gracefully in case of error. *)
and handle_cmds : Sign.t -> Parser.p_cmd loc list -> unit = fun sign cmds ->
  let handle_cmd cmd =
    try
      let cmd = Scope.scope_cmd sign cmd in
      match cmd.elt with
      | SymDecl(b,n,a) -> handle_symdecl sign b n a
      | Rules(rs)    -> handle_rules sign rs
      | SymDef(b,n,ao,t) ->
         (if b then handle_opaque else handle_defin) sign n ao t
      | Import(path) -> handle_import sign path
      | Debug(v,s)   -> set_debug v s
      | Verb(n)      -> verbose := n
      | Infer(t,c)   -> handle_infer sign t c
      | Eval(t,c)    -> handle_eval sign t c
      | Test(test)   -> handle_test sign test
      | Other(c)     ->
          if !debug then
            wrn "Unknown command %S at %a.\n" c.elt Pos.print c.pos
    with e ->
      fatal "Uncaught exception on a command at %a\n%s\n%!"
        Pos.print cmd.pos (Printexc.to_string e)
  in
  List.iter handle_cmd cmds

(** [compile sign force path] compiles the file corresponding to [path],
    when it is necessary (the corresponding object file does not
    exist, must be updated, or [force] is [true]).  In that case, the
    produced signature is stored in the corresponding object file. *)
and compile : Sign.t -> bool -> Files.module_path -> unit =
  fun sign force path ->
  let base = String.concat "/" path in
  let src = base ^ Files.src_extension in
  let obj = base ^ Files.obj_extension in
  if not (Sys.file_exists src) then fatal "File not found: %s\n" src;
  if Hashtbl.mem !current_state.s_loaded path then
    out 2 "Already loaded [%s]\n%!" src
  else
    begin
      if force || Files.more_recent src obj then
        begin
          let forced = if force then " (forced)" else "" in
          out 2 "Loading [%s]%s\n%!" src forced;
          Stack.push path !current_state.s_loading;
          let sign = Sign.create path in
          Hashtbl.add !current_state.s_loaded path sign;
          handle_cmds sign (Parser.parse_file src);
          if !gen_obj then Sign.write sign obj;
          ignore (Stack.pop !current_state.s_loading);
          out 1 "Checked [%s]\n%!" src;
        end
      else
        begin
          out 2 "Loading [%s]\n%!" src;
          let sign = Sign.read obj in
          Hashtbl.iter (fun mp _ -> compile sign false mp) sign.deps;
          Hashtbl.add !current_state.s_loaded path sign;
          Sign.link sign;
          out 2 "Loaded  [%s]\n%!" obj;
        end;
    end
