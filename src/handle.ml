(** Toplevel commands. *)

open Console
open Extra
open Parser
open Scope
open Files
open Terms
open Print
open Cmd
open Pos

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj : bool ref = ref false

(** [handle_newsym sign n a] extends the signature [sign] with a static symbol
    named [n], with type [a]. If [a] does not have sort [Type] or [Kind], then
    the program fails gracefully. *)
let handle_newsym : Sign.t -> strloc -> term -> unit = fun sign n a ->
  ignore (Typing.sort_type sign a); ignore (Sign.new_static sign n a)

(** [handle_newdef sign n a] extends [sign] with a definable symbol named [n],
    with type [a] (and no reduction rule). If [a] does not have sort [Type] or
    [Kind], then the program fails gracefully. *)
let handle_newdef : Sign.t -> strloc -> term -> unit = fun sign n a ->
  ignore (Typing.sort_type sign a); ignore (Sign.new_definable sign n a)

(** [handle_opaque sign x a t] checks that the opaque definition of symbol [x]
    is well-typed, which means that [t] has type [a]. In case of error (typing
    or sorting), the program fails gracefully. *)
let handle_opaque : Sign.t -> strloc -> term -> term -> unit = fun sg x a t ->
  ignore (Typing.sort_type sg a);
  if not (Typing.has_type sg empty_ctxt t a) then
    fatal "Cannot type the definition of %s %a\n" x.elt Pos.print x.pos;
  ignore (Sign.new_definable sg x a)

(** [handle_defin sign x a t] extends [sign] with a definable symbol with name
    [x] and type [a], and then adds a simple rewriting rule to  [t]. Note that
    this amounts to define a symbol with a single reduction rule.  In case  of
    error (typing, sorting, ...) the program fails gracefully. *)
let handle_defin : Sign.t -> strloc -> term -> term -> unit = fun sg x a t ->
  ignore (Typing.sort_type sg a);
  if not (Typing.has_type sg empty_ctxt t a) then
    fatal "Cannot type the definition of %s %a\n" x.elt Pos.print x.pos;
  let s = Sign.new_definable sg x a in
  let rule =
    let lhs = Bindlib.mvbind mkfree [||] (fun _ -> Bindlib.box []) in
    let rhs =
      let t = Bindlib.box t in
      Bindlib.mvbind mkfree [||] (fun _ -> t)
    in
    {arity = 0; lhs = Bindlib.unbox lhs ; rhs = Bindlib.unbox rhs}
  in
  Sign.add_rule sg s rule

(** [handle_rules sign rs] checks that the rules of [rs] are well-typed, while
    adding them to the corresponding symbol. The program fails gracefully when
    an error occurs. *)
let handle_rules = fun sign rs ->
  let rs = List.map (Sr.check_rule sign) rs in
  List.iter (fun (s,_,_,rule) -> Sign.add_rule sign s rule) rs

(** [handle_infer sign t] attempts to infer the type of [t] in [sign]. In case
    of error, the program fails gracefully. *)
let handle_infer : Sign.t -> term -> Eval.config -> unit = fun sign t c ->
  match Typing.infer sign empty_ctxt t with
  | Some(a) -> out 3 "(infr) %a : %a\n" pp t pp (Eval.eval c a)
  | None    -> fatal "%a : unable to infer\n%!" pp t

(** [handle_eval sign t] evaluates the term [t]. *)
let handle_eval : Sign.t -> term -> Eval.config -> unit = fun sign t c ->
  match Typing.infer sign empty_ctxt t with
  | Some(_) -> out 3 "(eval) %a\n" pp (Eval.eval c t)
  | None    -> fatal "unable to infer the type of [%a]\n" pp t

(** [handle_test sign test] runs the test [test] in the signature [sign]. When
    the test does not succeed, the program may fail gracefully or continue its
    exection depending on the value of [test.is_assert]. *)
let handle_test : Sign.t -> test -> unit = fun sign test ->
  let pp_test : out_channel -> test -> unit = fun oc test ->
    if test.must_fail then output_string oc "¬(";
    begin
      match test.contents with
      | Convert(t,u) -> Printf.fprintf oc "%a == %a" pp t pp u
      | HasType(t,a) -> Printf.fprintf oc "%a :: %a" pp t pp a
    end;
    if test.must_fail then output_string oc ")"
  in
  let result =
    match test.contents with
    | Convert(t,u) -> Eval.eq_modulo t u
    | HasType(t,a) -> ignore (Typing.sort_type sign a);
                      try Typing.has_type sign empty_ctxt t a with _ -> false
  in
  let success = result = not test.must_fail in
  match (success, test.is_assert) with
  | (true , true ) -> ()
  | (true , false) -> out 3 "(chck) OK\n"
  | (false, true ) -> fatal "Assertion failed: [%a]\n" pp_test test
  | (false, false) -> wrn "A check failed: [%a]\n" pp_test test

(** [handle_import sign path] compiles the signature corresponding to  [path],
    if necessary, so that it becomes available for further commands. *)
let rec handle_import : Sign.t -> module_path -> unit = fun sign path ->
  let open Sign in
  if path = sign.path then
    fatal "Self-referential import in \"%a\"...\n" Files.pp_path path;
  if not (Assoc.mem sign.deps path) then Assoc.add sign.deps path [];
  compile false path

(** [handle_cmds sign cmds] interprets the commands of [cmds] in order, in the
    signature [sign]. The program fails gracefully in case of error. *)
and handle_cmds : Sign.t -> p_cmd loc list -> unit = fun sign cmds ->
  let handle_cmd cmd =
    try
      let cmd = scope_cmd sign cmd in
      match cmd.elt with
      | NewSym(n,a)  -> handle_newsym sign n a
      | NewDef(n,a)  -> handle_newdef sign n a
      | Rules(rs)    -> handle_rules sign rs
      | Def(o,n,a,t) -> (if o then handle_opaque else handle_defin) sign n a t
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

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
and compile : bool -> string list -> unit = fun force path ->
  let base = String.concat "/" path in
  let src = base ^ src_extension in
  let obj = base ^ obj_extension in
  if not (Sys.file_exists src) then fatal "File not found: %s\n" src;
  if List.mem path !Sign.loading then
    begin
      err "Circular dependencies detected in file %S.\n" src;
      err "Dependency stack for module \"%a\":\n" Files.pp_path path;
      List.iter (err "  - \"%a\"\n" Files.pp_path) !Sign.loading;
      fatal "Build aborted...\n"
    end;
  if Sign.is_loaded path then out 2 "Already loaded [%s]\n%!" src
  else if force || more_recent src obj then
    begin
      let forced = if force then " (forced)" else "" in
      out 2 "Loading [%s]%s\n%!" src forced;
      Sign.loading := path :: !Sign.loading;
      let sign = Sign.create path in
      handle_cmds sign (parse_file src);
      if !gen_obj then Sign.write sign obj;
      Sign.loading := List.tl !Sign.loading;
      out 1 "Checked [%s]\n%!" src;
    end
  else
    begin
      out 2 "Loading [%s]\n%!" src;
      let sign = Sign.read obj in
      Assoc.iter (fun mp _ -> compile false mp) Sign.(sign.deps);
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj;
    end
