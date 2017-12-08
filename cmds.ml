(** Toplevel commands. *)

open Console
open Parser
open Scope
open Files
open Terms
open Print

(** [handle_newsym sign n a] extends the signature [sign] with a static symbol
    named [n], with type [a]. If [a] does not have sort [Type] or [Kind], then
    the program fails gracefully. *)
let handle_newsym : Sign.t -> string -> term -> unit = fun sign n a ->
  ignore (Typing.sort_type sign n a); ignore (Sign.new_static sign n a)

(** [handle_newdef sign n a] extends [sign] with a definable symbol named [n],
    with type [a] (and no reduction rule). If [a] does not have sort [Type] or
    [Kind], then the program fails gracefully. *)
let handle_newdef : Sign.t -> string -> term -> unit = fun sign n a ->
  ignore (Typing.sort_type sign n a); ignore (Sign.new_definable sign n a)

(** [handle_defin sign x a t] extends [sign] with a definable symbol with name
    [n] and type [a], and then adds a simple rewriting rule to  [t]. Note that
    this amounts to defining a symbol with a single reduction rule. In case of
    error (typing, sorting, ...) the program fails gracefully. *)
let handle_defin : Sign.t -> string -> term -> term -> unit = fun sg x a t ->
  ignore (Typing.sort_type sg x a);
  if not (Typing.has_type sg Ctxt.empty t a) then
    fatal "Cannot type the definition of %s...\n" x;
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

(** [handle_rules sign rs] check that the rules of [rs] are well-typed, before
    adding them to the corresponding symbol. The program fails gracefully when
    an error occurs. *)
let handle_rules = fun sign rs ->
  let rs = List.map (Typing.check_rule sign) rs in
  List.iter (fun (s,_,_,rule) -> Sign.add_rule sign s rule) rs

(** [handle_check sign t a] attempts to show that [t] has type [a], in [sign].
    In case of failure, the program fails gracefully. *)
let handle_check : Sign.t -> term -> term -> unit = fun sign t a ->
  if not (Typing.has_type sign Ctxt.empty t a) then
    fatal "%a does not have type %a...\n" pp t pp a;
  out 3 "(chck) OK\n"

(** [handle_infer sign t] attempts to infer the type of [t] in [sign]. In case
    of error, the program fails gracefully. *)
let handle_infer : Sign.t -> term -> unit = fun sign t ->
  match Typing.infer sign Ctxt.empty t with
  | Some(a) -> out 3 "(infr) %a : %a\n" pp t pp a
  | None    -> fatal "%a : unable to infer\n%!" pp t

(** [handle_eval sign t] evaluates the term [t]. *)
let handle_eval : Sign.t -> term -> unit = fun sign t ->
  (* FIXME check typing? *)
  out 3 "(eval) %a\n" pp (Eval.whnf t)

(** [handle_conv sign t u] checks the convertibility of the terms [t] and [u].
    The program fails gracefully if the check is not successful. *)
let handle_conv : Sign.t -> term -> term -> unit = fun sign t u ->
  if Eval.eq_modulo t u then out 3 "(conv) OK\n"
  else fatal "cannot convert %a and %a...\n" pp t pp u

(** [handle_import sign path] compiles the signature corresponding to  [path],
    if necessary, so that it becomes available for further commands. *)
let rec handle_import : Sign.t -> module_path -> unit = fun sign path ->
  let open Sign in
  if path = sign.path then fatal "Cannot require the current module...\n%!";
  if not (Hashtbl.mem sign.deps path) then Hashtbl.add sign.deps path [];
  compile false path

(** [handle_cmds sign cmds] interprets the commands of [cmds] in order, in the
    signature [sign]. The program fails gracefully in case of error. *)
and handle_cmds : Sign.t -> p_cmd list -> unit = fun sign cmds ->
  let handle_cmd cmd =
    match scope_cmd sign cmd with
    | NewSym(n,a)  -> handle_newsym sign n a
    | NewDef(n,a)  -> handle_newdef sign n a
    | Rules(rs)    -> handle_rules sign rs
    | Defin(n,a,t) -> handle_defin sign n a t
    | Import(path) -> handle_import sign path
    | Debug(v,s)   -> set_debug v s
    | Verb(n)      -> verbose := n
    | Check(t,a)   -> handle_check sign t a
    | Infer(t)     -> handle_infer sign t
    | Eval(t)      -> handle_eval sign t
    | Conv(a,b)    -> handle_conv sign a b
    | Other(c)     -> if !debug then wrn "Command %S not implemented.\n" c
  in
  try List.iter handle_cmd cmds with e ->
    fatal "Uncaught exception...\n%s\n%!" (Printexc.to_string e)

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
and compile : bool -> string list -> unit = fun force path ->
  let base = String.concat "/" path in
  let src = base ^ src_extension in
  let obj = base ^ obj_extension in
  if not (Sys.file_exists src) then fatal "File not found: %s\n" src;
  if Hashtbl.mem Sign.loaded path then out 2 "Already loaded [%s]\n%!" src
  else
    begin
      if force || more_recent src obj then
        begin
          let forced = if force then " (forced)" else "" in
          out 1 "Compiling [%s]%s\n%!" src forced;
          Stack.push path Sign.loading;
          let sign = Sign.create path in
          Hashtbl.add Sign.loaded path sign;
          handle_cmds sign (parse_file src);
          Sign.write sign obj;
          ignore (Stack.pop Sign.loading);
          out 2 "Compiled  [%s]\n%!" src;
        end
      else
        begin
          out 1 "Loading [%s]\n%!" src;
          let sign = Sign.read obj in
          Hashtbl.iter (fun mp _ -> compile false mp) Sign.(sign.deps);
          Hashtbl.add Sign.loaded path sign;
          Sign.link sign;
          out 2 "Loaded  [%s]\n%!" obj;
        end;
    end
