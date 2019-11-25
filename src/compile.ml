(** High-level compilation functions. *)

open Extra
open Timed
open Sign
open Console
open Files

(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not te generate them. *)
let gen_obj = Pervasives.ref false

(** [parse_file fname] selects and runs the correct parser on file [fname], by
    looking at its extension. *)
let parse_file : string -> Syntax.ast = fun fname ->
  match Filename.check_suffix fname src_extension with
  | true  -> Parser.parse_file fname
  | false -> Legacy_parser.parse_file fname

(** [compile force path] compiles the file corresponding to [path], when it is
    necessary (the corresponding object file does not exist,  must be updated,
    or [force] is [true]).  In that case,  the produced signature is stored in
    the corresponding object file. *)
let rec compile : bool -> Path.t -> unit = fun force path ->
  let base = String.concat Filename.dir_sep path in
  let src =
    let src = base ^ src_extension in
    let legacy = base ^ legacy_src_extension in
    match (Sys.file_exists src, Sys.file_exists legacy) with
    | (false, false) -> fatal_no_pos "File [%s.{lp|dk}] not found." base
    | (true , true ) -> fatal_no_pos "Both [%s] and [%s] exist." src legacy
    | (true , false) -> src
    | (false, true ) -> legacy
  in
  let obj = base ^ obj_extension in
  if List.mem path !loading then
    begin
      fatal_msg "Circular dependencies detected in [%s].\n" src;
      fatal_msg "Dependency stack for module [%a]:\n" Path.pp path;
      List.iter (fatal_msg "  - [%a]\n" Path.pp) !loading;
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
      let sig_st = Scope.empty_sig_state sign in
      (* [sign] is added to [loaded] before processing the commands so that it
         is possible to qualify the symbols of the current modules. *)
      loaded := PathMap.add path sign !loaded;
      let handle ss c =
        let (ss, p) = Handle.handle_cmd ss c in
        match p with
        | None       -> ss
        | Some(data) ->
            let (st,ts) = (data.pdata_p_state, data.pdata_tactics) in
            let st = List.fold_left (Tactics.handle_tactic ss) st ts in
            data.pdata_finalize ss st
      in
      ignore (List.fold_left handle sig_st (parse_file src));
      (* Removing private symbols from signature. *)
      let not_prv _ sym = not (Terms.is_private sym) in
      let not_prv_fst k s_ = not_prv k (fst s_) in
      sign.sign_symbols := StrMap.filter not_prv_fst !(sign.sign_symbols);
      sign.sign_builtins := StrMap.filter not_prv !(sign.sign_builtins);
      sign.sign_unops := StrMap.filter not_prv_fst !(sign.sign_unops);
      sign.sign_binops := StrMap.filter not_prv_fst !(sign.sign_binops);
      if Pervasives.(!gen_obj) then Sign.write sign obj;
      loading := List.tl !loading;
      out 1 "Checked [%s]\n%!" src;
    end
  else
    begin
      out 2 "Loading [%s]\n%!" src;
      let sign = Sign.read obj in
      PathMap.iter (fun mp _ -> compile false mp) !(sign.sign_deps);
      loaded := PathMap.add path sign !loaded;
      Sign.link sign;
      out 2 "Loaded  [%s]\n%!" obj;
    end

(* NOTE we need to give access to the compilation function to the parser. This
   is the only way infix symbols can be parsed, since they may be added to the
   scope by a “require” command. *)
let _ =
  let require mp =
    (* Save the current console state. *)
    Console.push_state ();
    (* Restore the console state to default for compiling. *)
    Console.reset_default ();
    (* Compile and go back to previous state. *)
    try
      compile false mp;
      try Console.pop_state () with _ -> assert false (* Unreachable. *)
    with e -> Console.pop_state (); raise e
  in
  Pervasives.(Parser.require := require)
