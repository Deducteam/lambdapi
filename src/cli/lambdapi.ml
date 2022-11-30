(** Main program. *)

open Lplib open Extra
open Common open Library open Error
open Parsing
open Core
open Cmdliner
open Version
open Handle
open Base

type qident = Core.Term.qident

module CLT = Cmdliner.Term

(* NOTE only standard [Stdlib] references here. *)

(** {3 Evaluation of commands. *)

(** Running the main type-checking mode. *)
let check_cmd : Config.t -> int option -> string list -> unit =
    fun cfg timeout files ->
  let run _ =
    let open Timed in
    Config.init cfg;
    (* We save time to run each file in the same environment. *)
    let time = Time.save () in
    let handle file =
      Console.reset_default ();
      Time.restore time;
      let sign =
        match timeout with
        | None    -> Compile.compile_file file
        | Some(i) ->
            try with_timeout i Compile.compile_file file
            with Timeout ->
              fatal_no_pos "Compilation timed out for [%s]." file
      in
      let run_checker prop fn chk kw =
        let run cmd =
          match Tool.External.run prop fn cmd sign with
          | Some(true ) -> ()
          | Some(false) -> fatal_no_pos "The rewrite system is not %s." kw
          | None        -> fatal_no_pos "The rewrite system may not be %s." kw
        in
        Option.iter run chk
      in
      run_checker "confluence" Export.Hrs.to_HRS cfg.confluence "confluent";
      run_checker
        "termination" Export.Xtc.to_XTC cfg.termination "terminating"
    in
    List.iter handle files
  in
  Error.handle_exceptions run

(** Running the parsing mode. *)
let parse_cmd : Config.t -> string list -> unit = fun cfg files ->
  let run _ =
    let open Timed in
    Config.init cfg;
    (* We save time to run each file in the same environment. *)
    let time = Time.save () in
    let consume _ = () in
    let handle file =
      Time.restore time;
      Debug.stream_iter consume (Parser.parse_file file) in
    List.iter handle files
  in
  Error.handle_exceptions run

(** Running the pretty-printing mode. *)
let export_cmd : Config.t -> string -> unit = fun cfg file ->
  let run _ =
    Config.init {cfg with verbose = Some 0};
    match cfg.output with
    | None
    | Some Lp -> Pretty.ast Format.std_formatter (Parser.parse_file file)
    | Some Dk -> Export.Dk.sign (Compile.compile_file file)
    | Some Hrs ->
      Export.Hrs.to_HRS Format.std_formatter (Compile.compile_file file)
    | Some Xtc ->
      Export.Xtc.to_XTC Format.std_formatter (Compile.compile_file file)
    | Some Coq -> To_coq.print (Parser.parse_file file)
  in Error.handle_exceptions run

(** Running the LSP server. *)
let lsp_server_cmd : Config.t -> bool -> string -> unit =
    fun cfg standard_lsp lsp_log_file ->
  let run _ = Config.init cfg; Lsp.Lp_lsp.main standard_lsp lsp_log_file in
  Error.handle_exceptions run

(** Printing a decision tree. *)
let decision_tree_cmd : Config.t -> qident -> bool -> unit =
  fun cfg (mp, sym) ghost ->
  let run _ =
    Config.init cfg;
    (* Search for a package from the current working directory. *)
    Package.apply_config (Filename.concat (Sys.getcwd()) ".");
    let sym =
      Timed.(Console.verbose := 0); (* To avoid printing "Checked ..." *)
      let sign = Compile.compile mp in
      let ss = Sig_state.of_sign sign in
      if ghost then
        (* Search through ghost symbols. *)
        try StrMap.find sym Timed.(!(Ghost.sign.sign_symbols))
        with Not_found -> fatal_no_pos "Unknown ghost symbol %s." sym
      else
        try Sig_state.find_sym ~prt:true ~prv:true ss (Pos.none (mp, sym))
        with Not_found ->
          fatal_no_pos "Unknown symbol %a.%s." Path.pp mp sym
    in
    if Timed.(!(sym.sym_rules)) = [] then
      wrn None "Cannot print decision tree: \
                symbol \"%s\" does not have any rule." sym.sym_name
    else Console.out 0 "%a" Tool.Tree_graphviz.to_dot sym
  in
  Error.handle_exceptions run

(** {3 Command line argument parsing} *)

(** Options that are specific to the ["check"] command. *)

let timeout : int option CLT.t =
  let timeout : int Arg.conv =
    let parse (s : string): (int, [>`Msg of string]) result =
      match int_of_string_opt s with
      | Some v when v > 0 -> Ok v
      | _ -> Error(`Msg "Invalid timeout value")
    in
    Arg.conv (parse, int)
  in
  let doc =
    "Timeout after $(docv) seconds. The program is interrupted with an error \
     as soon as the specified number of seconds is elapsed."
  in
  Arg.(value & opt (some timeout) None & info ["timeout"] ~docv:"NUM" ~doc)

(** Options that are specific to the ["lsp-server"] command. *)

let standard_lsp : bool CLT.t =
  let doc =
    "Restrict to standard LSP protocol, avoiding interactive proof support \
     extensions that are not supported by all editors."
  in
  Arg.(value & flag & info ["standard-lsp"] ~doc)

let lsp_log_file : string CLT.t =
  let default = Lsp.Lp_lsp.default_log_file in
  let doc =
    Printf.sprintf
      "Use file $(docv) as the log file for the LSP server. The default log \
       file is [%s]." default
  in
  Arg.(value & opt string default & info ["log-file"] ~docv:"FILE" ~doc)

(** Specific to the ["decision-tree"] command. *)

let qident : qident CLT.t =
  let qident : qident Arg.conv =
    let parse (s: string): (qident, [>`Msg of string]) result =
      try Ok(Parser.qident_of_string s)
      with Fatal(_,s) -> Error(`Msg(s))
    in
    let print fmt qid = Pretty.qident fmt (Pos.none qid) in
    Arg.conv (parse, print)
  in
  let doc = "Fully qualified symbol name with dot separated identifiers." in
  let i = Arg.(info [] ~docv:"MOD_PATH.SYM" ~doc) in
  Arg.(value & pos 0 qident ([], "") & i)

let ghost : bool CLT.t =
  let doc = "Print the decision tree of a ghost symbol." in
  Arg.(value & flag & info [ "ghost" ] ~doc)

(** Remaining arguments: source files. *)

let file : string CLT.t =
  let doc =
    Printf.sprintf
      "Source file with the [%s] extension (or with the [%s] extension when \
       using the Dedukti syntax)." lp_src_extension dk_src_extension
  in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let files : string list CLT.t =
  let doc =
    Printf.sprintf
      "Source file with the [%s] extension (or with the [%s] extension when \
       using the Dedukti syntax)." lp_src_extension dk_src_extension
  in
  Arg.(value & (pos_all non_dir_file []) & info [] ~docv:"FILE" ~doc)

(** Definition of the commands. *)

let man_pkg_file =
  let sample_pkg_file =
    let lines =
      [ "# Lines whose first non-whitespace charater is # are comments"
      ; "# The end of a non-comment line cannot be commented."
      ; "# The following two fields must be defined:"
      ; "package_name = my_package_name"
      ; "root_path = a.b.c"
      ; "# Unknown fields like the following are ignored."
      ; "unknown = this is useless" ]
    in
    `Pre (String.concat "\n" (List.map (Printf.sprintf "\t%s") lines))
  in
  [ `S Manpage.s_files
  ; `P "A package configuration files $(b,lambdapi.pkg) can be placed at the \
        root of a source tree, so that Lambdapi can determine under what \
        module path the underlying modules should be registered (relative to \
        the library root). If several candidate package configuration files \
        are found in the parent folders of a source file, the one in the \
        closest parent directory is used."
  ; `P "The syntax of package configuration files is line-based. Each line \
        can either be a comment (i.e., it starts with a '#') or a key-value \
        association of the form \"key = value\". Two such entries should be \
        given for a configuration file to be valid: a $(b,package_name) \
        entry whose value is an identifier and a $(b,root_path) entry whose \
        value is a module path."
  ; `P "An example of package configuration file is given bellow."
  ; sample_pkg_file ]

let check_cmd =
  let doc = "Type-checks the given files." in
  Cmd.v (Cmd.info "check" ~doc ~man:man_pkg_file)
    CLT.(const check_cmd $ Config.full $ timeout $ files)

let decision_tree_cmd =
  let doc =
    "Prints decision tree of a symbol to standard output using the \
     Dot language. Piping to `dot -Tpng | display' displays the tree."
  in
  Cmd.v (Cmd.info "decision-tree" ~doc ~man:man_pkg_file)
    CLT.(const decision_tree_cmd $ Config.full $ qident $ ghost)

let parse_cmd =
  let doc = "Run the parser on the given files." in
  Cmd.v (Cmd.info "parse" ~doc ~man:man_pkg_file)
    CLT.(const parse_cmd $ Config.full $ files)

let export_cmd =
  let doc = "Translate the given files to other formats." in
  Cmd.v (Cmd.info "export" ~doc ~man:man_pkg_file)
    CLT.(const export_cmd $ Config.full $ file)

let lsp_server_cmd =
  let doc = "Runs the LSP server." in
  Cmd.v (Cmd.info "lsp" ~doc ~man:man_pkg_file)
    CLT.(const lsp_server_cmd $ Config.full $ standard_lsp $ lsp_log_file)

let help_cmd =
  let doc = "Display the main help page for Lambdapi." in
  Cmd.v (Cmd.info "help" ~doc) CLT.(ret (const (`Help (`Pager, None))))

let version_cmd =
  let run () = Console.out 0 "Lambdapi version: %s" Version.version in
  let doc = "Display the current version of Lambdapi." in
  Cmd.v (Cmd.info "version" ~doc) CLT.(const run $ const ())

let _ =
  let t0 = Sys.time () in
  Stdlib.at_exit (Debug.print_time t0);
  Printexc.record_backtrace true;
  let cmds =
    [ check_cmd ; parse_cmd ; export_cmd ; lsp_server_cmd
    ; decision_tree_cmd ; help_cmd ; version_cmd
    ; Init.cmd ; Install.install_cmd ; Install.uninstall_cmd ]
  in
  let doc = "A type-checker for the lambdapi-calculus modulo rewriting." in
  let sdocs = Manpage.s_common_options in
  let info = Cmd.info "lambdapi" ~version ~doc ~sdocs in
  let default = CLT.(ret (const (`Help (`Pager, None)))) in
  exit (Cmd.eval (Cmd.group info ~default cmds))
