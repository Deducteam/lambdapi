(** Main program. *)

open! Lplib
open Lplib.Extra
open Common
open Parsing
open Core
open Cmdliner
open Library
open Console
open Version
open Handle

(* NOTE only standard [Stdlib] references here. *)

(** {3 Evaluation of commands. *)

(** Running the main type-checking mode. *)
let check_cmd : Config.t -> int option -> bool -> string list -> unit =
    fun cfg timeout recompile files ->
  let run _ =
    let open Timed in
    Config.init cfg; Stdlib.(Compile.recompile := recompile);
    (* We save time to run each file in the same environment. *)
    let time = Time.save () in
    let handle file =
      Console.reset_default ();
      Time.restore time;
      let sign =
        match timeout with
        | None    -> Compile.compile_file file
        | Some(i) ->
            if i <= 0 then fatal_no_pos "Invalid timeout value [%i] (≤ 0)." i;
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
      run_checker "confluence"  Tool.Hrs.to_HRS cfg.confluence  "confluent";
      run_checker "termination" Tool.Xtc.to_XTC cfg.termination "terminating"
    in
    List.iter handle files
  in
  Console.handle_exceptions run

(** Running the parsing mode. *)
let parse_cmd : Config.t -> string list -> unit = fun cfg files ->
  let run _ =
    let open Timed in
    Config.init cfg;
    (* We save time to run each file in the same environment. *)
    let time = Time.save () in
    let handle file = Time.restore time; ignore (Compile.parse_file file) in
    List.iter handle files
  in
  Console.handle_exceptions run

(** Running the pretty-printing mode. *)
let beautify_cmd : Config.t -> string -> unit = fun cfg file ->
  let run _ =
    Config.init cfg; Pretty.beautify (Compile.parse_file file) in
  Console.handle_exceptions run

(** Running the LSP server. *)
let lsp_server_cmd : Config.t -> bool -> string -> unit =
    fun cfg standard_lsp lsp_log_file ->
  let run _ = Config.init cfg; Lsp.Lp_lsp.main standard_lsp lsp_log_file in
  Console.handle_exceptions run

(** Printing a decision tree. *)
let decision_tree_cmd : Config.t -> Syntax.qident -> unit =
  fun cfg (mp, sym) ->
  let run _ =
    Timed.(verbose := 0); (* To avoid printing the "Checked ..." line *)
    (* By default, search for a package from the current working directory. *)
    let pth = Sys.getcwd () in
    let pth = Filename.concat pth "." in
    Package.apply_config pth;
    Config.init cfg;
    let sym =
      let sign = Compile.compile false mp in
      let ss = Sig_state.of_sign sign in
      if String.contains sym '#' then
        (* If [sym] contains a hash, it’s a ghost symbol. *)
        try fst (StrMap.find sym Timed.(!(Unif_rule.sign.sign_symbols)))
        with Not_found ->
          fatal_no_pos "Symbol \"%s\" not found in ghost modules." sym
      else
        try
          Sig_state.find_sym ~prt:true ~prv:true false ss (Pos.none (mp, sym))
        with Not_found ->
          fatal_no_pos "Symbol \"%s\" not found in module \"%a\"."
            sym Path.pp mp
    in
    if Timed.(!(sym.sym_rules)) = [] then
      wrn None "Cannot print decision tree: \
                symbol \"%s\" does not have any rule." sym.sym_name
    else
      out 0 "%a" Tool.Tree_graphviz.to_dot sym
  in
  Console.handle_exceptions run

(** {3 Command line argument parsing} *)

(** Options that are specific to the ["check"] command. *)

let timeout : int option Term.t =
  let doc =
    "Timeout after $(docv) seconds. The program is interrupted with an error \
     as soon as the specified number of seconds is elapsed."
  in
  Arg.(value & opt (some int) None & info ["timeout"] ~docv:"NUM" ~doc)

let recompile : bool Term.t =
  let doc =
    "Recompile the files even if they have an up-to-date object file."
  in
  Arg.(value & flag & info ["recompile"] ~doc)

(** Options that are specific to the ["lsp-server"] command. *)

let standard_lsp : bool Term.t =
  let doc =
    "Restrict to standard LSP protocol, avoiding interactive proof support \
     extensions that are not supported by all editors."
  in
  Arg.(value & flag & info ["standard-lsp"] ~doc)

let lsp_log_file : string Term.t =
  let default = Lsp.Lp_lsp.default_log_file in
  let doc =
    Printf.sprintf
      "Use file $(docv) as the log file for the LSP server. The default log \
       file is [%s]." default
  in
  Arg.(value & opt string default & info ["log-file"] ~docv:"FILE" ~doc)

(** Specific to the ["decision-tree"] command. *)

let qsym : Syntax.qident Term.t =
  let qsym_conv: Syntax.qident Arg.conv =
    let parse (s: string): (Syntax.qident, [>`Msg of string]) result =
      match Parser.qident_of_string s with
      | Error(p) ->
          Error(`Msg(Format.asprintf "[%a] invalid argument" Pos.pp p))
      | Ok(id) -> Ok(id)
    in
    let print fmt qid = Pretty.qident fmt (Pos.none qid) in
    Arg.conv (parse, print)
  in
  let doc = "Fully qualified symbol name with dot separated identifiers." in
  let i = Arg.(info [] ~docv:"MOD_PATH.SYM" ~doc) in
  Arg.(value & pos 0 qsym_conv ([], "") & i)

(** Remaining arguments: source files. *)

let file : string Term.t =
  let doc =
    Printf.sprintf
      "Source file with the [%s] extension (or with the [%s] extension when \
       using the Dedukti syntax)." src_extension legacy_src_extension
  in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let files : string list Term.t =
  let doc =
    Printf.sprintf
      "Source file with the [%s] extension (or with the [%s] extension when \
       using the legacy Dedukti syntax)." src_extension legacy_src_extension
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
  Term.(const check_cmd $ Config.full $ timeout $ recompile $ files),
  Term.info "check" ~doc ~man:man_pkg_file

let decision_tree_cmd =
  let doc =
    "Prints decision tree of a symbol to standard output using the \
     Dot language. Piping to `dot -Tpng | display' displays the tree."
  in
  Term.(const decision_tree_cmd $ Config.full $ qsym),
  Term.info "decision-tree" ~doc ~man:man_pkg_file

let parse_cmd =
  let doc = "Run the parser on the given files." in
  Term.(const parse_cmd $ Config.full $ files),
  Term.info "parse" ~doc ~man:man_pkg_file

let beautify_cmd =
  let doc = "Run the parser and pretty-printer on the given files." in
  Term.(const beautify_cmd $ Config.full $ file),
  Term.info "beautify" ~doc ~man:man_pkg_file

let lsp_server_cmd =
  let doc = "Runs the LSP server." in
  Term.(const lsp_server_cmd $ Config.full $ standard_lsp $ lsp_log_file),
  Term.info "lsp" ~doc ~man:man_pkg_file

let help_cmd =
  let doc = "Display the main help page for Lambdapi." in
  Term.(ret (const (`Help (`Pager, None)))),
  Term.info "help" ~doc

let version_cmd =
  let run () = out 0 "Lambdapi version: %s\n%!" Version.version in
  let doc = "Display the current version of Lambdapi." in
  Term.(const run $ const ()),
  Term.info "version" ~doc

let default_cmd =
  let doc = "A type-checker for the lambdapi-calculus modulo rewriting." in
  let sdocs = Manpage.s_common_options in
  Term.(ret (const (`Help (`Pager, None)))),
  Term.info "lambdapi" ~version ~doc ~sdocs

let _ =
  let cmds =
    [ check_cmd ; parse_cmd ; beautify_cmd ; lsp_server_cmd
    ; decision_tree_cmd ; help_cmd ; version_cmd
    ; Init.cmd ; Install.install_cmd ; Install.uninstall_cmd ]
  in
  Term.(exit (eval_choice default_cmd cmds))
