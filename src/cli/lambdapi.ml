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

module LPSearchMain =
struct

let sig_state_of_require =
 function
   None -> Core.Sig_state.dummy
 | Some req ->
    (* Search for a package from the current working directory. *)
    Package.apply_config (Filename.concat (Sys.getcwd()) ".") ;
    Core.Sig_state.of_sign
     (Compile.compile (Parsing.Parser.path_of_string req))

let search_cmd cfg rules require s dbpath_opt =
 Config.init cfg;
 let run () =
  Tool.Indexing.load_rewriting_rules rules ;
  let ss = sig_state_of_require require in
  let dbpath = Option.get Path.default_dbpath dbpath_opt in
  out Format.std_formatter "%s@."
   (Tool.Indexing.search_cmd_txt ss s ~dbpath) in
 Error.handle_exceptions run

let websearch_cmd cfg rules port require header_file dbpath_opt =
 Config.init cfg;
 let run () =
  Tool.Indexing.load_rewriting_rules rules ;
  let ss = sig_state_of_require require in
  let header = match header_file with
    | None ->
      "
      <style>
      .snippet {
        border: 1px solid grey;
        color: red;
        padding: 0 3px 0 3px;
        line-height: 1.6;
      }</style>
      <h1><a href=\"https://github.com/Deducteam/lambdapi\">LambdaPi</a>
      Search Engine</h1>

    <p>
        The <b>search</b> button answers the query. Read the <a href=
        \"https://lambdapi.readthedocs.io/en/latest/query_language.html\">
        query language specification</a> to learn about the query language.
        <br>The query language also uses the <a
        href=\"https://lambdapi.readthedocs.io/en/latest/terms.html\">
        Lambdapi terms syntax</a>.<br>
        In particular, the following constructors can come handy for
        writing queries:<br>
    </p>
    <ul>
        <li>an anonymous function<span class=\"snippet\">λ (x:A) y z,t</span>
        smapping <span class=\"snippet\">x</span>, <span class=\"snippet\">y
        </span> and <span class=\"snippet\">z</span> (of type <span class=\"
        snippet\">A</span> for <span class=\"snippet\">x</span>) to <span
        class=\"snippet\">t</span>.</li>
        <li>a dependent product <span class=\"snippet\">Π (x:A) y z,T</span>
        </li>
        <li>a non-dependent product <span class=\"snippet\">A → T</span>
         (syntactic sugar for <span class=\"snippet\">Π x:A,T</span> when
          <span class=\"snippet\">x</span> does not occur in <span class=
          \"snippet\">T</span>)</li>
    </ul>
      "
    | Some file -> Lplib.String.string_of_file file in
  let dbpath = Option.get Path.default_dbpath dbpath_opt in
  Tool.Websearch.start ~header ss ~port ~dbpath () in
 Error.handle_exceptions run

let index_cmd cfg add_only rules files dbpath_opt =
 Config.init cfg;
 let run () =
  if not add_only then Tool.Indexing.empty ();
  (* We save time to run each file in the same environment. *)
  let open Timed in
  let time = Time.save () in
  let handle file =
   Console.reset_default ();
   Time.restore time;
   Tool.Indexing.load_rewriting_rules rules;
   Tool.Indexing.index_sign (no_wrn Compile.compile_file file) in
  List.iter handle files;
  let dbpath = Option.get Path.default_dbpath dbpath_opt in
  Tool.Indexing.dump dbpath () in
 Error.handle_exceptions run

end

(** Running the main type-checking mode. *)
let check_cmd : Config.t -> int option -> string list -> unit =
    fun cfg tmout files ->
  let run _ =
    let open Timed in
    Config.init cfg;
    (* We save time to run each file in the same environment. *)
    let time = Time.save () in
    let handle file =
      Console.reset_default ();
      Time.restore time;
      let sign =
        match tmout with
        | None    -> Compile.compile_file file
        | Some(i) ->
            try timeout i Compile.compile_file file
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
      run_checker "confluence" Export.Hrs.sign cfg.confluence "confluent";
      run_checker "termination" Export.Xtc.sign cfg.termination "terminating"
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

(** Possible outputs for the export command. *)
type output = Lp | Dk | RawDk | Hrs | Xtc | RawCoq | SttCoq

(** Running the export mode. *)
let export_cmd (cfg:Config.t) (output:output option) (encoding:string option)
      (mapping:string option) (renaming:string option)
      (requiring:string option) (no_implicits:bool) (use_notations:bool)
      (file:string) : unit =
  let run _ =
    Config.init {cfg with verbose = Some 0};
    Export.Coq.use_implicits := not no_implicits;
    Export.Coq.use_notations := use_notations;
    match output with
    | None
    | Some Lp -> Pretty.ast Format.std_formatter (Parser.parse_file file)
    | Some Dk -> Export.Dk.sign (Compile.compile_file file)
    | Some RawDk -> Export.Rawdk.print (Parser.parse_file file)
    | Some Hrs ->
      Export.Hrs.sign Format.std_formatter (Compile.compile_file file)
    | Some Xtc ->
      Export.Xtc.sign Format.std_formatter (Compile.compile_file file)
    | Some RawCoq ->
        Export.Coq.stt := false;
        Option.iter Export.Coq.set_renaming renaming;
        Export.Coq.print (Parser.parse_file file)
    | Some SttCoq ->
        Export.Coq.stt := true;
        Option.iter Export.Coq.set_renaming renaming;
        Option.iter Export.Coq.set_encoding encoding;
        Option.iter Export.Coq.set_mapping mapping;
        Option.iter Export.Coq.set_requiring requiring;
        Export.Coq.print (Parser.parse_file file)
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

(** Options specific to the ["decision-tree"] command. *)

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

(** Options specific to the export command. *)

let output : output option CLT.t =
  let output : output Arg.conv =
    let parse (s: string) : (output, [>`Msg of string]) result =
      match s with
      | "lp" -> Ok Lp
      | "dk" -> Ok Dk
      | "raw_dk" -> Ok RawDk
      | "hrs" -> Ok Hrs
      | "xtc" -> Ok Xtc
      | "raw_coq" -> Ok RawCoq
      | "stt_coq" -> Ok SttCoq
      | _ -> Error(`Msg "Invalid format")
    in
    let print fmt o =
      string fmt
        (match o with
         | Lp -> "lp"
         | Dk -> "dk"
         | RawDk -> "raw_dk"
         | Hrs -> "hrs"
         | Xtc -> "xtc"
         | RawCoq -> "raw_coq"
         | SttCoq -> "stt_coq")
    in
    Arg.conv (parse, print)
  in
  let doc =
    "Set the output format of the export command. The value of $(docv) \
     must be `lp' (default), `raw_dk`, `dk`, `hrs`, `xtc`, `raw_coq` or \
     `stt_coq`."
  in
  Arg.(value & opt (some output) None & info ["output";"o"] ~docv:"FMT" ~doc)

let encoding : string option CLT.t =
  let encoding : string Arg.conv =
    let parse (s: string) : (string, [>`Msg of string]) result = Ok s in
    let print fmt s = string fmt s in
    Arg.conv (parse, print)
  in
  let doc = "Set config file for the command export -o stt_coq." in
  Arg.(value & opt (some encoding) None & info ["encoding"] ~docv:"FILE" ~doc)

let renaming : string option CLT.t =
  let renaming : string Arg.conv =
    let parse (s: string) : (string, [>`Msg of string]) result = Ok s in
    let print fmt s = string fmt s in
    Arg.conv (parse, print)
  in
  let doc = "Set config file for the command export -o stt_coq." in
  Arg.(value & opt (some renaming) None & info ["renaming"] ~docv:"FILE" ~doc)

let mapping : string option CLT.t =
  let mapping : string Arg.conv =
    let parse (s: string) : (string, [>`Msg of string]) result = Ok s in
    let print fmt s = string fmt s in
    Arg.conv (parse, print)
  in
  let doc = "Set config file for the command export -o stt_coq." in
  Arg.(value & opt (some mapping) None & info ["mapping"] ~docv:"FILE" ~doc)

let requiring : string option CLT.t =
  let requiring : string Arg.conv =
    let parse (s: string) : (string, [>`Msg of string]) result = Ok s in
    let print fmt s = string fmt s in
    Arg.conv (parse, print)
  in
  let doc = "Set config file for the command export -o stt_coq." in
  Arg.(value & opt (some requiring) None
       & info ["requiring"] ~docv:"FILE" ~doc)

let no_implicits : bool CLT.t =
  let doc = "Indicates that input symbols have no implicit arguments." in
  Arg.(value & flag & info ["no-implicits"] ~doc)

let use_notations : bool CLT.t =
  let doc = "Generate Coq code using notations." in
  Arg.(value & flag & info ["use-notations"] ~doc)

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
    CLT.(const export_cmd $ Config.full $ output $ encoding $ mapping
         $ renaming $ requiring $ no_implicits $ use_notations $ file)

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

let query_as_arg : string Cmdliner.Term.t =
  let doc = "Query to be executed." in
  Arg.(required & pos 0 (some string) None & info [] ~docv:"QUERY" ~doc)

let add_only_arg : bool CLT.t =
  let doc = "Adds more terms to the index without cleaning it first." in
  Arg.(value & flag & info ["add"] ~doc)

let port_arg : int CLT.t =
  let doc =
    "Port used by the webserver." in
  Arg.(value & opt int 8080 & info ["port"] ~docv:"PORT" ~doc)

let rules_arg : string list CLT.t =
  let doc =
    "File holding rewriting rules applied before indexing. Use option \
     multiple times to fetch rules from multiple files." in
  Arg.(value & opt_all string [] & info ["rules"] ~docv:"FILENAME" ~doc)

let require_arg : string option CLT.t =
  let doc =
    "LP file to be required before starting the search engine." in
  Arg.(value & opt (some string) None & info ["require"] ~docv:"PATH" ~doc)

let custom_dbpath : string option CLT.t =
  let doc =
    "Path to the search DB file." in
  Arg.(value & opt (some string) None & info ["db"] ~docv:"PATH" ~doc)

let header_file_arg : string option CLT.t =
  let doc =
    "html file holding the header of the web page of the server." in
  Arg.(value & opt (some string) None &
    info ["header"] ~docv:"PATH" ~doc)

let index_cmd =
 let doc = "Index the given files." in
 Cmd.v (Cmd.info "index" ~doc ~man:man_pkg_file)
  Cmdliner.Term.(const LPSearchMain.index_cmd $ Config.full
   $ add_only_arg $ rules_arg $ files $ custom_dbpath)

let search_cmd =
 let doc = "Run a search query against the index." in
 Cmd.v (Cmd.info "search" ~doc ~man:man_pkg_file)
  Cmdliner.Term.(const LPSearchMain.search_cmd $ Config.full
   $ rules_arg $ require_arg $ query_as_arg $ custom_dbpath)

let websearch_cmd =
 let doc =
  "Starts a webserver for searching the library." in
 Cmd.v (Cmd.info "websearch" ~doc ~man:man_pkg_file)
  Cmdliner.Term.(const LPSearchMain.websearch_cmd $ Config.full
   $ rules_arg $ port_arg $ require_arg $ header_file_arg $ custom_dbpath)

let _ =
  let t0 = Sys.time () in
  Stdlib.at_exit (Debug.print_time t0);
  Printexc.record_backtrace true;
  let cmds =
    [ check_cmd ; parse_cmd ; export_cmd ; lsp_server_cmd
    ; decision_tree_cmd ; help_cmd ; version_cmd
    ; Init.cmd ; Install.install_cmd ; Install.uninstall_cmd
    ; index_cmd ; search_cmd ; websearch_cmd ]
  in
  let doc = "A type-checker for the lambdapi-calculus modulo rewriting." in
  let sdocs = Manpage.s_common_options in
  let info = Cmd.info "lambdapi" ~version ~doc ~sdocs in
  let default = CLT.(ret (const (`Help (`Pager, None)))) in
  exit (Cmd.eval (Cmd.group info ~default cmds))
