(** Main program. *)

open Core
open Extra
open Files
open Console
open Version

(* NOTE only standard [Pervasives] references here. *)

(** {3 Evaluation of commands. *)

(** Configuration value for the commonly available options. *)
type config =
  { gen_obj     : bool
  ; lib_root    : string option
  ; map_dir     : (string * string) list
  ; write_tree  : bool
  ; keep_order  : bool
  ; verbose     : int
  ; no_warnings : bool
  ; debug       : string
  ; no_colors   : bool
  ; too_long    : float
  ; confluence  : string option
  ; termination : string option }

(** [init cfg] runs the necessary initializations according to [cfg]. This has
    to be done prior to any other (non-trivial) task. *)
let init : config -> unit = fun cfg ->
  (* Set all the flags and configs. *)
  Compile.gen_obj := cfg.gen_obj;
  Option.iter Files.set_lib_root cfg.lib_root;
  List.iter (fun (m,d) -> Files.new_lib_mapping (m ^ ":" ^ d)) cfg.map_dir;
  Handle.write_trees := cfg.write_tree;
  Tree.rule_order := cfg.keep_order;
  set_default_verbose cfg.verbose;
  no_wrn := cfg.no_warnings;
  set_default_debug cfg.debug;
  Console.color := not cfg.no_colors;
  Handle.too_long := cfg.too_long;
  (* Log some configuration data. *)
  if Timed.(!log_enabled) then
    begin
      Files.log_file "running directory: [%s]" (Files.current_path ());
      Files.log_file "library root path: [%s]" (Files.lib_root_path ());
      let fn = Files.log_file "mapping: [%a] → [%s]" Files.Path.pp in
      Files.ModMap.iter fn (Files.current_mappings ())
    end;
  (* Register the library root. *)
  Files.init_lib_root ()

(** Running the main type-checking mode. *)
let check_cmd : config -> int option -> string list -> unit =
    fun cfg timeout files ->
  let handle file =
    try
      let sign =
        match timeout with
        | None    -> Compile.compile_file file
        | Some(i) ->
            if i <= 0 then exit_with "Invalid timeout value [%i] (≤ 0)." i;
            try with_timeout i Compile.compile_file file
            with Timeout ->
              fatal_no_pos "Compilation timed out for [%s]." file
      in
      let run_checker prop fn chk kw =
        let run cmd =
          match External.run prop fn cmd sign with
          | Some(true ) -> ()
          | Some(false) -> fatal_no_pos "The rewrite system is not %s." kw
          | None        -> fatal_no_pos "The rewrite system may not be %s." kw
        in
        Option.iter run chk
      in
      run_checker "confluence"  Hrs.to_HRS cfg.confluence  "confluent";
      run_checker "termination" Xtc.to_XTC cfg.termination "terminating"
    with
    | Fatal(None,    msg) -> exit_with "%s" msg
    | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.print p msg
  in
  init cfg; List.iter handle files

(** Running the parsing mode. *)
let parse_cmd : config -> string list -> unit = fun cfg files ->
  let handle file =
    try ignore (Compile.parse_file file)
    with
    | Fatal(None,    msg) -> exit_with "%s" msg
    | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.print p msg
  in
  init cfg; List.iter handle files

(** Running the pretty-printing mode. *)
let beautify_cmd : config -> string list -> unit = fun cfg files ->
  let handle file =
    try Pretty.beautify (Compile.parse_file file)
    with
    | Fatal(None,    msg) -> exit_with "%s" msg
    | Fatal(Some(p), msg) -> exit_with "[%a] %s" Pos.print p msg
  in
  init cfg; List.iter handle files

(** Running the LSP server. *)
let lsp_server_cmd : config -> bool -> string -> unit =
    fun cfg standard_lsp lsp_log_file ->
  init cfg; Lsp.Lp_lsp.main standard_lsp lsp_log_file

(** {3 Command line argument parsing} *)

open Cmdliner

(** General purpose options. *)

let gen_obj : bool Term.t =
  let doc =
    Printf.sprintf
      "Produce object files with the [%s] extension. These object files can \
       then be read during subsequent calls to avoid re-type-checking fo the \
       corresponding source file. Note that an object file is only used when \
       it is up to date (i.e., more recent than the source). If that is not \
       the case then the outdated file is overwritten." obj_extension
  in
  Arg.(value & flag & info ["gen-obj"; "c"] ~doc)

let lib_root : string option Term.t =
  let doc =
    Printf.sprintf
      "Set the library root to be the directory $(docv). Roughly, the \
       library root is common path under which every module is placed. It \
       has the same purpose as the root directory \"/\" of Unix systems. \
       In fact it is possible to \"mount\" directories under the library \
       root with the \"--map-dir\" option. The default library root of the \
       system (set to \"%s\") should always be preferred. This option is \
       only provided for advanced usages."
      (Files.default_lib_root ())
  in
  Arg.(value & opt (some dir) None & info ["lib-root"] ~docv:"DIR" ~doc)

let map_dir : (string * string) list Term.t =
  let doc =
    "Map all the modules having MOD as a prefix of their module path to \
     files under the directory DIR. The corresponding modules under the \
     library root are then rendered inaccessible. This option is useful \
     during the development of a library, before it can be installed in the \
     expected folder under the library root."
  in
  let i = Arg.(info ["map-dir"] ~docv:"MOD:DIR" ~doc) in
  Arg.(value & opt_all (pair ~sep:':' string dir) [] & i)

let write_tree : bool Term.t =
  let doc =
    "Write decision trees to \".gv\" files when reduction rules are added \
     for a symbol. This is mainly useful for debugging."
  in
  Arg.(value & flag & info ["write-trees"] ~doc)

let keep_order : bool Term.t =
  let doc =
    "Respect the order of definition of the rewriting rules in files. In \
     other words, earlier rewriting rules are applied with higher priority."
  in
  Arg.(value & flag & info ["keep-rule-order"] ~doc)

(** Debugging and output options. *)

let verbose : int Term.t =
  let doc =
    "Set the verbosity level to $(docv). A value smaller or equal to 0 will \
     disable all printing (on standard output). Greater numbers lead to more \
     and more informations being written to standard output. There is no \
     difference between the values of 3 and more."
  in
  Arg.(value & opt int 1 & info ["verbose"; "v"] ~docv:"NUM" ~doc)

let no_warnings : bool Term.t =
  let doc =
    "Disable the printing of all warnings."
  in
  Arg.(value & flag & info ["no-warnings"; "w"] ~doc)

let debug : string Term.t =
  let descs =
    let fn (k, d) = Printf.sprintf "$(b,\"%c\") (for %s)" k d in
    String.concat ", " (List.map fn (Console.log_summary ()))
  in
  let doc =
    Printf.sprintf
      "Enables the debugging flags specified in $(docv). Every character of \
       $(docv) correspond to a flag. The available values are %s." descs
  in
  Arg.(value & opt string "" & info ["debug"] ~docv:"FLAGS" ~doc)

let no_colors : bool Term.t =
  let doc =
    "Disable the use of colors when printing to the terminal. Note that the \
     default behaviour is to rely on ANSI escape sequences in order to make \
     the debugging logs more readable."
  in
  Arg.(value & flag & info ["no-colors"] ~doc)

let too_long : float Term.t =
  let doc =
    "Print a warning every time that a command requires more than $(docv) \
     seconds to execute. The command is not interrupted."
  in
  Arg.(value & opt float infinity & info ["too-long"] ~docv:"FLOAT" ~doc)

(** External checker options. *)

let confluence : string option Term.t =
  let doc =
    "Use the command $(docv) for checking confluence. The command $(docv) \
     should accept HRS-formatted text on its standard input (For more info \
     see http://project-coco.uibk.ac.at/problems/hrs.php) \
     and the first line of its standard output should be either \"YES\", \
     \"NO\" or \"MAYBE\"."
  in
  Arg.(value & opt (some string) None & info ["confluence"] ~docv:"CMD" ~doc)

let termination : string option Term.t =
  let doc =
    "Use the command $(docv) for checking termination. The command $(docv) \
     should accept XTC-formatted text on its standard input (for more info \
     see https://tinyurl.com/XTC-format), and the first line of its standard \
     output should be either \"YES\", \"NO\" or \"MAYBE\"."
  in
  Arg.(value & opt (some string) None & info ["termination"] ~docv:"CMD" ~doc)

(** Gathering the globally available options. *)

(** [global_config] gathers the command line arguments that are common to most
    of the commands. *)
let global_config : config Term.t =
  let fn gen_obj lib_root map_dir write_tree keep_order verbose no_warnings
      debug no_colors too_long confluence termination =
    { gen_obj ; lib_root ; map_dir ; write_tree ; keep_order ; verbose
    ; no_warnings ; debug ; no_colors ; too_long ; confluence ; termination }
  in
  let open Term in
  const fn $ gen_obj $ lib_root $ map_dir $ write_tree $ keep_order $ verbose
    $ no_warnings $ debug $ no_colors $ too_long $ confluence $ termination

(** Options that are specific to the ["check"] command. *)

let timeout : int option Term.t =
  let doc =
    "Timeout after $(docv) seconds. The program is interrupted with an error \
     as soon as the specified number of seconds is elapsed."
  in
  Arg.(value & opt (some int) None & info ["timeout"] ~docv:"NUM" ~doc)

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

(** Remaining arguments: source files. *)

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
  Term.(const check_cmd $ global_config $ timeout $ files),
  Term.info "check" ~doc ~man:man_pkg_file

let parse_cmd =
  let doc = "Run the parser on the given files." in
  Term.(const parse_cmd $ global_config $ files),
  Term.info "parse" ~doc ~man:man_pkg_file

let beautify_cmd =
  let doc = "Run the parser and pretty-printer on the given files." in
  Term.(const beautify_cmd $ global_config $ files),
  Term.info "beautify" ~doc ~man:man_pkg_file

let lsp_server_cmd =
  let doc = "Runs the LSP server." in
  Term.(const lsp_server_cmd $ global_config $ standard_lsp $ lsp_log_file),
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
    ; help_cmd ; version_cmd ]
  in
  Term.(exit (eval_choice default_cmd cmds))
