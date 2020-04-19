(** Configuration for the CLI and common flags. *)

open Cmdliner
open Core
open Extra
open Files
open Console

(** {3 Configuration type for common values} *)

(** Configuration value for the commonly available options. *)
type config =
  { gen_obj     : bool
  ; lib_root    : string option
  ; map_dir     : (string * string) list
  ; keep_order  : bool
  ; verbose     : int option
  ; no_warnings : bool
  ; debug       : string
  ; no_colors   : bool
  ; too_long    : float
  ; confluence  : string option
  ; termination : string option }

(** Short synonym of the [config] type. *)
type t = config

(** Default configuration for commands that do not support all flags. *)
let default_config =
  { gen_obj     = false
  ; lib_root    = None
  ; map_dir     = []
  ; keep_order  = false
  ; verbose     = None
  ; no_warnings = false
  ; debug       = ""
  ; no_colors   = false
  ; too_long    = infinity
  ; confluence  = None
  ; termination = None }

(** [init cfg] runs the necessary initializations according to [cfg]. This has
    to be done prior to any other (non-trivial) task. *)
let init : config -> unit = fun cfg ->
  (* Set all the flags and configs. *)
  Compile.gen_obj := cfg.gen_obj;
  Option.iter Files.set_lib_root cfg.lib_root;
  List.iter (fun (m,d) -> Files.new_lib_mapping (m ^ ":" ^ d)) cfg.map_dir;
  Tree.rule_order := cfg.keep_order;
  Option.iter set_default_verbose cfg.verbose;
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
  Files.init_lib_root ();
  (* Initialise the [Pure] interface (this must come last). *)
  Pure.set_initial_time ()

(** {3 Commom command line argument parsing} *)

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

let keep_order : bool Term.t =
  let doc =
    "Respect the order of definition of the rewriting rules in files. In \
     other words, earlier rewriting rules are applied with higher priority."
  in
  Arg.(value & flag & info ["keep-rule-order"] ~doc)

(** Debugging and output options. *)

let verbose : int option Term.t =
  let doc =
    "Set the verbosity level to $(docv). A value smaller or equal to 0 will \
     disable all printing (on standard output). Greater numbers lead to more \
     and more informations being written to standard output. There is no \
     difference between the values of 3 and more."
  in
  Arg.(value & opt (some int) None & info ["verbose"; "v"] ~docv:"NUM" ~doc)

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

(** Gathering options under a configuration. *)

(** [full] gathers the command line arguments common to most commands. *)
let full : config Term.t =
  let fn gen_obj lib_root map_dir keep_order verbose no_warnings
      debug no_colors too_long confluence termination =
    { gen_obj ; lib_root ; map_dir ; keep_order ; verbose ; no_warnings
    ; debug ; no_colors ; too_long ; confluence ; termination }
  in
  let open Term in
  const fn $ gen_obj $ lib_root $ map_dir $ keep_order $ verbose
  $ no_warnings $ debug $ no_colors $ too_long $ confluence $ termination

(** [minimal] gathers the minimal command line options to enable debugging and
    accest to the library root. *)
let minimal : config Term.t =
  let fn lib_root map_dir verbose debug no_colors =
    { default_config with lib_root ; map_dir ; verbose ; debug ; no_colors }
  in
  Term.(const fn $ lib_root $ map_dir $ verbose $ debug $ no_colors)


