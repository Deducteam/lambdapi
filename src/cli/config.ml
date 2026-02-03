(** Configuration for the CLI and common flags. *)

open Lplib
open Cmdliner
open Common open Library
open Parsing

type qident = Core.Term.qident

module CLT = Cmdliner.Term

(** {3 Configuration type for common values} *)

(** Configuration value for the commonly available options. *)
type config =
  { gen_obj     : bool
  ; lib_root    : string option
  ; map_dir     : (Path.t * string) list
  ; verbose     : int option
  ; no_warnings : bool
  ; debug       : string
  ; no_colors   : bool
  ; record_time : bool
  ; too_long    : float
  ; confluence  : string option
  ; termination : string option
  ; no_sr_check : bool }

(** Short synonym of the [config] type. *)
type t = config

(** Default configuration for commands that do not support all flags. *)
let default_config =
  { gen_obj     = false
  ; lib_root    = None
  ; map_dir     = []
  ; verbose     = None
  ; no_warnings = false
  ; debug       = ""
  ; no_colors   = false
  ; record_time = false
  ; too_long    = infinity
  ; confluence  = None
  ; termination = None
  ; no_sr_check = false }

(** [init cfg] runs the necessary initializations according to [cfg]. This has
    to be done prior to any other (non-trivial) task. *)
let init : config -> unit = fun cfg ->
  (* Set all the flags and configs. *)
  Handle.Compile.gen_obj := cfg.gen_obj;
  Library.set_lib_root cfg.lib_root;
  List.iter Library.add_mapping cfg.map_dir;
  Option.iter Console.set_default_verbose cfg.verbose;
  Error.no_warnings := cfg.no_warnings;
  Logger.set_default_debug cfg.debug;
  Color.color := not cfg.no_colors;
  Debug.do_record_time := cfg.record_time;
  Handle.Command.too_long := cfg.too_long;
  Handle.Command.sr_check := not cfg.no_sr_check;
  (* Log some configuration data. *)
  if Logger.log_enabled () then
    begin
      Library.log "running directory: %s" (Filename.current_dir ());
      Library.log "library root path: %s"
        (match !lib_root with None -> assert false | Some(p) -> p);
      let f = Library.log "mapping: %a → %s" Path.pp in
      Library.iter f
    end;
  (* Initialise the [Pure] interface (this must come last). *)
  Pure.set_initial_time ()

(** {3 Commom command line argument parsing} *)

(** General purpose options. *)

let gen_obj : bool CLT.t =
  let doc =
    Printf.sprintf
      "Produce object files with the [%s] extension. These object files can \
       then be read during subsequent calls to avoid re-type-checking fo the \
       corresponding source file. Note that an object file is only used when \
       it is up to date (i.e., more recent than the source). If that is not \
       the case then the outdated file is overwritten." obj_extension
  in
  Arg.(value & flag & info ["gen-obj"; "c"] ~doc)

let no_sr_check : bool CLT.t =
  let doc = "Disable the verification that rewrite rules preserve typing." in
  Arg.(value & flag & info ["no-sr-check"] ~doc)

let lib_root : string option CLT.t =
  let doc =
    "Set the library root to be the directory $(docv). The library root \
     is a common path under which every module is placed. \
     It has the same purpose as the root directory \"/\" of Unix systems. \
     In fact it is possible to \"mount\" directories under the library \
     root with the \"--map-dir\" option. \
     Lambdapi uses $(docv) as library root if it is provided, \
     otherwise it uses $(b,\\$LAMBDAPI_LIB_ROOT/lib/lambdapi/lib_root) \
     if the environment variable $(b,LAMBDAPI_LIB_ROOT) is set, \
     then $(b,\\$OPAM_SWITCH_PREFIX/lib/lambdapi/lib_root) \
     if $(b,OPAM_SWITCH_PREFIX) is set or it uses \
     /usr/local/lib/lambdapi/lib_root."
  in
  Arg.(value & opt (some dir) None & info ["lib-root"] ~docv:"DIR" ~doc)

let map_dir : (Path.t * string) list CLT.t =
  let mod_path : Path.t Arg.conv =
    let parse (s: string) : (Path.t, [>`Msg of string]) result =
      try Ok(Parser.path_of_string s)
      with Error.Fatal(_,s) -> Error(`Msg(s))
    in
    let print fmt p = Path.pp fmt p in
    Arg.conv (parse, print)
  in
  let doc =
    "Map all the modules having MOD as a prefix of their module path to \
     files under the directory DIR. The corresponding modules under the \
     library root are then rendered inaccessible. This option is useful \
     during the development of a library, before it can be installed in the \
     expected folder under the library root."
  in
  let i = Arg.(info ["map-dir"] ~docv:"MOD:DIR" ~doc) in
  Arg.(value & opt_all (pair ~sep:':' mod_path dir) [] & i)

(** Debugging and output options. *)

let verbose : int option CLT.t =
  let doc =
    "Set the verbosity level to $(docv). A value smaller or equal to 0 will \
     disable all printing (on standard output). Greater numbers lead to more \
     and more informations being written to standard output.\
     In the case of the websearch command, a value larger or equal to 2 will\
     print the requests received by the server. A value larger than 3 will \
     also print the responses sent by the server.
     "
  in
  Arg.(value & opt (some int) None & info ["verbose"; "v"] ~docv:"NUM" ~doc)

let no_warnings : bool CLT.t =
  let doc =
    "Disable the printing of all warnings."
  in
  Arg.(value & flag & info ["no-warnings"; "w"] ~doc)

let debug : string CLT.t =
  let descs =
    let fn (k, d) = Printf.sprintf "$(b,%c) for %s" k d in
    String.concat ", " (List.map fn (Logger.log_summary ()))
  in
  let doc =
    Printf.sprintf
      "Enables the debugging flags specified in $(docv). Every character of \
       $(docv) correspond to a flag. The available values are: %s." descs
  in
  Arg.(value & opt string "" & info ["debug"] ~docv:"FLAGS" ~doc)

let no_colors : bool CLT.t =
  let doc =
    "Disable the use of colors when printing to the terminal. Note that the \
     default behaviour is to rely on ANSI escape sequences in order to make \
     the debugging logs more readable."
  in
  Arg.(value & flag & info ["no-colors"] ~doc)

let record_time : bool CLT.t =
  let doc =
    "Print statistics on the time spent in different tasks (parsing, typing, \
     etc.). Note that it slows down the program."
  in
  Arg.(value & flag & info ["record-time"] ~doc)

let too_long : float CLT.t =
  let doc =
    "Print a warning every time that a command requires more than $(docv) \
     seconds to execute. The command is not interrupted."
  in
  Arg.(value & opt float infinity & info ["too-long"] ~docv:"FLOAT" ~doc)

(** External checker options. *)

let confluence : string option CLT.t =
  let doc =
    "Use the command $(docv) for checking confluence. The command $(docv) \
     should accept HRS-formatted text on its standard input (For more info \
     see http://project-coco.uibk.ac.at/problems/hrs.php) \
     and the first line of its standard output should be either \"YES\", \
     \"NO\" or \"MAYBE\"."
  in
  Arg.(value & opt (some string) None & info ["confluence"] ~docv:"CMD" ~doc)

let termination : string option CLT.t =
  let doc =
    "Use the command $(docv) for checking termination. The command $(docv) \
     should accept XTC-formatted text on its standard input (for more info \
     see https://tinyurl.com/XTC-format), and the first line of its standard \
     output should be either \"YES\", \"NO\" or \"MAYBE\"."
  in
  Arg.(value & opt (some string) None & info ["termination"] ~docv:"CMD" ~doc)

(** Gathering options under a configuration. *)

(** [full] gathers the command line arguments common to most commands. *)
let full : config CLT.t =
  let f gen_obj lib_root map_dir verbose no_warnings debug no_colors
        record_time too_long confluence termination no_sr_check =
    {gen_obj; lib_root; map_dir; verbose; no_warnings; debug; no_colors;
     record_time; too_long; confluence; termination; no_sr_check }
  in
  let open Term in
  const f $ gen_obj $ lib_root $ map_dir $ verbose $ no_warnings $ debug
  $ no_colors $ record_time $ too_long $ confluence $ termination
  $ no_sr_check

(** [minimal] gathers the minimal command line options to enable debugging and
    access to the library root. *)
let minimal : config CLT.t =
  let fn lib_root map_dir verbose debug no_colors =
    { default_config with lib_root ; map_dir ; verbose ; debug ; no_colors }
  in
  CLT.(const fn $ lib_root $ map_dir $ verbose $ debug $ no_colors)
