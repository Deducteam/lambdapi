(** Functions for creating loggers. **)

open Lplib open Base open Color

(** Type of a logging function. It needs to be boxed for higher-rank
   polymorphism reasons *)
type logger_pp = { pp: 'a. 'a outfmt -> 'a }

(** Type of logging function data. *)
type logger =
  { logger_key : char (** Character used to unable the logger. *)
  ; logger_name : string (** Four-characters name used as prefix in logs. *)
  ; logger_desc : string (** Description of the log displayed in help. *)
  ; logger_enabled : bool ref (** Is the log enabled? *)
  ; logger_pp : logger_pp (** Type of a logging function. *)
  }

(** [loggers] contains the registered logging functions. *)
let loggers : logger list Stdlib.ref = Stdlib.ref []

(** [log_enabled] is the cached result of whether there exists an enabled
   logging function. Its main use is to guard logging operations to avoid
   performing unnecessary computations.*)
let _log_enabled = ref false
let log_enabled () = !_log_enabled
let update_log_enabled () =
  _log_enabled :=
    List.exists (fun logger -> !(logger.logger_enabled)) Stdlib.(!loggers)

(** [make key name desc] registers a new logger and returns its pp. *)
let make logger_key logger_name logger_desc =
  (* Sanity checks. *)
  if String.length logger_name <> 4 then
    invalid_arg "Logger.make: name must be 4 characters long";
  let check data =
    if logger_key  = data.logger_key then
      invalid_arg "Logger.make: key is already used";
    if logger_name = data.logger_name then
      invalid_arg "Logger.make: name is already used"
  in
  List.iter check Stdlib.(!loggers);

  let logger_enabled = ref false in
  (* Actual printing function. *)
  let pp fmt =
    update_with_color Stdlib.(!Error.err_fmt);
    let out = Format.(if !logger_enabled then fprintf else ifprintf) in
    out Stdlib.(!Error.err_fmt) (cya "[%s]" ^^ " @[" ^^ fmt ^^ "@]@.")
      logger_name
  in

  (* Logger registration. *)
  let logger =
    { logger_key ; logger_name
    ; logger_desc ; logger_enabled ; logger_pp = { pp } }
  in
  Stdlib.(loggers := logger :: !loggers);

  logger.logger_pp

(** [set_debug value key] enables or disables the loggers corresponding to
   every character of [str] according to [value]. *)
let set_debug value str =
  let fn { logger_key; logger_enabled; _ } =
    if String.contains str logger_key then logger_enabled := value
  in
  List.iter fn Stdlib.(!loggers);
  update_log_enabled ()

(** [default_loggers] lists the loggers enabled by default, in a string. *)
let default_loggers = Stdlib.ref ""

(** [set_default_debug str] declares the debug flags of [str] to be enabled by
   default. *)
let set_default_debug str =
  Stdlib.(default_loggers := str);
  set_debug true str

(** [get_activated_loggers ()] fetches the list of activated loggers,
      listed in a string *)
let get_activated_loggers () =
  Stdlib.(!loggers)
  |> List.filter_map
    (fun logger ->
       if !(logger.logger_enabled) then
         Some (String.make 1 logger.logger_key)
       else
         None)
  |> String.concat ""

(** [reset_loggers ~default ()] resets the debug flags to those in default.
   Without the optional argument, use [!default_loggers] *)
let reset_loggers ?(default=Stdlib.(! default_loggers)) () =
  let default_value = String.contains default in

  let fn { logger_key; logger_enabled; _ } =
    logger_enabled := default_value logger_key
  in
  List.iter fn Stdlib.(!loggers);
  update_log_enabled ()

(** [log_summary ()] gives the keys and descriptions for logging options. *)
let log_summary () =
  List.map (fun d -> (d.logger_key, d.logger_desc)) Stdlib.(!loggers)
