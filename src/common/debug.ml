open Lplib.Base
open Lplib.Extra
open Timed

(** Type of a logging function. *)
type logger = { logger : 'a. 'a outfmt -> 'a }

(** Type of logging function data. *)
type logger_data =
  { logger_key     : char     (** Character used to unable the logger.      *)
  ; logger_name    : string   (** 4 character name used as prefix in logs.  *)
  ; logger_desc    : string   (** Description of the log displayed in help. *)
  ; logger_enabled : bool ref (** Is the log enabled? *) }

(** [log_enabled] is (automatically) set to true by {!val:set_debug} or
    functions of {!module:State} when some logging functions may print
    messages. Its main use is to guard logging operations to avoid performing
    unnecessary computations. *)
let log_enabled : bool ref = ref false

(** [loggers] constains the registered logging functions. *)
let loggers : logger_data list Stdlib.ref = Stdlib.ref []

(** [default_loggers] give the loggers enabled by default. *)
let default_loggers : string Stdlib.ref = Stdlib.ref ""

(** [log_summary ()] gives the keys and descriptions for logging options. *)
let log_summary : unit -> (char * string) list = fun () ->
  let fn data = (data.logger_key, data.logger_desc) in
  let compare (c1, _) (c2, _) = Char.compare c1 c2 in
  List.sort compare (List.map fn Stdlib.(!loggers))

(** [set_log value key] enables or disables the loggers corresponding to every
    character of [str] according to [value]. *)
let set_debug : bool -> string -> unit = fun value str ->
  let fn {logger_key; logger_enabled; _} =
    if String.contains str logger_key then logger_enabled := value
  in
  List.iter fn Stdlib.(!loggers);
  let is_enabled data = !(data.logger_enabled) in
  log_enabled := List.exists is_enabled Stdlib.(!loggers)

(** [set_default_debug str] declares the debug flags of [str] to be enabled by
    default. *)
let set_default_debug : string -> unit = fun str ->
  Stdlib.(default_loggers := str); set_debug true str

(** [new_logger key name desc] returns (and registers) a new logger. *)
let new_logger : char -> string -> string -> logger = fun key name desc ->
  (* Sanity checks. *)
  if String.length name <> 4 then
    invalid_arg "Console.new_logger: name must be 4 characters long";
  let check data =
    if key = data.logger_key then
      invalid_arg "Console.new_logger: already used key";
    if name = data.logger_name then
      invalid_arg "Console.new_logger: already used name"
  in
  List.iter check Stdlib.(!loggers);
  (* Logger registration. *)
  let enabled = ref false in
  let data =
    { logger_key = key ; logger_name = name
    ; logger_desc = desc ; logger_enabled = enabled }
  in
  let cmp_loggers l1 l2 = Char.compare l1.logger_key l2.logger_key in
  Stdlib.(loggers := List.sort cmp_loggers (data :: !loggers));
  (* Actual printing function. *)
  let logger fmt =
    let pp = Format.(if !enabled then fprintf else ifprintf) in
    pp Stdlib.(!Error.err_fmt) ((cya "[%s] ") ^^ fmt ^^ "\n%!") name
  in
  {logger}

(** Logging function for command handling. *)
let logger_hndl = new_logger 'h' "hndl" "command handling"
let log_hndl = logger_hndl.logger

(** To print time data. *)
let do_print_time = ref true

(** Print current time. *)
let print_time : string -> unit = fun s ->
  if !do_print_time && !log_enabled then log_hndl "@%f %s" (Sys.time()) s

(** [time_of f x] computes [f x] and the time for computing it. *)
let time_of : (unit -> 'b) -> 'b = fun f ->
  if !do_print_time && !log_enabled then
      let t0 = Sys.time() in
      try let y = f () in log_hndl "%f" (Sys.time() -. t0); y
      with e -> log_hndl "%f" (Sys.time() -. t0); raise e
  else f ()

(** Printing functions. *)
module D = struct

  let string ppf s = Format.fprintf ppf "%S" s

  let option elt ppf o =
    match o with
    | None -> Format.fprintf ppf "None"
    | Some x -> Format.fprintf ppf "Some(%a)" elt x

  let list elt ppf l =
    let out fmt = Format.fprintf ppf fmt in
    out "["; let f x = out "%a;" elt x in List.iter f l; out "]"

  let map iter key sep1 elt sep2 ppf m =
    let out fmt = Format.fprintf ppf fmt in
    let f k t = out "%a%s%a%s" key k sep1 elt t sep2 in
    out "["; iter f m; out "]"

  let strmap elt = map StrMap.iter string "," elt ";"

end
