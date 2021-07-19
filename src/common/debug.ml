open Lplib.Base
open Lplib.Extra
open Timed

module Logger : sig
  (** [log_enabled] is the cached result of whether there exists
    an enabled logging function. Its main use is to guard logging operations
    to avoid performing unnecessary computations.*)
  val log_enabled : unit -> bool

  (** Type of a logging function.
      It needs to be boxed for higher-rank polymorphism reasons *)
  type logger_pp = { pp: 'a. 'a outfmt -> 'a }

  (** [make key name desc] registers a new logger and returns its pp. *)
  val make : char -> string -> string -> logger_pp

  (** [set_debug value key] enables or disables the loggers corresponding to
     every character of [str] according to [value]. *)
  val set_debug : bool -> string -> unit

  (** [set_default_debug str] declares the debug flags of [str] to be enabled
     by default. *)
  val set_default_debug : string -> unit

  (** [get_activated_loggers ()] fetches the list of activated loggers,
      listed in a string *)
  val get_activated_loggers : unit -> string

  (** [reset_loggers ()] resets the debug flags to those by default. *)
  val reset_loggers : ?default:string -> unit -> unit

  (** [log_summary ()] gives the keys and descriptions for logging options. *)
  val log_summary : unit -> (char * string) list
end = struct

  (** Type of a logging function.
      It needs to be boxed for higher-rank polymorphism reasons *)
  type logger_pp = { pp: 'a. 'a outfmt -> 'a }

  (** Type of logging function data. *)
  type logger =
    { logger_key : char (** Character used to unable the logger. *)
    ; logger_name : string (** Four-characters name used as prefix in logs. *)
    ; logger_desc : string (** Description of the log displayed in help. *)
    ; logger_enabled : bool ref (** Is the log enabled? *)
    ; logger_pp : logger_pp (** Type of a logging function. *)
    }

  module List = List


  (** [loggers] contains the registered logging functions. *)
  let loggers : logger list Stdlib.ref = Stdlib.ref []


  (** [log_enabled] is the cached result of whether there exists
      an enabled logging function. Its main use is to guard logging operations
      to avoid performing unnecessary computations.*)
  let _log_enabled = ref false
  let log_enabled () = !_log_enabled
  let update_log_enabled () =
    _log_enabled :=
      List.exists (fun logger -> !(logger.logger_enabled)) Stdlib.(!loggers)


  (** [make key name desc] registers a new logger and returns its pp. *)
  let make logger_key logger_name logger_desc =
      (* Sanity checks. *)
      if String.length logger_name <> 4 then
        invalid_arg "Debug.Logger.make: name must be 4 characters long";
      let check data =
        if logger_key  = data.logger_key then
          invalid_arg "Debug.Logger.make: key is already used";
        if logger_name = data.logger_name then
          invalid_arg "Debug.Logger.make: name is already used"
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

  (** [set_default_debug str] declares the debug flags of [str] to be enabled
     by default. *)
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
end

(** Printing functions. *)
module D = struct

  let ignore : 'a pp = fun _ _ -> ()

  let log_and_return logger el = logger el; el

  let log_and_raise logger exc = logger exc; raise exc

  let depth : int pp = fun ppf l ->
    for _i = 1 to l do out ppf " " done; out ppf "%d. " l

  let bool : bool pp = fun ppf b -> out ppf "%B" b

  let int : int pp = fun ppf i -> out ppf "%d" i

  let string : string pp = fun ppf s -> out ppf "%S" s

  let option : 'a pp -> 'a option pp = fun elt ppf o ->
    match o with
    | None -> out ppf "None"
    | Some x -> out ppf "Some(%a)" elt x

  let pair : 'a pp -> 'b pp -> ('a * 'b) pp = fun elt1 elt2 ppf (x1,x2) ->
    out ppf "%a,%a" elt1 x1 elt2 x2

  let list : 'a pp -> 'a list pp = fun elt ppf l ->
    match l with
    | [] -> out ppf "[]"
    | x::l ->
      out ppf "[%a" elt x;
      let f x = out ppf "; %a" elt x in
      List.iter f l;
      out ppf "]"

  let array : 'a pp -> 'a array pp = fun elt ppf a ->
    let n = Array.length a in
    if n = 0 then out ppf "[]"
    else begin
      out ppf "[%a" elt a.(0);
      for i = 1 to n-1 do out ppf "; %a" elt a.(i) done;
      out ppf "]"
    end

  let map : (('key -> 'elt -> unit) -> 'map -> unit)
    -> 'key pp -> string -> 'elt pp -> string -> 'map pp =
    fun iter key sep1 elt sep2 ppf m ->
    let f k t = out ppf "%a%s%a%s" key k sep1 elt t sep2 in
    out ppf "["; iter f m; out ppf "]"

  let strmap : 'a pp -> 'a StrMap.t pp = fun elt ->
    map StrMap.iter string ", " elt "; "

  let iter ?sep:(pp_sep = Format.pp_print_cut) iter pp_elt ppf v =
    let is_first = ref true in
    let pp_elt v =
      if !is_first then (is_first := false) else pp_sep ppf ();
      pp_elt ppf v
    in
    iter pp_elt v

  (* To be used in a hov (and not default) box *)
  let surround beg fin inside =
    fun fmt v -> Format.fprintf fmt "%s@;<0 2>@[<hv>%a@]@,%s" beg inside v fin

  let bracket inside = surround "[" "]" inside

end

(** Logging function for command handling. *)

(* The two successive let-bindings are necessary for type variable
   generalisation purposes *)
let log_hndl = Logger.make 'h' "hndl" "command handling"
let log_hndl = log_hndl.pp

(** To print time data. *)
let do_print_time = ref false

(** Print current time. *)
let print_time : string -> unit = fun s ->
  if !do_print_time && Logger.log_enabled () then
    log_hndl "@%f %s" (Sys.time()) s

(** [time_of f x] computes [f x] and the time for computing it. *)
let time_of : (unit -> 'b) -> 'b = fun f ->
  if !do_print_time && Logger.log_enabled () then begin
    let t0 = Sys.time () in
    try f () |> D.log_and_return (fun _ -> log_hndl "%f" (Sys.time () -. t0))
    with e ->
      e |> D.log_and_raise  (fun _ -> log_hndl "%f" (Sys.time () -. t0))
  end else f ()
