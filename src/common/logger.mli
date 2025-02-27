(** Functions for creating loggers. **)

open Lplib open Base

(** [log_enabled] is the cached result of whether there exists an enabled
   logging function. Its main use is to guard logging operations to avoid
   performing unnecessary computations.*)
val log_enabled : unit -> bool

(** Type of a logging function. It needs to be boxed for higher-rank
   polymorphism reasons *)
type logger_pp = { pp: 'a. 'a outfmt -> 'a }

(** [make key name desc] registers a new logger and returns its pp. *)
val make : char -> string -> string -> logger_pp

(** [set_debug value key] enables or disables the loggers corresponding to
   every character of [str] according to [value]. *)
val set_debug : bool -> string -> unit

(** [set_default_debug str] declares the debug flags of [str] to be enabled by
   default. *)
val set_default_debug : string -> unit

(** [get_activated_loggers ()] fetches the list of activated loggers, listed
   in a string *)
val get_activated_loggers : unit -> string

(** [reset_loggers ()] resets the debug flags to those by default. *)
val reset_loggers : ?default:string -> unit -> unit

(** [log_summary ()] gives the keys and descriptions for logging options. *)
val log_summary : unit -> (char * string) list

(** [set_debug_in s b f] sets the loggers in [s] to [b] to evaluate [f()]. *)
val set_debug_in : string -> bool -> (unit -> 'a) -> 'a
