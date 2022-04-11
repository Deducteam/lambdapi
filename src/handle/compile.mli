(** High-level compilation functions. *)

open Common
open Core

val gen_obj : bool Stdlib.ref
(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not to generate them. *)

val compile : ?force:bool -> Path.t -> Sign.t
(** [compile force mp] compiles module path [mp], forcing
    recompilation of up-to-date files if [force] is true. *)

val compile_file : ?force:bool -> string -> Sign.t
(** [compile_file force fname] looks for a package configuration file for
   [fname] and compiles [fname], forcing recompilation of up-to-date files if
   [force] is true. It is the main compiling function. It is called from the
   main program exclusively. *)

(** The functions provided in this module perform the same computations as the
   ones defined earlier, but restore the console state and the library
   mappings when they have finished. An optional library mapping or console
   state can be passed as argument to change the settings. *)
module PureUpToSign : sig
  val compile :
  ?lm:Path.t*string -> ?st:Console.State.t -> ?force:bool -> Path.t -> Sign.t
  val compile_file :
  ?lm:Path.t*string -> ?st:Console.State.t -> ?force:bool -> string -> Sign.t
end
