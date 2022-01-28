(** High-level compilation functions. *)

open Common
open Core

val gen_obj : bool Stdlib.ref
(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not to generate them. *)

val recompile : bool Stdlib.ref
(** [recompile] indicates whether we should recompile files who have an object
    file that is already up to date. Note that this flag only applies to files
    that are given on the command line explicitly, not their dependencies. *)

val compile : bool -> Path.t -> Sign.t
(** [compile force mp] compiles module path [mp] using [compile_with], forcing
    compilation of up-to-date files if [force] is true. *)

val compile_file : string -> Sign.t
(** [compile_file fname] looks for a package configuration file for
    [fname] and compiles [fname]. It is the main compiling function. It
    is called from the main program exclusively. *)

(** /!\ For testing only. Pure wrappers around compilation functions. The
   provided functions perform the same computations as the ones defined above,
   but restore the state when they have finished. An optional library mapping
   or state can be passed as argument to change the settings. *)
val pure_compile :
  ?lm:Path.t*string -> ?st:Console.State.t -> bool -> Path.t -> Sign.t
val pure_compile_file :
  ?lm:Path.t*string -> ?st:Console.State.t -> string -> Sign.t
