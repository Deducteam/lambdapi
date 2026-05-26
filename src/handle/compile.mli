(** High-level compilation functions. *)

open Common
open Core

val gen_obj : bool Stdlib.ref
(** [gen_obj] indicates whether we should generate object files when compiling
    source files. The default behaviour is not to generate them. *)

val compile : Path.t -> Sign.t
(** [compile mp] returns the signature associated to [mp]. *)

val compile_file : string -> Sign.t
(** [compile_file fname] looks for a package configuration file for
   [fname] and returns the signature associated to it [fname]. *)
