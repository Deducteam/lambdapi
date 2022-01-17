(** Define a ghost signature that contain symbols used by the kernel
    but not defined by the user. *)

open Timed
open Term
open Lplib
open Extra
open Common

(** The signature holding ghost symbols. *)
let sign =
  (* a path that's not in the image of the parser *)
  let path = [ ""; "ghost" ] in
  let sign = { (Sign.dummy ()) with sign_path = path } in
  Sign.loaded := Path.Map.add path sign !(Sign.loaded);
  sign

(** The path of the ghost signature *)
let path = sign.sign_path

(** [mem s] returns [true] if [s] is a ghost symbol. *)
let mem s = StrMap.mem s.sym_name !(sign.sign_symbols)

(** [iter f] iters function [f] on ghost symbols. *)
let iter : (sym -> unit) -> unit = fun f ->
  StrMap.iter (fun _ s -> f s) !(sign.sign_symbols)
