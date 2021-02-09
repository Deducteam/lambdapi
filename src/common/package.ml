(** Package configuration file interface. *)

open Lplib
open Lplib.Extra

open Module
open Console

(** A package configuration file is expected at the root of every package. The
    file is used to figure out the module path under which the package must be
    placed. This information is also useful for installation. *)

(** Pacage configuration file name. *)
let pkg_file : string = "lambdapi.pkg"

(** Configuration file format (using an example).

==== lambdapi.pkg ============
# only two required fields:
package_name = my_package
root_path    = contrib.my_pack
# comments not at end of line
undefined    = ignored
==============================

*)

(** Configuration data read from a file. *)
type config_data =
  { package_name : string
  ; root_path    : Path.t }

(** [read fname] reads configuration data from the file [fname]. The exception
    [Fatal] is raised in case of error (non-existing file, bad format). *)
let read : string -> config_data = fun fname ->
  (* Obtaining file lines. *)
  let lines =
    let ic =
      try open_in fname with Sys_error(_) ->
        fatal_no_pos "Package file [%s] does not exist." fname
    in
    let lines = input_lines ic in
    close_in ic; lines
  in
  (* Build a dictionary from the lines. *)
  let handle_line dict l =
    (* Spaces at the begining and end of line are ignored. *)
    let l = String.trim l in
    (* Empty lines and comments (lines starting with ['#']) are ignored. *)
    if String.length l = 0 || l.[0] = '#' then dict else
    (* Get key and value (separated by ['=']). *)
    match String.split_on_char '=' l with
    | [k; v] -> (String.trim k, String.trim v) :: dict
    | _      -> fatal_no_pos "Ill-formed package file [%s]." fname
  in
  let dict = List.fold_left handle_line [] lines in
  (* Getting a value given a key. *)
  let get k =
    try List.assoc k dict with Not_found ->
      fatal_no_pos "Ill-formed package file [%s]: missing field [%s]." fname k
  in
  (* Building the configuration. *)
  let package_name = get "package_name" in
  let root_path = Path.of_string (get "root_path") in
  {package_name; root_path}

(** [find_config fname] looks for a configuration file above [fname], which is
    typically a source file or an object file (it can also be a directory). If
    there is no configuration file in the same directory as [fname], then we
    look in the parent directory and so on, up to the root or as long as no
    [Sys_error] is raised. Note that [fname] is first normalized with a call
    to [Filename.realpath]. *)
let find_config : string -> string option = fun fname ->
  let fname = Filename.normalize fname in
  let rec find dir =
    let file = Filename.concat dir pkg_file in
    match Sys.file_exists file with
    | true                   -> Some(file)
    | false                  -> if dir = "/" then None else
                                find (Filename.dirname dir)
    | exception Sys_error(_) -> None
  in
  find fname

(** [apply_config fname] attempts to find a configuration file that applies to
    the (source) file [fname], and applies the corresponding configuration. *)
let apply_config : string -> unit = fun fname ->
  match find_config fname with
  | None           -> ()
  | Some(cfg_file) ->
  let {package_name = _; root_path} = read cfg_file in
  let root = Filename.dirname cfg_file in
  Module.new_lib_mapping (String.concat "." root_path ^ ":" ^ root)
