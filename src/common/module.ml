(** File utilities. *)

open Lplib
open Lplib.Base
open Lplib.Extra

open Timed
open Console

(** Logging function for evaluation. *)
let log_file = new_logger 'f' "file" "file system"
let log_file = log_file.logger

(** Representation of module names and related operations. *)
module Mod =
  struct
    (** Representation of a module name (roughly, a file path). *)
    type t = string list

    (** [compare] is a standard comparing function for module names. *)
    let compare : t -> t -> int = Stdlib.compare

    (** [pp ppf mp] prints [mp] on formatter [ppf]. *)
    let pp : t pp = fun ppf mp ->
      Format.pp_print_string ppf (String.concat "." mp)

    (** [ghost s] creates a special module of name [s] that cannot be handled
       by users. *)
    let ghost : string -> t = fun s -> [""; s]

    (** [of_string s] converts a string [s] lexed as qid into a path. *)
    let of_string : string -> t = Escape.split '.'
  end

(** Functional maps with module names as keys. *)
module ModMap = Map.Make(Mod)

(** Representation of the mapping from module paths to files. *)
module PathMap :
  sig
    (** Module path mapping. *)
    type t

    (** [empty] is an empty module path mapping. *)
    val empty : t

    (** Exception raised if an attempt is made to map an already mapped module
        (including the root). *)
    exception Already_mapped

    (** [set_root dir m] sets the library root of [m] to be [dir].
        @raise Already_mapped if library root of [m] is already set. *)
    val set_root : string -> t -> t

    (** [add mp fp map] extends the mapping [map] by associating the module
       path [mp] to the file path [fp].
       @raise Already_mapped when [mp] isalready mapped in [m]. *)
    val add : Mod.t -> string -> t -> t

    (** Exception raised if an attempt is made to use the [get] function prior
        to the root being set (using [set_root]). *)
    exception Root_not_set

    (** [get mp map] obtains the filename corresponding to the module path
       [mp] in [map] (with no particular extension).
       @raise Root_not_set when the root of [map] has not been set using
       [set_root].  *)
    val get : Mod.t -> t -> string

    (** [iter f map] calls function [f] on every binding stored in [map]. *)
    val iter : (Mod.t -> string -> unit) -> t -> unit

    (** [pp ppf t] prints [t] on formatter [ppf] (for debug). *)
    val pp : t pp
  end =
  struct
    type t = Node of string option * t StrMap.t

    let rec pp ppf (Node(po, map)) =
      let out fmt = Format.fprintf ppf fmt in
      out "Node(";
      (match po with None -> out "None" | Some p -> out "Some%S" p);
      out ",[";
      let f k t = out "(%S,%a);" k pp t in
      StrMap.iter f map;
      out "])"

    let empty = Node(None, StrMap.empty)

    exception Already_mapped

    let set_root dir (Node(po, map)) =
      match po with
      | None    -> Node(Some(dir), map)
      | Some(_) -> raise Already_mapped

    let rec singleton ks fp =
      match ks with
      | []      -> Node(Some(fp), StrMap.empty)
      | k :: ks -> Node(None, StrMap.singleton k (singleton ks fp))

    let rec add ks fp (Node(po, map)) =
      match (po, ks) with
      | (Some(_), []     ) -> raise Already_mapped
      | (None   , []     ) -> Node(Some(fp), map)
      | (_      , k :: ks) ->
          let k' = Escape.unescape k in
          try Node(po, StrMap.add k' (add ks fp (StrMap.find k' map)) map)
          with Not_found -> Node(po, StrMap.add k' (singleton ks fp) map)

    exception Root_not_set

    let get ks (Node(po, map)) =
      let concat root ks =
        List.fold_left Filename.concat root (List.map Escape.unescape ks) in
      let rec get (root, old_ks) ks map =
        match ks with
        | []      -> concat root old_ks
        | k :: ks ->
            let k' = Escape.unescape k in
            match StrMap.find k' map with
            | Node(Some(root), map) -> get (root, ks) ks map
            | Node(None      , map) -> get (root, old_ks) ks map
            | exception Not_found -> concat root old_ks
      in
      match po with
      | None       -> raise Root_not_set
      | Some(root) -> get (root, ks) ks map

    let iter f map =
      let rec iter mp (Node(po, map)) =
        Option.iter (fun fp -> f mp fp) po;
        StrMap.iter (fun k m -> iter (mp @ [k]) m) map
      in
      iter [] map
  end

(** [lib_root] stores the result of the ["--lib-root"] flag when given. *)
let lib_root : string option Stdlib.ref = Stdlib.ref None

(** [lib_mappings] stores the specified mappings of library paths. *)
let lib_mappings : PathMap.t ref = ref PathMap.empty

(** [set_lib_root dir] sets the library root to directory [dir].
    The following directories are set sequentially, such that the active one
    is the last valid one
    - [/usr/local/lib/lambdapi/lib_root/]
    - [$OPAM_SWITCH_PREFIX/lib/lambdapi/lib_root]
    - [$LAMBDAPI_LIB_ROOT/lib/lambdapi/lib_root]
    - the directory given as parameter of the [--lib-root] command line
      argument.
    If the directory given on command line is not a valid existing directory,
    the program terminates with a graceful error message. *)
let set_lib_root : string option -> unit = fun dir ->
  let open Stdlib in
  let prefix = Stdlib.ref "/usr/local" in
  let set_prefix p = prefix := p in
  Option.iter set_prefix (Sys.getenv_opt "OPAM_SWITCH_PREFIX");
  Option.iter set_prefix (Sys.getenv_opt "LAMBDAPI_LIB_ROOT");
  lib_root := Some(Filename.concat !prefix "lib/lambdapi/lib_root");
  let set_lr p =
    try lib_root := Some(Lplib.Filename.realpath p) with
    Invalid_argument(_) -> ()
  in
  Option.iter set_lr dir;
  (* Verify that [dir] exists and is a directory *)
  match !lib_root with
  | None -> assert false (* pth is set above. *)
  | Some(pth) ->
      begin
        try if not (Sys.is_directory pth) then
            fatal_no_pos "Invalid library root: [%s] is not a directory." pth
        with Sys_error(_) ->
          (* [Sys_error] is raised if [pth] does not exist. *)
          (* We try to create [pth]. *)
          let target = Filename.quote pth in
          let cmd = String.concat " " ["mkdir"; "--parent"; target] in
          match Sys.command cmd with
          | 0 -> ()
          | _ ->
              fatal_msg "Library root cannot be set:\n";
              fatal_no_pos "Command \"%s\" had a non-zero exit." cmd
          | exception Failure(msg) ->
              fatal_msg "Library root cannot be set:\n";
              fatal_msg "Command \"%s\" failed:\n" cmd;
              fatal_no_pos "%s" msg
      end;
      (* Register the library root as part of the module mapping.
         Required by [module_to_file]. *)
      Timed.(lib_mappings := PathMap.set_root pth !lib_mappings)

(** [new_lib_mapping s] attempts to parse [s] as a library mapping of the form
   ["<mod_path>:<file_path>"]. Then, if module path ["<mod_path>"] is not yet
   mapped to a file path, and if ["<file_path>"] corresponds to a valid
   directory, then a new mapping is registered. In case of failure the program
   terminates and a graceful error message is displayed. *)
let new_lib_mapping : string -> unit = fun s ->
  let (mod_path, file_path) =
    match Escape.split ':' s with
    | [mp; fp] -> (Mod.of_string mp, Escape.unescape fp)
    | _ ->
    fatal_no_pos "Bad syntax for \"--map-dir\" option (expecting MOD:DIR)."
  in
  let file_path =
    try Filename.realpath file_path
    with Invalid_argument(f) ->
      fatal_no_pos "new_lib_mapping: %s: No such file or directory" f
  in
  let new_mapping =
    try PathMap.add mod_path file_path !lib_mappings
    with PathMap.Already_mapped ->
      fatal_no_pos "Module path [%a] is already mapped." Mod.pp mod_path
  in
  lib_mappings := new_mapping

(** [current_mappings ()] gives the currently registered library mappings. *)
let current_mappings : unit -> PathMap.t = fun _ -> !lib_mappings

(** [file_of_mod mp] converts module path [mp] into the corresponding "file
    path" (with no attached extension). It is assumed that [lib_root] has been
    set, possibly with [set_lib_root]. *)
let file_of_mod : Mod.t -> string = fun mp ->
  let fp =
    try
      let res = PathMap.get mp !lib_mappings in
      if !log_enabled then
        log_file "file_of_mod %a %a -> %S"
          Mod.pp mp PathMap.pp !lib_mappings res;
      res
    with PathMap.Root_not_set -> fatal_no_pos "Library root not set."
  in
  log_file "[%a] points to base name [%s]." Mod.pp mp fp; fp

(** [src_extension] is the expected extension for source files. *)
let src_extension : string = ".lp"

(** [obj_extension] is the expected extension for binary (object) files. *)
let obj_extension : string = ".lpo"

(** [legacy_src_extension] is the extension for legacy source files. *)
let legacy_src_extension : string = ".dk"

(** [valids_extensions] is the list of valid file extensions. *)
let valid_extensions : string list =
  [src_extension; legacy_src_extension; obj_extension]

(** [mod_of_file path] computes the module path that corresponds to [path].
    The file described by [path] is expected to have a valid extension (either
    [src_extension] or the legacy extension [legacy_src_extension]). If [path]
    is invalid, the [Fatal] exception is raised. *)
let mod_of_file : string -> Mod.t = fun fname ->
  (* Sanity check: source file extension. *)
  let ext = Filename.extension fname in
  if not (List.mem ext valid_extensions) then
    begin
      fatal_msg "Invalid extension for [%s].\n" fname;
      let pp_exp = List.pp (fun ppf -> Format.fprintf ppf "[%s]") ", " in
      fatal_no_pos "Expected any of: %a." pp_exp valid_extensions
    end;
  (* Normalizing the file path. *)
  let fname = Filename.normalize fname in
  let base = Filename.chop_extension fname in
  (* Finding the best mapping under the root. *)
  let mapping = ref None in
  let f mp fp =
    if String.is_prefix fp base then
      match !mapping with
      | None       -> mapping := Some(mp, fp)
      | Some(_, p) ->
          if String.(length p < length fp) then mapping := Some(mp, p)
  in
  PathMap.iter f (current_mappings ());
  (* Fail if there is none. *)
  let (mp, fp) =
    match !mapping with
    | Some(mp, fp) -> (mp, fp)
    | None           ->
        fatal_msg "[%s] cannot be mapped under the library root.\n" fname;
        fatal_msg "Consider adding a package file under your source tree, ";
        fatal_no_pos "or use the [--map-dir] option."
  in
  (* Build the module path. *)
  let rest =
    let len_fp = String.length fp in
    let len_base = String.length base in
    String.sub base (len_fp + 1) (len_base - len_fp - 1)
  in
  let full_mp = mp @ String.split_on_char '/' rest in
  log_file "File [%s] is module [%a]." fname Mod.pp full_mp;
  full_mp

let install_path : string -> string = fun fname ->
  let mp = mod_of_file fname in
  let ext = Filename.extension fname in
  match Stdlib.(!lib_root) with
  | None -> assert false
  | Some(p) -> List.fold_left Filename.concat p mp ^ ext
