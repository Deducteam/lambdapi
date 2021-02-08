(** File utilities. *)

open Lplib
open Lplib.Base
open Lplib.Extra

open Timed
open Console

(** Logging function for evaluation. *)
let log_file = new_logger 'f' "file" "file system"
let log_file = log_file.logger

(** Representation of module paths and related operations. *)
module Path =
  struct
    (** Representation of a module path (roughly, a file path). *)
    type mod_path = string list

    (** Short synonym of [mod_path]. *)
    type t = mod_path

    (** [compare] is a standard comparing function for module paths. *)
    let compare : t -> t -> int = Stdlib.compare

    (** [pp oc mp] prints [mp] to channel [oc]. *)
    let pp : mod_path pp = fun oc mp ->
      Format.pp_print_string oc (String.concat "." mp)

    (** [check_simple mp] Checks that [mp] is a “simple” module path, that is,
        that its members are of the form ["[a-zA-Z_][a-zA-Z0-9_]*"]. *)
    let check_simple : t -> unit = fun mod_path ->
      let fail fmt =
        fatal_msg "The (simple) module path [%a] is ill-formed: " pp mod_path;
        fatal_no_pos fmt
      in
      let valid_path_member s =
        if String.length s = 0 then fail "empty module path member.";
        for i = 0 to String.length s - 1 do
          match String.get s i with
          | 'a'..'z' | 'A'..'Z' | '_' -> ()
          | '0'..'9' when i <> 0      -> ()
          | _                         -> fail "invalid path member [%s]." s
        done
      in
      List.iter valid_path_member mod_path

    (** [ghost s] creates a special module path for module of name [s]. Ghost
        modules cannot be handled by the user. *)
    let ghost : string -> t = fun s -> [""; s]
  end

(** Functional maps with module paths as keys. *)
module PathMap = Map.Make(Path)

(** Synonym of [string] for file paths. *)
type file_path = string

(** Representation of the mapping from module paths to files. *)
module ModMap :
  sig
    (** Module path mapping. *)
    type t

    (** [empty] is an empty module path mapping. *)
    val empty : t

    (** Exception raised if an attempt is made to map an already mapped module
        (including the root). *)
    exception Already_mapped

    (** [set_root path m] sets the library root of [m] to be [path].
        @raise Already_mapped if library root of [m] is already set. *)
    val set_root : file_path -> t -> t

    (** [add mp path m] extends the mapping [m] by associating the module path
        [mp] to the file path [path].
        @raise Already_mapped when [mp] is already mapped in [m]. *)
    val add : Path.t -> file_path -> t -> t

    (** Exception raised if an attempt is made to use the [get] function prior
        to the root being set (using [set_root]). *)
    exception Root_not_set

    (** [get mp m] obtains the file path corresponding to the module path [mp]
        in [m] (with no particular extension).
        @raise Root_not_set when the root of [m] has not been set using
        [set_root].  *)
    val get : Path.t -> t -> file_path

    (** [iter fn m] calls function [fn] on every binding stored in [m]. *)
    val iter : (Path.t -> file_path -> unit) -> t -> unit
  end =
  struct
    type t = Node of file_path option * t StrMap.t

    let empty = Node(None, StrMap.empty)

    exception Already_mapped

    let set_root path (Node(po, m)) =
      match po with
      | None    -> Node(Some(path), m)
      | Some(_) -> raise Already_mapped

    let rec singleton ks path =
      match ks with
      | []      -> Node(Some(path), StrMap.empty)
      | k :: ks -> Node(None, StrMap.singleton k (singleton ks path))

    let rec add ks path (Node(po, m)) =
      match (po, ks) with
      | (Some(_), []     ) -> raise Already_mapped
      | (None   , []     ) -> Node(Some(path), m)
      | (_      , k :: ks) ->
          try Node(po, StrMap.add k (add ks path (StrMap.find k m)) m)
          with Not_found -> Node(po, StrMap.add k (singleton ks path) m)

    exception Root_not_set

    let get ks (Node(po, m)) =
      let rec get (root, old_ks) ks m =
        match ks with
        | []      ->
            List.fold_left Filename.concat root old_ks
        | k :: ks ->
            match StrMap.find k m with
            | Node(Some(root), m) -> get (root, ks) ks m
            | Node(None      , m) -> get (root, old_ks) ks m
            | exception Not_found ->
                List.fold_left Filename.concat root old_ks
      in
      match po with
      | None       -> raise Root_not_set
      | Some(root) -> get (root, ks) ks m

    let iter fn m =
      let rec iter path (Node(po, m)) =
        Option.iter (fun file -> fn path file) po;
        StrMap.iter (fun k m -> iter (path @ [k]) m) m
      in
      iter [] m
  end

(** [lib_root] stores the result of the ["--lib-root"] flag when given. *)
let lib_root : string option Stdlib.ref =
  Stdlib.ref None

(** [lib_mappings] stores the specified mappings of library paths. *)
let lib_mappings : ModMap.t ref =
  ref ModMap.empty

(** [set_lib_root path] sets the library root. The following paths are
    set sequentially, such that the active one is the last valid path
    - [/usr/local/lib/lambdapi/lib_root/]
    - [$OPAM_SWITCH_PREFIX/lib/lambdapi/lib_root]
    - [$LAMBDAPI_LIB_ROOT/lib/lambdapi/lib_root]
    - the path given as parameter of the [--lib-root] command line argument;
      if the path given on command line is not a valid (existing) directory,
      the program terminates with a graceful error message. *)
let set_lib_root : string option -> unit = fun path ->
  let open Stdlib in
  let prefix = Stdlib.ref "/usr/local" in
  let set_prefx p = prefix := p in
  Option.iter set_prefx (Sys.getenv_opt "OPAM_SWITCH_PREFIX");
  Option.iter set_prefx (Sys.getenv_opt "LAMBDAPI_LIB_ROOT");
  lib_root := Some(Filename.concat !prefix "lib/lambdapi/lib_root");
  let set_lr p =
    try lib_root := Some(Lplib.Filename.realpath p) with
    Invalid_argument(_) -> ()
  in
  Option.iter set_lr path;
  (* Verify that the path exists and is a directory *)
  match !lib_root with
  | None -> assert false (* Path is set above. *)
  | Some(pth) ->
      begin
        try if not (Sys.is_directory pth) then
            fatal_no_pos "Invalid library root: [%s] is not a directory." pth
        with Sys_error(_) ->
          (* [Sys_error] is raised if [pth] does not exist. *)
          (* We try to create [pth]. *)
          let target = Filename.quote pth in
          let cmd = String.concat " " ["mkdir"; "--parent"; target] in
          begin
            match Sys.command cmd  with
            | 0 -> ()
            | _ ->
                fatal_msg "Library root cannot be set:\n";
                fatal_no_pos "Command \"%s\" had a non-zero exit." cmd
            | exception Failure(msg) ->
                fatal_msg "Library root cannot be set:\n";
                fatal_msg "Command \"%s\" failed:\n" cmd;
                fatal_no_pos "%s" msg
          end
      end;
      (* Register the library root as part of the module mapping.
         Required by [module_to_file] and [mod_path]. *)
      Timed.(lib_mappings := ModMap.set_root pth !lib_mappings)

(** [new_lib_mapping s] attempts to parse [s] as a library mapping of the form
    ["<modpath>:<path>"]. Then, if module path ["<modpath>"] is not yet mapped
    to a file path, and if ["<path>"] corresponds to a valid directory, then a
    new mapping is registered. In case of failure the program terminates and a
    graceful error message is displayed. *)
let new_lib_mapping : string -> unit = fun s ->
  let (mod_path, file_path) =
    match String.split_on_char ':' s with
    | [mp; dir] -> (String.split_on_char '.' mp, dir)
    | _         ->
    fatal_no_pos "Bad syntax for \"--map-dir\" option (expecting MOD:DIR)."
  in
  Path.check_simple mod_path;
  let file_path =
    try Filename.realpath file_path
    with Invalid_argument(f) ->
      fatal_no_pos "new_lib_mapping: %s: No such file or directory" f
  in
  let new_mapping =
    try ModMap.add mod_path file_path !lib_mappings
    with ModMap.Already_mapped ->
      fatal_no_pos "Module path [%a] is already mapped." Path.pp mod_path
  in
  lib_mappings := new_mapping

(** [current_path ()] returns the canonical running path of the program. *)
let current_path : unit -> string = fun _ ->
  Filename.realpath "."

(** [current_mappings ()] gives the currently registered library mappings. *)
let current_mappings : unit -> ModMap.t = fun _ -> !lib_mappings

(** [module_to_file mp] converts module path [mp] into the corresponding "file
    path" (with no attached extension). It is assumed that [lib_root] has been
    set, possibly with [set_lib_root]. *)
let module_to_file : Path.t -> file_path = fun mp ->
  let path =
    try ModMap.get mp !lib_mappings with ModMap.Root_not_set ->
      fatal_no_pos "Library root not set."
  in
  log_file "[%a] points to base name [%s]." Path.pp mp path; path

(** [src_extension] is the expected extension for source files. *)
let src_extension : string = ".lp"

(** [obj_extension] is the expected extension for binary (object) files. *)
let obj_extension : string = ".lpo"

(** [legacy_src_extension] is the extension for legacy source files. *)
let legacy_src_extension : string = ".dk"

(** [file_to_module path] computes the module path that corresponds to [path].
    The file described by [path] is expected to have a valid extension (either
    [src_extension] or the legacy extension [legacy_src_extension]). If [path]
    is invalid, the [Fatal] exception is raised. *)
let file_to_module : string -> Path.t = fun fname ->
  (* Sanity check: source file extension. *)
  let ext = Filename.extension fname in
  let valid_extensions =
    [ src_extension ; legacy_src_extension ; obj_extension ]
  in
  if not (List.mem ext valid_extensions) then
    begin
      fatal_msg "Invalid extension for [%s].\n" fname;
      let pp_exp = List.pp (fun ff -> Format.fprintf ff "[%s]") ", " in
      fatal_no_pos "Expected any of: %a." pp_exp valid_extensions
    end;
  (* Normalizing the file path. *)
  let fname = Filename.normalize fname in
  let base = Filename.chop_extension fname in
  (* Finding the best mapping under the root. *)
  let mapping = ref None in
  let fn mp path =
    if String.is_prefix path base then
      match !mapping with
      | None       -> mapping := Some(mp, path)
      | Some(_, p) -> if String.length p < String.length path then
                        mapping := Some(mp, p)
  in
  ModMap.iter fn (current_mappings ());
  (* Fail if there is none. *)
  let (mp, path) =
    match !mapping with
    | Some(mp, path) -> (mp, path)
    | None           ->
        fatal_msg "[%s] cannot be mapped under the library root.\n" fname;
        fatal_msg "Consider adding a package file under your source tree, ";
        fatal_no_pos "or use the [--map-dir] option."
  in
  (* Build the module path. *)
  let rest =
    let len_path = String.length path in
    let len_base = String.length base in
    String.sub base (len_path + 1) (len_base - len_path - 1)
  in
  let full_mp = mp @ String.split_on_char '/' rest in
  log_file "File [%s] is module [%a]." fname Path.pp full_mp;
  full_mp

let install_path : string -> string = fun fname ->
  let mod_path = file_to_module fname in
  let ext = Filename.extension fname in
  match Stdlib.(!lib_root) with
  | None -> assert false
  | Some(pth) ->
    List.fold_left Filename.concat pth mod_path ^ ext

(** [mod_time fname] returns the modification time of file [fname] represented
    as a [float]. [neg_infinity] is returned if the file does not exist. *)
let mod_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime) else neg_infinity

(** [more_recent source target] checks whether the [target] (produced from the
    [source] file) should be produced again. This is the case when [source] is
    more recent than [target]. *)
let more_recent : string -> string -> bool = fun source target ->
  mod_time source > mod_time target
