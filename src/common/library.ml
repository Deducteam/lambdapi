(** Lambdapi library management. *)

open Lplib
open Lplib.Base
open Lplib.Extra
open Timed
open Error
open Debug

let log_lib = Logger.make 'l' "libr" "library files"
let log_lib = log_lib.pp

(** Representation of the mapping from module paths to files. *)
module LibMap :
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
    val add : Path.t -> string -> t -> t

    (** Exception raised if an attempt is made to use the [get] function prior
        to the root being set (using [set_root]). *)
    exception Root_not_set

    (** [get mp map] obtains the filename corresponding to the module path
       [mp] in [map] (with no particular extension).
       @raise Root_not_set when the root of [map] has not been set using
       [set_root].  *)
    val get : Path.t -> t -> string

    (** [iter f map] calls function [f] on every binding stored in [map]. *)
    val iter : (Path.t -> string -> unit) -> t -> unit

    (** [pp ppf t] prints [t] on formatter [ppf] (for debug). *)
    val pp : t pp
  end =
  struct
    type t = Node of string option * t StrMap.t

    let rec pp ppf (Node(po, map)) =
      out ppf "Node(%a,%a)"
        (D.option D.string) po (D.strmap pp) map

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
          try Node(po, StrMap.add k (add ks fp (StrMap.find k map)) map)
          with Not_found -> Node(po, StrMap.add k (singleton ks fp) map)

    exception Root_not_set

    let get ks (Node(po, map)) =
      let concat root ks =
        List.fold_left Filename.concat root ks in
      let rec get (root, old_ks) ks map =
        if Logger.log_enabled () then
          log_lib "get @[<hv>\"%s\"@ [%a]@ [%a]@ %a@]" root
            (D.list D.string) old_ks (D.list D.string) ks (D.strmap pp) map;
        match ks with
        | []      -> concat root old_ks
        | k :: ks ->
            match StrMap.find k map with
            | Node(Some(root), map) -> get (root, ks) ks map
            | Node(None      , map) -> get (root, old_ks) ks map
            | exception Not_found -> concat root old_ks
      in
      match po with
      | None       -> raise Root_not_set
      | Some(root) -> get (root, ks) ks map

    let iter f map =
      let rec iter ks (Node(po, map)) =
        Option.iter (fun fp -> f ks fp) po;
        StrMap.iter (fun k m -> iter (ks @ [k]) m) map
      in
      iter [] map
  end

(** [lib_root] stores the result of the ["--lib-root"] flag when given. *)
let lib_root : string option Stdlib.ref = Stdlib.ref None

(** [lib_mappings] stores the specified mappings of library paths. *)
let lib_mappings : LibMap.t ref = ref LibMap.empty

(** [iter f] iterates [f] on current mappings. *)
let iter : (Path.t -> string -> unit) -> unit = fun f ->
  LibMap.iter f !lib_mappings

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
              fatal_msg "Library root cannot be set:@.";
              fatal_no_pos "Command \"%s\" had a non-zero exit." cmd
          | exception Failure msg ->
              fatal_msg "Library root cannot be set:@.";
              fatal_msg "Command \"%s\" failed:@." cmd;
              fatal_no_pos "%s" msg
      end;
      (* Register the library root as part of the module mapping.
         Required by [module_to_file]. *)
      Timed.(lib_mappings := LibMap.set_root pth !lib_mappings)

(** [add_mapping (mn, fn)] adds a new mapping from the module name [mn] to
   the file name [fn] if [mn] is not already mapped and [fn] is a valid
   directory. In case of failure the program terminates and a graceful error
   message is displayed. *)
let add_mapping : Path.t * string -> unit = fun (mp, fn) ->
  let fn =
    try Filename.realpath fn
    with Invalid_argument f -> fatal_no_pos "%s: No such file or directory" f
  in
  let new_mapping =
    try LibMap.add mp fn !lib_mappings
    with LibMap.Already_mapped ->
      fatal_no_pos "Module path [%a] is already mapped." Path.pp mp
  in
  lib_mappings := new_mapping

(** [file_of_path mp] converts module path [mp] into the corresponding "file
    path" (with no attached extension). It is assumed that [lib_root] has been
    set, possibly with [set_lib_root]. *)
let file_of_path : Path.t -> string = fun mp ->
  let mp = List.map Escape.unescape mp in
  try
    let fp = LibMap.get mp !lib_mappings in
    if Logger.log_enabled () then
      log_lib "file_of_path @[<hv>%a@ %a@ = \"%s\"@]"
        Path.pp mp LibMap.pp !lib_mappings fp;
    fp
  with LibMap.Root_not_set -> fatal_no_pos "Library root not set."

(** [lp_src_extension] is the expected extension for source files. *)
let lp_src_extension : string = ".lp"

(** [dk_src_extension] is the extension for dk source files. *)
let dk_src_extension : string = ".dk"

(** [is_valid_src_extension s] returns [true] iff [s] ends with
   [lp_src_extension] or [dk_src_extension]. *)
let is_valid_src_extension : string -> bool = fun s ->
  Filename.check_suffix s lp_src_extension
  || Filename.check_suffix s dk_src_extension

(** [obj_extension] is the expected extension for binary (object) files. *)
let obj_extension : string = ".lpo"

(** [valids_extensions] is the list of valid file extensions. *)
let valid_extensions : string list =
  [lp_src_extension; dk_src_extension; obj_extension]

(** [path_of_file escape fname] computes the module path that corresponds to
   the filename [fname]. [escape] converts irregular path elements into
   escaped identifiers if needed.
@raise [Fatal] if [fn] doesn't have a valid extension. *)
let path_of_file : (string -> string) -> string -> Path.t =
  fun escape fname ->
  (* Sanity check: source file extension. *)
  let ext = Filename.extension fname in
  if not (List.mem ext valid_extensions) then
    begin
      fatal_msg "Invalid extension for [%s].@." fname;
      let exp = List.pp (fun ppf -> out ppf "[%s]") ", " in
      fatal_no_pos "Expected any of: %a." exp valid_extensions
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
  LibMap.iter f !lib_mappings;
  (* Fail if there is none. *)
  let (mp, fp) =
    match !mapping with
    | Some(mp, fp) -> (mp, fp)
    | None           ->
        fatal_msg "%s cannot be mapped under the library root.@." fname;
        fatal_msg "Consider adding a package file under your source tree, ";
        fatal_no_pos "or use the [--map-dir] option."
  in
  (* Build the module path. *)
  let rest =
    let len_fp = String.length fp in
    let len_base = String.length base in
    String.sub base (len_fp + 1) (len_base - len_fp - 1)
  in
  let full_mp = mp @ List.map escape (String.split_on_char '/' rest) in
  log_lib "path_of_file @[<hv>\"%s\"@ = %a@]" fname Path.pp full_mp;
  full_mp

(** [install_path fname] prefixes the filename [fname] by the path to the
   library root. *)
let install_path : string -> string = fun fname ->
  let mp = path_of_file (fun s -> s) fname in
  let ext = Filename.extension fname in
  match Stdlib.(!lib_root) with
  | None -> assert false
  | Some(p) -> List.fold_left Filename.concat p mp ^ ext
