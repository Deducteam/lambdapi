(** File utilities. *)

open Extra
open Console

(** Logging function for evaluation. *)
let log_file = new_logger 'f' "file" "file system"
let log_file = log_file.logger

(** Representation of module paths and related operations. *)
module Path =
  struct
    (** Representation of a module path (roughly, a file path). *)
    type module_path = string list

    (** Short synonym of [module_path]. *)
    type t = module_path

    (** [compare] is a standard comparing function for module paths. *)
    let compare : t -> t -> int = Pervasives.compare

    (** [pp oc mp] prints [mp] to channel [oc]. *)
    let pp : module_path pp = fun oc mp ->
      Format.pp_print_string oc (String.concat "." mp)
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

    (** [set_root path m] sets the library root of [m] to be [path]. If it was
        already set, the the exception [Already_mapped] is raised. *)
    val set_root : file_path -> t -> t

    (** [add mp path m] extends the mapping [m] by associating the module path
        [mp] to the file path [path]. In the case where [mp] is already mapped
        in [m], the exception [Already_mapped] is raised. *)
    val add : Path.t -> file_path -> t -> t

    (** Exception raised if an attempt is made to use the [get] function prior
        to the root being set (using [set_root]). *)
    exception Root_not_set

    (** [get mp m] obtains the file path corresponding to the module path [mp]
        in [m] (with no particular extension). The exception [Root_not_set] is
        raised if the root of [m] was not previously set with [set_root]. *)
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
let lib_root : string option Pervasives.ref =
  Pervasives.ref None

(** [set_lib_root path] sets the library root to the given file [path]. If the
    given [path] does not refer to a valid (existing) directory the program is
    terminated with a graceful error message. *)
let set_lib_root : string -> unit = fun path ->
  try
    let path = Filename.realpath path in
    if not (Sys.is_directory path) then
      exit_with "Invalid library root ([%s] is not a directory)." path;
    match Pervasives.(!lib_root) with
    | None    -> Pervasives.(lib_root := Some(path))
    | Some(_) -> exit_with "The library root was already set."
  with Sys_error(_) | Invalid_argument(_) ->
    exit_with "Invalid library root (no such file or directory [%s])." path

(** [default_lib_root ()] returns the default library root curently configured
    for the system. It depends on the current Opam switch (if any), and it may
    or may not correspond to an existing directory. *)
let default_lib_root : unit -> string = fun _ ->
  match run_process "opam var lib" with
  | Some([l]) -> Filename.concat l "lambdapi/lib_root"
  | _         -> "/usr/local/lib/lambdapi/lib_root"

(** [lib_root_path ()] returns the canonical library root path. It corresponds
    to a valid path to a directory. The function fails gracefully if it is not
    able to find such a directory. Note that prior to installation, the option
    ["--lib-root"] must be used so that this function does not fail. *)
let lib_root_path : unit -> string = fun _ ->
  match Pervasives.(!lib_root) with Some(path) -> path | None ->
  let path = default_lib_root () in
  try
    let path = Filename.realpath path in
    if not (Sys.is_directory path) then
      exit_with "Invalid default library root [%s] (not a directory)." path;
    path
  with Sys_error(_) | Invalid_argument(_) ->
    exit_with "Default library root [%s] does not exist." path

(** [lib_mappings] stores the specified mappings of library paths. *)
let lib_mappings : ModMap.t Pervasives.ref =
  Pervasives.ref ModMap.empty

(** [init_lib_root ()] registers the currently set library root as part of our
    module mapping. This function MUST be called before one can consider using
    [module_to_file] or [module_path]. *)
let init_lib_root : unit -> unit = fun _ ->
  let root = lib_root_path () in
  Pervasives.(lib_mappings := ModMap.set_root root !lib_mappings)

(** [new_lib_mapping s] attempts to parse [s] as a library mapping of the form
    ["<modpath>:<path>"]. Then, if module path ["<modpath>"] is not yet mapped
    to a file path, and if ["<path>"] corresponds to a valid directory, then a
    new mapping is registered. In case of failure the program terminates and a
    graceful error message is displayed. *)
let new_lib_mapping : string -> unit = fun s ->
  let fail s = exit_with ("Ill-formed argument to \"--map\": " ^^ s ^^ ".") in
  let (module_path, file_path) =
    match String.split_on_char ':' s with
    | [mp; dir] -> (String.split_on_char '.' mp, dir)
    | _         -> fail "bad syntax (use \"--help\")"
  in
  let valid_path_member s =
    if String.length s = 0 then fail "empty module path member";
    for i = 0 to String.length s - 1 do
      match String.get s i with
      | 'a'..'z' | 'A'..'Z' | '_' -> ()
      | '0'..'9' when i <> 0      -> ()
      | _                         -> fail "invalid path member \"%s\"" s
    done
  in
  List.iter valid_path_member module_path;
  let file_path = Filename.realpath file_path in
  let new_mapping =
    try ModMap.add module_path file_path !lib_mappings
    with ModMap.Already_mapped ->
      fail "module path [%a] is already mapped" Path.pp module_path
  in
  Pervasives.(lib_mappings := new_mapping)

(** [current_path ()] returns the canonical running path of the program. *)
let current_path : unit -> string = fun _ ->
  Filename.realpath "."

(** [current_mappings ()] gives the currently registered library mappings. *)
let current_mappings : unit -> ModMap.t = fun _ ->
  Pervasives.(!lib_mappings)

(** [module_to_file mp] converts module path [mp] into the corresponding "file
    path" (with no attached extension). It is assumed that [init_lib_root] was
    called prior to any call to this function. *)
let module_to_file : Path.t -> file_path = fun mp ->
  let path =
    try ModMap.get mp Pervasives.(!lib_mappings) with ModMap.Root_not_set ->
      assert false (* Unreachable after [init_lib_root] is called. *)
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
  if not (List.mem ext [ src_extension ; legacy_src_extension ]) then
    fatal_no_pos "Invalid extension for [%s] (expected [%s] or [%s])." fname
      src_extension legacy_src_extension;
  (* Normalizing the file path. *)
  let fname =
    try Filename.realpath fname with Invalid_argument(_) ->
      fatal_no_pos "No such file or directory [%s]." fname
  in
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
        fatal_no_pos "[%s] cannot be placed under the library mapping." fname
  in
  ignore (mp, path);
  (* Build the module path. *)
  let rest =
    let len_path = String.length path in
    let len_base = String.length base in
    String.sub base (len_path + 1) (len_base - len_path - 1)
  in
  let full_mp = mp @ String.split_on_char '/' rest in
  log_file "File [%s] is module [%a]." fname Path.pp full_mp;
  full_mp

(** [mod_time fname] returns the modification time of file [fname] represented
    as a [float]. [neg_infinity] is returned if the file does not exist. *)
let mod_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime) else neg_infinity

(** [more_recent source target] checks whether the [target] (produced from the
    [source] file) should be produced again. This is the case when [source] is
    more recent than [target]. *)
let more_recent : string -> string -> bool = fun source target ->
  mod_time source > mod_time target
