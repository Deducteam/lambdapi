(** File utilities. *)

open Console

(** [src_extension] is the expected extension for source files. *)
let src_extension : string = ".dk"

(** [obj_extension] is the expected extension for binary (object) files. *)
let obj_extension : string = ".dko"

(** Representation of a module path (roughly, a file path). *)
type module_path = string list

(** [module_path path] computes the [module_path] corresponding to a (relatve)
    file [path], which should not use [".."]. The returned list is formed with
    the subdirectories along the [path], and it is terminated by the file name
    (without extension). Although it is removed, the extension should be given
    on the file name, and it should correspond to [src_extension]. When [path]
    is invalid, [Invalid_argument "invalid module path"] is raised. *)
let module_path : string -> module_path = fun fname ->
  let check p = if not p then invalid_arg "invalid module path" in
  check (Filename.check_suffix fname src_extension);
  check (Filename.is_relative fname);
  let base = Filename.chop_extension (Filename.basename fname) in
  let dir = Filename.dirname fname in
  check (dir <> Filename.parent_dir_name);
  let rec build_path acc dir =
    let dirbase = Filename.basename dir in
    let dirdir  = Filename.dirname  dir in
    check (dirdir <> Filename.parent_dir_name);
    if dirbase = Filename.current_dir_name then acc
    else build_path (dirbase::acc) dirdir
  in
  build_path [base] dir

(** [mod_time fname] returns the modification time of file [fname] represented
    as a [float]. [neg_infinity] is returned if the file does not exist. *)
let mod_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime) else neg_infinity

(** [binary_time] is the modification time of the compiled program. *)
let binary_time : float = mod_time "/proc/self/exe"

(** [more_recent source target] checks whether the [target] (produced from the
    [source] file) should be produced again. This is the case when [source] is
    more recent than [target] or when the binary of the program is more recent
    than [target]. *)
let more_recent : string -> string -> bool = fun source target ->
  let s_time = mod_time source in
  let t_time = mod_time target in
  s_time > t_time || binary_time > t_time
