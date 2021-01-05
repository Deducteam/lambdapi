include Stdlib.Filename

(** [realpath path] returns the absolute canonical path to file [path]. If
    [path] is invalid (i.e., it does not describe an existing file), then the
    exception [Invalid_argument] is raised. *)
external realpath : string -> string = "c_realpath"

let rec normalize fname =
  if Sys.file_exists fname then
    realpath fname
  else
    let dirnm = dirname fname in
    let basenm = basename fname in
    concat (normalize dirnm) basenm
