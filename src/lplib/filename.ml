include Stdlib.Filename

(** [realpath path] returns the absolute canonical path to file [path]. If
    [path] is invalid (i.e., it does not describe an existing file), then the
    exception [Invalid_argument] is raised. *)
external realpath : string -> string = "c_realpath"
