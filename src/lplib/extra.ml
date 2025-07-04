(** Functional maps with [int] keys. *)
module IntMap = Map.Make (Base.Int)

(** Functional sets of integers. *)
module IntSet = Set.Make (Base.Int)

(** Functional maps with [string] keys. *)
module StrMap = Map.Make (String)

(** Functional sets of strings. *)
module StrSet = Set.Make (String)

(** [time f x] times the application of [f] to [x], and returns the evaluation
    time in seconds together with the result of the application. *)
let time : ('a -> 'b) -> 'a -> float * 'b =
 fun f x ->
  let t = Sys.time () in
  let r = f x in
  (Sys.time () -. t, r)

(** Exception raised by the [timeout] function on a timeout. *)
exception Timeout

(** [timeout nbs f x] computes [f x] with a timeout of [nbs] seconds. The
    exception [Timeout] is raised if the computation takes too long, otherwise
    everything goes the usual way. *)
let timeout : int -> ('a -> 'b) -> 'a -> 'b =
 fun nbs f x ->
  let sigalrm_handler = Sys.Signal_handle (fun _ -> raise Timeout) in
  let old_behavior = Sys.signal Sys.sigalrm sigalrm_handler in
  let reset_sigalrm () =
    let _ = Unix.alarm 0 in
    Sys.set_signal Sys.sigalrm old_behavior
  in
  try
    let _ = Unix.alarm nbs in
    let res = f x in
    reset_sigalrm (); res
  with e -> reset_sigalrm (); raise e

(** [input_lines ic] reads the input channel [ic] line by line and returns its
    contents. The trailing newlines are removed in lines. The input channel is
    not closed by the function. *)
let input_lines : in_channel -> string list = fun ic ->
  let lines = ref [] in
  try while true do lines := input_line ic :: !lines done; assert false
  with End_of_file -> List.rev !lines

(** [run_process cmd] runs the command [cmd] and returns the list of the lines
    that it printed to its standard output (if the command was successful). If
    the command failed somehow, then [None] is returned. *)
let run_process : string -> string list option =
 fun cmd ->
  let oc, ic, ec = Unix.open_process_full cmd (Unix.environment ()) in
  let res = input_lines oc in
  match Unix.close_process_full (oc, ic, ec) with
  | Unix.WEXITED 0 -> Some res
  | _ -> None

(** [file_time fname] returns the modification time of file [fname]
   represented as a [float]. [neg_infinity] is returned if the file does not
   exist. *)
let file_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime) else neg_infinity

(** [more_recent source target] checks whether the [target] (produced from the
    [source] file) should be produced again. This is the case when [source] is
    more recent than [target]. *)
let more_recent : string -> string -> bool = fun source target ->
  file_time source > file_time target

(** [files f d] returns all the filenames in [d] and its sub-directories
   recursively satisfying the function [f], assuming that [d] is a
   directory. *)
let files : (string -> bool) -> string -> string list = fun chk ->
  let rec files acc dirs =
    match dirs with
    | [] -> acc
    | d::dirs ->
        let f (fnames, dnames) s =
          let s = Filename.concat d s in
          if Sys.is_directory s then (fnames, s::dnames)
          else if chk s then (s::fnames, dnames) else (fnames, dnames)
        in
        let acc, dirs = Array.fold_left f (acc, dirs) (Sys.readdir d) in
        files acc dirs
  in fun d -> files [] [d]
