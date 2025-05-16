(** Functional maps with [int] keys. *)
module IntMap = Map.Make (Base.Int)

(** Functional sets of integers. *)
module IntSet = Set.Make (Base.Int)

(** Functional maps with [string] keys. *)
module StrMap = Map.Make (String)

(** Functional sets of strings. *)
module StrSet = Set.Make (String)

(** If [s] ends by a sequence of digits with no useless leading zeros then
    [root_and_index s = (root,i)] such that [i] is the biggest integer such
    that [s = root^string_of_int i]. Otherwise, [root_and_index s = (s,-1)].*)
let root_and_index =
  let re = Str.regexp "[^0-9][0-9]+$" in
  fun s ->
  (*print_endline("root_and_index "^s);*)
  let n = String.length s in
  try let i = 1 + Str.search_backward re s (n-1) in
      (* skip leading zeros *)
      let i =
        if s.[i] <> '0' then i
        else
          begin
            let j = ref (i+1) in
            while !j < n && s.[!j] = '0' do incr j done;
            !j - 1
          end
      in
      (*print_endline("search_backward = "^string_of_int i);*)
      String.sub s 0 i, int_of_string(String.sub s i (n-i))
  with Not_found -> s, -1

(* unit tests *)
let _ =
  assert (root_and_index "x" = ("x",-1));
  assert (root_and_index "x0" = ("x",0));
  assert (root_and_index "xy0" = ("xy",0));
  assert (root_and_index "x0y" = ("x0y",-1));
  assert (root_and_index "x00" = ("x0",0));
  assert (root_and_index "x000" = ("x00",0))

(*let strings (idmap:int StrMap.t) : StrSet.t =
  StrMap.fold (fun p i set -> if i < 0 then p else p^string_of_int i)
    idmap StrSet.empty*)

let add_name s idmap = let r,i = root_and_index s in StrMap.add r i idmap

(** Assume that [root_and_index p = (r,i)]. If [i<0] then [get_safe_prefix p
    idmap] returns [p,StrMap.add p (-1) idmap] and, for all non-negative
    integer [k], [StrSet.mem (p^string_of_int k) (strings
    idmap')=false]. Otherwise, [get_safe_prefix p idmap] returns
    [r^string_of_int k,StrMap.add r k idmap], where [k] is greater than or
    equal to [i] and 1 + the index of [r] in [idmap]. *)
let get_safe_prefix (s:string) (idmap: int StrMap.t): string * int StrMap.t =
  (*print_endline("get_safe_prefix "^s^" in");
    StrSet.iter print_endline idmap;*)
  let r,i = root_and_index s in
  match StrMap.find_opt r idmap with
  | None -> s, StrMap.add r i idmap
  | Some j -> let k = max i j + 1 in r^string_of_int k, StrMap.add r k idmap

(* unit tests *)
let _ =
  let idmap = StrMap.(add "x" 1 (add "x0" 0 empty)) in
  let test s1 s2 = assert (fst (get_safe_prefix s1 idmap) = s2) in
  test "y" "y";
  test "x" "x2";
  test "x0" "x2";
  test "x00" "x01";
  test "xy" "xy"

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
