(** Fast extraction of the dependencies of a set of Lambdapi files without
    parsing them. *)

(* FIXME: extend to Dedukti files *)

(** [string_of_file filename] returns the contents of [filename] as a
    string *)
let string_of_file filename =
  let ic = Stdlib.open_in filename in
  let n = Stdlib.in_channel_length ic in
  let s = Bytes.create n in
  Stdlib.really_input ic s 0 n;
  Stdlib.close_in ic;
  Bytes.to_string s

(* FIXME: does not handle escaped names {|...|}. *)
let re_mod = Str.regexp "\\([^ \n\t]+\\)"

(* FIXME: do not print files starting with the root_path. *)
let search_mod root_path content =
  print_endline ("search_mod: "^content);
  let rec search start =
    try let _ = Str.search_forward re_mod content start in
        let s = Str.matched_group 1 content in
        if String.starts_with ~prefix:root_path s then print_endline s;
        search (Str.match_end())
    with _ -> ()
  in search 0

(* FIXME: does not handle comments /* ... */ between module names, or comments
   // ... at the end of a line. *)
let re_req =
  Str.regexp "\\(^\\|[ \t]\\)require\\([ \n\t]+open\\)?[ \n\t]+\\([^;]+\\);"

let search_req root_path content =
  let rec search start =
    try let _ = Str.search_forward re_req content start in
        search_mod root_path (Str.matched_group 3 content);
        search (Str.match_end())
    with _ -> ()
  in search 0

let print_deps_file root_path filename =
  search_req root_path (string_of_file filename)

let print_deps = function
  | [] -> ()
  | (f::_) as fs ->
      match Parsing.Package.root_path f with
      | None -> Common.Error.fatal_no_pos "No lambdapi.pkd found."
      | Some root_path ->
          List.iter (print_deps_file (String.concat "." root_path)) fs
