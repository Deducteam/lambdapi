
let string_of_file (f:string) :string =
  let ic = Stdlib.open_in f in
  let n = Stdlib.in_channel_length ic in
  let s = Bytes.create n in
  Stdlib.really_input ic s 0 n;
  Stdlib.close_in ic;
  Bytes.to_string s

let re = Str.regexp {|^require[ \n\t]+\(open[ \n\t]+\)?\([^;]+\);|}

let search (content:string) =
  let rec search (start:int) :unit =
    try let _ = Str.search_forward re content start in
        print_endline (Str.matched_group 2 content);
        search (Str.match_end())
    with _ -> ()
  in search 0

let print_deps_file filename = search (string_of_file filename)

let print_deps = List.iter print_deps_file
