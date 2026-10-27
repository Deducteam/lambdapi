(** Fast extraction of the dependencies of a set of Lambdapi files without
    parsing them. *)

let space = function ' '|'\t'|'\n' -> true | _ -> false
let not_space = function ' '|'\t'|'\n' -> false | _ -> true
let letter = function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true | _ -> false
let mod_end = function ' '|'\t'|'\n'|';' -> true | _ -> false

let print_deps filename =
  print_string (Filename.chop_extension filename);
  print_string ".lpo:";
  let s = Lplib.String.string_of_file filename in
  let n = String.length s in
  let root_path = !Parsing.Package.root_path^"." in
  let p = String.length root_path in
  let k = ref 0 in
  let skip_until f = while !k < n && not (f s.[!k]) do incr k done in
  let starts_with w =
    let m = String.length w in
    try for i = 0 to m-1 do if w.[i] <> s.[!k+i] then raise Exit done; true
    with Exit -> false
  in
  let print i m =
    for j=i to i+m-1 do
      if s.[j] = '.' then print_char '/' else print_char s.[j]
    done
  in
  let rec search_require() =
    skip_until ((=) 'r');
    if !k+7 >= n then raise Exit;
    if not (starts_with "require") then (incr k; search_require());
    k := !k+7;
    if not_space s.[!k] then (incr k; search_require());
    search_module()
  and search_module() =
    skip_until not_space;
    if s.[!k] = ';' then (incr k; search_require());
    if not (starts_with root_path) then (skip_until mod_end; search_module());
    let i = !k + p in
    skip_until mod_end;
    print_char ' ';
    print i (!k-i);
    print_string ".lpo";
    search_module()
  in
  begin try search_require() with Exit -> () end;
  print_newline()
