(** Fast extraction of the dependencies of a set of Lambdapi files without
    parsing them. *)

let space = function ' '|'\t'|'\n' -> true | _ -> false
let not_space = function ' '|'\t'|'\n' -> false | _ -> true
let letter =
  function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true | _ -> false

let print_deps filename =
  let is_lp =
    match Filename.extension filename with
    | ".lp" -> true
    | ".dk" -> false
    | _ -> Common.Error.fatal_no_pos
             {|"%s" does not end with ".lp" or ".dk"|} filename
  in
  print_string filename;
  print_string "o:";
  let s = Lplib.String.string_of_file filename in
  let n = String.length s in
  let k = ref 0 in
  let comment_level = ref 0 in
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
  begin
    try
      let mod_end = function ' '|'\t'|'\n'|';' -> true | _ -> false in
      if is_lp then
        let root_path = !Parsing.Package.root_path^"." in
        let p = String.length root_path in
        let rec skip_until f =
          if !k >= n then raise Exit;
          match s.[!k] with
          | '/' ->
            if !k+1 >= n then raise Exit
            else
              begin
                match s.[!k+1] with
                | '/' -> k := !k+2; skip_until ((=)'\n')
                | '*' -> k := !k+2; incr comment_level; skip_until f
                | c -> if f '/' || f c then () else (k := !k+2; skip_until f)
              end
          | '*' when !k+1 < n && s.[!k+1] = '/' ->
            decr comment_level; k := !k+2; skip_until f
          | c -> if f c then () else (incr k; skip_until f)
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
          if not (starts_with root_path) then
            (skip_until mod_end; search_module());
          let i = !k + p in
          skip_until mod_end;
          print_char ' ';
          print i (!k-i);
          print_string ".lpo";
          search_module()
        in
        search_require()
      else
        let mod_end = function ' '|'\t'|'\n'|'.' -> true | _ -> false in
        let rec skip_until f =
          if !k >= n then raise Exit;
          match s.[!k] with
          | '(' ->
            if !k+1 >= n then raise Exit
            else
              begin
                match s.[!k+1] with
                | ';' -> k := !k+2; incr comment_level; skip_until f
                | c -> if f '(' || f c then () else (k := !k+2; skip_until f)
              end
          | ';' when !k+1 < n && s.[!k+1] = ')' ->
            decr comment_level; k := !k+2; skip_until f
          | c -> if f c then () else (incr k; skip_until f)
        in
        let rec search_require() =
          skip_until ((=) '#');
          if !k+8 >= n then raise Exit;
          if not (starts_with "#REQUIRE") then (incr k; search_require());
          k := !k+8;
          if not_space s.[!k] then (incr k; search_require());
          search_module()
        and search_module() =
          skip_until not_space;
          if s.[!k] = '.' then (incr k; search_require());
          let i = !k in
          skip_until mod_end;
          print_char ' ';
          print i (!k-i);
          print_string ".dko";
          search_module()
        in
        search_require()
    with Exit -> ()
  end;
  print_newline()
