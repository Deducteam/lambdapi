(** Fast extraction of the dependencies of a set of Lambdapi files without
    parsing them. *)

let space = function ' '|'\t'|'\r'|'\n' -> true | _ -> false
let not_space = function ' '|'\t'|'\r'|'\n' -> false | _ -> true

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
  let print i k =
    for j=i to k do
      (*if s.[j] = '\r' then print_char '\n' else*)
      if s.[j] = '.' then print_char '/' else print_char s.[j]
    done
  in
  let starts_with w =
    let l = String.length w in
    (*print_string {|starts "|}; print !k (!k+l-1); print_string {|" with "|};
    print_string w; print_endline {|" ?|};*)
    try for i = 0 to l-1 do if w.[i] <> s.[!k+i] then raise Exit done; true
    with Exit -> false
  in
  let _print_cur_char m = (* for debug *)
    let w = 10 in
    print_string m;
    print_string {|[before:"|}; print (max 0 (!k-w)) (!k-1);
    print_string {|",current(|}; print_int !k; print_string {|):"|};
    print_char s.[!k];
    print_string {|",after:"|}; print (min (!k+1) (n-1)) (min (!k+w) (n-1));
    print_string {|"]|}; print_string "\n";
    flush stdout
  in
  begin
    try
      if is_lp then
        let mod_end = function ' '|'\t'|'\r'|'\n'|';' -> true | _ -> false in
        let root_path = String.concat "." !Common.Library.root_path ^ "." in
        let p = String.length root_path in
        let rec skip_until f =
          if !k >= n then raise Exit;
          match s.[!k] with
          | '/' ->
            if !k+1 >= n then raise Exit
            else
              begin
                match s.[!k+1] with
                | '/' -> k := !k+2; skip_until ((=) '\n')
                | '*' -> k := !k+2; incr comment_level; skip_until f
                | c -> if f '/' || f c then () else (k := !k+2; skip_until f)
              end
          | '*' when !k+1 < n && s.[!k+1] = '/' ->
            decr comment_level; k := !k+2; skip_until f
          | c -> if f c then () else (incr k; skip_until f)
        in
        let skip_keyword w =
          let l = String.length w in
          if !k+l+1 < n && starts_with w && space s.[!k+l] then
            (k := !k+l+1; skip_until not_space)
        in
        let rec search_require() =
          skip_until ((=) 'r');
          if !k+7 >= n then raise Exit;
          if not (starts_with "require") then (incr k; search_require());
          k := !k+7;
          (*print_cur_char "1";*)
          if not_space s.[!k] then (incr k; search_require());
          skip_until not_space;
          (*print_cur_char "2";*)
          skip_keyword "private";
          (*print_cur_char "3";*)
          skip_keyword "open";
          search_module()
        and search_module() =
          (*print_cur_char "4";
            print_endline "A";*)
          if !k >= n then raise Exit;
          if s.[!k] = ';' then (incr k; search_require());
          (*print_endline "B";*)
          if not (starts_with root_path) then
            (skip_until mod_end; skip_until not_space; search_module());
          (*print_endline "C";*)
          let i = !k + p in
          skip_until mod_end;
          (*print_endline "D";
          print_cur_char "5";
            print_endline "E";*)
          print_char ' ';
          print i (!k-1);
          print_string ".lpo";
          (*print_endline "F";*)
          skip_until not_space;
          search_module()
        in
        search_require()
      else
        let mod_end = function ' '|'\t'|'\r'|'\n'|'.' -> true | _ -> false in
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
          print i (!k-1);
          print_string ".lpo\n";
          search_module()
        in
        search_require()
    with Exit -> ()
  end;
  print_newline()
