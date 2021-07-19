(** Simple (and very naive) tool to generate all the #REQUIRE statements for a
    given legacy syntax file.

    Example use: "ocaml deps.ml file.dk modname", where "modname" simply gives
    the module name corresponding to "file.dk" (in this case, "file"). This is
    used to support old files for which module name was not constrained by the
    name of the source file. *)

module M = Set.Make(String)

let fold_lines : ('a -> string -> 'a) -> 'a -> string -> 'a =
  fun f acc fname ->
    let ic = open_in fname in
    let acc = ref acc in
    try
      while true do
        acc := f !acc (input_line ic)
      done; assert false
    with End_of_file -> close_in ic; !acc

let is_mod_char : char -> bool = fun c ->
  match c with
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' | '.' -> true
  | _                                                -> false

let rec handle_line : M.t -> string -> M.t = fun s l ->
  let len = String.length l in
  if len = 0 then s else
  let pos = ref 0 in
  while !pos < len && not (is_mod_char l.[!pos]) do incr pos done;
  let start = !pos in
  while !pos < len && is_mod_char l.[!pos] do incr pos done;
  let siz = !pos - start in
  let m = String.sub l start siz in
  let m =
    let len = String.length m in
    if len > 0 && m.[len-1] = '.' then String.sub m 0 (len - 1) else m
  in
  let get_module m =
    let i = try String.index m '.' with _ -> assert false in
    String.sub m 0 i
  in
  let s =
    if m <> "" && m <> "." && String.contains m '.' then
      M.add (get_module m) s
    else s
  in
  handle_line s (String.sub l !pos (len - !pos))

let _ =
  let work f n =
    let mods = M.remove n (fold_lines handle_line M.empty f) in
    M.iter (Format.printf "#REQUIRE %s.@.") mods
  in
  match Sys.argv with
  | [| _ ; f ; n |] -> work f n
  | _               ->
      Format.eprintf "Usage: %s file.dk modname@." Sys.argv.(0)
