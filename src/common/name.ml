(** Generation of fresh names. *)

open Lplib open Base open Extra
open Debug

(** If [s] ends with some digits, then [root_and_index s = (root,i)] such that
    [i] is the biggest integer such that [s = root^string_of_int
    i]. Otherwise, [root_and_index s = (s,-1)].*)
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
