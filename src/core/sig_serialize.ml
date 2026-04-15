open Sign
open Term
open Lplib.Extra
open Common
open Error
open Timed


  type t =
  { sign_symbols  : sym StrMap.t
        [@to_yojson fun m ->
         strmap_to_yojson sym_to_yojson m]
        [@of_yojson fun j ->
         strmap_of_yojson sym_of_yojson j]
  ; sign_path     : Path.t
  ; sign_deps     : dep_data Path.Map.t
        [@to_yojson fun m ->
         pathmap_to_yojson dep_data_to_yojson m]
        [@of_yojson fun m ->
          pathmap_of_yojson dep_data_of_yojson m ]
  ; sign_builtins : sym StrMap.t
        [@to_yojson fun m ->
         strmap_to_yojson sym_to_yojson m]
        [@of_yojson fun j ->
          strmap_of_yojson sym_of_yojson j ]
  ; sign_ind      : ind_data SymMap.t
        [@to_yojson fun m ->
          symmap_to_yojson ind_data_to_yojson m
         ]
        [@of_yojson fun json ->
            symmap_of_yojson
              (ind_data_of_yojson
              ) json
          ]
  ; sign_cp_pos   : cp_pos list SymMap.t
        [@to_yojson fun m ->
          symmap_to_yojson (fun lst ->
            `List (List.map (fun elt -> cp_pos_to_yojson elt) lst)
            ) m
         ]
        [@of_yojson fun json ->
            symmap_of_yojson
              (fun j ->
                match j with
                | `List lst ->
                  let rec aux acc = function
                    | [] -> Ok (List.rev acc)
                    | x :: xs ->
                      (match cp_pos_of_yojson x with
                      | Ok v -> aux (v :: acc) xs
                      | Error e -> Error e)
                  in
                  aux [] lst
                | _ -> Error "Expected list for cp_pos list"
              )
              json
          ]
  }
  [@@deriving yojson]

let to_sign_serializable (s:Sign.t) : t =
  { sign_symbols  = Timed.(!)s.sign_symbols
  ; sign_path     = s.sign_path
  ; sign_deps     = Timed.(!)s.sign_deps
  ; sign_builtins = Timed.(!)s.sign_builtins
  ; sign_ind      = Timed.(!)s.sign_ind
  ; sign_cp_pos   = Timed.(!)s.sign_cp_pos
  }

let of_sign_serializable (s:t) : Sign.t =
  { sign_symbols  = Timed.ref s.sign_symbols
  ; sign_path     = s.sign_path
  ; sign_deps     = Timed.ref s.sign_deps
  ; sign_builtins = Timed.ref s.sign_builtins
  ; sign_ind      = Timed.ref s.sign_ind
  ; sign_cp_pos   = Timed.ref s.sign_cp_pos
  }


let to_yojson_with_version (t : Sign.t) (version : string) : Yojson.Safe.t =
  match to_yojson (to_sign_serializable t) with
  | `Assoc fields ->
    `Assoc (("version", `String version) :: fields)
  | _ -> assert false

let of_yojson_with_version json =
  let version =
    json
    |> Yojson.Safe.Util.member "version"
    |> Yojson.Safe.Util.to_string in

  if version <> Version.version then
        raise (Failure
          ("Version " ^ version ^ " found but in lpo file but" ^
          Version.version ^ "expected (current)"));

    match json with
    |`Assoc fields ->
        begin match of_yojson (`Assoc (List.remove_assoc "version" fields))
        with
        | Ok s -> Ok (of_sign_serializable s)
        | Error e -> Error e
      end
    |_ -> raise (Failure "Unknown po format.
                Field version missing or corrupted file")


(** [write sign file] writes the signature [sign] to the file [fname]. *)
let write : Sign.t -> string -> unit = fun sign fname ->
  (* [Unix.fork] is used to safely [unlink] and write an object file, while
     preserving a valid copy of the written signature in the parent
     process. *)
  match Unix.fork () with
  | 0 -> let oc = open_out fname in
         unlink sign;
         let sign_json = to_yojson_with_version sign Version.version  in
         let _pp = Yojson.Safe.pretty_to_string sign_json in
         Yojson.Safe.to_channel oc sign_json;
         (* Marshal.to_channel oc sign [Marshal.Closures]; *)
         close_out oc; Stdlib.(Debug.do_print_time := false); exit 0
  | i -> ignore (Unix.waitpid [] i); Stdlib.(Debug.do_print_time := true)

let write s n = Debug.(record_time Writing (fun () -> write s n))

(** [read fname] reads a signature from the object file [fname]. Note that the
    file can only be read properly if it was build with the same binary as the
    one being evaluated. If this is not the case, the program gracefully fails
    with an error message. *)
(* NOTE here, we rely on the fact that a marshaled closure can only be read by
   processes running the same binary as the one that produced it. *)
let read : string -> Sign.t = fun fname ->
  let ic = open_in fname in
  let sign:Sign.t =
    try
      let json_sign = Yojson.Safe.from_channel ic in
      let sign = of_yojson_with_version json_sign in

  (* READ sign_symbols and update sign *)

      (* let sign = Marshal.from_channel ic in *)
      close_in ic;
      match sign with
      | Ok sign -> sign
      | Error e -> raise (Failure e)
    with Failure msg ->
      close_in ic;
      fatal_no_pos
        "File \"%s\" is incompatible with current binary. %s" fname msg
  in
  (* Timed references need reset after unmarshaling (see [Timed] doc). *)
  unsafe_reset sign.sign_symbols;
  unsafe_reset sign.sign_deps;
  unsafe_reset sign.sign_builtins;
  unsafe_reset sign.sign_ind;
  unsafe_reset sign.sign_cp_pos;
  let shallow_reset_sym s =
    unsafe_reset s.sym_type;
    unsafe_reset s.sym_def;
    unsafe_reset s.sym_rules;
    (* s.sym_dtree is not reset since it is recomputed. *)
  in
  let rec reset_term t =
    match unfold t with
    | Type
    | Kind
    | Vari _ -> ()
    | Symb s -> shallow_reset_sym s
    | Prod(a,b)
    | Abst(a,b) -> reset_term a; reset_term (snd (unbind b))
    | LLet(a,t,b) -> reset_term a; reset_term t; reset_term (snd(unbind b))
    | Appl(a,b) -> reset_term a; reset_term b
    | Patt(_,_,ts) -> Array.iter reset_term ts
    | Bvar _ -> assert false
    | TRef _ -> assert false
    | Wild -> assert false
    | Meta _ -> assert false
    | Plac _ -> assert false
  in
  let reset_rule r =
    List.iter reset_term r.lhs;
    reset_term r.rhs
  in
  let reset_sym s =
    shallow_reset_sym s;
    reset_term !(s.sym_type);
    Option.iter reset_term !(s.sym_def);
    List.iter reset_rule !(s.sym_rules)
  in
  StrMap.iter (fun _ s -> reset_sym s) !(sign.sign_symbols);
  StrMap.iter (fun _ s -> shallow_reset_sym s) !(sign.sign_builtins);
  let f _ {dep_symbols=sm; _} =
    StrMap.iter (fun _ sd -> List.iter reset_rule sd.rules) sm in
  Path.Map.iter f !(sign.sign_deps);
  let reset_ind i =
    shallow_reset_sym i.ind_prop; List.iter shallow_reset_sym i.ind_cons in
  let f s i = shallow_reset_sym s; reset_ind i in
  SymMap.iter f !(sign.sign_ind);
  let reset_cp_pos (_,l,r,_,l_p) =
    reset_term l; reset_term r; reset_term l_p in
  let f s cps = shallow_reset_sym s; List.iter reset_cp_pos cps in
  SymMap.iter f !(sign.sign_cp_pos);
  sign

let read =
  let open Stdlib in let r = ref Ghost.sign in fun n ->
  Debug.(record_time Reading (fun () -> r := read n)); !r


let%test "rev" =
  let rule =
    {Term.lhs     = [Term.dump_term]
  ; names    = [|"rule1"|]
  ; rhs      = Term.dump_term
  ; arity    = 0
  ; arities  = [|1; 2|]
  ; vars_nb  = 5
  ; xvars_nb = 9
  ; rule_pos = Some { fname      = Some "file"
          ; start_line      = 0
          ; start_col       = 0
          ; start_offset    = 0
          ; end_line        = 1
          ; end_col         = 1
          ; end_offset      = 1
          }
  } in
  let sym_data = {rules=[rule]; nota=None} in
  let dep_data = {dep_symbols = (StrMap. add "key1" sym_data StrMap.empty)
    ; dep_open   = true
  } in
  let sign = Ghost.sign in
  let symbols = Timed.(!) sign.sign_symbols in
  let symbols = StrMap.add ""
    {
      sym_dump
    with
      sym_path = ["rep"; "file"]
    }
    symbols in
  let sign = {sign
      with sign_symbols = Timed.ref symbols
    ; sign_deps         = Timed.ref
            (Path.Map.add (Path.ghost "path_here") dep_data Path.Map.empty)
    ; sign_builtins     = Timed.ref symbols
    } in
  write sign "/tmp/test_sign_read_write.json";
  let r_sign = read "/tmp/test_sign_read_write.json" in

  sign.sign_path = r_sign.sign_path &&
   (StrMap.equal
    (fun a b ->
      (Sym.compare a b) = 0
      (* Should compare :  *)
        (*  a.sym_expo = b.sym_expo
        && (Path.compare a.sym_path b.sym_path = 0)
        && (a.sym_name = b.sym_name) *)
    )
    (Timed.(!)(sign.sign_symbols))
    (Timed.(!)(r_sign.sign_symbols))
     )