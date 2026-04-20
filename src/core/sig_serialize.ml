open Sign
open Term
open Lplib.Extra
open Common
open Error
open Timed


let strmap_to_yojson to_elt (m : 'a StrMap.t) : Yojson.Safe.t =
  `List (
    StrMap.bindings m
    |> List.map (fun (k, v) ->
         `List [`String k; to_elt v])
  )

let strmap_of_yojson of_elt (json : Yojson.Safe.t)
  : ('a StrMap.t, string) result =
  match json with
  | `List lst ->
      let rec aux acc = function
        | [] -> Ok acc
        | `List [`String k; v_json] :: tl ->
            begin match of_elt v_json with
            | Ok v -> aux (StrMap.add k v acc) tl
            | Error e -> Error e
            end
        | _ -> Error "StrMap.of_yojson: invalid entry"
      in
      aux StrMap.empty lst
  | _ -> Error "StrMap.of_yojson: expected list"

let pathmap_to_yojson to_elt (m : 'a Path.Map.t) : Yojson.Safe.t =
   `List (
    Path.Map.bindings m
      |> List.map (fun (k, v) ->
        `List [`String (Format.asprintf "%a" Path.Path.pp k); to_elt v]
   ))

let pathmap_of_yojson of_elt json =
  match json with
  | `List lst ->
    let rec aux acc l =
      match l with
      | [] -> Ok acc
      | `List [`String k; v_json] :: lt ->
        begin match of_elt v_json with
        | Ok v ->
          aux (Path.Map.add (Path.Path.make k) v acc) lt
        | Error e -> Error e
        end
      | _ -> Error "pas list"
    in
    aux Path.Map.empty lst
  | _ -> Error "pathmap_of_yojson: expected list"


let symmap_to_yojson to_elt (m : 'a SymMap.t) : Yojson.Safe.t =
  `List (
    SymMap.bindings m
    |> List.map (fun (k, v) ->
         `List [ sym_to_yojson k; to_elt v ])
  )

let symmap_of_yojson of_elt (json : Yojson.Safe.t)
  : ('a SymMap.t, string) result =
  match json with
  | `List lst ->
      let rec aux acc = function
        | [] -> Ok acc
        | `List [k_json; v_json] :: tl ->
            begin match (sym_of_yojson k_json), of_elt v_json with
            | Ok k, Ok v ->
                aux (SymMap.add k v acc) tl
            | Error e, _ -> Error e
            | _, Error e -> Error e
            end
        | _ -> Error "SymMap.of_yojson: invalid entry"
      in
      aux SymMap.empty lst
  | _ -> Error "SymMap.of_yojson: expected list"


module StrMap = struct
include StrMap
  let to_yojson to_elt m = strmap_to_yojson to_elt m
  let of_yojson of_elt json = strmap_of_yojson of_elt json
end

module Path = struct
  include Path
  module Map = struct
  include Map
    let to_yojson to_elm m =
         pathmap_to_yojson to_elm m
    let of_yojson of_elm m =
          pathmap_of_yojson of_elm m
  end
end

module SymMap = struct
include SymMap
let to_yojson to_elm m =
  symmap_to_yojson to_elm m
let of_yojson of_elm m =
  symmap_of_yojson of_elm  m
end

type ind_data =
  { ind_cons : sym list
  ; ind_prop : sym
  ; ind_nb_params : int (** Number of parameters. *)
  ; ind_nb_types : int  (** Number of mutually defined types. *)
  ; ind_nb_cons : int   (** Number of constructors. *) }
  [@@deriving yojson]

let rule_to_yojson r = rule_serializable_to_yojson (to_rule_serializable r)
let rule_of_yojson j =
  match rule_serializable_of_yojson j with
  | Ok r -> Ok (of_rule_serializable r)
  | Error e -> Error e

type sym_data =
  { rules : rule list
  ; nota : float notation option }[@@deriving yojson]

type dep_data =
  { dep_symbols : sym_data StrMap.t
  ; dep_open : bool }
  [@@deriving yojson]

let to_ind_data_serializable (i : Sign.ind_data) : ind_data =
  { ind_cons      = i.ind_cons
  ; ind_prop      = i.ind_prop
  ; ind_nb_params = i.ind_nb_params
  ; ind_nb_types  = i.ind_nb_types
  ; ind_nb_cons   = i.ind_nb_cons
  }

let of_ind_data_serializable (i : ind_data) : Sign.ind_data =
  { ind_cons      = i.ind_cons
  ; ind_prop      = i.ind_prop
  ; ind_nb_params = i.ind_nb_params
  ; ind_nb_types  = i.ind_nb_types
  ; ind_nb_cons   = i.ind_nb_cons
  }

let to_sym_data_serializable (s : Sign.sym_data) : sym_data =
  { rules = s.rules
  ; nota  = s.nota}

  let of_sym_data_serializable (s : sym_data) : Sign.sym_data =
  { rules = s.rules
  ; nota  = s.nota}

let to_dep_data_serializable (d:Sign.dep_data) : dep_data =
  {   dep_symbols = StrMap.map to_sym_data_serializable d.dep_symbols
    ; dep_open  = d.dep_open
  }

let of_dep_data_serializable (d:dep_data) : Sign.dep_data =
  {   dep_symbols = StrMap.map of_sym_data_serializable d.dep_symbols
    ; dep_open  = d.dep_open
  }

type t =
  { sign_symbols  : sym StrMap.t
  ; sign_path     : Path.t
  ; sign_deps     : dep_data Path.Map.t
  ; sign_builtins : sym StrMap.t
  ; sign_ind      : ind_data SymMap.t
  ; sign_cp_pos   : cp_pos list SymMap.t
  }
  [@@deriving yojson]

let to_sign_serializable (s:Sign.t) : t =
  { sign_symbols  = Timed.(!)s.sign_symbols
  ; sign_path     = s.sign_path
  ; sign_deps     = (Path.Map.map
                      (fun d -> to_dep_data_serializable d)
                      (Timed.(!)s.sign_deps))
  ; sign_builtins = Timed.(!)s.sign_builtins
  ; sign_ind      = (SymMap.map
                      (fun c -> to_ind_data_serializable c)
                      (Timed.(!)(s.sign_ind)))
  ; sign_cp_pos   = Timed.(!)s.sign_cp_pos
  }

let of_sign_serializable (s:t) : Sign.t =
  { sign_symbols  = Timed.ref s.sign_symbols
  ; sign_path     = s.sign_path
  ; sign_deps     = Timed.ref (Path.Map.map
                      (fun d -> of_dep_data_serializable d) (s.sign_deps))
  ; sign_builtins = Timed.ref s.sign_builtins
  ; sign_ind      = Timed.ref (SymMap.map
                      (fun c -> of_ind_data_serializable c) s.sign_ind)
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
  let f _ ({dep_symbols=sm; _}:Sign.dep_data) =
    StrMap.iter
    (fun _ (sd:Sign.sym_data) -> List.iter reset_rule sd.rules)
    sm in
  Path.Map.iter f !(sign.sign_deps);
  let reset_ind (i:Sign.ind_data) =
    shallow_reset_sym i.ind_prop; List.iter shallow_reset_sym i.ind_cons in
  let f s (i : Sign.ind_data) = shallow_reset_sym s; reset_ind i in
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
  let sym_data:Sign.sym_data = {rules=[rule]; nota=None} in
  let dep_data:Sign.dep_data =
    {dep_symbols = (StrMap. add "key1" sym_data StrMap.empty)
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