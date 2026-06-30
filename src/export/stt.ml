(** Base module for translating lp proofs encoded in simple type theory. *)

open Lplib open Extra
open Common open Pos open Error
open Parsing open Syntax
open Core

let log = Logger.make 'x' "xprt" "export"
let log = log.pp

module Qid = struct type t = Term.qident let compare = Stdlib.compare end
module QidMap = Map.Make(Qid)

(** Symbols necessary to encode STT. *)

type builtin =
  Set | Prop | Arr | El | Imp | All | Prf | Eq | Or | And | Ex | Not

let index_of_builtin = function
  | Set -> 0 | Prop -> 1 | Arr -> 2 | El -> 3 | Imp -> 4 | All -> 5
  | Prf -> 6 | Eq -> 7 | Or -> 8 | And -> 9 | Ex -> 10 | Not -> 11

let nb_builtins = 12

let builtin_of_index = function
  | 0 -> Set | 1 -> Prop | 2 -> Arr | 3 -> El | 4 -> Imp | 5 -> All
  | 6 -> Prf | 7 -> Eq | 8 -> Or | 9 -> And | 10 -> Ex | 11 -> Not
  | _ -> assert false

let _ = (* sanity check *)
  for i = 0 to nb_builtins - 1 do
    assert (index_of_builtin (builtin_of_index i) = i)
  done

let index_of_name = function
  | "Set" -> Some 0 | "prop" -> Some 1 | "arr" -> Some 2 | "El" -> Some 3
  | "imp" -> Some 4 | "all" -> Some 5 | "Prf" -> Some 6 | "eq" -> Some 7
  | "or" -> Some 8 | "and" -> Some 9 | "ex" -> Some 10 | "not" -> Some 11
  | _ -> None

let name_of_index = function
  | 0 -> "Set" | 1 -> "prop" | 2 -> "arr" | 3 -> "El" | 4 -> "imp"| 5 -> "all"
  | 6 -> "Prf" | 7 -> "eq" | 8 -> "or" | 9 -> "and" | 10 -> "ex" | 11 -> "not"
  | _ -> assert false

let _ = (* sanity check *)
  for i = 0 to nb_builtins - 1 do
    assert (index_of_name (name_of_index i) = Some i)
  done

let builtin : Term.qident array =
  let path = ["STTfa"] in
  Array.init nb_builtins (fun i -> path, name_of_index i)

let sym b = builtin.(index_of_builtin b)

(** Set renaming map from file. *)

let rmap = ref StrMap.empty
let codom = ref StrSet.empty

let add_renaming pos s1 s2 =
  let f = function
    | None -> Some s2
    | Some s2' ->
      fatal pos "\"%s\" renamed to both \"%s\" and \"%s\"" s1 s2' s2
  in
  if Logger.log_enabled() then log "rename %s into %s" s1 s2;
  rmap := StrMap.update s1 f !rmap;
  codom := StrSet.add s2 !codom

let set_renaming : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(string,{elt=(p,lp_id);pos=pos_id});pos} ->
      if p = [] then add_renaming pos lp_id string
      else fatal pos_id "Qualified identifier."
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(** Set symbols whose declarations have to be erased. *)

let mapping = ref QidMap.empty

let map_to qid string =
  if Logger.log_enabled() then
    log "map %a to \"%s\"" Pretty.qident qid string;
  mapping := QidMap.add qid.elt string !mapping

let set_mapping : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(string,lp_qid);_} -> map_to lp_qid string
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

let current_mp = Stdlib.ref []

let is_mapped id =
  QidMap.mem ([],id) !mapping || QidMap.mem (!current_mp,id) !mapping

(** Set encoding. *)

let encoding = ref QidMap.empty

let set_encoding : string -> unit = fun f ->
  let found = Array.make nb_builtins false in
  let consume = function
    | {elt=P_builtin(n,({elt=qid;_} as lp_qid));pos} ->
        begin match index_of_name n with
        | Some i ->
            if Logger.log_enabled() then
              log "builtin \"%s\" = %a" n Pretty.qident lp_qid;
            builtin.(i) <- qid;
            found.(i) <- true;
            let b = builtin_of_index i in
            encoding := QidMap.add qid b !encoding;
            if b = El || b = Prf then map_to lp_qid n
        | None -> fatal pos "Unknown builtin."
        end
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f);
  Array.iteri
    (fun i b ->
      if not b then
        fatal None(*FIXME*) "Builtin %s undefined." (name_of_index i))
    found

let is_encoded id =
  QidMap.mem ([],id) !encoding || QidMap.mem (!current_mp,id) !encoding

(** Map from symbol name to number of type variables (>0). A symbol with no
    entry is not polymorphic (arity =0). *)

let tvs_map : (int StrMap.t ref) = ref StrMap.empty

let set_tvs_map (fname:string): unit =
  let ic = open_in_bin fname in
  tvs_map := StrMap.add "el" 1 (input_value ic);
  close_in ic

(** Basic printing functions. We use Printf for efficiency reasons. *)

let out = Printf.printf

let char = output_char
let string = output_string

let prefix pre elt oc x = string oc pre; elt oc x
let suffix elt suf oc x = elt oc x; string oc suf

let list elt sep oc xs =
  match xs with
  | [] -> ()
  | x::xs -> elt oc x; List.iter (prefix sep elt oc) xs

(** Translation of identifiers. *)

let check : (popt -> string -> unit) Stdlib.ref = ref (fun _ _ -> ())

let translate_ident {elt=s;pos}: string =
  try StrMap.find s !rmap
  with Not_found ->
    if StrSet.mem s !codom then s^"__alt__" else (!check pos s; s)

let ident oc id = string oc (translate_ident id)

let param_id oc idopt =
  match idopt with
  | Some id -> ident oc id
  | None    -> char oc '_'

let param_ids = list param_id " "

let path_elt pos oc id = !check pos id; string oc id

let path oc {elt;pos} = list (path_elt pos) "." oc elt

let alias = Stdlib.ref StrMap.empty

let rec qident oc {elt=((mp,id) as qid);pos} =
  match mp with
  | [] ->
    begin match QidMap.find_opt (!current_mp,id) !mapping with
      | None ->
        begin match QidMap.find_opt ([],id) !mapping with
          | None -> ident oc {elt=id;pos}
          | Some s -> string oc s
        end
      | Some s -> string oc s
    end
  | [p] ->
    begin match StrMap.find_opt p !alias with
      | Some mp -> qident oc {elt=(mp,id);pos}
      | None ->
        match QidMap.find_opt qid !mapping with
        | None -> path oc {elt=mp;pos}; char oc '.'; ident oc {elt=id;pos}
        | Some s -> string oc s
    end
  | _::mp ->
    begin match QidMap.find_opt (mp,id) !mapping with
    | None -> path oc {elt=mp;pos}; char oc '.'; ident oc {elt=id;pos}
    | Some s -> string oc s
    end

(** Translation of terms. *)

let stt = Stdlib.ref false
let use_implicits = Stdlib.ref false
let use_notations = Stdlib.ref false

(* redefinition of p_get_args ignoring P_Wrap's. *)
let p_get_args : p_term -> p_term * p_term list = fun t ->
  let rec p_get_args t acc =
    match t.elt with
    | P_Appl(t, u) -> p_get_args t (u::acc)
    | P_Wrap t -> p_get_args t acc
    | _ -> t, acc
  in p_get_args t []

let app t default cases =
  let h, ts = p_get_args t in
  if !stt then
    match h.elt with
    | P_Iden({elt;_},expl) ->
        begin match QidMap.find_opt elt !encoding with
        | None -> default h ts
        | Some builtin -> cases h ts expl builtin
        end
    | _ -> default h ts
  else default h ts

let is_lem x = is_opaq x || is_priv x

(** Set required file. *)

let require = ref None

let set_requiring : string -> unit = fun f -> require := Some f
