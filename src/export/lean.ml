(** Translate the parser-level AST to Lean.

There are two modes:

- raw_lean mode (option -o raw_lean): translation of the AST as it is
  (lambdapi-calculus is a subset system of lean if we ignore rules)

- stt_lean mode (option -o stt_lean): translation of the AST as an encoding in
  simple type theory.

  The encoding can be specified through a lambdapi file (option --encoding).

In both modes, a renaming map can be provided to rename some identifiers.

The renaming map can be specified through a lambdapi file (option --renaming).
*)

open Lplib open Extra
open Common open Pos open Error
open Parsing open Syntax
open Core

let log = Coq.log

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

let set_renaming : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(lean_id,{elt=([],lp_id);_});_} ->
        if Logger.log_enabled() then log "rename %s into %s" lp_id lean_id;
        rmap := StrMap.add lp_id lean_id !rmap
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(** Set symbols whose declarations have to be erased. *)

let erase = ref StrSet.empty

module Qid = struct type t = Term.qident let compare = Stdlib.compare end
module QidMap = Map.Make(Qid)

let map_erased_qid_lean = ref QidMap.empty

let set_mapping : string -> unit = fun f ->
  let consume = function
    | {elt=P_builtin(lean_id,lp_qid);_} ->
        if Logger.log_enabled() then
          log "rename %a into %s" Pretty.qident lp_qid lean_id;
        let id = snd lp_qid.elt in
        if Logger.log_enabled() then log "erase %s" id;
        erase := StrSet.add id !erase;
        map_erased_qid_lean :=
          QidMap.add lp_qid.elt lean_id !map_erased_qid_lean;
        if fst lp_qid.elt = [] && id <> lean_id then
          rmap := StrMap.add id lean_id !rmap
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f)

(** Set encoding. *)

let map_qid_builtin = ref QidMap.empty

let set_encoding : string -> unit = fun f ->
  let found = Array.make nb_builtins false in
  let consume = function
    | {elt=P_builtin(n,lp_qid);pos} ->
        begin match index_of_name n with
        | Some i ->
            if Logger.log_enabled() then
              log "builtin \"%s\" = %a" n Pretty.qident lp_qid;
            builtin.(i) <- lp_qid.elt;
            found.(i) <- true;
            let b = builtin_of_index i in
            map_qid_builtin := QidMap.add lp_qid.elt b !map_qid_builtin;
            if b = El || b = Prf then
              (if Logger.log_enabled() then log "erase %s" (snd lp_qid.elt);
               erase := StrSet.add (snd lp_qid.elt) !erase)
        | None -> fatal pos "Unknown builtin."
        end
    | {pos;_} -> fatal pos "Invalid command."
  in
  Stream.iter consume (Parser.parse_file f);
  Array.iteri
    (fun i b ->
      if not b then
        let pos =
          Some {fname=Some f;start_line=0;start_col=0;end_line=0;end_col=0}
        in fatal pos "Builtin %s undefined." (name_of_index i))
    found

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

let translate_ident : string -> string = fun s ->
  try StrMap.find s !rmap with Not_found -> s

let raw_ident oc s = string oc (translate_ident s)

let ident oc {elt;_} = raw_ident oc elt

let param_id oc idopt =
  match idopt with
  | Some id -> ident oc id
  | None    -> char oc '_'

let param_ids = list param_id " "

let raw_path = list string "."

let path oc {elt;_} = raw_path oc elt

let qident oc {elt=(mp,s);_} =
  match mp with
  | [] -> raw_ident oc s
  | _::_ -> raw_path oc mp; char oc '.'; raw_ident oc s

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
        begin match QidMap.find_opt elt !map_qid_builtin with
        | None -> default h ts
        | Some builtin -> cases h ts expl builtin
        end
    | _ -> default h ts
  else default h ts

let rec term oc t =
  (*if Logger.log_enabled() then
    log "pp %a" (*Pos.short t.pos*) Pretty.term t;*)
  match t.elt with
  | P_Meta _ -> wrn t.pos "TODO"; assert false
  | P_Patt _ -> wrn t.pos "TODO"; assert false
  | P_Expl _ -> wrn t.pos "TODO"; assert false
  | P_Type -> string oc "Type"
  | P_Wild -> char oc '_'
  | P_NLit i ->
      if !stt then
        match QidMap.find_opt ([],i) !map_erased_qid_lean with
        | Some s -> string oc s
        | None -> raw_ident oc i
      else raw_ident oc i
  | P_Iden(qid,b) ->
      if b then char oc '@';
      if !stt then
        match QidMap.find_opt qid.elt !map_erased_qid_lean with
        | Some s -> string oc s
        | None -> qident oc qid
      else qident oc qid
  | P_Arro(u,v) -> arrow oc u v
  | P_Abst(xs,u) -> abst oc xs u
  | P_Prod(xs,u) -> prod oc xs u
  | P_LLet(x,xs,a,u,v) ->
    string oc "let "; ident oc x; params_list oc xs; typopt oc a;
    string oc " := "; term oc u; string oc " in "; term oc v
  | P_Wrap u -> term oc u
  | P_Appl _ ->
      let default h ts = paren oc h; char oc ' '; list paren " " oc ts in
      app t default
        (fun h ts expl builtin ->
          match !use_notations, !use_implicits && not expl, builtin, ts with
          | _, _, (El|Prf), [u] -> term oc u
          | _, _, (Arr|Imp), [u;v] -> arrow oc u v
          | _, _, All, [_;{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}]
          | _, true, All, [{elt=P_Wrap({elt=P_Abst([_] as xs,u);_});_}]
            -> prod oc xs u
          | _, _, Ex, [_;{elt=P_Wrap({elt=P_Abst([x],u);_});_}]
          | _, true, Ex, [{elt=P_Wrap({elt=P_Abst([x],u);_});_}] ->
              string oc "exists "; raw_params oc x; string oc ", "; term oc u
          | true, _, Eq, [_;u;v]
          | true, true, Eq, [u;v] -> paren oc u; string oc " = "; paren oc v
          | true, _, Or, [u;v] -> paren oc u; string oc " \\/ "; paren oc v
          | true, _, And, [u;v] ->  paren oc u; string oc " /\\ "; paren oc v
          | true, _, Not, [u] -> string oc "~ "; paren oc u
          | _ -> default h ts)

and arrow oc u v = paren oc u; string oc " -> "; term oc v
and abst oc xs u =
  string oc "fun"; params_list_in_abs oc xs; string oc " => "; term oc u
and prod oc xs u =
  string oc "∀"; params_list_in_abs oc xs; string oc ", "; term oc u

and paren oc t =
  let default() = char oc '('; term oc t; char oc ')' in
  match t.elt with
  | P_Arro _ | P_Abst _ | P_Prod _ | P_LLet _ | P_Wrap _ -> default()
  | P_Appl _ ->
      app t (fun _ _ -> default())
        (fun _ ts _ builtin ->
          match builtin, ts with
          | (El|Prf), [u] -> paren oc u
          | _ -> default())
  | _ -> term oc t

and raw_params oc (ids,t,_) = param_ids oc ids; typopt oc t

and params oc ((ids,t,b) as x) =
  match b, t with
  | true, _ -> char oc '{'; raw_params oc x; char oc '}'
  | false, Some _ -> char oc '('; raw_params oc x; char oc ')'
  | false, None -> param_ids oc ids

(* starts with a space if the list is not empty *)
and params_list oc = List.iter (prefix " " params oc)

(* starts with a space if the list is not empty *)
and params_list_in_abs oc l =
  match l with
  | [ids,t,false] -> char oc ' '; param_ids oc ids; typopt oc t
  | _ -> params_list oc l

(* starts with a space if <> None *)
and typopt oc t = Option.iter (prefix " : " term oc) t

(** Translation of commands. *)

let is_lem x = is_opaq x || is_priv x

let requires = ref []
let openings = ref []

let command oc {elt; pos} =
  begin match elt with
  | P_open ps -> openings := List.rev_append ps !openings
  | P_require (true, ps) ->
      requires := List.rev_append ps !requires;
      openings := List.rev_append ps !openings
  | P_require (false, ps) ->
      requires := List.rev_append ps !requires
  | P_require_as _ ->
    wrn pos "Command not translated."
  | P_symbol
    { p_sym_mod; p_sym_nam; p_sym_arg; p_sym_typ;
      p_sym_trm; p_sym_prf=_; p_sym_def } ->
      if not (StrSet.mem p_sym_nam.elt !erase) then
        let p_sym_arg =
          if !stt then
            let pos = None in
            (* Parameters with no type are assumed to be of type [Set]. *)
            let _Set = {elt=P_Iden({elt=sym Set;pos},false);pos} in
            List.map (function ids, None, b -> ids, Some _Set, b | x -> x)
              p_sym_arg
          else p_sym_arg
        in
        begin match p_sym_def, p_sym_trm, p_sym_arg, p_sym_typ with
          | true, Some t, _, Some a when List.exists is_lem p_sym_mod ->
            (* If they have a type, opaque or private defined symbols are
               translated as Lemma's so that their definition is loaded in
               memory only when it is necessary. *)
            string oc "theorem "; ident oc p_sym_nam;
            params_list oc p_sym_arg; string oc " : "; term oc a;
            string oc " := "; term oc t; string oc "\n"
          | true, Some t, _, _ ->
            if List.exists is_opaq p_sym_mod then string oc "opaque "
            else string oc "def ";
            ident oc p_sym_nam;
            params_list oc p_sym_arg; typopt oc p_sym_typ;
            string oc " := "; term oc t;
            string oc "\n"
          | false, _, [], Some t ->
            string oc "axiom "; ident oc p_sym_nam; string oc " : ";
            term oc t; string oc "\n"
          | false, _, _, Some t ->
            string oc "axiom "; ident oc p_sym_nam; string oc " : ∀";
            params_list oc p_sym_arg; string oc ", "; term oc t;
            string oc "\n"
          | _ -> wrn pos "Command not translated."
        end
  | _ -> wrn pos "Command not translated."
  end

let ast oc = Stream.iter (command oc)

(** Set Lean required file. *)

let require = ref None

let set_requiring : string -> unit = fun f -> require := Some f

let print : string -> ast -> unit = fun file s ->
  let oc = stdout in
  begin match !require with
  | Some f -> string oc ("import "^f^"\nopen "^f^"\n")
  | None -> ()
  end;
  let import r = string oc "import "; path oc r; string oc "\n" in
  let opening r = string oc "open "; path oc r; string oc "\n" in
  List.iter import (List.rev !requires);
  List.iter opening (List.rev !openings);
  let file = Filename.chop_extension file in
  let mp = Library.path_of_file LpLexer.escape file in
  string oc "\nnamespace "; path oc (Pos.none mp); string oc "\n\n";
  ast oc s
