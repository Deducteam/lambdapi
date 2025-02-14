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
open Stt

(** Translation of terms. *)

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
        match QidMap.find_opt ([],i) !map_erased_qid with
        | Some s -> string oc s
        | None -> raw_ident oc i
      else raw_ident oc i
  | P_Iden(qid,b) ->
      if b then char oc '@';
      if !stt then
        match QidMap.find_opt qid.elt !map_erased_qid with
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

let req_mod oc p = string oc "import "; path oc p; string oc "\n"
let open_mod oc p = string oc "open "; path oc p; string oc "\n"

let openings = ref []

let command oc {elt; pos} =
  begin match elt with
  | P_open ps -> List.iter (open_mod oc) ps
  | P_require (b, ps) ->
      List.iter (req_mod oc) ps;
      if b then openings := List.rev_append ps !openings
  | P_require_as _ -> wrn pos "Command not translated."
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
            else string oc "noncomputable def ";
            ident oc p_sym_nam;
            params_list oc p_sym_arg; typopt oc p_sym_typ;
            string oc " := "; term oc t; string oc "\n"
          | false, _, [], Some t ->
            string oc "axiom "; ident oc p_sym_nam; string oc " : ";
            term oc t; string oc "\n"
          | false, _, _, Some t ->
            string oc "axiom "; ident oc p_sym_nam;
            string oc " : ∀"; params_list oc p_sym_arg; string oc ", ";
            term oc t; string oc "\n"
          | _ -> wrn pos "Command not translated."
        end
  | _ -> wrn pos "Command not translated."
  end

let commands oc = Stream.iter (command oc)

let handle_requires s =
  let rec handle_next_elt() =
    let x = Stream.next s in
    match x.elt with
    | P_require (b, ps) ->
        List.iter (req_mod stdout) ps;
        if b then openings := List.rev_append ps !openings;
        handle_next_elt()
    | _ -> Some x
  in
  try handle_next_elt() with Stream.Failure -> None

let print : string -> ast -> unit = fun file s ->
  let oc = stdout in
  Option.iter (fun s -> string oc ("import "^s^"\n")) !require;
  match handle_requires s with
  | None -> ()
  | Some c ->
  Option.iter (fun s -> string oc ("open "^s^"\n")) !require;
  List.iter (open_mod oc) (List.rev !openings);
  string oc "\nnamespace ";
  string oc (Filename.chop_extension file);
  string oc "\n\n";
  command oc c;
  commands oc s
