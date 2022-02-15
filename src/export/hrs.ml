(** This module provides a function to translate a signature to the HRS format
    used in the confluence competition.

    @see <http://project-coco.uibk.ac.at/problems/hrs.php>. *)

open Lplib open Base open Extra
open Timed
open Core open Term open Print

(** [print_sym ppf s] outputs the fully qualified name of [s] to [ppf]. The
   name is prefixed by ["c_"], and modules are separated with ["_"], not
   ["."]. *)
let print_sym : sym pp = fun ppf s ->
  let print_path = List.pp string "_" in
  out ppf "c_%a_%s" print_path s.sym_path s.sym_name

(** [print_patt ppf p] outputs TPDB format corresponding to the pattern [p],
   to [ppf]. *)
let print_term : bool -> term pp = fun lhs ->
  let rec pp ppf t =
    match unfold t with
    (* Forbidden cases. *)
    | Meta(_,_)    -> assert false
    | Plac _       -> assert false
    | TRef(_)      -> assert false
    | Db _ -> assert false
    | Wild         -> assert false
    | Kind         -> assert false
    (* Printing of atoms. *)
    | Vari(x)      -> out ppf "%a" var x
    | Type         -> out ppf "TYPE"
    | Symb(s)      -> print_sym ppf s
    | Patt(None,_,_) -> assert false
    | Patt(Some i,n,ts) ->
        if ts = [||] then out ppf "$%d" i else
          pp ppf (Array.fold_left (fun t u -> mk_Appl(t,u))
                   (mk_Patt(Some i,n,[||])) ts)
    | Appl(t,u)    -> out ppf "app(%a,%a)" pp t pp u
    | Abst(a,t)    ->
        let (x, t) = unbind t in
        if lhs then out ppf "lam(m_typ,\\%a.%a)" var x pp t
        else out ppf "lam(%a,\\%a.%a)" pp a var x pp t
    | Prod(a,b)    ->
        let (x, b) = unbind b in
        out ppf "pi(%a,\\%a.%a)" pp a var x pp b
    | LLet(_,t,u)  -> pp ppf (subst u t)
  in pp

(** [print_rule ppf lhs rhs] outputs the rule declaration [lhs]->[rhs]
    to [ppf] *)
let print_rule : Format.formatter -> term -> term -> unit =
  fun ppf lhs rhs ->
  (* gets pattern and binded variable names *)
  let add_var_names : StrSet.t -> term -> StrSet.t = fun ns t ->
    let names = Stdlib.ref ns in
    let fn t =
      match t with
      | Patt(None,_,_) -> assert false
      | Patt(Some i,_,_) ->
        let name = Format.sprintf "$%d" i in
        Stdlib.(names := StrSet.add name !names)
      | Abst(_,b) ->
        let (x, _) = unbind b in
        Stdlib.(names := StrSet.add (name_of x) !names)
      | _           -> ()
    in
    LibTerm.iter fn t;
    Stdlib.(!names)
  in
  let names = add_var_names StrSet.empty lhs in
  let names = add_var_names names rhs in
  if not (StrSet.is_empty names) then
    begin
      let print_name ppf x = out ppf "  %s : term\n" x in
      let strset ppf = StrSet.iter (print_name ppf) in
      out ppf "(VAR\n%a)\n" strset names
    end;
  (* Print the rewriting rule. *)
  out ppf "(RULES %a" (print_term true) lhs;
  out ppf "\n    -> %a)\n" (print_term false) rhs

(** [print_sym_rule ppf s r] outputs the rule declaration corresponding [r]
   (on the symbol [s]), to [ppf]. *)
let print_sym_rule : Format.formatter -> sym -> rule -> unit = fun ppf s r ->
  let x = s,r in print_rule ppf (lhs x) (rhs x)

(** [to_HRS ppf sign] outputs a TPDB representation of the rewriting system of
    the signature [sign] to [ppf]. *)
let to_HRS : Format.formatter -> Sign.t -> unit = fun ppf sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let iter_symbols : (sym -> unit) -> unit = fun fn ->
    let not_on_ghosts _ s = if not (Unif_rule.mem s) then fn s in
    let iter_symbols sign =
      StrMap.iter not_on_ghosts Sign.(!(sign.sign_symbols))
    in
    List.iter (fun (_, sign) -> iter_symbols sign) deps
  in
  (* Print the prelude. *)
  let prelude =
    [ "(FUN"
    ; "  lam  : term -> (term -> term) -> term"
    ; "  app  : term -> term -> term"
    ; "  pi   : term -> (term -> term) -> term"
    ; "  type : term"
    ; ")"
    ; ""
    ; "(COMMENT beta-reduction)"
    ; "(VAR"
    ; "  v_x   : term"
    ; "  m_typ : term"
    ; "  m_B   : term"
    ; "  m_F   : term -> term"
    ; ")"
    ; "(RULES app(lam(m_typ,\\v_x. m_F v_x), m_B) -> m_F(m_B))"
    ; ""
    ; "(COMMENT TYPE keyword)"
    ; "(FUN TYPE : term)" ]
  in
  List.iter (out ppf "%s\n") prelude;
  (* Print the symbol declarations. *)
  out ppf "\n(COMMENT symbols)\n";
  let print_symbol s = out ppf "(FUN %a : term)\n" print_sym s in
  iter_symbols print_symbol;
  (* Print the rewriting rules. *)
  out ppf "\n(COMMENT rewriting rules)\n";
  let print_rules s =
    match !(s.sym_def) with
    | Some(d) -> print_rule ppf (mk_Symb s) d
    | None    -> List.iter (print_sym_rule ppf s) !(s.sym_rules)
  in
  iter_symbols print_rules
