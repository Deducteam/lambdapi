(** This module provides a function to translate a signature to the HRS format
    used in the confluence competition.

    @see <http://project-coco.uibk.ac.at/problems/hrs.php>. *)

open Extra
open Timed
open Terms

(** [print_sym oc s] outputs the fully qualified name of [s] to [oc]. The name
    is prefixed by ["c_"], and modules are separated with ["_"], not ["."]. *)
let print_sym : sym pp = fun oc s ->
  let print_path = List.pp Format.pp_print_string "_" in
  Format.fprintf oc "c_%a_%s" print_path s.sym_path s.sym_name

(** [print_patt oc p] outputs TPDB format corresponding to the pattern [p], to
    the channel [oc]. *)
let print_term : bool -> term pp = fun lhs ->
  let rec pp oc t =
    let out fmt = Format.fprintf oc fmt in
    match unfold t with
    (* Forbidden cases. *)
    | Meta(_,_)    -> assert false
    | TRef(_)      -> assert false
    | TEnv(_,_)    -> assert false
    | Wild         -> assert false
    | Kind         -> assert false
    (* Printing of atoms. *)
    | Vari(x)      -> out "v_%s" (Bindlib.name_of x)
    | Type         -> out "TYPE"
    | Symb(s,_)    -> print_sym oc s
    | Patt(i,n,ts) ->
        if ts = [||] then out "&%s" n else
        pp oc (Array.fold_left (fun t u -> Appl(t,u)) (Patt(i,n,[||])) ts)
    | Appl(t,u)    -> out "app(%a,%a)" pp t pp u
    | Abst(a,t)    ->
        let (x, t) = Bindlib.unbind t in
        if lhs then out "lam(m_typ,\\v_%s.%a)" (Bindlib.name_of x) pp t
        else out "lam(%a,\\v_%s.%a)" pp a (Bindlib.name_of x) pp t
    | Prod(a,b)    ->
        let (x, b) = Bindlib.unbind b in
        out "pi(%a,\\v_%s.%a)" pp a (Bindlib.name_of x) pp b
  in pp

(** [print_rule oc s r] outputs the rule declaration corresponding [r] (on the
    symbol [s]), to the output channel [oc]. *)
let print_rule : Format.formatter -> sym -> rule -> unit = fun oc s r ->
  (* Print the pattern variable declarations. *)
  let get_patt_names : term list -> string list = fun ts ->
    let names = Pervasives.ref [] in
    let fn t =
      match t with
      | Patt(_,n,_) -> Pervasives.(names := n :: !names)
      | _           -> ()
    in
    List.iter (Basics.iter fn) ts;
    List.sort_uniq String.compare Pervasives.(!names)
  in
  let names = get_patt_names r.lhs in
  if names <> [] then
    begin
      let print_name oc x = Format.fprintf oc "  &%s : term" x in
      Format.fprintf oc "(VAR\n%a\n)\n" (List.pp print_name "\n") names
    end;
  (* Print the rewriting rule. *)
  let lhs = Basics.add_args (Symb(s,Qualified)) r.lhs in
  Format.fprintf oc "(RULES %a" (print_term true) lhs;
  let rhs = Basics.term_of_rhs r in
  Format.fprintf oc "\n    -> %a)\n" (print_term false) rhs

(** [to_HRS oc sign] outputs a TPDB representation of the rewriting system of
    the signature [sign] to the output channel [oc]. *)
let to_HRS : Format.formatter -> Sign.t -> unit = fun oc sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let iter_symbols : (sym -> unit) -> unit = fun fn ->
    let iter_symbols sign =
      StrMap.iter (fun _ (s,_) -> fn s) Sign.(!(sign.sign_symbols))
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
  List.iter (Format.fprintf oc "%s\n") prelude;
  (* Print the symbol declarations. *)
  Format.fprintf oc "\n(COMMENT symbols)\n";
  let print_symbol s = Format.fprintf oc "(FUN %a : term)\n" print_sym s in
  iter_symbols print_symbol;
  (* Print the rewriting rules. *)
  Format.fprintf oc "\n(COMMENT rewriting rules)\n";
  let print_rules s =
    match !(s.sym_def) with
    | Some(d) -> Format.fprintf oc "(RULES %a\n" print_sym s;
                 Format.fprintf oc "    -> %a)\n" (print_term false) d
    | None    -> List.iter (print_rule oc s) !(s.sym_rules)
  in
  iter_symbols print_rules
