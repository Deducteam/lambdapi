(*
   We assume we have:
// Builtins
<builtin> ::=
  | "0"
  | "+1"
  | "T"
  | "P"    pour la fonction interprétant Prop dans TYPE
  | "S"    pour la fonction interprétant Set  dans TYPE
  | "Prop" pour le type des propositions
  | "Set"  pour le type des données
  | "eq"
  | "refl"
  | "eq_ind"
  | "top"
  | "bot"
  | "not"
  | "or"
  | "and"
  | "imp"
*)

open Timed
open Terms
open Syntax

type inductive =
  { name  : ident      ; (* the name of the inductive type     *)
    sort  : p_type     ; (* the sort of the inductive type     *)
    rule  : sym list   ; (* the list of constructors           *)
    _ind  : sym option ; (* one inductive principle (Prop one) *)
    _rec  : sym option ; (* one recursive principle (Set one)  *)
    _rect : sym option ; (* one recursive principle (Type one) *)
    _inv  : sym option   (* one inversion principle            *) }

let constructor_to_term : sym -> term = fun symbol -> (* @WORK in Progress *)
  !(symbol.sym_type)

let create_inductive_principal : inductive -> inductive = fun i ->
  (* head principal *)
  let head = Wild (* Prod *) in
  (* premises principal *)
  let rec create_premises : sym list -> term = fun syml ->
    match syml with
    | []   -> assert false
    | [a]  -> constructor_to_term a
    | t::q -> Appl(constructor_to_term t, create_premises q)
  in
  let premises = create_premises i.rule in
  (* ending principal *)
  let ending = Wild (* Prod *) in
  let t = Appl(head, Appl(premises, ending)) in
  let induc_principle =
    { sym_name  = (i.name.elt)^"_ind" ;
      sym_type = ref t ;
      sym_path = Files.file_to_module (Files.current_path ());
      sym_def = ref None ;
      sym_impl = [] ;
      sym_rules = ref [] ;
      sym_tree  = ref Tree_types.empty_dtree ;
      sym_prop = Const ;
      sym_expo = Public }
  in
  {i with _ind = Some induc_principle}
