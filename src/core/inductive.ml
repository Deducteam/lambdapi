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

(*open Console
open Pos
open Timed*)
open Terms
(*open Syntax*)

type inductive =
  { ind_constructors : sym list   ; (** the list of constructors           *)
    ind_prop         : sym option ; (** one inductive principle (Prop one) *) }
(*
let rec create_head_principle : inductive -> sym -> term = fun i s ->
  let rec create_head_principle_aux : term -> sym -> tbox = fun t s ->
    match t with
    | Vari x       -> _Vari x (* Prod(Var x, \_ -> s) *)
    | Type         -> _Type (*Vari (Bindlib.new_var mkfree (i.i_name.elt))*)
    | Kind         -> assert false
    | Symb s       -> _Symb s
    | Prod(t, tb)  -> let t  = create_head_principle_aux t s    in
                      if Bindlib.binder_occur tb then
                        let tb = create_head_principle_aux tb s in
                        _Prod(t, tb)
                      else
                        let (_,tb) = Bindlib.unbind tb          in
                        let tb = create_head_principle_aux tb s in
                        _Impl t tb
    | Abst(t, tb)  -> wrn None "Not yet implemented..."
                     ; t
    | Appl(t1, t2) -> wrn None "Application doesn't allow in inductive type."
                     ; t
    | Meta _       -> wrn None "Metavariable doesn't allow in inductive type."
                     ; t
    | Patt _       -> wrn None "Pattern doesn't allow in inductive type
                                (only used in rewriting rules LHS)."
                     ; t
    | TEnv _       ->
        wrn None "Term environment doesn't allow in inductive type
                  (only used in rewriting rules RHS)."
                     ; t
    | Wild         -> wrn None "Wildcard doesn't allow in inductive type
                                (only used for surface matching)."
                     ; t
    | TRef _       -> wrn None "Reference cell doesn't allow in inductive type
                                (only used for surface matching)."
                     ; t
    | LLet(a,t,u)  -> wrn None "Let-building doesn't allow in inductive type."
                     ; t
  in
  create_head_principle_aux Kind s(*i.type_ind s*)


let constructor_to_term : sym -> term = fun symbol -> (* @WORK in Progress *)
  (*let rec constructor_to_term_aux : term -> term = fun t ->
    match t with
    | Vari x      -> Kind (* Prod(Var x, \_ -> s) *)
    | Type        -> Vari (i.name_ind var)
    | Kind        -> assert false
    | Symb s      -> Kind
    | Prod(t, tb) -> Prod(t, constructor_to_term_aux tb s)
    | Abst(t, tb) -> wrn t.pos "Not yet implemented..."
                     ; t
    | Appl(t1, t2)-> wrn t.pos "Application doesn't allow in constructor."
                     ; t
    | Meta _      -> wrn t.pos "Metavariable doesn't allow in constructor."
                     ; t
    | Patt _      -> wrn t.pos "Pattern doesn't allow in constructor
                                  (only used in rewriting rules LHS)."
                     ; t
    | TEnv _      ->
        wrn t.pos "Term environment doesn't allow in constructor
                   (only used in rewriting rules RHS)."
                     ; t
    | Wild        -> wrn t.pos "Wildcard doesn't allow in constructor
                                  (only used for surface matching)."
                     ; t
    | TRef _      -> wrn t.pos "Reference cell doesn't allow in constructor
                                  (only used for surface matching)."
                     ; t
    | LLet(a,t,u) -> wrn i.pos "Let-building doesn't allow in constructor."
                     ; t
  in
  constructor_to_term_aux (!(symbol.sym_type))*)
 (!(symbol.sym_type))

let create_inductive_principal : inductive -> sym -> inductive = fun i s ->
  let anything = Bindlib.new_var mkfree "_" in
  (*Donc en supposant que t'aies un symbole nat, tu appelles lift (Symb(nat))
  pour le transformer en tbox , puis tu peux faire
  Bindlib.bind_var anything (lift (Symb(nat)

  val bind_var : 'a var -> 'b box -> ('a, 'b) binder box)*)
  let impl_term : term -> term -> term = fun t1 t2 ->
    Prod(t1, Bindlib.unbox (Bindlib.bind_var anything (lift t2))) in
  let impl_sym  : term -> sym  -> term = fun t  s  ->
    Prod(t,  Bindlib.unbox (Bindlib.bind_var anything (lift(Symb s)))) in
  (* head principal *)
  let _Impl : tbox -> tbox -> tbox =
  let dummy = Bindlib.new_var mkfree "_" in
  fun a b -> _Prod a (Bindlib.bind_var dummy b)
  let head = create_head_principle i s in
  (* premises principal *)
  let rec create_premises : sym list -> sym -> term = fun syml s ->
    match syml with
    | []   -> assert false
    | [a]  -> constructor_to_term a
    | t::q -> impl_term (constructor_to_term t) (create_premises q s)
     (*Prod(constructor_to_term t, (fun _ -> create_premises q))*)
  in
  let premises = create_premises i.i_rule s in
  (* ending principal *)
  let ending = Wild (* Prod *) in
  (* head -> premises -> ending *)
  let t = impl_term head (impl_term premises ending)
  (*Prod(head, fun _ -> Prod(premises, fun _ -> ending))*) in
  let induc_principle = create_sym () t Const Public in
    { sym_name  = i.i_name.elt^"_ind" ;
  in
  {i with ind_prop = Some induc_principle}
 *)
