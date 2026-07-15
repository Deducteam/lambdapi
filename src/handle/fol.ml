(** Configuration for tactics based on first-order logic. *)

open Common open Error
open Core open Term

let dom pos s =
  match unfold Timed.(!(s.sym_type)) with
  | Prod(a,_) ->
    begin
      match unfold a with
      | Symb s -> s
      | _ -> fatal pos "The type of %a is not of the form s → _ \
                        with s a symbol." Print.sym s
    end
  | _ -> fatal pos "The type of %a is not a product" Print.sym s

(* check the type of builtins *)
module B = struct

type builtins = {elt:term; set:term; prf:term; prop:term}

let elt b = b.elt
let set b = b.set
let prf b = b.prf
let prop b = b.prop

let arr f g b = mk_Arro(f b, g b)
let app f g b = mk_Appl(f b, g b)
let var x _b = mk_Vari x
let prod f g b = mk_Prod(f b, let x = new_var "a" in bind_var x (g x b))

let _ =
  let register =
    Builtin.register_expected_type (Eval.eq_modulo []) Print.term in
  let register s f = register s (fun ss pos ->
      let builtin = Builtin.get ss pos [] in
      let sym_prf = builtin "P" and sym_elt = builtin "T" in
      let prop = mk_Symb (dom pos sym_prf)
      and set = mk_Symb (dom pos sym_elt)
      and prf = mk_Symb sym_prf and elt = mk_Symb sym_elt in
      f {elt;set;prf;prop})
  in
  let unary = arr prop prop in
  let binary = arr prop unary in
  let quant = prod set (fun a -> arr (arr (app elt (var a)) prop) prop) in
  register "bot" prop;
  register "top" prop;
  register "not" unary;
  register "or" binary;
  register "and" binary;
  register "imp" binary;
  register "eqv" binary;
  register "ex" quant;
  register "all" quant;

end

(** Builtin configuration for propositional logic. *)
type config =
  { symb_Prop: sym (** Type of propositions. *)
  ; symb_P   : sym (** Encoding of propositions. *)
  ; symb_Set : sym (** Type of sets. *)
  ; symb_T   : sym (** Encoding of types. *)
  ; symb_or  : sym (** Disjunction(∨) symbol. *)
  ; symb_and : sym (** Conjunction(∧) symbol. *)
  ; symb_imp : sym (** Implication(⇒) symbol. *)
  ; symb_eqv : sym (** Equivalence(⇔) symbol. *)
  ; symb_bot : sym (** Bot(⊥) symbol. *)
  ; symb_top : sym (** Top(⊤) symbol. *)
  ; symb_not : sym (** Not(¬) symbol. *)
  ; symb_ex  : sym (** Exists(∃) symbol. *)
  ; symb_all : sym (** Forall(∀) symbol. *) }

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos [] in
  let symb_P = builtin "P" and symb_T = builtin "T" in
  let symb_Prop = dom pos symb_P and symb_Set = dom pos symb_T in
  { symb_Prop
  ; symb_P
  ; symb_Set
  ; symb_T
  ; symb_or  = builtin "or"
  ; symb_and = builtin "and"
  ; symb_imp = builtin "imp"
  ; symb_eqv = builtin "eqv"
  ; symb_bot = builtin "bot"
  ; symb_top = builtin "top"
  ; symb_not = builtin "not"
  ; symb_ex  = builtin "ex"
  ; symb_all = builtin "all" }
