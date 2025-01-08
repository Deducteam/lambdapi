(** Configuration for tactics based on first-order logic. *)

open Common open Error
open Core open Term

(** Builtin configuration for propositional logic. *)
type config =
  { symb_Prop: sym (** Type of propositions. *)
  ; symb_P   : sym (** Encoding of propositions. *)
  ; symb_T   : sym (** Encoding of types. *)
  ; symb_or  : sym (** Disjunction(∨) symbol. *)
  ; symb_and : sym (** Conjunction(∧) symbol. *)
  ; symb_imp : sym (** Implication(⇒) symbol. *)
  ; symb_bot : sym (** Bot(⊥) symbol. *)
  ; symb_top : sym (** Top(⊤) symbol. *)
  ; symb_not : sym (** Not(¬) symbol. *)
  ; symb_ex  : sym (** Exists(∃) symbol. *)
  ; symb_all : sym (** Forall(∀) symbol. *) }

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  let symb_P = builtin "P" in
  let symb_Prop =
    match unfold Timed.(!(symb_P.sym_type)) with
    | Prod(a,_) ->
        begin
          match unfold a with
          | Symb s -> s
          | _ ->
              fatal pos "The type of %a is not of the form Prop → _ \
                         with Prop a symbol." Print.sym symb_P
        end
    | _ -> fatal pos "The type of %a is not a product" Print.sym symb_P
  in
  { symb_Prop
  ; symb_P
  ; symb_T   = builtin "T"
  ; symb_or  = builtin "or"
  ; symb_and = builtin "and"
  ; symb_imp = builtin "imp"
  ; symb_bot = builtin "bot"
  ; symb_top = builtin "top"
  ; symb_not = builtin "not"
  ; symb_ex  = builtin "ex"
  ; symb_all = builtin "all" }
