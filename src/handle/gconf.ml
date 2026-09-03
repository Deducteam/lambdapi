(** Configuration for tactics based on first-order logic. *)

open Common open Error
open Core open Term

type config =
  { symb_Prop: sym (** Type of propositions. *)
  ; symb_P   : sym (** Encoding of propositions. *)
  ; symb_Set : sym (** Type of sets. *)
  ; symb_T   : sym (** Encoding of types. *)
  ; symb_imp : sym (** Implication(⇒) symbol. *)
  ; symb_all : sym (** Forall(∀) symbol. *)
   }

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos [] in
  let symb_P = builtin "P" and symb_T = builtin "T" in
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
  and symb_Set =
    match unfold Timed.(!(symb_T.sym_type)) with
    | Prod(a,_) ->
        begin
          match unfold a with
          | Symb s -> s
          | _ ->
              fatal pos "The type of %a is not of the form Prop → _ \
                         with Prop a symbol." Print.sym symb_T
        end
    | _ -> fatal pos "The type of %a is not a product" Print.sym symb_T
  in
  { symb_Prop
  ; symb_P
  ; symb_Set
  ; symb_T
  ; symb_imp = builtin "imp"
  ; symb_all = builtin "all"
  }
