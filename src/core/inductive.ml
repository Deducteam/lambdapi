(** Generating of induction principles. *)

open Timed
open Pos
open Console
open Terms
open Print

(** Builtin configuration for induction. *)
type config =
  { symb_Prop : sym (** : TYPE. Type of propositions. *)
  ; symb_prf  : sym (** : Prop → TYPE.
                        Interpretation of propositions as types. *) }

(** [get_config ss pos] build the configuration using [ss]. *)
let get_config : Sig_state.t -> Pos.popt -> config = fun ss pos ->
  let builtin = Builtin.get ss pos in
  { symb_Prop = builtin "Prop"
  ; symb_prf  = builtin "P" }

let principle : Sig_state.t -> popt -> sym -> sym list -> term =
  fun ss pos sind scons_list ->
  let c = get_config ss pos in
  let ind = _Symb sind in
  let prop = _Symb c.symb_Prop in
  let p = Bindlib.new_var mkfree "p" in
  let prf_of_p t = _Appl (_Symb c.symb_prf) (_Appl (_Vari p) t) in
  let app = List.fold_left _Appl in

  let case_of scons =
    let rec case xs a =
      match unfold a with
      | Symb(s) ->
         if s == sind then prf_of_p (app (_Symb scons) (List.rev xs))
         else fatal pos "%a is not a constructor of %a"
                pp_symbol scons pp_symbol sind
      | Prod(a,b) ->
         let (x,b) = Bindlib.unbind b in
         let b = case ((Bindlib.box_var x)::xs) b in
         begin
           match unfold a with
           | Symb(s) ->
               let b =
                 if s == sind then _Impl (prf_of_p (Bindlib.box_var x)) b
                 else b
               in
              _Prod (Bindlib.box a) (Bindlib.bind_var x b)
           | _ -> fatal pos "The type of %a is not supported"
                    pp_symbol scons
         end
      | _ ->
         fatal pos "The type of %a is not supported"
           pp_symbol scons
    in
    case [] !(scons.sym_type)
  in

  let t =
    let x = Bindlib.new_var mkfree "x" in
    _Prod ind (Bindlib.bind_var x (prf_of_p (_Vari x)))
  in
  let add_case t scons = _Impl (case_of scons) t in
  let t = List.fold_left add_case t scons_list in
  let t = _Prod (_Impl ind prop) (Bindlib.bind_var p t) in
  Bindlib.unbox t
