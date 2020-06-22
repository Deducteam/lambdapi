(** Generating of induction principles. *)

open Timed
open Pos
open Console
open Terms
open Print
open Syntax

(** Logging function for generating of inductive principle. *)
let log_ind = new_logger 'g' "indu" "generating induction principle"
let log_ind = log_ind.logger

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

(** [principle ss pos sind scons_list] returns an induction principle which
    is created thanks to the symbol of the inductive type [sind] (and its
    position [pos]), its constructors [scons_list] and the signature [ss]. *)
let principle : Sig_state.t -> popt -> sym -> sym list -> term =
  fun ss pos sind scons_list ->
  let c = get_config ss pos in
  let ind = _Symb sind in
  let prop = _Symb c.symb_Prop in
  let p = Bindlib.new_var mkfree "p" in
  let prf_of_p t = _Appl (_Symb c.symb_prf) (_Appl (_Vari p) t) in
  let app = List.fold_left _Appl in

  (* [case_of scons] creates a clause according to a constructor [scons]. *)
  let case_of : sym -> tbox = fun scons ->
    let rec case : tbox list -> term-> tbox = fun xs a ->
      match unfold a with
      | Symb(s) ->
         if s == sind then prf_of_p (app (_Symb scons) (List.rev xs))
         else fatal pos "%a is not a constructor of %a"
                pp_symbol scons pp_symbol sind
      | Prod(a,b) ->
          let (x,b) =
            if Bindlib.binder_occur b then
              Bindlib.unbind b
            else
              let x = Bindlib.new_var mkfree "x" in
              (x, Bindlib.subst b (Vari x))
          in
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
  let rec add_case l r = match l with
    | []   -> r
    | t::q -> let t = case_of t in
              _Impl t (add_case q r)
  in
  let t = add_case scons_list t in
  let t = _Prod (_Impl ind prop) (Bindlib.bind_var p t) in
  Bindlib.unbox t

(** [ind_rule type_name ind_prop_name ind_prop_type cons_list] returns the
    p_rules linking with an induction principle of the inductive type named
    [type_name] (with its constructors [scons_list]). The name of this induc-
    tion principle is [ind_prop_name] and its type is [ind_prop_type]. *)
let ind_rule : string -> string -> term -> sym list -> p_rule list =
  fun type_name ind_prop_name ind_prop_type cons_list ->
  (* Create the common head of the rules *)
  let arg : sym list -> qident -> p_term = fun l ind_prop ->
    let p = Pos.none "p" in
    let p_iden = Pos.none (P_Iden(ind_prop, true)) in
    let p_patt = Pos.none (P_Patt(Some p, [||]))   in
    let head = P_Appl(p_iden, p_patt)                  in
    let rec aux : sym list -> p_term -> p_term = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          let t = Pos.none ("p" ^ t.sym_name)           in
          let p_patt = Pos.none (P_Patt(Some t, [||])) in
          aux q (Pos.none (P_Appl(acc, p_patt)))
    in
    aux l (Pos.none head)
  in
  let common_head = arg cons_list (Pos.none ([], ind_prop_name)) in
  (* Build the whole of the rules *)
  let build_p_rules : term -> sym list -> p_rule list = fun _ l ->
    let rec aux : sym list -> p_rule list -> p_rule list = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          begin
          let pt       = Pos.none ("p" ^ t.sym_name)       in (* RHS *)
          let p_patt   = Pos.none (P_Patt(Some pt, [||]))  in
          let qident_t = Pos.none ([], t.sym_name)         in (* LHS *)
          let t_ident  = Pos.none (P_Iden(qident_t, true)) in
          let tmp      = aux q acc                         in
          (* [create_p_rule arg_list t hyp_rec_list] creates a p_rule
             according to a constructor [scons]. *)
          let rec create_p_rule :
                    p_term list -> term -> p_term list -> p_rule =
            fun arg_list t hyp_rec_list -> match unfold t with
            | Symb(s) ->
                if s.sym_name == type_name then
                  let appl a b = Pos.none (P_Appl(a,b)) in
                  let (lhs_end, rhs_x_head) =
                    match List.rev arg_list with
                    | []   -> t_ident, p_patt
                    | x::z ->
                        List.fold_left appl (Pos.none (P_Appl(t_ident, x))) z,
                        List.fold_left appl (Pos.none (P_Appl(p_patt , x))) z
                  in
                  let lhs_x = Pos.none (P_Appl(common_head, lhs_end))  in
                  let rhs_x = match hyp_rec_list with
                    | []   -> rhs_x_head
                    | x::z ->
                      List.fold_left appl (Pos.none (P_Appl(rhs_x_head, x))) z
                  in
                  if !log_enabled then
                    log_ind "The rule [%a] --> %a"
                      Pretty.pp_p_term lhs_x Pretty.pp_p_term rhs_x;
                  Pos.none (lhs_x, rhs_x)
                else assert false (* See the function named "principle" *)
            | Prod(a, b) ->
                let (_,b) =
                  if Bindlib.binder_occur b then
                    Bindlib.unbind b
                  else
                    let x = Bindlib.new_var mkfree "x" in
                    (x, Bindlib.subst b (Vari x))
                in
                begin
                  match unfold a with
                  | Symb(s) ->
                      let arg = Pos.none s.sym_name                    in
                      let arg_patt = Pos.none (P_Patt(Some arg, [||])) in
                      if s.sym_name == type_name then
                        let x = Pos.none s.sym_name in
                        let x_patt = Pos.none (P_Patt(Some x, [||])) in
                        let hyp_rec_x =
                          Pos.none (P_Appl (common_head, x_patt))
                        in
                        create_p_rule
                          (arg_patt::arg_list) b (hyp_rec_x::hyp_rec_list)
                      else
                        create_p_rule (arg_patt::arg_list) b hyp_rec_list
                  | _ -> assert false (* See the function named "principle" *)
                end
            | _ -> assert false (* See the function named "principle" *)
          in
          (create_p_rule [] (!(t.sym_type)) [])::tmp
          end
    in
    aux l []
  in
  build_p_rules ind_prop_type cons_list
