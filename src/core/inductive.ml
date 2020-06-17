(** Generating of induction principles. *)

open Timed
open Pos
open Console
open Terms
open Print
open Syntax

(** Logging function for generating of inductive principle. *)
let log_induc = new_logger 'g' "indu" "generating induction principle"
let log_induc = log_induc.logger

(** Logging function for rules about inductive type. *)
let log_induc_rule = new_logger 'l' "irul" "inductive rule"
let log_induc_rule = log_induc_rule.logger

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
  (* let add_case t scons = _Impl (case_of scons) t in
     let t = List.fold_left add_case t scons_list   in *)
  let rec add_case l r = match l with
    | []   -> r
    | t::q -> let t = case_of t in
              _Impl t (add_case q r)
  in
  let t = add_case scons_list t in
  let t = _Prod (_Impl ind prop) (Bindlib.bind_var p t) in
  Bindlib.unbox t

let ind_rule : Sig_state.t -> popt -> string -> string -> term -> sym list
               -> p_rule list =
  fun _ pos type_name ind_prop_name ind_prop_type cons_list ->
  (* Find the induction principale *)
  (* let i =
       try SymMap.find sind !(ss.signature.sign_ind)
       with Not_found -> assert false
     in*)
    (* Create the common head of the rules *)
  let arg : sym list -> qident -> p_term = fun l ind_prop ->
    let p = Pos.make pos "p" in
    let p_iden = Pos.make pos (P_Iden(ind_prop, true)) in
    let p_patt = Pos.make pos (P_Patt(Some p, [||]))   in
    let head = P_Appl(p_iden, p_patt)                  in
    (*if !log_enabled then log_induc_rule "try to create the common head of the rules [%a]" Pretty.pp_p_term p_iden;*)
    let rec aux : sym list -> p_term -> p_term = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          let t = Pos.make pos ("p" ^ t.sym_name)           in
          let p_patt = Pos.make pos (P_Patt(Some t, [||])) in
          aux q (Pos.make pos (P_Appl(acc, p_patt)))
    in
    aux l (Pos.make pos head)
  in
  let common_head = arg cons_list (Pos.make pos ([], ind_prop_name)) in
  (* Build the whole of the rules *)
  let e : term -> sym list -> p_rule list = fun _ l ->
    let rec aux : sym list -> p_rule list -> p_rule list = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          begin
          let pt       = Pos.make pos ("p" ^ t.sym_name)       in (* RHS *)
          let p_patt   = Pos.make pos (P_Patt(Some pt, [||]))  in
          let qident_t = Pos.make pos ([], t.sym_name)         in (* LHS *)
          let t_ident  = Pos.make pos (P_Iden(qident_t, true)) in
          let tmp      = aux q acc                             in
          let rec truc arg_list t hyp_rec_list = match unfold t with
            | Symb(s) ->
                if s.sym_name == type_name then
                  let appl a b = Pos.make pos (P_Appl(a,b)) in
                  let (lhs_end, rhs_x_head) =
                    match arg_list with
                    | []   -> t_ident, p_patt
                    | x::z ->
                        let arg_list = List.fold_right appl z x in
                        Pos.make pos (P_Appl(t_ident, arg_list)),
                        Pos.make pos (P_Appl(p_patt, arg_list))
                  in
                  let lhs_x = Pos.make pos (P_Appl(common_head, lhs_end))  in
                  let rhs_x = match hyp_rec_list with
                    | []   -> rhs_x_head
                    | x::z ->
                        let hyp_rec_list = List.fold_right appl z x in
                        Pos.make pos (P_Appl(rhs_x_head, hyp_rec_list))
                  in
                  let t = Pos.make pos (lhs_x, rhs_x) in t::tmp
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
                      let arg = Pos.make pos s.sym_name                    in
                      let arg_patt = Pos.make pos (P_Patt(Some arg, [||])) in
                      if s.sym_name == type_name then
                        let x = Pos.make pos s.sym_name in
                        let x_patt = Pos.make pos (P_Patt(Some x, [||])) in
                        let hyp_rec_x =
                          Pos.make pos (P_Appl (common_head, x_patt))
                        in
                        truc (arg_patt::arg_list) b (hyp_rec_x::hyp_rec_list)
                      else
                        truc (arg_patt::arg_list) b hyp_rec_list
                  | _ -> assert false (* See the function named "principle" *)
                end
            (*if Bindlib.binder_occur b then
                fatal pos "Oups..."
              else
                let x = Pos.make pos "x"                                  in
                let x_patt = Pos.make pos (P_Patt(Some x, [||]))          in
                let hyp_rec_x = Pos.make pos (P_Appl(common_head,x_patt)) in
                let rhs_x_head = Pos.make pos (P_Appl(p_patt, x_patt))    in
                let rhs_x = Pos.make pos (P_Appl(rhs_x_head, hyp_rec_x))  in
                let lhs_end = Pos.make pos (P_Appl(t_ident, x_patt))      in
                let lhs_x = Pos.make pos (P_Appl(common_head, lhs_end))   in
                let t = Pos.make pos (lhs_x, rhs_x) in t::tmp             *)
            | _ -> assert false (* See the function named "principle" *)
          in
          truc [] (!(t.sym_type)) []
          end
    in
    aux l []
  in
  e ind_prop_type cons_list
    (*    [Pos.make pos (common_head, common_head)]ù*)
