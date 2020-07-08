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

(** [change_codom_ind_typ pos ind_sym codom] assumes that the type of
    [ind_sym] is of the form [Πx1:a1,..., Πxn:an, TYPE]. It then generates
    a [tbox] similar to this type except that [TYPE] is replaced by
    [codom [x1;...;xn]]. *)
let change_codom_ind_typ : popt -> sym -> (tbox list -> tbox) -> tbox =
  fun pos ind_sym codom ->
  let rec aux : tvar list -> term -> tbox = fun xs a ->
    match Basics.get_args a with
    | (Type, _) -> codom (List.rev_map _Vari xs)
    | (Prod(a,b), _) ->
        let (x,b) = Basics.unbind_name b in
        _Prod (lift a) (Bindlib.bind_var x (aux (x::xs) b))
    | _ -> fatal pos "The type of %a is not supported" pp_symbol ind_sym
  in aux [] !(ind_sym.sym_type)

(** [principle ss pos ind_sym cons_list] returns an induction principle which
    is created thanks to the symbol of the inductive type [ind_sym] (and its
    position [pos]), its constructors [cons_list] and the signature [ss]. *)
let principle : Sig_state.t -> popt -> sym -> sym list -> term =
  fun ss pos ind_sym cons_list ->

  (* STEP 0: Define some tools which will be useful *)
  let c = get_config ss pos in
  let p = Bindlib.new_var mkfree "p" in
  let app  : tbox -> tbox list -> tbox = List.fold_left _Appl in
  let fapp : sym  -> tbox list -> tbox = fun f ts -> app (_Symb f) ts in
  let prf_of_p : tbox list -> tbox -> tbox = fun ts t ->
    fapp c.symb_prf [_Appl (app (_Vari p) ts) t]
  in

  (* STEP 1: Create the type of the property p *)
  let prop = _Symb c.symb_Prop in
  let codom ts = _Impl (fapp ind_sym ts) prop in
  let p_type = change_codom_ind_typ pos ind_sym codom in

  (* STEP 2: Create each clause according to a constructor *)
  (* [case_of cons_sym] creates a clause according to a constructor
     [cons_sym]. *)
  let case_of : sym -> tbox = fun cons_sym ->
    let rec aux : tbox list -> term -> tbox = fun xs a ->
      match Basics.get_args a with
      | (Symb(s), ts) ->
          if s == ind_sym then
            prf_of_p (List.map lift ts) (app (_Symb cons_sym) (List.rev xs))
          else
            fatal pos "%a is not a constructor of %a"
              pp_symbol cons_sym pp_symbol ind_sym
      | (Prod(a,b), _) ->
          let (x,b) = Basics.unbind_name b in
          let b = aux ((Bindlib.box_var x)::xs) b in
          begin
            match Basics.get_args a with
            | (Symb(s), ts) ->
                let b =
                  (* In case of a recursive argument, we create an inductive
                     hypothesis. *)
                  if s == ind_sym then
                    _Impl (prf_of_p (List.map lift ts) (Bindlib.box_var x)) b
                  else b
                in
                _Prod (lift a) (Bindlib.bind_var x b)
            | _ ->
                fatal pos "The type of %a is not supported" pp_symbol cons_sym
          end
      | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
    in
    let res = aux [] !(cons_sym.sym_type) in
    if !log_enabled then
      log_ind "The clause of the constructor [%a] is %a"
        Print.pp_term (Symb(cons_sym))
        Print.pp_term (Bindlib.unbox res);
    res
  in

  (* STEP 3: Create the conclusion of the inductive principle *)
  let codom ts =
    let x = Bindlib.new_var mkfree "x" in
    let t = Bindlib.bind_var x (prf_of_p ts (_Vari x)) in
    _Prod (fapp ind_sym ts) t
  in
  let conclusion = change_codom_ind_typ pos ind_sym codom in

  (* STEP 4: Create the induction principle *)

  let t =
    List.fold_right (fun a b -> _Impl (case_of a) b) cons_list conclusion
  in
  let t = _Prod p_type (Bindlib.bind_var p t) in
  if !log_enabled then
    log_ind "The induction principle of the inductive type [%a] is %a"
      Print.pp_term (Symb(ind_sym)) Print.pp_term (Bindlib.unbox t);
  Bindlib.unbox t

(** [type_to_pattern t] creates a pattern which matches with the type [t]. *)
let rec type_to_pattern : term -> p_term = fun t ->
  match t with
  | Vari x    -> Pos.none (P_Patt (Some (Pos.none (Bindlib.name_of x)), None))
  | Symb s       -> Pos.none (P_Iden (Pos.none ([], s.sym_name), true))
  | Appl(t1, t2) -> Pos.none (P_Appl (type_to_pattern t1, type_to_pattern t2))
  | Prod _       -> fatal None "Prod - Not yet implemented"
  | Abst _       -> fatal None "Abst - Not yet implemented"
  | LLet _       -> fatal None "LLet - Not yet implemented"
  | Type         -> fatal None "TYPE - Not yet implemented"(*Pos.none P_Type*)
  | Kind         -> fatal None "[Kind] not possible"
  | Wild         -> fatal None "[Wild] not possible"
  | TRef _       -> fatal None "[TRef] not possible"
  | Meta _       -> fatal None "[Meta] not possible"
  | Patt _       -> fatal None "[Patt] not possible"
  | TEnv _       -> fatal None "[TEnv] not possible"

(** Some constructors to create a p_term without position *)

let _P_Iden : qident -> bool -> p_term = fun ident b ->
  Pos.none (P_Iden(ident, b))

let _P_Patt : strloc option -> p_term array -> p_term = fun s ts ->
  Pos.none (P_Patt(s, Some ts))

let _P_Appl : p_term -> p_term -> p_term = fun t1 t2 ->
  Pos.none (P_Appl(t1, t2))

(** [create_patt t] creates a pattern $[t] without position *)
let create_patt : strloc -> p_term = fun t -> _P_Patt (Some t) [||]

(*
let create_arg : int -> p_term list = fun len ->
  let rec aux : int -> p_term list -> p_term list = fun i acc ->
    if i = 0 then
      acc
    else
      let head =
        Pos.none (P_Patt (Some (Pos.none ("a" ^ (string_of_int i))), None))
      in
      aux (i-1) (head::acc)
  in
  aux len []*)

(** [rec_rules ind_sym rec_sym cons_list] returns the p_rules linking with an
    induction principle [rec_sym] of the inductive type [ind_sym] (with its
    constructors [cons_list]). *)
let rec_rules : sym -> sym -> sym list -> p_rule list =
  fun ind_sym rec_sym cons_list ->

  (* STEP 0: Define some tools which will be useful *)
  let app   : p_term -> p_term list -> p_term = List.fold_left _P_Appl in
  let fapp  : p_term list -> p_term -> p_term = fun ts f -> app f ts in
(*  let app2  : sym -> sym list -> p_term = fun t q ->
    let p_patt = create_patt (Pos.none ("pi" ^ t.sym_name)) in
    List.fold_left (fun q -> _P_Appl q p_patt)
  in
  let fapp2 : p_term -> sym list -> p_term = fun p ts -> app2 p ts  in*)


  (* STEP 1: Create the common head of the rules *)

  (*let p_iden = _P_Iden (Pos.none ([], sym_ind.sym_name)) true in
  let p_patt = create_patt (Pos.none "p")                     in
  let head =
    List.map (fun c -> create_patt (Pos.none ("pi" ^ c.sym_name))) cons_list
  in
  let common_head = fapp head (_P_Appl p_iden p_patt) in*)
  let p_iden = _P_Iden (Pos.none ([], rec_sym.sym_name)) true in
  let p_patt = create_patt (Pos.none "p") in
  let head   = _P_Appl p_iden p_patt in
  let arg : sym list -> p_term = fun l  ->
    let rec aux : sym list -> p_term -> p_term = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          let p_patt = create_patt (Pos.none ("p" ^ t.sym_name)) in
          aux q (_P_Appl acc p_patt)
    in
    aux l head
  in
  let common_head = arg cons_list in

  (* STEP 2: Create each p_rule according to a constructor *)
  (* [create_p_rule cons_sym] creates a p_rule according to a constructor
     [cons_sym]. *)
  let create_p_rule : sym -> p_rule = fun cons_sym ->
    let pt       = Pos.none ("p" ^ cons_sym.sym_name) in (* RHS *)
    let p_patt   = create_patt pt in
    let qident_t = Pos.none ([], cons_sym.sym_name) in (* LHS *)
    let t_ident  = _P_Iden qident_t true in
    let rec aux : p_term list -> term -> p_term list -> int -> p_rule =
      fun arg_list t hyp_rec_list i ->
      match Basics.get_args t with
      | (Symb(s), ts) ->
          if s == ind_sym then
            let (lhs_end, rhs_x_head) =
              let tmp = fapp (List.rev arg_list) in
              tmp t_ident, tmp p_patt
            in
            let ts = List.map type_to_pattern ts in
            (*let len = List.length l in
            let arg_type = app common_head (create_arg len) in*)
            let arg_type = app common_head ts in
            let lhs_x = _P_Appl arg_type lhs_end in
            let rhs_x = app rhs_x_head hyp_rec_list in
            if !log_enabled then
              log_ind "The rule [%a] --> %a"
                Pretty.pp_p_term lhs_x Pretty.pp_p_term rhs_x;
            Pos.none (lhs_x, rhs_x)
            else assert false (* See the function named "principle" *)
      | (Prod(a, b), _) ->
          let (_,b) = Basics.unbind_name b in
          begin
            match Basics.get_args a with
            | (Symb(s), ts) ->
                let x =
                  Bindlib.new_var mkfree ("x" ^ (string_of_int i))
                in
                let arg = Pos.none (Bindlib.name_of x) in
                let arg_patt = create_patt arg in
                if s == ind_sym then
                  let ts = List.map type_to_pattern ts in
                  (*let len = List.length l in
                  let arg_type = app common_head (create_arg len) in*)
                  let arg_type = app common_head ts in
                  let hyp_rec_x = _P_Appl arg_type arg_patt in
                  let new_hyp_rec_x = hyp_rec_x::hyp_rec_list in
                  aux (arg_patt::arg_list) b new_hyp_rec_x (i+1)
                else aux (arg_patt::arg_list) b hyp_rec_list  (i+1)
            | _ -> assert false (* See the function named "principle" *)
          end
      | _ -> assert false (* See the function named "principle" *)
    in
    aux [] (!(cons_sym.sym_type)) [] 0
  in

  (* STEP 3: Build all the p_rules *)
  List.rev (List.map create_p_rule cons_list)
