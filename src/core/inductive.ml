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

(** [unbind_name b] unbinds the binder [b] and substitutes the variable in the
    case of undependent product. It returns the variable and the term which
    was the body of the binder. *)
let unbind_name : (term, term) Bindlib.binder -> tvar * term = fun b ->
  if Bindlib.binder_occur b then
    Bindlib.unbind b
  else
    let x = Bindlib.new_var mkfree "x" in
    (x, Bindlib.subst b (Vari x))

(** [create_instance_of pos sind f] creates an instance of the symbol [sind],
    which defined on the position [pos], and applies [f] to this instance.
    It's useful to build the type of the property p or build the conclusion
    of the inductive principle. *)
let create_instance_of : popt -> sym -> (tbox list -> tbox) -> tbox =
  fun pos sind f ->
  let rec aux : tvar list -> term -> tbox =
    fun xs a ->
    match Basics.get_args a with
    | (Type, _) ->
        let ts = List.rev_map _Vari xs in f ts
    | (Prod(a,b), _) ->
        let (x,b) = unbind_name b in
        _Prod (lift a) (Bindlib.bind_var x (aux (x::xs) b))
    | _ ->
        fatal pos "The type of %a is not supported" pp_symbol sind
  in aux [] !(sind.sym_type)

(** [principle ss pos sind scons_list] returns an induction principle which
    is created thanks to the symbol of the inductive type [sind] (and its
    position [pos]), its constructors [scons_list] and the signature [ss]. *)
let principle : Sig_state.t -> popt -> sym -> sym list -> term =
  fun ss pos sind scons_list ->

  (* STEP 0: Define some tools which will be useful *)
  let c = get_config ss pos          in
  let prop = _Symb c.symb_Prop       in
  let p = Bindlib.new_var mkfree "p" in
  let app : tbox -> tbox list -> tbox = List.fold_left _Appl         in
  let fapp : sym -> tbox list -> tbox = fun f ts -> app (_Symb f) ts in
  let prf_of_p : tbox list -> tbox -> tbox =
    fun ts t -> fapp c.symb_prf [_Appl (app (_Vari p) ts) t]
  in

  (* STEP 1: Create the type of the property p *)
  let to_find_p_type : tbox list -> tbox = fun ts ->
    _Impl (fapp sind ts) prop
  in
  let p_type = create_instance_of pos sind to_find_p_type in

  (* STEP 2: Create each clause according to a constructor *)
  (* [case_of scons] creates a clause according to a constructor [scons]. *)
  let case_of : sym -> tbox = fun scons ->
    let rec case : tbox list -> term -> tbox = fun xs a ->
      match Basics.get_args a with
      | (Symb(s), l) ->
          (* Check if the current constructor is a constructor of the current
             inductive type. *)
          if s == sind then
            let l = List.map lift l in
            prf_of_p l (app (_Symb scons) (List.rev xs))
          else fatal pos "%a is not a constructor of %a"
                 pp_symbol scons pp_symbol sind
      | (Prod(a,b), _) ->
          (* Take a name and the body of the term *)
          let (x,b) = unbind_name b                in
          (* Do the same thing until the end of the constructor's type *)
          let b = case ((Bindlib.box_var x)::xs) b in
          begin
            match Basics.get_args a with
            | (Symb(s), l) ->
                let b =
                  (* If the current symbol is equal to the inductive type,
                     we create an inductive hypothesis. *)
                  if s == sind then
                    let l = List.map lift l in
                    _Impl (prf_of_p l (Bindlib.box_var x)) b
                  else b
                in
                let res = _Prod (lift a) (Bindlib.bind_var x b) in
                if !log_enabled then
                  log_ind "The clause of the constructor [%a] is %a"
                    Print.pp_term (Symb(scons))
                    Print.pp_term (Bindlib.unbox res); res
            | _ -> fatal pos "The type of %a is not supported"
                     pp_symbol scons
          end
      | _ ->
          fatal pos "The type of %a is not supported"
            pp_symbol scons
    in
    case [] !(scons.sym_type)
  in

  (* STEP 3: Create the conclusion of the inductive principle *)
  let to_create_end  : tbox list -> tbox = fun ts ->
    let x = Bindlib.new_var mkfree "x" in
    let t = Bindlib.bind_var x (prf_of_p ts (_Vari x)) in
    _Prod (fapp sind ts) t
  in
  let conclusion = create_instance_of pos sind to_create_end  in

  (* STEP 4: Create the inductive principle *)
  let rec add_case l r =
    match l with
    | []   -> r
    | t::q -> let t = case_of t in
              _Impl t (add_case q r)
  in
  let t = add_case scons_list conclusion in
  let t = _Prod p_type (Bindlib.bind_var p t) in
  if !log_enabled then
    log_ind "The induction principle of the inductive type [%a] is %a"
      Print.pp_term (Symb(sind)) Print.pp_term (Bindlib.unbox t);
  Bindlib.unbox t

(** [term_to_p_term t] converts the term [t] to the type p_term. *)
let rec term_to_p_term : term -> p_term = fun t ->
  match t with
  | Vari x    -> Pos.none (P_Patt (Some (Pos.none (Bindlib.name_of x)), None))
  | Type         -> Pos.none P_Type
  | Kind         -> fatal None "Kind not possible"
  | Symb s       -> Pos.none (P_Iden (Pos.none ([], s.sym_name), true))
  | Prod _       -> fatal None "Prod - Not yet impleted"
  | Abst _       -> fatal None "Abst - Not yet impleted"
  | Appl(t1, t2) -> Pos.none (P_Appl (term_to_p_term t1, term_to_p_term t2))
  | Meta _       -> fatal None "Meta - Not yet impleted"
  | Patt _       -> fatal None "Patt - Not yet impleted"
  | TEnv _       -> fatal None "TEnv - Not yet impleted"
  | Wild         -> Pos.none P_Wild
  | TRef _       -> fatal None "TRef - Not yet impleted"
  | LLet _       -> fatal None "LLet - Not yet impleted"

(** Some constructors to create a p_term without position *)

let _P_Iden : qident * bool -> p_term =
  fun (ident, b) -> Pos.none (P_Iden(ident, b))

let _P_Patt : strloc option * p_term array -> p_term =
  fun (s, arr) -> Pos.none (P_Patt(s, Some arr))

let _P_Appl : p_term * p_term -> p_term =
  fun (t1, t2) -> Pos.none (P_Appl(t1, t2))

(** [create_patt t] creates a pattern $[t] without position *)
let create_patt : strloc -> p_term = fun t -> _P_Patt(Some t, [||])

(** [fold_app a l ] computes f (... (f (f a l1) l2) ...) ln where
    [l1 ; ... ln] is the list [l]. *)
let fold_app : p_term -> p_term list -> p_term =
  fun a l -> List.fold_left (fun a b -> _P_Appl(a,b)) a l

(** [ind_rule type_name ind_prop_name ind_prop_type cons_list] returns the
    p_rules linking with an induction principle of the inductive type named
    [type_name] (with its constructors [scons_list]). The name of this induc-
    tion principle is [ind_prop_name] and its type is [ind_prop_type]. *)
let ind_rule : string -> string -> term -> sym list -> p_rule list =
  fun type_name ind_prop_name ind_prop_type cons_list ->

  (* STEP 0: Create the common head of the rules *)
  let arg : sym list -> qident -> p_term = fun l ind_prop ->
    let p_iden = _P_Iden(ind_prop, true) in
    let p_patt = create_patt (Pos.none "p")   in
    let head = _P_Appl(p_iden, p_patt)   in
    let rec aux : sym list -> p_term -> p_term = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          let p_patt = create_patt (Pos.none ("p" ^ t.sym_name)) in
          aux q (_P_Appl(acc, p_patt))
    in
    aux l head
  in
  let common_head = arg cons_list (Pos.none ([], ind_prop_name)) in

  (* STEP 1: Build the whole of the rules *)
  let build_p_rules : term -> sym list -> p_rule list = fun _ l ->
    let rec aux : sym list -> p_rule list -> p_rule list = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          begin
          let pt       = Pos.none ("p" ^ t.sym_name) in (* RHS *)
          let p_patt   = create_patt pt      in
          let qident_t = Pos.none ([], t.sym_name)   in (* LHS *)
          let t_ident  = _P_Iden(qident_t, true)     in
          let tmp      = aux q acc                   in
          (* [create_p_rule arg_list t hyp_rec_list] creates a p_rule
             according to a constructor [scons]. *)
          let rec create_p_rule :
                    p_term list -> term -> p_term list -> int -> p_rule =
            fun arg_list t hyp_rec_list i -> match Basics.get_args t with
            | (Symb(s), l) ->
                if s.sym_name == type_name then
                  let (lhs_end, rhs_x_head) =
                    match List.rev arg_list with
                    | []   -> t_ident, p_patt
                    | x::z ->
                        fold_app (_P_Appl(t_ident, x)) z,
                        fold_app (_P_Appl(p_patt , x)) z
                  in
                  let l = List.map term_to_p_term l in
                  let arg_type = fold_app common_head l  in
                  let lhs_x = _P_Appl(arg_type, lhs_end) in
                  let rhs_x = match hyp_rec_list with
                    | []   -> rhs_x_head
                    | x::z -> fold_app (_P_Appl(rhs_x_head, x)) z
                  in
                  if !log_enabled then
                    log_ind "The rule [%a] --> %a"
                      Pretty.pp_p_term lhs_x Pretty.pp_p_term rhs_x;
                  Pos.none (lhs_x, rhs_x)
                else assert false (* See the function named "principle" *)
            | (Prod(a, b), _) ->
                let (_,b) = unbind_name b in
                begin
                  match Basics.get_args a with
                  | (Symb(s), l) ->
                      let x =
                        Bindlib.new_var mkfree ("x"^(string_of_int i))
                      in
                      let arg = Pos.none (Bindlib.name_of x)         in
                      let arg_patt = create_patt arg in
                      if s.sym_name == type_name then
                        let l = List.map term_to_p_term l     in
                        let arg_type = fold_app common_head l in
                        let hyp_rec_x =
                          _P_Appl (arg_type, arg_patt)
                        in
                        let new_hyp_rec_x = hyp_rec_x::hyp_rec_list in
                        create_p_rule
                          (arg_patt::arg_list) b new_hyp_rec_x (i+1)
                      else
                        create_p_rule
                          (arg_patt::arg_list) b hyp_rec_list (i+1)
                  | _ -> assert false (* See the function named "principle" *)
                end
            | _ -> assert false (* See the function named "principle" *)
          in
          (create_p_rule [] (!(t.sym_type)) [] 0)::tmp
          end
    in
    aux l []
  in
  build_p_rules ind_prop_type cons_list
