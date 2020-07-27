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

(** [gen_ind_typ_codom pos ind_sym codom] assumes that the type of [ind_sym]
    is of the form [Πx1:a1,..., Πxn:an, TYPE]. It then generates a [tbox]
    similar to this type except that [TYPE] is replaced by
    [codom [x1;...;xn]]. *)
let gen_ind_typ_codom : popt -> sym -> (tbox list -> tbox) -> tbox =
  fun pos ind_sym codom ->
  let rec aux : tvar list -> term -> tbox = fun xs a ->
    match Basics.get_args a with
    | (Type, _) -> codom (List.rev_map _Vari xs)
    | (Prod(a,b), _) ->
        let (x,b) = Basics.unbind_name b in
        _Prod (lift a) (Bindlib.bind_var x (aux (x::xs) b))
    | _ -> fatal pos "The type of %a is not supported" pp_symbol ind_sym
  in aux [] !(ind_sym.sym_type)

module P  =
  struct

    (** [iden s] creates an identifier without position thanks to the string
        [s]. *)
    let iden : string -> p_term = fun s ->
      Pos.none (P_Iden(Pos.none ([], s), true))

    (** [patt s ts] creates a pattern without position thanks to the string
        [s] and the terms [ts]. *)
    let patt : string -> p_term array option -> p_term = fun s ts ->
      Pos.none (P_Patt (Some (Pos.none s), ts))

    (** [patt0 s] creates a pattern without position thanks to the string
        [s]. *)
    let patt0 : string -> p_term = fun s -> patt s None

    (** [appl t1 t2] creates an application of [t1] to [t2] without
        position. *)
    let appl : p_term -> p_term -> p_term = fun t1 t2 ->
      Pos.none (P_Appl(t1, t2))

    (** [nb_wild head i] creates a p_term which has [i] wildcard(s) after the
        head [head]. *)
    let nb_wild : p_term -> int -> p_term = fun head i ->
      let rec aux acc i =
        if i = 0 then acc else aux (appl acc (Pos.none P_Wild)) (i-1)
      in
      aux head i
  end

(** [fold_cons_typ pos codom get_name build_rec_hyp domrec dom ind_sym
    cons_sym f_rec f_not_rec acc] generates some value iteratively by going
    through the structure of [cons_sym.sym_type]. The position [pos] is the
    position of the command inductive where the constructors were defined.
    On the codomain, the function [codom] is called on the arguments to which
    [ind_sym] is applied and the variables of the products (in reverse order).
    In case of a product, the function [get_name] splits the product and
    naming the variable if it is not the case. In case of recursive occurren-
    ces, the function [build_rec_hyp] builds the recursive hypothesis associa-
    ted, and then the function [domrec] is applied to conclude the building.
    Otherwise, the function [dom] is called. If you would like to store a tem-
    porary result, the initial value is [acc], and you can change this value
    in the recursive case with the function [f_rec], and on the other case
    with the function [f_not_rec]. *)
let fold_cons_typ :
      popt ->
      (term list -> 'b list -> 'a -> 'c) ->
      ( (term, term) Bindlib.binder -> int -> 'b * term ) ->
      (term list -> 'b -> 'a) ->
      (term -> 'b -> 'a -> 'c -> 'c) ->
      (term -> 'b -> 'c -> 'c) ->
      sym -> sym ->
      ('a -> 'b -> 'a -> 'a) ->
      ('a -> 'b -> 'a) ->
      'a ->
      'c =
  fun pos codom get_name build_rec_hyp domrec dom ind_sym
      cons_sym f_rec f_not_rec acc->
  let rec aux : 'b list -> 'a -> int -> term -> 'c = fun xs p i a ->
    match Basics.get_args a with
    | (Symb(s), ts) ->
       if s == ind_sym then codom ts xs p
       else fatal pos "%a is not a constructor of %a"
              pp_symbol cons_sym pp_symbol ind_sym
    | (Prod(a,b), _) ->
       let (x,b) = get_name b i in
       begin
         match Basics.get_args a with
         | (Symb(s), ts) ->
             if s == ind_sym then
               let rec_hyp = build_rec_hyp ts x in
               let next = aux (x::xs) (f_rec p x rec_hyp) (i+1) b in
               domrec a x rec_hyp next
             else
               let next = aux (x::xs) (f_not_rec p x) (i+1) b in
               dom a x next
         | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
       end
    | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
  in aux [] acc 0 !(cons_sym.sym_type)

(** [gen_rec_rules ind_sym rec_sym cons_list] returns the p_rules linking
    with an induction principle [rec_sym] of the inductive type [ind_sym]
    (with its constructors [cons_list]). *)
let gen_rec_rules : sym -> sym -> sym list -> p_rule list =
  fun ind_sym rec_sym cons_list ->

  (* STEP 0: Define some tools which will be useful *)
  let app : p_term -> p_term list -> p_term = List.fold_left P.appl in

  (* STEP 1: Create the common head of the rules *)
  let p_iden = P.iden rec_sym.sym_name in
  let p_patt = P.patt0 "p" in
  let head = P.appl p_iden p_patt in
  let arg : sym list -> p_term = fun l ->
    let rec aux : sym list -> p_term -> p_term = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          let p_patt = P.patt0 ("pi" ^ t.sym_name) in
          aux q (P.appl acc p_patt)
    in
    aux l head
  in
  let common_head = arg cons_list in

  (* STEP 2: Create each p_rule according to a constructor *)
  (* [gen_rule_cons cons_sym] creates a p_rule according to a constructor
     [cons_sym]. *)
  let gen_rule_cons : sym -> p_rule = fun cons_sym ->
   let gr_codom : term list -> p_term list -> p_term -> p_rule =
      fun ts xs p ->
      let lhs_end =
        app (P.iden cons_sym.sym_name) (List.rev xs)
      in
      let arg_type = P.nb_wild common_head (List.length ts) in
      let lhs_x = P.appl arg_type lhs_end in
      if !log_enabled then
        log_ind "The rule [%a] --> %a"
          Pretty.pp_p_term lhs_x Pretty.pp_p_term p;
      Pos.none (lhs_x, p)
    in
    let gr_get_name : (term, term) Bindlib.binder -> int -> p_term * term =
      fun b i ->
      let (_,b) = Basics.unbind_name b in
      (P.patt0 ("x" ^ (string_of_int i)), b)
    in
    let gr_build_rec_hyp : term list -> p_term -> p_term =
      fun ts x ->
      let arg_type = P.nb_wild common_head (List.length ts) in
      P.appl arg_type x
    in
    let gr_domrec : term -> p_term -> p_type -> p_rule -> p_rule =
      fun _ _ _ next -> next in
    let gr_dom : term -> p_term -> p_rule -> p_rule =
      fun _ _ next -> next in
    let f_rec : p_term -> p_term -> p_term -> p_term =
      fun p x rec_hyp -> P.appl (P.appl p x) rec_hyp
    in
    let f_not_rec : p_term -> p_term -> p_term =
      fun p x -> P.appl p x
    in
    let acc : p_term = P.patt0 ("pi" ^ cons_sym.sym_name) in
    fold_cons_typ None gr_codom gr_get_name gr_build_rec_hyp gr_domrec
      gr_dom ind_sym cons_sym f_rec f_not_rec acc
  in

  (* STEP 3: Build all the p_rules *)
  List.rev_map gen_rule_cons cons_list





(** [gen_rec_type ss pos ind_sym cons_list] generates the induction principle
    of the inductive type [ind_sym] (and its position [pos]) with the cons-
    tructors [cons_list]. Each recursive argument is followed by its induction
    hypothesis. For instance, with [inductive T:TYPE := c: T->T->T], we have
    [ind_T: Πp:T->Prop, (Πx1:T, π(p x1)-> Πx2:T, π(p x2)-> π(p(c x1 x2)) ->
    Π x:T,π(p x)]. *)
let gen_rec_type : Sig_state.t -> popt -> sym -> sym list -> term =
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
  let p_type = gen_ind_typ_codom pos ind_sym codom in

  (* STEP 2: Create each clause according to a constructor *)
  (* [case_of cons_sym] creates a clause according to a constructor
     [cons_sym]. *)
  let case_of : sym -> tbox = fun cons_sym ->
    let gip_codom : term list -> tvar list -> tbox -> tbox = fun ts xs _ ->
      prf_of_p (List.map lift ts)
        (app (_Symb cons_sym) (List.rev_map _Vari xs))
    in
    let gip_get_name : (term, term) Bindlib.binder -> int -> tvar * term =
      fun b _ ->
      Basics.unbind_name b
    in
    let gip_build_rec_hyp : term list -> tvar -> tbox = fun ts x ->
      prf_of_p (List.map lift ts) (_Vari x)
    in
    let gip_domrec : term -> tvar -> tbox -> tbox -> tbox =
      fun a x rec_hyp next ->
      _Prod (lift a) (Bindlib.bind_var x (_Impl rec_hyp next))
    in
    let gip_dom : term -> tvar -> tbox -> tbox = fun a x next ->
      _Prod (lift a) (Bindlib.bind_var x next)
    in
    let f_rec : tbox -> tvar -> tbox -> tbox = fun a _ _ -> a in
    let f_not_rec : tbox -> tvar -> tbox = fun a _ -> a in
    let acc : tbox = _Type in
    fold_cons_typ pos gip_codom gip_get_name gip_build_rec_hyp gip_domrec
      gip_dom ind_sym cons_sym f_rec f_not_rec acc
  in

  (* STEP 3: Create the conclusion of the inductive principle *)
  let codom ts =
    let x = Bindlib.new_var mkfree "x" in
    let t = Bindlib.bind_var x (prf_of_p ts (_Vari x)) in
    _Prod (fapp ind_sym ts) t
  in
  let conclusion = gen_ind_typ_codom pos ind_sym codom in

  (* STEP 4: Create the induction principle *)
  let t =
    List.fold_right (fun a b -> _Impl (case_of a) b) cons_list conclusion
  in
  let t = _Prod p_type (Bindlib.bind_var p t) in
  if !log_enabled then
    log_ind "The induction principle of the inductive type [%a] is %a"
      Print.pp_term (Symb(ind_sym)) Print.pp_term (Bindlib.unbox t);
  Bindlib.unbox t

















































(* OLD FOLD

   
(** [fold_cons_typ pos codom domrec dom ind_sym cons_sym] generates some value
    iteratively by going through the structure of [sym_cons.sym_type]. On
    the codomain, the function [codom] is called on the arguments to which
    [ind_sym] is applied and the variables of the products (in reverse order).
    In case of a product, the functions [domrec] and [dom] are called depend-
    ing on whether the domain type is recursive or not. They are applied to
    the terms to which [ind_sym] is applied, the variable of the product, and
    the value built from the codomain. *)
let fold_cons_typ :
      popt -> (term list -> tvar list -> 'a)
      -> (term list -> term -> tvar -> 'a -> 'a)
      -> (term list -> term -> tvar -> 'a -> 'a)
      -> sym -> sym -> 'a =
  fun pos codom domrec dom ind_sym cons_sym ->
  let rec aux xs a =
    match Basics.get_args a with
    | (Symb(s), ts) ->
       if s == ind_sym then codom ts xs
       else fatal pos "%a is not a constructor of %a"
              pp_symbol cons_sym pp_symbol ind_sym
    | (Prod(a,b), _) ->
       let (x,b) = Basics.unbind_name b in
       let b = aux (x::xs) b in
       begin
         match Basics.get_args a with
         | (Symb(s), ts) ->
            if s == ind_sym then domrec ts a x b else dom ts a x b
         | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
       end
    | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
  in aux [] !(cons_sym.sym_type)
 *)

(*
(** [gen_rec_type ss pos ind_sym cons_list] generates the induction principle
    of the inductive type [ind_sym] (and its position [pos]) with the cons-
    tructors [cons_list]. Each recursive argument is followed by its induction
    hypothesis. For instance, with [inductive T:TYPE := c: T->T->T], we have
    [ind_T: Πp:T->Prop, (Πx1:T, π(p x1)-> Πx2:T, π(p x2)-> π(p(c x1 x2)) ->
    Π x:T,π(p x)]. *)
let gen_rec_type : Sig_state.t -> popt -> sym -> sym list -> term =
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
  let p_type = gen_ind_typ_codom pos ind_sym codom in

  (* STEP 2: Create each clause according to a constructor *)
  (* [case_of cons_sym] creates a clause according to a constructor
     [cons_sym]. *)
  let case_of : sym -> tbox = fun cons_sym ->
    let codom ts xs =
      prf_of_p (List.map lift ts)
        (app (_Symb cons_sym) (List.rev_map _Vari xs))
    in
    let domrec ts a x b =
      let ts = List.map lift ts in
      let b = _Impl (prf_of_p ts (_Vari x)) b in
      _Prod (lift a) (Bindlib.bind_var x b)
    in
    let dom _ a x b =
      _Prod (lift a) (Bindlib.bind_var x b)
    in
    fold_cons_typ pos codom domrec dom ind_sym cons_sym
  in

  (* STEP 3: Create the conclusion of the inductive principle *)
  let codom ts =
    let x = Bindlib.new_var mkfree "x" in
    let t = Bindlib.bind_var x (prf_of_p ts (_Vari x)) in
    _Prod (fapp ind_sym ts) t
  in
  let conclusion = gen_ind_typ_codom pos ind_sym codom in

  (* STEP 4: Create the induction principle *)
  let t =
    List.fold_right (fun a b -> _Impl (case_of a) b) cons_list conclusion
  in
  let t = _Prod p_type (Bindlib.bind_var p t) in
  if !log_enabled then
    log_ind "The induction principle of the inductive type [%a] is %a"
      Print.pp_term (Symb(ind_sym)) Print.pp_term (Bindlib.unbox t);
  Bindlib.unbox t
 *)

(*
(** [gen_rec_type ss pos ind_sym cons_list] returns an induction principle which
    is created thanks to the symbol of the inductive type [ind_sym] (and its
    position [pos]), its constructors [cons_list] and the signature [ss]. *)
let gen_rec_type : Sig_state.t -> popt -> sym -> sym list -> term =
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
  let p_type = gen_ind_typ_codom pos ind_sym codom in

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
          (*let b = aux ((Bindlib.box_var x)::xs) b in*)
          begin
            match Basics.get_args a with
            | (Symb(s), ts) ->
                  (* In case of a recursive argument, we create an inductive
                     hypothesis. *)
                  if s == ind_sym then
                    let hyp_rec = prf_of_p (List.map lift ts) (_Vari x) in
                    _Prod (lift a) (Bindlib.bind_var x (_Impl hyp_rec (aux ((_Vari x)::xs) b)))
                  else
                    _Prod (lift a) (Bindlib.bind_var x (aux ((_Vari x)::xs) b))
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
  let conclusion = gen_ind_typ_codom pos ind_sym codom in

  (* STEP 4: Create the induction principle *)

  let t =
    List.fold_right (fun a b -> _Impl (case_of a) b) cons_list conclusion
  in
  let t = _Prod p_type (Bindlib.bind_var p t) in
  if !log_enabled then
    log_ind "The induction principle of the inductive type [%a] is %a"
      Print.pp_term (Symb(ind_sym)) Print.pp_term (Bindlib.unbox t);
  Bindlib.unbox t


 *)








   
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

  (*
(** [gen_rec_rules ind_sym rec_sym cons_list] returns the p_rules linking
    with an induction principle [rec_sym] of the inductive type [ind_sym]
    (with its constructors [cons_list]). *)
let gen_rec_rules : sym -> sym -> sym list -> p_rule list =
  fun ind_sym rec_sym cons_list ->

  (* STEP 0: Define some tools which will be useful *)
  let app   : p_term -> p_term list -> p_term = List.fold_left P.appl in
  let _  : p_term list -> p_term -> p_term = fun ts f -> app f ts in
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
  let p_iden = P.iden rec_sym.sym_name in
  let p_patt = P.patt0 "p" in
  let head   = P.appl p_iden p_patt in
  let arg : sym list -> p_term = fun l  ->
    let rec aux : sym list -> p_term -> p_term = fun l acc ->
      match l with
      | []   -> acc
      | t::q ->
          let p_patt = P.patt0 ("p" ^ t.sym_name) in
          aux q (P.appl acc p_patt)
    in
    aux l head
  in
  let common_head = arg cons_list in

  (* STEP 2: Create each p_rule according to a constructor *)
  (* [gen_rule_cons cons_sym] creates a p_rule according to a constructor
     [cons_sym]. *)
  let gen_rule_cons : sym -> p_rule = fun cons_sym ->
    let p_patt = P.patt0 ("p" ^ cons_sym.sym_name) in (* RHS *)
    let t_ident = P.iden cons_sym.sym_name in (* LHS *)
    let rec aux : p_term list -> p_term -> term -> int -> p_patt * p_term =
      fun arg_list p t i ->
      match Basics.get_args t with
      | (Symb(s), ts) ->
          if s == ind_sym then
            (*let arg_hyp_rec_list = List.rev arg_hyp_rec_list in
            let rhs_x =
              List.fold_left (fun acc (a,b) -> match b with
                                             | None -> P.appl acc a
                                             | Some b -> P.appl (P.appl acc a) b)
                p_patt arg_hyp_rec_list in
            let lhs_end =
              List.fold_left (fun acc (a,_) -> P.appl acc a) t_ident arg_hyp_rec_list
            in*)





            
            (*let rec ert : (p_term * p_term option) list -> p_term -> p_term =
              fun l acc->
              match l with
              | []        -> acc
              | (a, b)::q -> match b with
                             | None   -> ert q (P.appl acc a)
                             | Some b -> ert q (P.appl (P.appl acc a) b)
            in*)
            (*let rec ert2 : (p_term * p_term option) list -> p_term -> p_term =
              fun l acc->
              match l with
              | []        -> acc
              | (a, _)::q -> ert2 q (P.appl acc a)
            in*)
            
            (*let arg_hyp_rec_list = List.rev arg_hyp_rec_list in*)
            (*let rec ert : (p_term * p_term option) list -> p_term -> p_term =
              fun l acc->
              match l with
              | []        -> acc
              | (a, b)::q -> let res = ert q acc in
                             match b with
                             | None   -> P.appl res a
                             | Some b -> P.appl (P.appl res a) b
            in
            let rec ert2 : (p_term * p_term option) list -> p_term -> p_term =
              fun l acc->
              match l with
              | []        -> acc
              | (a, _)::q -> let res = ert2 q acc in
                             P.appl res a
            in*)
            (*let l_left = List.rev_map ert arg_hyp_rec_list in
            let fun_left = fun ((arg, hyp), q) -> P.appl (P.appl (arg, hyp), q) in*)
            (*let fun_right = fun ((arg, _), q) -> P.appl arg q in
            let tmp = fun f t -> List.fold_left f t arg_hyp_rec_list in*)
            (*let lhs_end = ert2 arg_hyp_rec_list t_ident in*)
              (*let (arg_list, hyp_rec_list) =
                fapp (List.rev arg_hyp_rec_list) in
              arg_list t_ident, arg_list p_patt*)

            let lhs_end = app t_ident (List.rev arg_list) in
            (*let ts = List.map type_to_pattern ts in*)
            let arg_type = P.nb_wild common_head (List.length ts) in
            let lhs_x = P.appl arg_type lhs_end in
            (*let rhs_x = app rhs_x_head hyp_rec_list in*)
            if !log_enabled then
              log_ind "The rule [%a] --> %a"
                Pretty.pp_p_term lhs_x Pretty.pp_p_term p;
            (lhs_x, p)
            else assert false (* See the function named "principle" *)
      | (Prod(a, b), _) ->
          let (_,b) = Basics.unbind_name b in
          begin
            match Basics.get_args a with
            | (Symb(s), ts) ->
                let arg_patt =
                  P.patt0 ("x" ^ (string_of_int i))
                in
                if s == ind_sym then
                  (*let ts = List.map type_to_pattern ts in*)
                  let arg_type = P.nb_wild common_head (List.length ts) in
                  let hyp_rec_x = P.appl arg_type arg_patt in
                  aux (arg_patt::arg_list) (P.appl (P.appl p arg_patt) hyp_rec_x) b (i+1)
                else
                  aux (arg_patt::arg_list) (P.appl p arg_patt) b (i+1)
            | _ -> assert false (* See the function named "principle" *)
          end
      | _ -> assert false (* See the function named "principle" *)
    in
    Pos.none (aux [] p_patt (!(cons_sym.sym_type)) 0)
  in

  (* STEP 3: Build all the p_rules *)
  List.rev (List.map gen_rule_cons cons_list)
   *)
