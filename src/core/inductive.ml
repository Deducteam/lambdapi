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

(** [check_typ_ind rec_typ] checks if the type of the term [rec_typ] is the
    constant TYPE. *)
let check_type_ind : popt -> term -> unit = fun pos rec_typ ->
  match Typing.infer [] rec_typ with
  | Some t ->
      begin
        let err_msg t =
          fatal pos "The type of the generated inductive \
                     principle of [%a] can't begin by %s. \
                     Please, raise an issue." pp_term rec_typ t
        in
        match t with
        | Type   -> ()
        | Symb _ -> err_msg "a symbol"
        | Prod _ -> err_msg "a dependent product"
        | Appl _ -> err_msg "an application"
        | Vari _ -> err_msg "a variable"
        | Kind   -> err_msg "the constant KIND"
        | Meta _ -> err_msg "a meta-variable application"
        | Patt _ -> err_msg "a pattern variable application"
        | TEnv _ -> err_msg "a term environment"
        | Wild   -> err_msg "a wildcard"
        | TRef _ -> err_msg "a reference cell"
        | LLet _ -> err_msg "a let-construction"
        | Abst _ -> err_msg "a abstraction"
      end
  | None   ->
      fatal pos "The type of the generated inductive principle of
                 [%a] isn't typable. Please, raise an issue."
        pp_term rec_typ

(** [gen_ind_typ_codom pos ind_sym codom] assumes that the type of [ind_sym]
    is of the form [Π(i1:a1),...,Π(in:an), TYPE]. It then generates a [tbox]
    similar to this type except that [TYPE] is replaced by
    [codom [i1;...;in]]. *)
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

module T =
  struct

    (** [fold_app a [b1;...;bn]] returns (... ((a b1) b2) ...) bn. *)
    let fold_app  : tbox -> tbox list -> tbox = List.fold_left _Appl

    (** [fold_app_special f ts] returns the same result that
        fold_app (_Symb [f]) [ts]. *)
    let fold_app_special : sym -> tbox list -> tbox = fun f ts ->
      fold_app (_Symb f) ts

    (** [prf_of p c ts t] returns a proof of the form
        c.symb_prf ( (((p ts1) ...) tsn) t) where ts = [ts1;...;tsn]. *)
    let prf_of : tvar -> config -> tbox list -> tbox -> tbox = fun p c ts t ->
      fold_app_special c.symb_prf [_Appl (fold_app (_Vari p) ts) t]
  end

(** [preprocessing pos c ind_typ_list] creates an associated list between
    an inductive type and its predicat, and the list of conclusions, according
    to the list of the type of the inductive types [ind_typ_list]. *)
let preprocessing :
  popt -> config -> sym list -> ((sym * (tvar * tbox)) list * tbox list) =
  fun pos c ind_typ_list ->
  let prop = _Symb c.symb_Prop in

  let rec aux :
    int -> (sym * (tvar * tbox)) list -> tbox list -> sym list
    -> ((sym * (tvar * tbox)) list * tbox list) =
    fun i assoc_predicats conclusion_list ind_typ_list ->
    match ind_typ_list with
    | [] -> assoc_predicats, conclusion_list
    | ind_sym::q ->
        (* STEP 1 - Create the predicat (name + type) associated to the
           symbol [ind_sym]. *)
          (* A - Create the name of the predicat. *)
        let p_name = "p" ^ (string_of_int i) in
        let p = Bindlib.new_var mkfree p_name in
          (* B - Create the type of the predicat p. *)
        let codom ts = _Impl (T.fold_app_special ind_sym ts) prop in
        let p_type = gen_ind_typ_codom pos ind_sym codom in
        (* STEP 2 - Create the conclusion of the inductive principle
           associated to [ind_sym]. *)
        let codom ts =
          let x = Bindlib.new_var mkfree "x" in
          let t = Bindlib.bind_var x (T.prf_of p c ts (_Vari x)) in
          _Prod (T.fold_app_special ind_sym ts) t
        in
        let conclusion = gen_ind_typ_codom pos ind_sym codom in
        aux (i+1) ((ind_sym, (p, p_type))::assoc_predicats)
          (conclusion::conclusion_list) q
  in
  aux 0 [] [] ind_typ_list

(** [fold_cons_typ pos codom get_name build_rec_hyp domrec dom ind_sym
    cons_sym f_rec f_not_rec acc] generates some value iteratively by going
    through the structure of [cons_sym.sym_type].
    We introduce some notations:
      - A product Π([x] : [a]), [b]
      - [xs] stores each variable of the intial product during the computation
      - [ts] is the arguments of the current symbol
      - [rec_hyp] is the current recursive hypothesis
      - [next] is the result of the recursive call
      - [res] is a computation built incrementally
    Now, we can describe each argument of the function [fold_cons_typ]:
      - The argument [pos] is the position of the command inductive where the
      constructors were defined.
      - On the codomain, the function [codom ts xs res] is called on the
      arguments to which [ind_sym] is applied [ts], the variables of the
      products [xs] (in reverse order) and a computation built incrementally
      [res].
      - In case of a product, the function [get_name b i] splits the product
      [b] and gives a name to the variable if it has none, thanks to the
      number [i].
      - In case of recursive occurrences, the function [build_rec_hyp ts x]
      builds the recursive hypothesis associated, and then the function
      [domrec a x rec_hyp next] is applied to conclude the building.
      - Otherwise, the function [dom a x next] is called.
      - If you would like to store a temporary result, the initial value is
      [acc], and you can change this value in the recursive case with the
      function [f_rec res x rec_hyp], and on the other case with the function
      [f_not_rec res x]. *)
let fold_cons_typ (pos : popt)
      (codom : tvar -> term list -> 'b list -> 'a -> 'c)
      (get_name : tbinder -> int -> 'b * term )
      (build_rec_hyp : sym * (tvar * tbox) -> term list -> 'b -> 'a)
      (domrec : term -> 'b -> 'a -> 'c -> 'c) (dom : term -> 'b -> 'c -> 'c)
      (ind_sym : sym) (cons_sym : sym) (f_rec : 'a -> 'b -> 'a -> 'a)
      (f_not_rec : 'a -> 'b -> 'a) (acc : 'a)
      (assoc_predicat : (sym * (tvar * tbox)) list) : 'c =
  let rec aux : 'b list -> 'a -> int -> term -> 'c = fun xs res i a ->
    match Basics.get_args a with
    | (Symb(s), ts) ->
        if s == ind_sym then
          let p,_ = List.assq s assoc_predicat in
          codom p ts xs res
        else fatal pos "%a is not a constructor of %a"
               pp_symbol cons_sym pp_symbol ind_sym
    | (Prod(a,b), _) ->
       let (x,b) = get_name b i in
       begin
         match Basics.get_args a with
         | (Symb(s), ts) ->
             begin
               match List.assq_opt s assoc_predicat with
               | Some p ->
                   let rec_hyp = build_rec_hyp (s,p) ts x in
                   let next = aux (x::xs) (f_rec res x rec_hyp) (i+1) b in
                   domrec a x rec_hyp next
               | None ->
                   let next = aux (x::xs) (f_not_rec res x) (i+1) b in
                   dom a x next
             end
         | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
       end
    | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
  in aux [] acc 0 !(cons_sym.sym_type)

(** [gen_rec_type ss pos ind_typ_list cons_list_list] generates the induction
    principle for each inductive type in the list [ind_typ_list] (defined at
    the position [pos]) with the list of constructors [cons_list]. Each
    recursive argument is followed by its induction hypothesis. For instance,
    with only one inductive type [inductive T:TYPE := c: T->T->T], we have
    [ind_T: Πp:T->Prop, (Πx0:T, π(p x0)-> Πx1:T, π(p x1)-> π(p (c x0 x1)) ->
    Πx:T, π(p x)]. Indeed, if the user doesn't give a name for an argument
    (in case of no dependent product in fact), a fresh name will create (xi
    with a fresh i). In general, thanks to this function, the command
    inductive T : Π(i1:A1),...,Π(im:Am), TYPE := c1:T1 | ... | cn:Tn generates
    ind_T: Π(p:Π(i1:A1),...,Π(im:Am), T i1 ... im -> Prop), U1 -> ... -> Un ->
    (Π(i1:A1),...,Π(im:Am), Π(t:T i1 ... im), π(p i1 ... im t))
    where Ui is the clause associated to the constructor ci. *)
let gen_rec_type :
      Sig_state.t -> popt -> sym list -> (sym list) list
      -> (term list * (sym * (tvar * tbox)) list) =
  fun ss pos ind_typ_list cons_list_list ->
  let c = get_config ss pos in
  (* STEP 1 - Do preprocessing *)
  let assoc_predicats, conclusion_list = preprocessing pos c ind_typ_list in
  let conclusion_list = List.rev conclusion_list in

  (* STEP 2 - Create each clause according to a constructor *)
  (* [case_of cons_sym] creates a clause according to a constructor
     [cons_sym]. *)
  let case_of : sym -> sym -> tbox = fun ind_sym cons_sym ->
    let codom : tvar -> term list -> tvar list -> 'a -> tbox =
      fun p ts xs _ ->
      T.prf_of p c (List.map lift ts)
        (T.fold_app_special cons_sym (List.rev_map _Vari xs))
    in
    let get_name : tbinder -> int -> tvar * term = fun b _ ->
      Basics.unbind_name b
    in
    let build_rec_hyp : sym * (tvar * tbox) -> term list -> tvar -> tbox =
      fun (_,(p,_)) ts x ->
      T.prf_of p c (List.map lift ts) (_Vari x)
    in
    let domrec : term -> tvar -> tbox -> tbox -> tbox =
      fun a x rec_hyp next ->
      _Prod (lift a) (Bindlib.bind_var x (_Impl rec_hyp next))
    in
    let dom : term -> tvar -> tbox -> tbox = fun a x next ->
      _Prod (lift a) (Bindlib.bind_var x next)
    in
    let f_rec : tbox -> tvar -> tbox -> tbox = fun a _ _ -> a in
    let f_not_rec : tbox -> tvar -> tbox = fun a _ -> a in
    let acc : tbox = _Type in
    fold_cons_typ pos codom get_name build_rec_hyp domrec dom ind_sym
      cons_sym f_rec f_not_rec acc assoc_predicats
  in
  (* Very closed to the function "fold_right2", but "f" is the function
     "fold_right" and it needs a neutral element. *)
  let rec clauses ind_typ_list cons_list_list e =
    match ind_typ_list, cons_list_list with
    | [], [] -> e
    | i::qi, cl::qcl ->
        let res = clauses qi qcl e in
        List.fold_right (fun a b -> _Impl (case_of i a) b) cl res
    | _ -> raise (Invalid_argument "Yours 2 lists have different lengths.")
  in
  let t = List.map (clauses ind_typ_list cons_list_list) conclusion_list in

  (* STEP 3 - Create the induction principle. *)
  let f t =
    List.fold_left
      (fun e (_,(name,typ)) -> _Prod typ (Bindlib.bind_var name e)) t
      assoc_predicats
  in
  let t = List.map f t in
  if !log_enabled then
    let f ind_sym elt =
      log_ind "The induction principle of the inductive type [%a] is %a"
        Pretty.pp_ident (Pos.none ind_sym.sym_name)
        Print.pp_term (Bindlib.unbox elt)
    in
    List.iter2 f ind_typ_list t
  else ();
  (List.map Bindlib.unbox t, assoc_predicats)

(** [gen_rec_rules ind_typ_list cons_list_list assoc_predicats] returns the
    p_rules associated to the list of inductive types [ind_typ_list] and the
    list of lists of constructors [cons_list_list].
    That means, for only one inductive type, the command
    inductive T : Π(i1:A1),...,Π(im:Am), TYPE := c1:T1 | ... | cn:Tn generates
    a rule for each constructor. If Ti = Π(b1:B1), ... , Π(bk:Bk), T then the
    rule for ci is:
    rule ind_T p pic1 ... picn _ ... _ (ci x0 ... x(k-1)) -->
    pici x0 t0? ... x(k-1) t(k-1)?
    with m underscores and tj? = nothing if xj isn't a value of the inductive
    type and tj? = (ind_T p pic1 ... picn _ ... _ xj) if xj is a value of the
    inductive type T (i.e. xj = T v1 ... vm) *)
let gen_rec_rules :
      sym list -> sym list -> (sym list) list -> (sym * (tvar * tbox)) list
      -> p_rule list list =
  fun ind_typ_list rec_sym_list cons_list_list assoc_predicats ->

  (* STEP 1 - Create the common head of the rules *)
  let f e (_, (name, _)) = P.appl e (P.patt0 (Bindlib.name_of name)) in
  let properties head_sym = List.fold_left f head_sym assoc_predicats in
  let add_arg e s =
    P.appl e (P.patt0 ("pi" ^ s.sym_name))
  in
  let common_head head_sym =
    List.fold_left add_arg (properties (P.iden head_sym))
      (List.flatten cons_list_list)
  in

  (* STEP 2 - Create each p_rule according to a constructor *)
  (* [gen_rule_cons cons_sym] creates a p_rule according to a constructor
     [cons_sym]. *)
  let gen_rule_cons :
        sym -> sym -> sym -> p_rule = fun ind_sym rec_sym cons_sym ->
    let pos : popt = None in
    let codom : tvar -> term list -> p_term list -> p_term -> p_rule =
      fun _ ts xs p ->
      let rec_arg = P.fold_appl (P.iden cons_sym.sym_name) (List.rev xs) in
      let common_head = common_head rec_sym.sym_name in
      let lhs = P.appl (P.appl_wild common_head (List.length ts)) rec_arg in
      if !log_enabled then
        log_ind "The rule [%a] --> %a"
          Pretty.pp_p_term lhs Pretty.pp_p_term p;
      P.rule lhs p
    in
    let get_name : tbinder -> int -> p_term * term = fun b i ->
      let (_,b) = Basics.unbind_name b in
      (P.patt0 ("x" ^ (string_of_int i)), b)
    in
    let build_rec_hyp : sym * (tvar * tbox) -> term list -> p_term -> p_term =
      fun (s,_) ts x ->
      let common_head = common_head ("ind_"^s.sym_name) in (* @FIX *)
      let arg_type = P.appl_wild common_head (List.length ts) in
      P.appl arg_type x
    in
    let domrec : term -> p_term -> p_term -> p_rule -> p_rule =
      fun _ _ _ next -> next
    in
    let dom : term -> p_term -> p_rule -> p_rule = fun _ _ next -> next in
    let f_rec : p_term -> p_term -> p_term -> p_term =
      fun p x rec_hyp -> P.appl (P.appl p x) rec_hyp
    in
    let f_not_rec : p_term -> p_term -> p_term = fun p x -> P.appl p x in
    let acc : p_term = P.patt0 ("pi" ^ cons_sym.sym_name) in
    fold_cons_typ pos codom get_name build_rec_hyp domrec dom ind_sym
      cons_sym f_rec f_not_rec acc assoc_predicats
  in

  (* STEP 3 - Build all the p_rules *)
  let f ind_sym rec_sym cons_list =
    List.rev_map (gen_rule_cons ind_sym rec_sym) cons_list
  in
  let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | t1::q1, t2::q2, t3::q3 -> (f t1 t2 t3)::(map3 f q1 q2 q3)
    | _ -> raise (Invalid_argument "Yours 3 lists have different lengths.")
  in
  map3 f ind_typ_list rec_sym_list cons_list_list
