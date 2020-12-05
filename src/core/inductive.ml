(** Generation of induction principles.

   We only consider first-order dependent types (no functional
   arguments). Polymorphic types can be encoded by using codes. In case of a
   mutually defined types, we generate an induction for each type. A single
   induction principle can be defined from those individual induction
   principles by using a conjunction operator.

   In the OCaml code, the prefix "ind" is used for inductive types. The prefix
   "rec" is used for recursors, aka induction principles. *)

open! Lplib
open Timed
open Pos
open Console
open Terms
open Print
open Syntax

(** Logging function for generating of inductive principle. *)
let log_ind = new_logger 'g' "indu" "generating induction principle"
let log_ind = log_ind.logger

(** Type for inductive type definitions. *)
type inductive = (sym * sym list) list

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

(** [check_typ_ind pos rec_typ] checks that the type of [rec_typ] is
    TYPE. [pos] is the position of the correspoding inductive type. *)
let check_rec_type : popt -> term -> unit = fun pos rec_typ ->
  match Typing.infer [] rec_typ with
  | Some t ->
      begin
      match unfold t with
      | Type   -> ()
      | _ -> fatal pos "The type of the generated inductive principle of [%a]
                        isn't the constant TYPE. Please, raise an issue."
               pp_term rec_typ
      end
  | None   ->
      fatal pos "The type of the generated inductive principle of
                 [%a] isn't typable. Please, raise an issue."
        pp_term rec_typ

(** [gen_ind_typ_codom pos ind_sym codom s] assumes that the type of [ind_sym]
   is of the form [Π(i1:a1),...,Π(in:an), TYPE]. It then generates a [tbox]
   similar to this type except that [TYPE] is replaced by [codom
   [i1;...;in]]. The string [s] is used as prefix for the variables [ik]. *)
let gen_ind_typ_codom : popt -> sym -> (tbox list -> tbox) -> string -> tbox =
  fun pos ind_sym codom s ->
  let rec aux : tvar list -> term -> tbox = fun xs a ->
    match Basics.get_args a with
    | (Type, _) -> codom (List.rev_map _Vari xs)
    | (Prod(a,b), _) ->
        let (x,b) = Basics.unbind_name b s in
        _Prod (lift a) (Bindlib.bind_var x (aux (x::xs) b))
    | _ -> fatal pos "The type of %a is not supported" pp_symbol ind_sym
  in aux [] !(ind_sym.sym_type)

(** [prf_of p c ts t] returns the term [c.symb_prf (p t1 ... tn t)] where ts =
   [ts1;...;tsn]. *)
let prf_of : config -> tvar -> tbox list -> tbox -> tbox = fun c p ts t ->
  _Appl_symb c.symb_prf [_Appl (_Appl_list (_Vari p) ts) t]

(** compute safe prefixes for predicate and constructor argument variables. *)
let gen_safe_prefixes : inductive -> string * string = fun ind_list ->
  let clashing_names =
    let add_name_from_sym set sym =
      let s = sym.sym_name in
      if s <> "" && (s.[0] = 'x' || s.[0] = 'p') then Extra.StrSet.add s set
      else set
    in
    let add_names_from_ind set (sym_ind, sym_cons_list) =
      let set = add_name_from_sym set sym_ind in
      List.fold_left add_name_from_sym set sym_cons_list
    in
    List.fold_left add_names_from_ind Extra.StrSet.empty ind_list
  in
  let p_str = Extra.get_safe_prefix "p" clashing_names in
  let x_str = Extra.get_safe_prefix "x" clashing_names in
  p_str, x_str

(** Type of association maps for associating some useful data for the
   generation of induction principles to each inductive type. *)
type sym_pred_map = (sym * (tvar * tbox * tbox)) list

(** [create_sym_pred_map pos c ind_list p_str x_str] builds an association
   list mapping each inductive type symbol of [ind_list] in reverse order to
   some data useful for generating the induction principles:

- a predicate variable (e.g. p)

- its type (e.g. Nat -> Prop)

- its conclusion (e.g. Πx, π (p x))

[p_str] is used as prefix for predicate variable names, and [x_str] as prefix
   for the names of the variable arguments of the predicate. *)
let create_sym_pred_map :
      popt -> config -> inductive -> string -> string -> sym_pred_map =
  fun pos c ind_list p_str x_str ->
  let prop = _Symb c.symb_Prop in
  let create_sym_pred_data i (ind_sym,_) =
    (* predicate variable *)
    let p_str = p_str ^ string_of_int i in
    let p = Bindlib.new_var mkfree p_str in
    (* predicate type *)
    let codom ts = _Impl (_Appl_symb ind_sym ts) prop in
    let p_type = gen_ind_typ_codom pos ind_sym codom p_str in
    (* predicate conclusion *)
    let codom ts =
      let x = Bindlib.new_var mkfree x_str in
      let t = Bindlib.bind_var x (prf_of c p ts (_Vari x)) in
      _Prod (_Appl_symb ind_sym ts) t
    in
    let conclusion = gen_ind_typ_codom pos ind_sym codom p_str in
    (ind_sym, (p, p_type, conclusion))
  in
  List.rev_mapi create_sym_pred_data ind_list

(** [fold_cons_typ pos codom inj_var build_rec_hyp domrec dom ind_sym cons_sym
    f_rec f_not_rec init s sym_pred_map] generates some value iteratively
    by going through the structure of [cons_sym.sym_type]. The argument [pos]
    is the position of the command inductive where the inductive type was
    defined. The symbol [ind_sym] is the type of the current inductive type,
    and the symbol [cons_sym] is the current constructor. If you would like to
    store a temporary result, the initial value is [init], and you can change
    this value in the recursive case with the function [f_rec res x rec_hyp],
    and on the other case with the function [f_not_rec res x]. The string [s]
    is the prefix of variables' name. It's useful for the function [inj_var]
    to have names with no clash. The data structure [sym_pred_map] maps
    every inductive type to a predicate variable and its type.
    In this iteration, we keep track of the variables [xs] we went through
    (the last variable comes first) and some accumulator [acc:'a]. Note that,
    at the beginning, the function [fold_cons_typ] is equal to
    [aux [] init  !(cons_sym.sym_type)] where
    [aux : 'b list -> 'a -> term -> 'c = fun xs acc a].

    During an iteration, there are several cases:

      1) If the current type is of the form [ind_sym ts], then we call
         [codom ts xs acc].

      2) If the current type is a product of the form [Π(x:ind_sym ts), b],
         then we are in case of recursive occurrences, so the function
         [build_rec_hyp s p ts x] builds the recursive hypothesis associated,
         then the function [domrec a x rec_hyp next] is applied to conclude
         the building ([rec_hyp] is the current recursive hypothesis and
         [next] is the result of the recursive call).

      3) If the current type is a product [Π(x:a), b] not of the previous
         form, then the function [dom a x next] is called.

      4) Any other case is an error. *)
let fold_cons_type (pos : popt)
      (codom : tvar -> term list -> 'b list -> 'a -> 'c)
      (inj_var : 'b list -> tvar -> 'b)
      (build_rec_hyp : sym -> tvar -> term list -> 'b -> 'a)
      (domrec : term -> 'b -> 'a -> 'c -> 'c) (dom : term -> 'b -> 'c -> 'c)
      (ind_sym : sym) (cons_sym : sym) (f_rec : 'a -> 'b -> 'a -> 'a)
      (f_not_rec : 'a -> 'b -> 'a) (init : 'a) (s : string)
      (sym_pred_map : sym_pred_map) : 'c =
  let rec aux : 'b list -> 'a -> term -> 'c = fun xs acc a ->
    match Basics.get_args a with
    | (Symb(s), ts) ->
        if s == ind_sym then
          let p,_,_ = List.assq s sym_pred_map in
          codom p ts xs acc
        else fatal pos "%a is not a constructor of %a"
               pp_symbol cons_sym pp_symbol ind_sym
    | (Prod(a,b), _) ->
       let (x,b) = Basics.unbind_name b s in
       let x = inj_var xs x in
       begin
         match Basics.get_args a with
         | (Symb(s), ts) ->
             begin
               match List.assq_opt s sym_pred_map with
               | Some (p,_,_) ->
                   let rec_hyp = build_rec_hyp s p ts x in
                   let next = aux (x::xs) (f_rec acc x rec_hyp) b in
                   domrec a x rec_hyp next
               | None ->
                   let next = aux (x::xs) (f_not_rec acc x) b in
                   dom a x next
             end
         | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
       end
    | _ -> fatal pos "The type of %a is not supported" pp_symbol cons_sym
  in aux [] init !(cons_sym.sym_type)

(** [gen_rec_type ss pos ind_list] generates the induction principles for each
   type in the inductive definition [ind_list] defined at the position
   [pos]. Each recursive argument is followed by its induction hypothesis. For
   instance, with [inductive T:TYPE := c: T->T->T], we get [ind_T: Πp:T->Prop,
   (Πx0:T, π(p x0)-> Πx1:T, π(p x1)-> π(p (c x0 x1)) -> Πx:T, π(p x)]. *)
let gen_rec_types :
      config -> Sig_state.t -> popt -> inductive -> sym_pred_map -> string
      -> term list =
  fun c ss pos ind_list sym_pred_map x_str ->

  (* [case_of ind_sym cons_sym] creates the clause for the constructor
     [cons_sym] in the induction principle of [ind_sym]. *)
  let case_of : sym -> sym -> tbox = fun ind_sym cons_sym ->
    let codom : tvar -> term list -> tvar list -> 'a -> tbox =
      fun p ts xs _ ->
      prf_of c p (List.map lift ts)
        (_Appl_symb cons_sym (List.rev_map _Vari xs))
    in
    let inj_var : tvar list -> tvar -> tvar = fun _ x -> x in
    let build_rec_hyp : sym -> tvar -> term list -> tvar -> tbox =
      fun _ p ts x ->
      prf_of c p (List.map lift ts) (_Vari x)
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
    let init : tbox = _Type in
    fold_cons_type pos codom inj_var build_rec_hyp domrec dom ind_sym
      cons_sym f_rec f_not_rec init x_str sym_pred_map
  in

  (* Generates an induction principle for each type. *)
  let gen_rec_type (_, (_,_,conclusion)) =
    let add_clause_cons ind_sym cons_sym c =
      _Impl (case_of ind_sym cons_sym) c
    in
    let add_clauses_ind (ind_sym, cons_sym_list) c =
      List.fold_right (add_clause_cons ind_sym) cons_sym_list c
    in
    let conclusion = List.fold_right add_clauses_ind ind_list conclusion in
    let add_quantifier c (_,(v,a,_)) = _Prod a (Bindlib.bind_var v c) in
    let conclusion = List.fold_left add_quantifier conclusion sym_pred_map in
    Bindlib.unbox conclusion
  in
  let res = List.map gen_rec_type sym_pred_map in
  (if !log_enabled then
    let print_informative_message (ind_sym,_) elt =
      log_ind "The induction principle of the inductive type [%a] is %a"
        Pretty.pp_ident (Pos.none ind_sym.sym_name) Print.pp_term elt
    in
    List.iter2 print_informative_message sym_pred_map res);
  res

(** [gen_rec_rules pos ind_list sym_pred_map] returns the p_rules associa-
    ted to the list of inductive types [ind_typ_list], defined at the position
    [pos], the list of theirs induction principles [rec_sym_list] and the list
    of lists of constructors [cons_list_list], where
    [ind_list = List.combine3 ind_typ_list cons_list_list rec_sym_list].
    That means, for only one inductive type, the command
    inductive T : Π(i1:A1),...,Π(im:Am), TYPE := c1:T1 | ... | cn:Tn generates
    a rule for each constructor. If Ti = Π(b1:B1), ... , Π(bk:Bk), T then the
    rule for ci is:
    rule ind_T p pic1 ... picn _ ... _ (ci x0 ... x(k-1)) -->
    pici x0 t0? ... x(k-1) t(k-1)?
    with m underscores and tj? = nothing if xj isn't a value of the inductive
    type and tj? = (ind_T p pic1 ... picn _ ... _ xj) if xj is a value of the
    inductive type T (i.e. xj = T v1 ... vm).
    Note: There cannot be name clashes between pattern variable names and
    function symbols names since pattern variables are prefixed by $. *)
let gen_rec_rules :
      popt -> inductive -> sym list -> sym_pred_map -> p_rule list list =
  fun pos ind_list rec_sym_list sym_pred_map ->

  (* [commond_head n] generates the common head of the rule LHS's of a
     recursor symbol of name [n]. *)
  let lhs_head : string -> p_term = fun sym_name ->
    let head = P.iden sym_name in
    let add_patt t n = P.appl t (P.patt0 n) in
    (* add a predicate variable for each inductive type *)
    let head =
      let add_pred (_,(v,_,_)) head = add_patt head (Bindlib.name_of v) in
      List.fold_right add_pred sym_pred_map head
    in
    (* add a case variable for each constructor *)
    let add_case head cons_sym = add_patt head ("pi" ^ cons_sym.sym_name) in
    let add_ind head (_, cons_sym_list) =
      List.fold_left add_case head cons_sym_list
    in
    List.fold_left add_ind head ind_list
  in

  (* [gen_rule_cons ind_sym rec_sym cons_sym] generates the p_rule of the
     recursor [rec_sym] of the inductive type [ind_sym] for the constructor
     [cons_sym]. *)
  let gen_rule_cons : sym -> sym -> sym -> p_rule =
    fun ind_sym rec_sym cons_sym ->
    let codom : tvar -> term list -> p_term list -> p_term -> p_rule =
      fun _ ts xs p ->
      let rec_arg = P.fold_appl (P.iden cons_sym.sym_name) (List.rev xs) in
      let lhs_head = lhs_head rec_sym.sym_name in
      let lhs = P.appl (P.appl_wild lhs_head (List.length ts)) rec_arg in
      if !log_enabled then
        log_ind "The rule [%a] --> %a"
          Pretty.pp_p_term lhs Pretty.pp_p_term p;
      P.rule lhs p
    in
    let inj_var : p_term list -> tvar -> p_term = fun xs _ ->
      P.patt0 ("x" ^ (string_of_int (List.length xs)))
    in
    let build_rec_hyp : sym -> tvar -> term list -> p_term -> p_term =
      fun s _ ts x ->
      let lhs_head = lhs_head ("ind_" ^ s.sym_name) in (* @FIX *)
      let arg_type = P.appl_wild lhs_head (List.length ts) in
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
    let init : p_term = P.patt0 ("pi" ^ cons_sym.sym_name) in
    fold_cons_type pos codom inj_var build_rec_hyp domrec dom ind_sym
      cons_sym f_rec f_not_rec init "" sym_pred_map
  in

  (* generates all rules *)
  let gen_rules_ind (ind_sym, cons_sym_list) rec_sym =
    List.map (gen_rule_cons ind_sym rec_sym) cons_sym_list
  in
  List.map2 gen_rules_ind ind_list rec_sym_list
