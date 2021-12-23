(** This module provides a function to translate a signature to the XTC format
    used in the termination competition.
    @see <http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB/file/tip/xml/xtc.xsd>
*)

open! Lplib
open Lplib.Base
open Lplib.Extra
open Timed
open Core
open Term
open Print

(** [print_sym ppf s] outputs the fully qualified name of [s] to
   [ppf]. Modules are separated with ["."]. *)
let print_sym : sym pp = fun ppf s ->
  out ppf "%a.%a" pp_path s.sym_path pp_uid s.sym_name

type symb_status = Object_level | Basic_type | Type_cstr

(** [status s] returns [Type_cstr] if [s] has a type of the form
    T1 -> ... -> Tn -> [TYPE] with n > 0, [Basic_type] if [s] has type [TYPE]
    and [Object_level] otherwise. *)
let status : sym -> symb_status = fun s ->
  (* the argument [b] of [is_arrow_kind] is a boolean saying if we have
     already gone under a product *)
  let rec is_arrow_kind : Term.term -> bool -> symb_status = fun t b ->
    match t with
    | Prod(_,b) -> is_arrow_kind (snd (Bindlib.unbind b)) true
    | Type      -> if b then Type_cstr else Basic_type
    | _         -> Object_level
  in is_arrow_kind !(s.sym_type) false

(** [print_term ppf p] outputs XTC format corresponding to the term [t], to
    [ppf]. *)
let rec print_term : int -> string -> term pp = fun i s ppf t ->
  match unfold t with
  (* Forbidden cases. *)
  | Meta(_,_)               -> assert false
  | TRef(_)                 -> assert false
  | TEnv(_,_)               -> assert false
  | Wild                    -> assert false
  | Kind                    -> assert false
  (* [TYPE] and products are necessarily at type level *)
  | Type                    -> assert false
  | Prod(_,_)               -> assert false
  (* Printing of atoms. *)
  | Vari(x)                 -> out ppf "<var>v_%a</var>@." pp_var x
  | Symb(s)                 ->
     out ppf "<funapp>@.<name>%a</name>@.</funapp>@." print_sym s
  | Patt(j,n,ts)            ->
     if ts = [||] then out ppf "<var>%s_%i_%s</var>@." s i n else
       print_term i s ppf
         (Array.fold_left (fun t u -> mk_Appl(t,u)) (mk_Patt(j,n,[||])) ts)
  | Appl(t,u)               -> out ppf "<application>@.%a%a</application>@."
                                 (print_term i s) t (print_term i s) u
  | Abst(a,t)               ->
     let (x, t) = Bindlib.unbind t in
     out ppf "<lambda>@.<var>v_%a</var>@.<type>%a<type>@.%a</lambda>@."
       pp_var x (print_type i s) a (print_term i s) t
  | LLet(_,t,u)             -> print_term i s ppf (Bindlib.subst u t)

and print_type : int -> string -> term pp = fun i s ppf t ->
  match unfold t with
  (* Forbidden cases. *)
  | Meta(_,_)               -> assert false
  | TRef(_)                 -> assert false
  | TEnv(_,_)               -> assert false
  | Wild                    -> assert false
  | Kind                    -> assert false
  (* Variables are necessarily at object level *)
  | Vari(_)                 -> assert false
  | Patt(_,_,_)             -> assert false
  (* Printing of atoms. *)
  | Type                    -> out ppf "<TYPE/>@."
  | Symb(s)                 -> out ppf "<basic>%a</basic>@." print_sym s
  | Appl(t,u)               -> out ppf "<application>@.%a%a</application>@."
                      (print_type i s) t (print_term i s) u
  | Abst(a,t)               ->
     let (x, t) = Bindlib.unbind t in
     out ppf "<lambda>@.<var>v_%a</var>@.<type>%a<type>@.%a</lambda>@."
       pp_var x (print_type i s) a (print_type i s) t
  | Prod(a,b)               ->
     if Bindlib.binder_constant b
     then
       out ppf "<arrow>@.<type>@.%a</type>@.<type>@.%a</type>@.</arrow>@."
         (print_type i s) a
         (print_type i s) (snd (Bindlib.unbind b))
     else
       let (x, b) = Bindlib.unbind b in
       out ppf "<arrow>@.<var>v_%a</var>@." pp_var x;
       out ppf "<type>@.%a</type>@.<type>@.%a</type>@.</arrow>"
         (print_type i s) a (print_type i s) b
  | LLet(_,t,u)             -> print_type i s ppf (Bindlib.subst u t)

(** [print_rule ppf s r] outputs the rule declaration corresponding [r] (on
   the symbol [s]), to [ppf]. *)
let print_rule : Format.formatter -> int -> sym -> rule -> unit =
  fun ppf i s r ->
  (* Print the rewriting rule. *)
  let lhs = add_args (mk_Symb s) r.lhs in
  out ppf "<rule>@.<lhs>@.%a</lhs>@." (print_term i s.sym_name) lhs;
  let rhs = LibTerm.term_of_rhs r in
  out ppf "<rhs>@.%a</rhs>@.</rule>@." (print_term i s.sym_name) rhs

(** [print_tl_rule] is identical to [print_rule] but for type-level rule  *)
let print_tl_rule : Format.formatter -> int -> sym -> rule -> unit =
  fun ppf i s r ->
  (* Print the type level rewriting rule. *)
  let lhs = add_args (mk_Symb s) r.lhs in
  out ppf "<typeLevelRule>@.<TLlhs>@.%a</TLlhs>@."
    (print_type i s.sym_name) lhs;
  let rhs = LibTerm.term_of_rhs r in
  out ppf "<TLrhs>@.%a</TLrhs>@.</typeLevelRule>@."
    (print_type i s.sym_name) rhs

(** [get_vars s r] returns the list of variables used in the rule [r],
    in the form of a pair containing the name of the variable and its type,
    inferred by the solver. *)
let get_vars : sym -> rule -> (string * Term.term) list = fun s r ->
  let rule_ctx : tvar option array = Array.make (Array.length r.vars) None in
  let var_list : tvar list ref = ref [] in
  let rec subst_patt v t =
    match t with
    | Type
    | Kind
    | TEnv (_, _)
    | Meta (_, _)
    | TRef _
    | Wild
    | Prod (_, _)
    | LLet(_) (* No let in LHS *)
    | Vari _              -> assert false
    | Symb (_)            -> t
    | Abst (t1, b)        ->
       let (x,t2) = Bindlib.unbind b in
       mk_Abst(
           subst_patt v t1,
           Bindlib.unbox (Bindlib.bind_var x (lift (subst_patt v t2)))
         )
    | Appl (t1, t2)        -> mk_Appl(subst_patt v t1, subst_patt v t2)
    | Patt (None, x, a)    ->
       let v_i = new_tvar x in
       var_list := v_i :: !var_list;
       Array.fold_left (fun acc t -> mk_Appl(acc,t)) (mk_Vari v_i) a
    | Patt (Some(i), x, a) ->
       if v.(i) = None
       then
         (let v_i = new_tvar x in
          var_list := v_i :: !var_list;
          v.(i) <- Some(v_i));
       let v_i =
         match v.(i) with
         |Some(vi) -> vi
         |None -> assert false
       in
       Array.fold_left (fun acc t -> mk_Appl(acc,t)) (mk_Vari v_i) a
  in
  let lhs =
    List.fold_left
      (fun t h -> mk_Appl(t, subst_patt rule_ctx (unfold h)))
      (mk_Symb s) r.lhs
  in
  let ctx =
    let p = new_problem() in
    let f l x = (x, (mk_Meta(LibMeta.fresh p mk_Type 0,[||])), None) :: l in
    List.fold_left f [] !var_list
  in
  let p = new_problem() in
  match Infer.infer_noexn p ctx lhs with
  | None -> assert false
  | Some _ ->
  let cs = List.rev_map (fun (_,t,u) -> (t,u)) !p.to_solve in
  let ctx = List.map (fun (x,a,_) -> (x,a)) ctx in
  List.map (fun (v,ty) -> Bindlib.name_of v, List.assoc ty cs) ctx

(** [to_XTC ppf sign] outputs a XTC representation of the rewriting system of
    the signature [sign] to [ppf]. *)
let to_XTC : Format.formatter -> Sign.t -> unit = fun ppf sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let iter_symbols : (sym -> unit) -> unit = fun fn ->
    (* Iterate on all symbols of a signature, excluding ghost symbols. *)
    let iter_symbols sign =
      let not_on_ghosts _ s = if not (Unif_rule.is_ghost s) then fn s in
      StrMap.iter not_on_ghosts Sign.(!(sign.sign_symbols))
    in
    List.iter (fun (_, sign) -> iter_symbols sign) deps
  in
  (* Print the prelude and the postlude. *)
  let prelude =
    [ "<?xml version=\"1.0\" encoding=\"UTF-8\"?>"
    ; "<?xml-stylesheet href=\"xtc2tpdb.xsl\" type=\"text/xsl\"?>"
    ; "<problem xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\""
    ; "type=\"termination\""
    ; "xsi:noNamespaceSchemaLocation=\"http://dev.aspsimon.org/xtc.xsd\">"
    ; "<trs>" ]
  in
  let postlude =
    [ "</trs>"
    ; "<strategy>FULL</strategy>"
    ; "<metainformation>"
    ; "<originalfilename>Produced from a Dedukti file</originalfilename>"
    ; "</metainformation>"
    ; "</problem>" ]
  in
  (* Print the object level rewrite rules. *)
  let print_object_rules : sym -> unit = fun s ->
    if status s = Object_level then
      match !(s.sym_def) with
      | Some(d) ->
         out ppf
           "<rule>@.<lhs>@.<funapp>@.<name>%a</name>@.</funapp>@.</lhs>@."
           print_sym s;
         out ppf
           "<rhs>@.%a</rhs>@.</rule>@." (print_term 0 s.sym_name) d
      | None    ->
         let c = ref 0 in
         List.iter (fun x -> incr c; print_rule ppf !c s x) !(s.sym_rules)
  in
  (* Print the type level rewrite rules. *)
  let print_type_rules : sym -> unit = fun s ->
    if status s != Object_level then
      match !(s.sym_def) with
      | Some(d) ->
         out ppf
           "<rule>@.<lhs>@.<funapp>@.<name>%a</name>@.</funapp>@.</lhs>@."
           print_sym s;
         out ppf
           "<rhs>@.%a</rhs>@.</rule>@." (print_term 0 s.sym_name) d
      | None    ->
         let c = ref 0 in
         List.iter (incr c; print_tl_rule ppf !c s) !(s.sym_rules)
  in
  (* Print the variable declarations *)
  let print_vars : sym -> unit = fun s ->
    let c = ref 0 in
    List.iter
      (fun r ->
        incr c;
        List.iter
          (fun (x,ty) ->
            out ppf
              "<varDeclaration>@.<var>%s_%i_%s</var>@." s.sym_name !c x;
            out ppf
              "<type>@.%a</type>@.</varDeclaration>@."
              (print_type !c s.sym_name) ty
          )
          (get_vars s r)
      )
      !(s.sym_rules)
  in
  (* Print the symbol declarations at object level. *)
  let print_symbol : sym -> unit = fun s ->
    if status s = Object_level then (
      out ppf "<funcDeclaration>@.<name>%a</name>@." print_sym s;
      out ppf
        "<typeDeclaration>@.<type>@.%a</type>@."
        (print_type 0 s.sym_name) !(s.sym_type);
      out ppf "</typeDeclaration>@.</funcDeclaration>@."
    )
  in
  (* Print the type constructor declarations. *)
  let print_type_cstr : sym -> unit = fun s ->
    (* We don't declare type constant which do not take arguments for
       compatibility issue with simply-typed higher order category of the
       competition. *)
    if status s = Type_cstr then (
      out ppf "<typeConstructorDeclaration>@.<name>%a</name>@."
        print_sym s;
      out ppf "<typeDeclaration>@.<type>@.%a</type>@."
        (print_type 0 s.sym_name) !(s.sym_type);
      out ppf "</typeDeclaration>@.</typeConstructorDeclaration>@."
    )
  in
  List.iter (out ppf "%s@.") prelude;
  out ppf "<rules>@.";
  iter_symbols print_object_rules;
  out ppf "</rules>@.";
  let type_rule_presence = ref false in
  iter_symbols
    (fun s ->
      if status s != Object_level && !(s.sym_def) != None
         && !(s.sym_rules) != []
      then type_rule_presence := true);
  if !type_rule_presence then (
    out ppf "<typeLevelRules>@.";
    iter_symbols print_type_rules;
    out ppf "</typeLevelRules>@."
  );
  out ppf "<higherOrderSignature>@.";
  out ppf "<variableTypeInfo>@.";
  iter_symbols print_vars;
  out ppf "</variableTypeInfo>@.";
  out ppf "<functionSymbolTypeInfo>@.";
  iter_symbols print_symbol;
  out ppf "</functionSymbolTypeInfo>@.";
  let type_cstr_presence = ref false in
  iter_symbols
    (fun s -> if status s = Type_cstr then type_cstr_presence := true);
  if !type_cstr_presence then (
    out ppf "<typeConstructorTypeInfo>@.";
    iter_symbols print_type_cstr;
    out ppf "</typeConstructorTypeInfo>@."
  );
  out ppf "</higherOrderSignature>@.";
  List.iter (out ppf "%s@.") postlude
