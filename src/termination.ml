(** Temination checking.
    This module allows the translation of a signature in the TPDB format used
    in the termination competition, see Termination Problem Database:
    http://cl2-informatik.uibk.ac.at/mercurial.cgi/TPDB
 *)

open Extra
open Timed
open Console
open Terms

(** Logging function for the termination checker interface. *)
let log_conf = new_logger 'n' "norm" "informations for the termination checker"
let log_conf = log_conf.logger
             
(** [print_sym oc s] outputs the fully qualified name of [s] to [oc]. The name
    is prefixed by ["c_"], and moduls are separated with ["_"], not ["."]. *)
let print_sym : sym pp = fun oc s ->
  let print_path = List.pp Format.pp_print_string "_" in
  Format.fprintf oc "c_%a_%s" print_path s.sym_path s.sym_name

type symb_status = Object_level | Basic_type | Type_cstr
  
(** [status s] returns [Type_cstr] if [s] has a type of the form
    T1 -> ... -> Tn -> [TYPE] with n > 0, [Basic_type] if [s] has type [TYPE]
    and [Object_level] otherwise. *)
let status : sym -> symb_status = fun s ->
  (* the argument [b] of [is_arrow_kind] is a boolean saying if we have already
     gone under a product *)
  let rec is_arrow_kind : Terms.term -> bool -> symb_status = fun t b ->
    match t with
    | Prod(_,b) -> is_arrow_kind (snd (Bindlib.unbind b)) true
    | Type      -> if b then Type_cstr else Basic_type
    | _         -> Object_level
  in is_arrow_kind !(s.sym_type) false
  
(** [print_term oc p] outputs XTC format corresponding to the term [t], to
    the channel [oc]. *)
let rec print_term : int -> string -> term pp = fun i s oc t ->
  let out fmt = Format.fprintf oc fmt in
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
  | Vari(x)                 -> out "<var>v_%s</var>@." (Bindlib.name_of x)
  | Symb(sy,_)              ->
     out "<funapp>@.<name>%a</name>@.</funapp>@." print_sym sy
  | Patt(j,n,ts)            ->
     if ts = [||] then out "<var>%s_%i_%s</var>@." s i n else
       print_term i s oc
         (Array.fold_left (fun t u -> Appl(t,u)) (Patt(j,n,[||])) ts)
  | Appl(Symb(sy,_),_) as t ->
     let args = snd (Basics.get_args t) in
     out "<funapp>@.<name>%a</name>@.%a</funapp>@."
       print_sym sy
       (fun oc l ->
         List.iter
           (fun x -> Format.fprintf oc "<arg>%a</arg>@." (print_term i s) x) l
       ) args
  | Appl(t,u)               -> out "<application>@.%a%a</application>@."
                              (print_term i s) t (print_term i s) u
  (* Abstractions and products are only printed at priority [`Func]. *)
  | Abst(a,t)               ->
     let (x, t) = Bindlib.unbind t in
     out "<lambda>@.<var>v_%s</var>@.<type>%a<type>@.%a</lambda>@."
       (Bindlib.name_of x) (print_type i s) a (print_term i s) t
     
and print_type : int -> string -> term pp = fun i s oc t ->
  let out fmt = Format.fprintf oc fmt in
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
  | Type                    -> out "<TYPE/>@."
  | Symb(s,_)               -> out "<basic>%a</basic>@." print_sym s
  | Appl(Symb(sy,_),_) as t ->
     let args = snd (Basics.get_args t) in
     out "<funapp>@.<name>%a</name>@.%a</funapp>@."
       print_sym sy
       (fun oc l ->
         List.iter
           (fun x -> Format.fprintf oc "<arg>%a</arg>@." (print_term i s) x) l
       ) args
  | Appl(t,u)               -> out "<application>@.%a%a</application>@."
                      (print_type i s) t (print_term i s) u
  (* Abstractions and products are only printed at priority [`Func]. *)
  | Abst(a,t)               ->
     let (x, t) = Bindlib.unbind t in
     out "<lambda>@.<var>v_%s</var>@.<type>%a<type>@.%a</lambda>@."
       (Bindlib.name_of x) (print_type i s) a (print_type i s) t
  | Prod(a,b)               ->
     if Bindlib.binder_constant b
     then
       out "<arrow>@.<type>@.%a</type>@.<type>@.%a</type>@.</arrow>@."
         (print_type i s) a
         (print_type i s) (snd (Bindlib.unbind b))
     else
       let (x, b) = Bindlib.unbind b in
       out "<arrow>@.<var>v_%s</var>@." (Bindlib.name_of x);
       out "<type>@.%a</type>@.<type>@.%a</type>@.</arrow>"
         (print_type i s) a (print_type i s) b
       
(** [print_rule oc s r] outputs the rule declaration corresponding [r] (on the
    symbol [s]), to the output channel [oc]. *)
let print_rule : Format.formatter -> int -> sym -> rule -> unit =
  fun oc i s r ->
  (* Print the rewriting rule. *)
  let lhs = Basics.add_args (Symb(s,Qualified)) r.lhs in
  Format.fprintf oc "<rule>@.<lhs>@.%a</lhs>@." (print_term i s.sym_name) lhs;
  let rhs = Basics.term_of_rhs r in
  Format.fprintf oc "<rhs>@.%a</rhs>@.</rule>@." (print_term i s.sym_name) rhs
  
(** [print_tl_rule] is identical to [print_rule] but for type-level rule  *)
let print_tl_rule : Format.formatter -> int -> sym -> rule -> unit =
  fun oc i s r ->
  (* Print the type level rewriting rule. *)
  let lhs = Basics.add_args (Symb(s,Qualified)) r.lhs in
  Format.fprintf oc "<typeLevelRule>@.<TLlhs>@.%a</TLlhs>@."
    (print_type i s.sym_name) lhs;
  let rhs = Basics.term_of_rhs r in
  Format.fprintf oc "<TLrhs>@.%a</TLrhs>@.</typeLevelRule>@."
    (print_type i s.sym_name) rhs
  
(** [get_vars s r] returns the list of variable of used in the rule [r],
    in the form of a couple containing the name of the variable and its type,
    inferred by the solver. *)
let get_vars : sym -> rule -> (string * Terms.term) list = fun s r ->
  (*check_rule s r;*)
  let rule_ctx : tvar option array = Array.make (Array.length r.ctxt) None in
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
    | Vari _              -> assert false
    | Symb (s, p)         -> Symb(s, p)
    | Abst (t1, b)        ->
       let (x,t2) = Bindlib.unbind b in
       Abst(
           subst_patt v t1,
           Bindlib.unbox (Bindlib.bind_var x (lift (subst_patt v t2)))
         )
    | Appl (t1, t2)        -> Appl(subst_patt v t1, subst_patt v t2)
    | Patt (None, x, a)    ->
       let v_i = Bindlib.new_var mkfree x in
       var_list := v_i :: !var_list;
       Array.fold_left (fun acc t -> Appl(acc,t))
         (Vari(v_i)) a
    | Patt (Some(i), x, a) ->
       if v.(i) = None
       then
         (let v_i = Bindlib.new_var mkfree x in
          var_list := v_i :: !var_list;
          v.(i) <- Some(v_i));
       let v_i =
         match v.(i) with
         |Some(vi) -> vi
         |None -> assert false
       in
       Array.fold_left (fun acc t -> Appl(acc,t)) (Vari(v_i)) a
  in
  let lhs =
    List.fold_left
      (fun t h -> Appl(t,subst_patt rule_ctx (unfold h)))
      (Symb(s,Nothing)) r.lhs
  in
  let ctx =
    List.fold_left (fun l x -> (x,Meta(fresh_meta Type 0,[||]))::l) [] !var_list
  in
  let (_,l) = Typing.infer ctx lhs in
  List.map (fun (v,ty) -> Bindlib.name_of v, List.assoc ty l) ctx

(** [to_XTC oc sign] outputs a XTC representation of the rewriting system of
    the signature [sign] to the output channel [oc]. *)
let to_XTC : Format.formatter -> Sign.t -> unit = fun oc sign ->
  (* Get all the dependencies (every needed symbols and rewriting rules). *)
  let deps = Sign.dependencies sign in
  (* Function to iterate over every symbols. *)
  let iter_symbols : (sym -> unit) -> unit = fun fn ->
    let iter_symbols sign =
      StrMap.iter (fun _ (s,_) -> fn s) Sign.(!(sign.sign_symbols))
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
    if status s = Object_level
    then (
      match !(s.sym_def) with
      | Some(d) ->
         Format.fprintf oc
           "<rule>@.<lhs>@.<funapp>@.<name>%a</name>@.</funapp>@.</lhs>@."
           print_sym s;
         Format.fprintf oc "<rhs>@.%a</rhs>@.</rule>@." (print_term 0 s.sym_name) d
      | None    ->
         let c = ref 0 in
         List.iter (fun x -> incr c; print_rule oc !c s x) !(s.sym_rules)
    ) else ()
  in
  (* Print the type level rewrite rules. *)
  let print_type_rules : sym -> unit = fun s ->
    if status s != Object_level
    then (
      match !(s.sym_def) with
      | Some(d) ->
         Format.fprintf oc
           "<rule>@.<lhs>@.<funapp>@.<name>%a</name>@.</funapp>@.</lhs>@."
           print_sym s;
         Format.fprintf oc
           "<rhs>@.%a</rhs>@.</rule>@." (print_term 0 s.sym_name) d
      | None    ->
         let c = ref 0 in
         List.iter (incr c; print_tl_rule oc !c s) !(s.sym_rules)
    ) else ()
  in
  (* Print the variable declarations *)
  let print_vars : sym -> unit = fun s ->
    let c = ref 0 in
    List.iter
      (fun r ->
        incr c;
        List.iter
          (fun (x,ty) ->
            Format.fprintf oc
              "<varDeclaration>@.<var>%s_%i_%s</var>@." s.sym_name !c x;
            Format.fprintf oc
              "<type>@.%a</type>@.</varDeclaration>@."
              (print_type !c s.sym_name) ty
          )
          (get_vars s r)
      )
      !(s.sym_rules)
  in
  (* Print the symbol declarations at object level. *)
  let print_symbol : sym -> unit = fun s ->
    if status s = Object_level
    then (
      Format.fprintf oc "<funcDeclaration>@.<name>%a</name>@." print_sym s;
      Format.fprintf oc
        "<typeDeclaration>@.<type>@.%a</type>@."
        (print_type 0 s.sym_name) !(s.sym_type);
      Format.fprintf oc "</typeDeclaration>@.</funcDeclaration>@."
    )
  in
  (* Print the type constructor declarations. *)
  let print_type_cstr : sym -> unit = fun s ->
    (* We don't declare type constant which do not take arguments for
       compatibility issue with simply-typed higher order category of the
       competition. *)
    if status s = Type_cstr
    then (
      Format.fprintf oc "<typeConstructorDeclaration>@.<name>%a</name>@."
        print_sym s;
      Format.fprintf oc
        "<typeDeclaration>@.<type>@.%a</type>@." (print_type 0 s.sym_name) !(s.sym_type);
      Format.fprintf oc "</typeDeclaration>@.</typeConstructorDeclaration>@."
    )
  in
  List.iter (Format.fprintf oc "%s@.") prelude;
  Format.fprintf oc "<rules>@.";
  iter_symbols print_object_rules;
  Format.fprintf oc "</rules>@.";
  let type_rule_presence = ref false in
  iter_symbols
    (fun s ->
      if status s != Object_level && !(s.sym_def) != None
         && !(s.sym_rules) != []
      then type_rule_presence := true);
  if !type_rule_presence
  then (
    Format.fprintf oc "<typeLevelRules>@.";
    iter_symbols print_type_rules;
    Format.fprintf oc "</typeLevelRules>@."
  );
  Format.fprintf oc "<higherOrderSignature>@.";
  Format.fprintf oc "<variableTypeInfo>@.";
  iter_symbols print_vars;
  Format.fprintf oc "</variableTypeInfo>@.";
  Format.fprintf oc "<functionSymbolTypeInfo>@.";
  iter_symbols print_symbol;
  Format.fprintf oc "</functionSymbolTypeInfo>@.";
  let type_cstr_presence = ref false in
  iter_symbols
    (fun s -> if status s = Type_cstr then type_cstr_presence := true);
  if !type_cstr_presence
  then (
    Format.fprintf oc "<typeConstructorTypeInfo>@.";
    iter_symbols print_type_cstr;
    Format.fprintf oc "</typeConstructorTypeInfo>@."
  );
  Format.fprintf oc "</higherOrderSignature>@.";
  List.iter (Format.fprintf oc "%s@.") postlude
  
(** [check cmd sign] runs the termination checker specified by command [cmd] on
    the rewrite system of signature [sign]. The return value is [Some true] in
    the case where the system is terminating.  It is [Some false] if the  system
    is not terminating, and it is [None] if the tool cannot conclude.  Note that
    it is assumed that [cmd] corresponds to a command that accepts XTC format
    on its standard output, and outputs either ["YES"], ["NO"] or ["MAYBE"] as
    the first line of its standard output. The exception [Fatal] may be raised
    if [cmd] does not behave as expected. *)
let check : string -> Sign.t -> bool option = fun cmd sign ->
  (* Run the command. *)
  if !log_enabled then log_conf "Running command [%s]" cmd;
  let (ic, oc, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  (* Feed it the XTC problem. *)
  to_XTC (Format.formatter_of_out_channel oc) sign;
  flush oc; close_out oc;
  if !log_enabled then log_conf "Wrote the data and closed the pipe.";
  (* Read the answer (and possible error messages). *)
  let out = input_lines ic in
  if !log_enabled && out <> [] then
    begin
      log_conf "==== Data written to [stdout] ====";
      List.iter (log_conf "%s") out;
      log_conf "==================================";
    end;
  let err = input_lines ec in
  if !log_enabled && err <> [] then
    begin
      log_conf "==== Data written to [stderr] ====";
      List.iter (log_conf "%s") err;
      log_conf "=================================="
    end;
  (* Terminate the process. *)
  match (Unix.close_process_full (ic, oc, ec), out) with
  | (Unix.WEXITED 0  , "YES"  ::_) -> Some true
  | (Unix.WEXITED 0  , "NO"   ::_) -> Some false
  | (Unix.WEXITED 0  , "MAYBE"::_) -> None
  | (Unix.WEXITED 0  , []        ) ->
      fatal_no_pos "The termination checker prodced no output."
  | (Unix.WEXITED 0  , _         ) ->
      fatal_no_pos "The termination checker gave an unexpected answer."
  | (Unix.WEXITED i  , _         ) ->
      fatal_no_pos "The termination checker returned with code [%i]." i
  | (Unix.WSIGNALED i, _         ) ->
      fatal_no_pos "The termination checker was killed by signal [%i]." i
  | (Unix.WSTOPPED  i, _         ) ->
      fatal_no_pos "The termination checker was stopped by signal [%i]." i
(* NOTE the simplest, valid termination checking command is ["echo MAYBE"]. The
   command ["cat > out.xml; echo MAYBE"] can conveniently be used to write the
   generated XTC problem to the file ["out.xml"] for debugging purposes. *)
