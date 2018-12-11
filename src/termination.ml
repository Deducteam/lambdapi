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
    the channel [oc].*)
let rec print_term : term pp = fun oc t ->
  let out fmt = Format.fprintf oc fmt in
  match unfold t with
  (* Forbidden cases. *)
  | Meta(_,_)    -> assert false
  | TRef(_)      -> assert false
  | TEnv(_,_)    -> assert false
  | Wild         -> assert false
  | Kind         -> assert false
  (* [TYPE] and products are necessarily at type level *)
  | Type         -> assert false
  | Prod(_,_)    -> assert false
  (* Printing of atoms. *)
  | Vari(x)      -> out "<var>v_%s</var>@." (Bindlib.name_of x)
  | Symb(s,_)    -> out "<funapp>@.<name>%a</name>@.</funapp>@." print_sym s
  | Patt(i,n,ts) ->
     if ts = [||] then out "<var>&%s</var>@." n else
       print_term oc
         (Array.fold_left (fun t u -> Appl(t,u)) (Patt(i,n,[||])) ts)
  | Appl(t,u)    -> out "<application>@.%a%a</application>@."
                      print_term t print_term u
  (* Abstractions and products are only printed at priority [`Func]. *)
  | Abst(a,t)    ->
     let (x, t) = Bindlib.unbind t in
     out "<lambda>@.<var>v_%s</var>@.<type>%a<type>@.%a</lambda>@."
       (Bindlib.name_of x) print_type a print_term t

and print_type : term pp = fun oc t ->
  let out fmt = Format.fprintf oc fmt in
  match unfold t with
  (* Forbidden cases. *)
  | Meta(_,_)    -> assert false
  | TRef(_)      -> assert false
  | TEnv(_,_)    -> assert false
  | Wild         -> assert false
  | Kind         -> assert false
  (* Variables are necessarily at object level *)
  | Vari(_)      -> assert false
  | Patt(_,_,_)  -> assert false
  (* Printing of atoms. *)
  | Type         -> out "<TYPE>@."
  | Symb(s,_)    -> out "<basic>%a</basic>@." print_sym s
  | Appl(t,u)    -> out "<application>@.%a%a</application>@."
                      print_type t print_term u
  (* Abstractions and products are only printed at priority [`Func]. *)
  | Abst(a,t)    ->
     let (x, t) = Bindlib.unbind t in
     out "<lambda>@.<var>v_%s</var>@.<type>%a<type>@.%a</lambda>@."
       (Bindlib.name_of x) print_type a print_type t
  | Prod(a,b)    ->
     if Bindlib.binder_constant b
     then
       out "<arrow>@.<type>@.%a</type>@.<type>@.%a</type>@.</arrow>@."
         print_type a
         print_type (snd (Bindlib.unbind b))
     else
       let (x, b) = Bindlib.unbind b in
       out "<arrow>@.<var>v_%s</var>@." (Bindlib.name_of x);
       out "<type>@.%a</type>@.<type>@.%a</type>@.</arrow>"
         print_type a print_type b

(** [print_rule oc s r] outputs the rule declaration corresponding [r] (on the
    symbol [s]), to the output channel [oc]. *)
let print_rule : Format.formatter -> sym -> rule -> unit = fun oc s r ->
  (* Print the rewriting rule. *)
  let lhs = Basics.add_args (Symb(s,Qualified)) r.lhs in
  Format.fprintf oc "<rule>@.<lhs>@.%a</lhs>@." print_term lhs;
  let rhs = Basics.term_of_rhs r in
  Format.fprintf oc "<rhs>@.%a</rhs>@.</rule>@." print_term rhs

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
         Format.fprintf oc "<rhs>@.%a</rhs>@.</rule>@." print_term d
      | None    -> List.iter (print_rule oc s) !(s.sym_rules)
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
         Format.fprintf oc "<rhs>@.%a</rhs>@.</rule>@." print_term d
      | None    -> List.iter (print_rule oc s) !(s.sym_rules)
    ) else ()
  in
  (* Print the symbol declarations at object level. *)
  let print_symbol : sym -> unit = fun s ->
    if status s = Object_level
    then (
      Format.fprintf oc "<funcDeclaration>@.<name>%a</name>@." print_sym s;
      Format.fprintf oc
        "<typeDeclaration>@.<type>@.%a</type>@." print_type !(s.sym_type);
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
        "<typeDeclaration>@.<type>@.%a</type>@." print_type !(s.sym_type);
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
