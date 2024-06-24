(** This module provides a function to translate a simply typed signature to
   the XTC format used in the termination competition.

    @see <https://raw.githubusercontent.com/TermCOMP/TPDB/master/xml/xtc.xsd>

Remarks:

- SizeChangeTool accepts an extension of the XTC format with lambda and
   application in types and:

<arrow> <var>...</var> <type>...</type> <type>...</type> </arrow>

<typeLevelRule> <TLlhs>...</TLlhs> <TLrhs>...</TLrhs> </typeLevelRule>

*)

open Lplib open Base open Extra
open Core open Term
open Common open Error

(** [syms] maps every symbol to a name. *)
let syms = ref SymMap.empty

(** [bvars] is the set of abstracted variables. *)
let bvars = ref StrSet.empty

(** [nb_rules] is the number of rewrite rules. *)
let nb_rules = ref 0

(** [pvars] is the list of all pattern variables with their type. *)
let pvars = ref []

(** [typ] is a reference to the types of the pvars of the current rules. *)
let type_of_pvar = ref [||]

(** [sym_name s] translates the symbol name of [s]. *)
let sym_name : sym pp = fun ppf s ->
  out ppf "%a.%s" Path.pp s.sym_path s.sym_name

(** [add_sym] declares a Lambdapi symbol. *)
let add_sym : sym -> unit = fun s ->
  syms := SymMap.add s (Format.asprintf "%a" sym_name s) !syms

(** [type_sym ppf s] translates the Lambdapi type symbol [s]. *)
let type_sym : sym pp = fun ppf s ->
  out ppf "<type><basic>%a</basic></type>" sym_name s

(** [sym ppf s] translates the Lambdapi symbol [s]. *)
let sym : sym pp = fun ppf s ->
  out ppf "<name>%s</name>"
    (try SymMap.find s !syms with Not_found -> assert false)

(** [add_bvar v] declares an abstracted Lambdapi variable. *)
let add_bvar : var -> unit = fun v ->
  bvars := StrSet.add (base_name v) !bvars

(** [bvar v] translates the Lambdapi bound variable [v]. *)
let bvar : var pp = fun ppf v -> out ppf "<var>%s</var>" (base_name v)

(** [pvar i] translates the Lambdapi pattern variable [i]. *)
let pvar : int pp = fun ppf i -> out ppf "<var>%d_%d</var>" !nb_rules i

(** [term ppf t] translates the term [t]. *)
let rec term : term pp = fun ppf t ->
  let h, ts = get_args t in
  match h with
  | Symb s when LibTerm.is_kind Timed.(!(s.sym_type)) ->
    fatal s.sym_pos "Type symbol in a term."
  | Symb s -> add_sym s;
    let arg ppf t = out ppf "<arg>%a</arg>" term t in
    out ppf "<funapp>%a%a</funapp>" sym s (List.pp arg "") ts
  | _ ->
    match ts with
    | [] -> head ppf h
    | t::ts ->
      let rec args : (term * term list) pp = fun ppf (t,ts) ->
        match ts with
        | [] -> term ppf t
        | u::us ->
          out ppf "<application>%a%a</application>" term t args (u,us)
      in
      out ppf "<application>%a%a</application>" head h args (t,ts)

and head : term pp = fun ppf t ->
  match unfold t with
  | Meta _ -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | Db _ -> assert false
  | Wild -> assert false
  | Kind -> assert false
  | Type -> assert false
  | Vari v -> bvar ppf v
  | Symb _ -> assert false (* done in term *)
  | Patt(None,_,_) -> assert false
  | Patt(Some i,_,ts) -> pvar_app ppf (i,ts)
  | Appl(t,u) -> out ppf "<application>%a%a</application>" term t term u
  | Abst(a,b) ->
    let x, b = unbind b in add_bvar x;
    out ppf "<lambda>%a%a%a</lambda>" bvar x typ a term b
  | Prod _ -> assert false
  | LLet(a,t,b) -> term ppf (mk_Appl(mk_Abst(a,b),t))

and pvar_app : (int * term array) pp = fun ppf (i,ts) ->
  let arity = Array.length ts in
  let rec arg ppf k =
    if k < 0 then pvar ppf i
    else out ppf "<application>%a%a</application>" arg (k-1) term ts.(k)
  in arg ppf (arity - 1)

and typ : term pp = fun ppf t ->
  match unfold t with
  | Meta _ -> assert false
  | Plac _ -> assert false
  | TRef _ -> assert false
  | Db _ -> assert false
  | Wild -> assert false
  | Kind -> assert false
  | Type -> assert false
  | Vari _ -> assert false
  | Symb s -> type_sym ppf s
  | Patt(None,_,_) -> assert false
  | Patt(Some i,_,[||]) -> typ ppf !type_of_pvar.(i)
  | Patt(Some _,_,_) -> assert false
  | Appl _ -> fatal_no_pos "Dependent type."
  | Abst _ -> fatal_no_pos "Dependent type."
  | Prod(a,b) ->
    if binder_occur b then fatal_no_pos "Dependent type." else
    let x, b = unbind b in add_bvar x;
    out ppf "<type><arrow>%a%a</arrow></type>" typ a typ b
  | LLet(_,t,b) -> typ ppf (subst b t)

(** [add_pvars s r] adds the types of the pvars of [r] in [pvars]. *)
let add_pvars : sym -> rule -> unit = fun s r ->
  let n = r.vars_nb in
  (* Generate n fresh variables and n fresh metas for their types. *)
  let var = Array.init n (new_var_ind "$") in
  let p = new_problem() in
  type_of_pvar := Array.init n (fun _ -> LibMeta.make p [] mk_Type);
  (* Replace in lhs pattern variables by variables. *)
  let rec subst_patt t =
    match unfold t with
    | Type -> assert false
    | Kind -> assert false
    | Db _ -> assert false
    | Meta _ -> assert false
    | Plac _ -> assert false
    | TRef _ -> assert false
    | Wild -> assert false
    | Prod _ -> assert false
    | LLet _ -> assert false
    | Vari _
    | Symb _ -> t
    | Abst(a,b) ->
      begin
        match unfold a with
        | Patt(Some i,_,[||]) ->
          let x,b = unbind b in
          mk_Abst(!type_of_pvar.(i), bind_var x (subst_patt b))
        | Patt(Some _,_,_) -> assert false (*FIXME*)
        | _ -> assert false
      end
    | Appl(a,b) -> mk_Appl(subst_patt a, subst_patt b)
    | Patt(None, _, _) -> assert false
    | Patt(Some i, _, ts) ->
      Array.fold_left (fun acc t -> mk_Appl(acc,t)) (mk_Vari var.(i)) ts
  in
  let lhs =
    List.fold_left (fun h t -> mk_Appl(h, subst_patt t)) (mk_Symb s) r.lhs
  in
  (* Create a typing context mapping every variable to its type. *)
  let ctx =
    Array.to_list (Array.mapi (fun i v -> v, !type_of_pvar.(i), None) var) in
  (* Infer the type of lhs in ctx. *)
  (*Logger.set_debug true "+iu"; Console.set_flag "print_domaines" true;*)
  match Infer.infer_noexn p ctx lhs with
  | None -> assert false
  | Some _ ->
    (* Solve constraints. *)
    if Unif.solve_noexn ~type_check:false p then
      (* Add the infered type of each pvar. *)
      for i=0 to n-1 do
        pvars := (!nb_rules, i, !type_of_pvar.(i))::!pvars
      done
    else fatal_no_pos "Cannot infer the type of %a" Print.sym_rule (s,r)

(** [rule ppf r] translates the pair of terms [r] as a rule. *)
let rule : (term * term) pp = fun ppf (l, r) -> out ppf "
      <rule>
        <lhs>
          %a
        </lhs>
        <rhs>
          %a
        </rhs>
      </rule>" term l term r

(** [sym_rule ppf s r] increases the number of rules and translates the
   sym_rule [r]. *)
let sym_rule : sym -> rule pp = fun s ppf r ->
  incr nb_rules; add_pvars s r; let sr = s, r in rule ppf (lhs sr, rhs sr)

(** Translate the rules of symbol [s]. *)
let rules_of_sym : sym pp = fun ppf s ->
  match Timed.(!(s.sym_def)) with
  | Some d -> rule ppf (mk_Symb s, d)
  | None -> List.iter (sym_rule s ppf) Timed.(!(s.sym_rules))

(** Translate the rules of a dependency except if it is a ghost signature. *)
let rules_of_sign : Sign.t pp = fun ppf sign ->
  if sign != Ghost.sign then
    StrMap.iter (fun _ -> rules_of_sym ppf) Timed.(!(sign.sign_symbols))

(** [sign ppf s] translates the Lambdapi signature [s]. *)
let sign : Sign.t pp = fun ppf sign ->
  (* First, generate the RULES section in a buffer, because it generates data
     necessary for the other sections. *)
  let buf_rules = Buffer.create 1000 in
  let ppf_rules = Format.formatter_of_buffer buf_rules in
  Sign.iterate (rules_of_sign ppf_rules) sign;
  Format.pp_print_flush ppf_rules ();
  (* Function for printing the types of function symbols. *)
  let pp_syms : string SymMap.t pp = fun ppf syms ->
    let sym_decl : (sym * string) pp = fun ppf (s,n) ->
      out ppf "
        <funcDeclaration>
          <name>%s</name>
          <typeDeclaration>%a</typeDeclaration>
        </funcDeclaration>" n typ Timed.(!(s.sym_type)) in
    let sym_decl s n = sym_decl ppf (s,n) in SymMap.iter sym_decl syms
  in
  (* Function for printing the types of pattern variables. *)
  let pp_pvars : (int * int * term) list pp = fun ppf pvars ->
    let pvar_decl (n,i,t) = out ppf "
        <varDeclaration>
          <var>$%d_%d</var>
          %a
        </varDeclaration>" n i typ t in
    List.iter pvar_decl pvars in
  (* Finally, generate the whole hrs file. *)
  out ppf "\
<?xml version=\"1.0\" encoding=\"UTF-8\"?>
<?xml-stylesheet href=\"xtc2tpdb.xsl\" type=\"text/xsl\"?>
<problem xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" \
type=\"termination\" \
xsi:noNamespaceSchemaLocation=\"http://dev.aspsimon.org/xtc.xsd\">
  <trs>
    <rules>%s
    </rules>
    <higherOrderSignature>
      <variableTypeInfo>%a
      </variableTypeInfo>
      <functionSymbolTypeInfo>%a
      </functionSymbolTypeInfo>
    </higherOrderSignature>
  </trs>
  <strategy>FULL</strategy>
  <metainformation>
    <originalfilename>%a.lp</originalfilename>
  </metainformation>
</problem>\n" (Buffer.contents buf_rules) pp_pvars !pvars pp_syms !syms
  Path.pp sign.sign_path
