(** Pretty-printing for the core AST.

    The functions of this module are used for printing terms and other objects
    defined in the {!module:Term} module.  This is mainly used for displaying
    log messages, and feedback in case of success or error while type-checking
    terms or testing convertibility. *)

open! Lplib
open Lplib.Base
open Lplib.Extra
open Timed
open Common
open Debug
open Term
open Sig_state

(** Logging function for printing. *)
let log_prnt = Logger.make 'p' "prnt" "pretty-printing"
let log_prnt = log_prnt.pp

(** Current signature state. *)
let sig_state : sig_state ref = ref Sig_state.dummy

(** [notation_of s] returns the notation of symbol [s] or [None]. *)
let notation_of : sym -> Sign.notation option = fun s ->
  SymMap.find_opt s !sig_state.notations

(** Flag for printing the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag for printing implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag for printing the type of uninstanciated metavariables. Remark: this
   does not generate parsable terms; use for debug only. *)
let print_meta_types : bool ref =
  Console.register_flag "print_meta_types" false

(** Flag for printing the arguments of metavariables. Remark: this does not
   generate parsable terms; use for debug only. *)
let print_meta_args : bool ref =
  Console.register_flag "print_meta_args" true

(** Flag for printing contexts in unification problems. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

let pp_assoc : Pratter.associativity pp = fun ppf assoc ->
  match assoc with
  | Neither -> ()
  | Left -> out ppf " left associative"
  | Right -> out ppf " right associative"

let pp_notation : Sign.notation pp = fun ppf notation ->
  match notation with
  | Prefix(p) -> out ppf "prefix %f" p
  | Infix(a,p) -> out ppf "infix%a %f" pp_assoc a p
  | Zero -> out ppf "builtin \"0\""
  | Succ -> out ppf "builtin \"+1\""
  | Quant -> out ppf "quantifier"

let pp_uid = Format.pp_print_string

let pp_path : Path.t pp = List.pp pp_uid "."

let pp_prop : prop pp = fun ppf p ->
  match p with
  | AC true -> out ppf "left associative commutative "
  | AC false -> out ppf "associative commutative "
  | Assoc true -> out ppf "left associative "
  | Assoc false -> out ppf "associative "
  | Const -> out ppf "constant "
  | Commu -> out ppf "commutative "
  | Defin -> ()
  | Injec -> out ppf "injective "

let pp_expo : expo pp = fun ppf e ->
  match e with
  | Privat -> out ppf "private "
  | Protec -> out ppf "protected "
  | Public -> ()

let pp_match_strat : match_strat pp = fun ppf s ->
  match s with
  | Eager -> ()
  | Sequen -> out ppf "sequential "

let pp_sym : sym pp = fun ppf s ->
  if !print_implicits && s.sym_impl <> [] then out ppf "@";
  let ss = !sig_state and n = s.sym_name and p = s.sym_path in
  if Path.Set.mem p ss.open_paths then pp_uid ppf n
  else
    match Path.Map.find_opt p ss.path_alias with
    | None ->
        (* Hack for printing symbols replacing metavariables in infer.ml
           unqualified. *)
        if n <> "" && let c = n.[0] in c = '$' || c = '?' then pp_uid ppf n
        else out ppf "%a.%a" pp_path p pp_uid n
    | Some alias -> out ppf "%a.%a" pp_uid alias pp_uid n

let pp_var : 'a Bindlib.var pp = fun ppf x -> pp_uid ppf (Bindlib.name_of x)

(** Exception raised when trying to convert a term into a nat. *)
exception Not_a_nat

(** [nat_of_term t] converts a term into a natural number.
    @raise Not_a_nat if this is not possible. *)
let nat_of_term : term -> int = fun t ->
  let get_builtin name =
    try StrMap.find name (!sig_state).builtins
    with Not_found -> raise Not_a_nat
  in
  let zero = get_builtin "0" in
  match get_args t with
  | (Symb s, []) when s == zero -> 0
  | _ ->
  let succ = get_builtin "+1" in
  let rec nat acc = fun t ->
    match get_args t with
    | (Symb s, [u]) when s == succ -> nat (acc+1) u
    | (Symb s,  []) when s == zero -> acc
    | _ -> raise Not_a_nat
  in nat 0 t

(** [are_quant_args args] returns [true] iff [args] has only one argument
   that is an abstraction. *)
let are_quant_args : term list -> bool = fun args ->
  match args with
  | [b] -> is_abst b
  | _ -> false

let pp_meta_name : meta pp = fun ppf m ->
  out ppf "%d" m.meta_key

(** The possible priority levels are [`Func] (top level, including abstraction
   and product), [`Appl] (application) and [`Atom] (smallest priority). *)
type priority = [`Func | `Appl | `Atom]

let rec pp_meta : meta pp = fun ppf m ->
  if !print_meta_types then
    out ppf "(?%a:%a)" pp_meta_name m pp_term !(m.meta_type)
  else out ppf "?%a" pp_meta_name m

and pp_type : term pp = fun ppf a ->
  if !print_domains then out ppf ": %a" pp_term a

and pp_term : term pp = fun ppf t ->
  let rec atom ppf t = pp `Atom ppf t
  and appl ppf t = pp `Appl ppf t
  and func ppf t = pp `Func ppf t
  and pp p ppf t =
    let (h, args) = get_args t in
    let pp_appl h args =
      match args with
      | []   -> pp_head (p <> `Func) ppf h
      | args ->
          if p = `Atom then out ppf "(";
          pp_head true ppf h;
          List.iter (out ppf " %a" atom) args;
          if p = `Atom then out ppf ")"
    in
    match h with
    | Symb(s) ->
        if !print_implicits && s.sym_impl <> [] then pp_appl h args
        else
          let args = LibTerm.remove_impl_args s args in
          begin match notation_of s with
          | Some Quant when are_quant_args args ->
              if p <> `Func then out ppf "(";
              pp_quantifier s args;
              if p <> `Func then out ppf ")"
          | Some (Infix _) ->
              begin
                match args with
                | l::r::args ->
                    if p <> `Func then out ppf "(";
                    (* Can be improved by looking at symbol priority. *)
                    if args = []
                    then out ppf "%a %a %a" appl l pp_sym s appl r
                    else out ppf "(%a %a %a)" appl l pp_sym s appl r;
                    List.iter (out ppf " %a" appl) args;
                    if p <> `Func then out ppf ")"
                | [] ->
                  out ppf "("; pp_head true ppf h; out ppf ")"
                | _ ->
                  if p = `Atom then out ppf "(";
                  out ppf "("; pp_head true ppf h; out ppf ")";
                  List.iter (out ppf " %a" atom) args;
                  if p = `Atom then out ppf ")"
              end
          | Some Zero -> out ppf "0"
          | Some Succ ->
              (try out ppf "%i" (nat_of_term t)
               with Not_a_nat -> pp_appl h args)
          | _ -> pp_appl h args
          end
    | _ -> pp_appl h args

  and pp_quantifier s args =
    (* assume [are_quant_args s args = true] *)
    match args with
    | [b] ->
        begin
          match unfold b with
          | Abst(a,b) ->
              let (x,p) = Bindlib.unbind b in
              out ppf "`%a %a%a, %a" pp_sym s pp_var x pp_type a func p
          | _ -> assert false
        end
    | _ -> assert false

  and pp_head wrap ppf t =
    let pp_env ppf ar =
      if !print_meta_args && ar <> [||] then
        out ppf "[%a]" (Array.pp func ";") ar
    in
    let pp_term_env ppf te =
      match te with
      | TE_Vari(m) -> pp_var ppf m
      | _          -> assert false
    in
    match unfold t with
    | Appl(_,_)   -> assert false
    (* Application is handled separately, unreachable. *)
    | Wild        -> out ppf "_"
    | TRef(r)     ->
        (match !r with
         | None -> out ppf "<TRef>"
         | Some t -> atom ppf t)
    (* Atoms are printed inconditonally. *)
    | Vari(x)     -> pp_var ppf x
    | Type        -> out ppf "TYPE"
    | Kind        -> out ppf "KIND"
    | Symb(s)     -> pp_sym ppf s
    | Meta(m,e)   -> out ppf "%a%a" pp_meta m pp_env e
    | Plac(_)     -> out ppf "_"
    | Patt(_,n,e) -> out ppf "$%a%a" pp_uid n pp_env e
    | TEnv(t,e)   -> out ppf "$%a%a" pp_term_env t pp_env e
    (* Product and abstraction (only them can be wrapped). *)
    | Abst(a,b)   ->
        if wrap then out ppf "(";
        let (x,t) = Bindlib.unbind b in
        out ppf "λ %a" pp_bvar (b,x);
        if !print_domains then out ppf ": %a, %a" func a func t
        else pp_abstractions ppf t;
        if wrap then out ppf ")"
    | Prod(a,b)   ->
        if wrap then out ppf "(";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out ppf "Π %a: %a, %a" pp_var x appl a func t
        else out ppf "%a → %a" appl a func t;
        if wrap then out ppf ")"
    | LLet(a,t,b) ->
        if wrap then out ppf "(";
        out ppf "let ";
        let (x,u) = Bindlib.unbind b in
        pp_bvar ppf (b,x);
        if !print_domains then out ppf ": %a" atom a;
        out ppf " ≔ %a in %a" func t func u;
        if wrap then out ppf ")"
  and pp_bvar ppf (b,x) =
    if Bindlib.binder_occur b then out ppf "%a" pp_var x else out ppf "_"
  and pp_abstractions ppf t =
    match unfold t with
    | Abst(_,b) ->
        let (x,t) = Bindlib.unbind b in
        out ppf " %a%a" pp_bvar (b,x) pp_abstractions t
    | t -> out ppf ", %a" func t
  in
  func ppf (cleanup t)

(*let pp_term ppf t = out ppf "<%a printed %a>" Term.pp_term t pp_term t*)
(*let pp_term = Term.pp_term*)

let rec pp_prod : (term * bool list) pp = fun ppf (t, impl) ->
  match unfold t, impl with
  | Prod(a,b), true::impl ->
      let x, b = Bindlib.unbind b in
      out ppf "Π {%a: %a}, %a" pp_var x pp_term a pp_prod (b, impl)
  | Prod(a,b), false::impl ->
      let x, b = Bindlib.unbind b in
      out ppf "Π %a: %a, %a" pp_var x pp_term a pp_prod (b, impl)
  | _ -> pp_term ppf t

let pp_rule : (sym * rule) pp = fun ppf (s,r) ->
  let lhs = add_args (mk_Symb s) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  out ppf "%a ↪ %a" pp_term lhs pp_term rhs

let pp_unif_rule : (sym * rule) pp = fun ppf (s,r) ->
  let lhs = add_args (mk_Symb s) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  out ppf "%a ↪ [ %a ]" pp_term lhs pp_term rhs

(* ends with a space if [!print_contexts = true] *)
let pp_ctxt : ctxt pp = fun ppf ctx ->
  if !print_contexts then
    begin
      let pp_def ppf t = out ppf " ≔ %a" pp_term t in
      let pp_decl ppf (x,a,t) =
        out ppf "%a%a%a" pp_var x pp_type a (Option.pp pp_def) t in
      out ppf "%a%s⊢ "
        (List.pp pp_decl ",@ ") (List.rev ctx)
        (if ctx <> [] then "@ " else "")
    end

let pp_typing : constr pp = fun ppf (ctx, t, u) ->
  out ppf "%a%a@ : %a" pp_ctxt ctx pp_term t pp_term u

let pp_constr : constr pp = fun ppf (ctx, t, u) ->
  out ppf "%a%a@ ≡ %a" pp_ctxt ctx pp_term t pp_term u

let pp_constrs : constr list pp = List.pp pp_constr ";@ "

(* for debug only *)
let pp_metaset : MetaSet.t pp =
  D.iter ~sep:(fun fmt () -> Format.fprintf fmt ",@ ") MetaSet.iter pp_meta

let pp_problem : problem pp = fun ppf p ->
  out ppf
    "{ recompute=%b;@ metas={%a};@ to_solve=[%a];@  unsolved=[%a] }"
    !p.recompute pp_metaset !p.metas pp_constrs !p.to_solve pp_constrs
    !p.unsolved
