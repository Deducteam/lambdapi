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
open Format

let out = fprintf

(** Logging function for printing. *)
let log_prnt = new_logger 'p' "prnt" "pretty-printing"
let log_prnt = log_prnt.logger

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
let print_meta_type : bool ref = Console.register_flag "print_meta_type" false

(** Flag for printing contexts in unification problems. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

let pp_assoc : Pratter.associativity pp = fun ppf assoc ->
  match assoc with
  | Neither -> ()
  | Left -> out ppf " left associative"
  | Right -> out ppf " right associative"

let pp_notation : Sign.notation pp = fun ppf notation ->
  match notation with
  | Prefix(n,p,_)  -> out ppf "prefix \"%s\" with priority %f" n p
  | Infix(n,a,p,_) ->
      out ppf "infix \"%s\"%a with priority %f" n pp_assoc a p
  | Zero           -> out ppf "builtin \"0\""
  | Succ           -> out ppf "builtin \"+1\""
  | Quant          -> out ppf "quantifier"

let pp_uid = Parsing.LpLexer.pp_uid

let pp_path : Path.t pp = List.pp pp_uid "."

let pp_sym : sym pp = fun ppf s ->
  if StrMap.mem s.sym_name !sig_state.in_scope then pp_uid ppf s.sym_name
  else
    match Path.Map.find_opt s.sym_path (!sig_state).path_alias with
    | None -> out ppf "%a.%a" pp_path s.sym_path pp_uid s.sym_name
    | Some alias -> out ppf "%a.%a" pp_uid alias pp_uid s.sym_name

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
  let succ = get_builtin "+1" in
  let rec nat acc = fun t ->
    match LibTerm.get_args t with
    | (Symb s, [u]) when s == succ -> nat (acc+1) u
    | (Symb s,  []) when s == zero -> acc
    | _ -> raise Not_a_nat
  in nat 0 t

(** [are_quant_args s args] returns [true] iff the first element of
    [args] which is non-implicit for [s] is an abstraction. *)
let are_quant_args : sym -> term list -> bool = fun s args ->
  match (args, s.sym_impl) with
  | ([_;b], ([]|[true])) -> is_abst b
  | (_    , _          ) -> false

let rec pp_meta : meta pp = fun ppf m ->
  if !print_meta_type then
    out ppf "(%a:%a)" pp_uid (Meta.name m) pp_term !(m.meta_type)
  else pp_uid ppf (Meta.name m)

and pp_term : term pp = fun ppf t ->
  let rec atom ppf t = pp `Atom ppf t
  and appl ppf t = pp `Appl ppf t
  and func ppf t = pp `Func ppf t
  and pp (p : Parsing.Pretty.priority) ppf t =
    let (h, args) = LibTerm.get_args t in
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
        begin
          let eargs =
            if !print_implicits then args else LibTerm.expl_args s args
          in
          match notation_of s with
          | Some Quant when are_quant_args s args ->
              if p <> `Func then out ppf "(";
              pp_quantifier s args;
              if p <> `Func then out ppf ")"
          | Some (Infix(op,_,_,_))
            when not !print_implicits || s.sym_impl <> [] ->
              begin
                match eargs with
                | l::r::[] ->
                    if p <> `Func then out ppf "(";
                    (* Can be improved by looking at symbol priority. *)
                    out ppf "%a %s %a" appl l op appl r;
                    if p <> `Func then out ppf ")"
                | l::r::eargs ->
                    if p <> `Func then out ppf "(";
                    (* Can be improved by looking at symbol priority. *)
                    out ppf "(%a %s %a)" appl l op appl r;
                    List.iter (out ppf " %a" atom) eargs;
                    if p <> `Func then out ppf ")"
                | _ -> pp_appl h eargs
              end
          | Some Zero -> out ppf "0"
          | Some Succ ->
              begin
                try out ppf "%i" (nat_of_term t)
                with Not_a_nat -> pp_appl h args
              end
          | _ -> pp_appl h eargs
        end
    | _ -> pp_appl h args

  and pp_quantifier s args =
    (* assume [are_quant_args s args = true] *)
    match args with
    | [_;b] ->
        begin
          match unfold b with
          | Abst(a,b) ->
              let (x,p) = Bindlib.unbind b in
              out ppf "`%a %a" pp_sym s pp_var x;
              if !print_implicits then out ppf ": %a" func a;
              out ppf ", %a" func p
          | _ -> assert false
        end
    | _ -> assert false

  and pp_head wrap ppf t =
    let pp_env ppf ar =
      if ar <> [||] then out ppf "[%a]" (Array.pp appl ",") ar
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
          out ppf "Π %a: %a, %a" pp_var x func a func t
        else out ppf "%a → %a" appl a func t;
        if wrap then out ppf ")"
    | LLet(a,t,b) ->
        if wrap then out ppf "(";
        out ppf "let ";
        let (x,u) = Bindlib.unbind b in
        pp_bvar ppf (b,x);
        if !print_domains then out ppf ": %a" atom a;
        out ppf " ≔ %a in %a" atom t atom u;
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

let pp_rule : (sym * rule) pp = fun ppf (s,r) ->
  let lhs = LibTerm.add_args (Symb s) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  out ppf "%a ↪ %a" pp_term lhs pp_term rhs

(* ends with a space if [!print_contexts = true] *)
let pp_ctxt : ctxt pp = fun ppf ctx ->
  if !print_contexts then
    begin
      let pp_def ppf t = out ppf " ≔ %a" pp_term t in
      let pp_decl ppf (x,a,t) =
        out ppf "%a : %a%a" pp_var x pp_term a (Option.pp pp_def) t in
      List.pp pp_decl ", " ppf (List.rev ctx);
      out ppf " ⊢ "
    end

let pp_typing : constr pp = fun ppf (ctx, t, u) ->
  out ppf "%a%a : %a" pp_ctxt ctx pp_term t pp_term u

let pp_constr : constr pp = fun ppf (ctx, t, u) ->
  out ppf "%a%a ≡ %a" pp_ctxt ctx pp_term t pp_term u

(* for debug only *)
let pp_problem : problem pp = fun ppf p ->
  let constr ppf c = out ppf "\n; %a" pp_constr c in
  out ppf "{ recompute = %b;\nto_solve = [%a];\nunsolved = [%a] }"
    p.recompute (List.pp constr "") p.to_solve (List.pp constr "") p.unsolved
