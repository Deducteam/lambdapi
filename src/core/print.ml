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
open Module

(** Logging function for printing. *)
let log_prnt = new_logger 'p' "prnt" "pretty-printing"
let log_prnt = log_prnt.logger

(** Current signature state. *)
let sig_state : sig_state ref = ref Sig_state.dummy

(** Flag controling the printing of the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag controling the printing of implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag controling the printing of implicit arguments. *)
let print_meta_type : bool ref = Console.register_flag "print_meta_type" false

(** Flag controlling the printing of the context in unification. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** [assoc oc a] prints associativity [a] to channel [oc]. *)
let pp_assoc : Pratter.associativity pp = fun oc assoc ->
  match assoc with
  | Neither -> ()
  | Left -> Format.fprintf oc " left associative"
  | Right -> Format.fprintf oc " right associative"

(** [notation oc n] notation setter [n] to output [oc]. *)
let notation : Sign.notation pp = fun oc notation ->
  match notation with
  | Prefix(n,p,_)  -> Format.fprintf oc "prefix \"%s\" with priority %f" n p
  | Infix(n,a,p,_) ->
      Format.fprintf oc "infix \"%s\"%a with priority %f" n pp_assoc a p
  | Zero           -> Format.fprintf oc "builtin \"0\""
  | Succ           -> Format.fprintf oc "builtin \"+1\""
  | Quant          -> Format.fprintf oc "quantifier"

(** [qualified s] prints symbol [s] fully qualified to channel [oc]. *)
let pp_qualified : sym pp = fun oc s ->
  match PathMap.find_opt s.sym_mod (!sig_state).mod_map with
  | None -> Format.fprintf oc "%a.%s" Path.pp s.sym_mod s.sym_name
  | Some alias -> Format.fprintf oc "%s.%s" alias s.sym_name

(** [notatin_of sym] returns the notation properties symbol [sym] or
    [None]. *)
let notation_of : sym -> Sign.notation option = fun s ->
  SymMap.find_opt s !sig_state.notations

(** [pp_symbol oc s] prints the name of the symbol [s] to channel [oc]. *)
let pp_symbol : sym pp = fun oc s ->
  if StrMap.mem s.sym_name !sig_state.in_scope
  then Format.pp_print_string oc s.sym_name
  else pp_qualified oc s

(** [pp_var oc x] prints the Bindlib variable [x] to the channel [oc]. *)
let pp_var : 'a Bindlib.var pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

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
  let is_abst t = match unfold t with Abst(_) -> true | _ -> false in
  match (args, s.sym_impl) with
  | ([_;b], ([]|[true])) -> is_abst b
  | (_    , _          ) -> false

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let rec pp_meta : meta pp = fun oc m ->
  if !print_meta_type then
    Format.fprintf oc "(%s:%a)" (Meta.name m) pp_term !(m.meta_type)
  else
    Format.pp_print_string oc (Meta.name m)

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
and pp_term : term pp = fun oc t ->
  let out = Format.fprintf in
  (* The possible priority levels are [`Func] (top level, including
     abstraction or product), [`Appl] (application) and [`Atom] (smallest
     priority). *)
  let rec pp (p : [`Func | `Appl | `Atom]) oc t =
    let (h, args) = LibTerm.get_args t in
    let pp_appl h args =
      match args with
      | []   -> pp_head (p <> `Func) oc h
      | args ->
          if p = `Atom then out oc "(";
          pp_head true oc h;
          List.iter (out oc " %a" (pp `Atom)) args;
          if p = `Atom then out oc ")"
    in
    match h with
    | Symb(s) ->
        begin
          let eargs =
            if !print_implicits then args else LibTerm.expl_args s args
          in
          match notation_of s with
          | Some Quant when are_quant_args s args ->
              if p <> `Func then out oc "(";
              pp_quantifier s args;
              if p <> `Func then out oc ")"
          | Some (Infix(op,_,_,_))
            when not !print_implicits || s.sym_impl <> [] ->
              begin
                match eargs with
                | l::r::[] ->
                    if p <> `Func then out oc "(";
                    (* Can be improved by looking at symbol priority. *)
                    out oc "%a %s %a" (pp `Appl) l op (pp `Appl) r;
                    if p <> `Func then out oc ")"
                | l::r::eargs ->
                    if p <> `Func then out oc "(";
                    (* Can be improved by looking at symbol priority. *)
                    out oc "(%a %s %a)" (pp `Appl) l op (pp `Appl) r;
                    List.iter (out oc " %a" (pp `Atom)) eargs;
                    if p <> `Func then out oc ")"
                | _ -> pp_appl h eargs
              end
          | Some Zero -> out oc "0"
          | Some Succ ->
              begin
                try out oc "%i" (nat_of_term t)
                with Not_a_nat -> pp_appl h args
              end
          | _   -> pp_appl h eargs
        end
    | _       -> pp_appl h args

  and pp_quantifier s args =
    (* assume [are_quant_args s args = true] *)
    match args with
    | [_;b] ->
        begin
          match unfold b with
          | Abst(a,b) ->
              let (x,p) = Bindlib.unbind b in
              out oc "`%a %a" pp_symbol s pp_var x;
              if !print_implicits then out oc ": %a" (pp `Func) a;
              out oc ", %a" (pp `Func) p
          | _ -> assert false
        end
      | _ -> assert false

  and pp_head wrap oc t =
    let pp_env oc ar =
      if ar <> [||] then out oc "[%a]" (Array.pp (pp `Appl) ",") ar
    in
    let pp_term_env oc te =
      match te with
      | TE_Vari(m) -> out oc "%s" (Bindlib.name_of m)
      | _          -> assert false
    in
    match unfold t with
    | Appl(_,_)   -> assert false
    (* Application is handled separately, unreachable. *)
    | Wild        -> out oc "_"
    | TRef(r)     ->
        (match !r with
         | None -> out oc "<TRef>"
         | Some t -> pp `Atom oc t)
    (* Atoms are printed inconditonally. *)
    | Vari(x)     -> pp_var oc x
    | Type        -> out oc "TYPE"
    | Kind        -> out oc "KIND"
    | Symb(s)     -> pp_symbol oc s
    | Meta(m,e)   -> out oc "%a%a" pp_meta m pp_env e
    | Patt(_,n,e) -> out oc "$%s%a" n pp_env e
    | TEnv(t,e)   -> out oc "$%a%a" pp_term_env t pp_env e
    (* Product and abstraction (only them can be wrapped). *)
    | Abst(a,b)   ->
        if wrap then out oc "(";
        let (x,t) = Bindlib.unbind b in
        out oc "λ %a" pp_bvar (b,x);
        if !print_domains then out oc ": %a, %a" (pp `Func) a (pp `Func) t
        else pp_abstractions oc t;
        if wrap then out oc ")"
    | Prod(a,b)   ->
        if wrap then out oc "(";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out oc "Π %a: %a, %a" pp_var x (pp `Func) a (pp `Func) t
        else out oc "%a → %a" (pp `Appl) a (pp `Func) t;
        if wrap then out oc ")"
    | LLet(a,t,b) ->
        if wrap then out oc "(";
        out oc "let ";
        let (x,u) = Bindlib.unbind b in
        pp_bvar oc (b,x);
        if !print_domains then out oc ": %a" (pp `Atom) a;
        out oc " ≔ %a in %a" (pp `Atom) t (pp `Atom) u;
        if wrap then out oc ")"
  and pp_bvar oc (b,x) =
    if Bindlib.binder_occur b then out oc "%a" pp_var x else out oc "_"
  and pp_abstractions oc t =
    match unfold t with
    | Abst(_,b) ->
        let (x,t) = Bindlib.unbind b in
        out oc " %a" pp_bvar (b,x); pp_abstractions oc t
    | t -> out oc ", %a" (pp `Func) t
  in
  pp `Func oc (cleanup t)

(** [pp_rule oc (s,h,r)] prints the rule [r] of symbol [s] to the output
   channel [oc]. *)
let pp_rule : (sym * rule) pp = fun oc (s,r) ->
  let lhs = LibTerm.add_args (Symb s) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  Format.fprintf oc "%a ↪ %a" pp_term lhs pp_term rhs

(** [pp_ctxt oc ctx] displays context [ctx] if {!val:print_contexts} is
    true, with [ ⊢ ] after; and nothing otherwise. *)
let pp_ctxt : ctxt pp = fun oc ctx ->
  if !print_contexts then
    let pp_ctxt : ctxt pp = fun oc ctx ->
      let pp_e oc (x,a,t) =
        match t with
        | None    -> Format.fprintf oc "%a: %a" pp_var x pp_term a
        | Some(t) ->
            Format.fprintf oc "%a: %a ≔ %a" pp_var x pp_term a pp_term t
      in
      if ctx = [] then Format.pp_print_string oc "∅"
      else List.pp pp_e ", " oc (List.rev ctx)
    in
    Format.fprintf oc "%a ⊢ " pp_ctxt ctx

(** [pp_typing oc (c,t,u)] prints the typing constraint [c] to the
    output channel [oc]. *)
let pp_typing : constr pp = fun oc (ctx, t, u) ->
  Format.fprintf oc "%a%a : %a" pp_ctxt ctx pp_term t pp_term u

(** [pp_constr oc c] prints the unification constraints [c] to the
    output channel [oc]. *)
let pp_constr : constr pp = fun oc (ctx, t, u) ->
  Format.fprintf oc "%a%a ≡ %a" pp_ctxt ctx pp_term t pp_term u

(** [pp_constr oc p] prints the unification problem [p] to the
    output channel [oc]. *)
let pp_problem : problem pp = fun oc p ->
  let constr oc c = Format.fprintf oc "\n; %a" pp_constr c in
  Format.fprintf oc
    "{ recompute = %b;\nto_solve = [%a];\nunsolved = [%a] }"
    p.recompute (List.pp constr "") p.to_solve (List.pp constr "") p.unsolved
