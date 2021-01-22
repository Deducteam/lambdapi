(** Pretty-printing for the core AST.

    The functions of this module are used for printing terms and other objects
    defined in the {!module:Terms} module.  This is mainly used for displaying
    log messages, and feedback in case of success or error while type-checking
    terms or testing convertibility. *)

open! Lplib
open Lplib.Base
open Lplib.Extra

open Timed
open Terms
open Console
open Syntax
open Sig_state

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

let pp_prop : prop pp = fun oc p ->
  match p with
  | Defin -> ()
  | Const -> Format.fprintf oc "constant "
  | Injec -> Format.fprintf oc "injective "

let pp_expo : expo pp = fun oc e ->
  match e with
  | Public -> ()
  | Protec -> Format.fprintf oc "protected "
  | Privat -> Format.fprintf oc "private "

let pp_match_strat : match_strat pp = fun oc s ->
  match s with
  | Sequen -> Format.fprintf oc "sequential "
  | Eager -> ()

(** [assoc oc a] prints associativity [a] to channel [oc]. *)
let pp_assoc : assoc pp = fun oc assoc ->
  match assoc with
  | Assoc_none -> ()
  | Assoc_left -> Format.fprintf oc " left associative"
  | Assoc_right -> Format.fprintf oc " right associative"

(** [hint oc a] prints hint [h] to channel [oc]. *)
let pp_hint : pp_hint pp = fun oc pp_hint ->
  match pp_hint with
  | Unqual         -> ()
  | Prefix(n,p,_)  -> Format.fprintf oc "prefix \"%s\" with priority %f" n p
  | Infix(n,a,p,_) ->
      Format.fprintf oc "infix \"%s\"%a with priority %f" n pp_assoc a p
  | Zero           -> Format.fprintf oc "builtin \"0\""
  | Succ           -> Format.fprintf oc "builtin \"+1\""
  | Quant          -> Format.fprintf oc "quantifier"

(** [qualified s] prints symbol [s] fully qualified to channel [oc]. *)
let pp_qualified : sym pp = fun oc s ->
  match Files.PathMap.find_opt s.sym_path (!sig_state).path_map with
  | None -> Format.fprintf oc "%a.%s" Files.Path.pp s.sym_path s.sym_name
  | Some alias -> Format.fprintf oc "%s.%s" alias s.sym_name

(** Get the printing hint of a symbol. *)
let get_pp_hint : sym -> pp_hint = fun s ->
  try SymMap.find s (!sig_state).pp_hints with Not_found -> Unqual

(** [pp_symbol oc s] prints the name of the symbol [s] to channel [oc]. *)
let pp_symbol : sym pp = fun oc s ->
  if SymMap.mem s (!sig_state).pp_hints
     || Files.Path.compare s.sym_path (!sig_state).signature.sign_path = 0
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
    match Basics.get_args t with
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
    let (h, args) = Basics.get_args t in
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
            if !print_implicits then args else Basics.expl_args s args
          in
          match get_pp_hint s with
          | Quant when are_quant_args s args ->
              if p <> `Func then out oc "(";
              pp_quantifier s args;
              if p <> `Func then out oc ")"
          | Infix(op,_,_,_) when not !print_implicits || s.sym_impl <> [] ->
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
          | Zero -> out oc "0"
          | Succ ->
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
              out oc "%a%a" pp_symbol s pp_var x;
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
        out oc "λ%a" pp_bvar (b,x);
        if !print_domains then out oc ": %a, %a" (pp `Func) a (pp `Func) t
        else pp_abstractions oc t;
        if wrap then out oc ")"
    | Prod(a,b)   ->
        if wrap then out oc "(";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out oc "Π%a: %a, %a" pp_var x (pp `Func) a (pp `Func) t
        else out oc "%a → %a" (pp `Appl) a (pp `Func) t;
        if wrap then out oc ")"
    | LLet(a,t,b) ->
        if wrap then out oc "(";
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
  let lhs = Basics.add_args (Symb s) r.lhs in
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
