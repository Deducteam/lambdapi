(** Pretty-printing for the core AST.

    The functions of this module are used for printing terms and other objects
    defined in the {!module:Terms} module.  This is mainly used for displaying
    log messages, and feedback in case of success or error while type-checking
    terms or testing convertibility. *)

open Timed
open Extra
open Terms
open Console
open Syntax
open Sig_state

(** Logging function for printing. *)
let log_prnt = new_logger 'p' "prnt" "pretty-printing"
let log_prnt = log_prnt.logger

(** Current signature state. *)
let sig_state : sig_state ref = ref Sig_state.empty

(** Flag controling the printing of the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag controling the printing of implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag controling the printing of implicit arguments. *)
let print_meta_type : bool ref = Console.register_flag "print_meta_type" false

(** Flag controlling the printing of the context in unification. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** [assoc oc a] prints associativity [a] to channel [oc]. *)
let pp_assoc : assoc pp = fun oc assoc ->
  Format.fprintf oc
    (match assoc with
     | Assoc_none -> ""
     | Assoc_left -> "left"
     | Assoc_right -> "right")

(** [hint oc a] prints hint [h] to channel [oc]. *)
let pp_hint : hint pp = fun oc pp_hint ->
  match pp_hint with
  | No_hint -> ()
  | Prefix(n,p,_) -> Format.fprintf oc "prefix %s %f" n p
  | Infix(n,a,p,_) -> Format.fprintf oc "infix %s %a %f" n pp_assoc a p

(** [qualified s] prints symbol [s] fully qualified to channel [oc]. *)
let pp_qualified : sym pp = fun oc s ->
  Format.fprintf oc "%a.%s" Files.Path.pp s.sym_path s.sym_name
    (*FIXME: handle aliases. *)

(** Get the printing hint of a symbol. *)
let get_hint : sym -> hint = fun s ->
  try SymMap.find s (!sig_state).hints with Not_found -> No_hint

(** [pp_symbol oc s] prints the name of the symbol [s] to channel [oc]. *)
let pp_symbol : sym pp = fun oc s ->
  if SymMap.mem s (!sig_state).hints then Format.pp_print_string oc s.sym_name
  else pp_qualified oc s

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let rec pp_meta : meta pp = fun oc m ->
  if !print_meta_type then
    Format.fprintf oc "(%s:%a)" (meta_name m) pp_term !(m.meta_type)
  else
    Format.pp_print_string oc (meta_name m)

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
    | Symb(s) when not !print_implicits ->
        begin
          let args = Basics.expl_args s args in
          match get_hint s with
          | No_hint -> pp_appl h args
          | Prefix(_) -> pp_appl h args
          | Infix(op,_,_,_) ->
              begin
                match args with
                | l::r::[] ->
                    if p <> `Func then out oc "(";
                    (* Can be improved by looking at symbol priority. *)
                    out oc "%a %s %a" (pp `Appl) l op (pp `Appl) r;
                    if p <> `Func then out oc ")"
                | l::r::ts ->
                    if p <> `Func then out oc "(";
                    out oc "(";
                    (* Can be improved by looking at symbol priority. *)
                    out oc "%a %s %a" (pp `Appl) l op (pp `Appl) r;
                    out oc ")";
                    List.iter (out oc " %a" (pp `Atom)) ts;
                    if p <> `Func then out oc ")"
                | _ -> pp_appl h args
              end
        end
    | _       -> pp_appl h args
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
    (* Application is handled separately, unreachable. *)
    | Appl(_,_)   -> assert false
    (* Forbidden cases. *)
    | Wild        -> assert false
    | TRef(_)     -> assert false
    (* Atoms are printed inconditonally. *)
    | Vari(x)     -> pp_tvar oc x
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
        if !print_domains then
          out oc "λ%a: %a, %a" pp_var (b,x) (pp `Func) a (pp `Func) t
        else out oc "λ%a%a" pp_var (b,x) pp_abstractions t;
        if wrap then out oc ")"
    | Prod(a,b)   ->
        if wrap then out oc "(";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out oc "Π%a: %a, %a" pp_tvar x (pp `Func) a (pp `Func) t
        else out oc "%a → %a" (pp `Appl) a (pp `Func) t;
        if wrap then out oc ")"
    | LLet(a,t,b) ->
        if wrap then out oc "(";
        let (x,u) = Bindlib.unbind b in
        pp_var oc (b,x);
        if !print_domains then out oc ": %a" (pp `Atom) a;
        out oc " ≔ %a in %a" (pp `Atom) t (pp `Atom) u;
        if wrap then out oc ")"
  and pp_var oc (b,x) =
    if Bindlib.binder_occur b then out oc "%a" pp_tvar x else out oc "_"
  and pp_abstractions oc t =
    match unfold t with
    | Abst(_,b) ->
        let (x,t) = Bindlib.unbind b in
        out oc " %a" pp_var (b,x); pp_abstractions oc t
    | t -> out oc ", %a" (pp `Func) t
  in
  pp `Func oc (cleanup t)

(** [pp_rule oc (s,h,r)] prints the rule [r] of symbol [s] to the output
   channel [oc]. *)
let pp_rule : (sym * rule) pp
  = fun oc (s,r) ->
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
        | None    -> Format.fprintf oc "%a: %a" pp_tvar x pp_term a
        | Some(t) ->
            Format.fprintf oc "%a: %a ≔ %a" pp_tvar x pp_term a pp_term t
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
  Format.fprintf oc "{ to_solve = [%a]; unsolved = [%a]; recompute = %b }"
    (List.pp pp_constr "; ") p.to_solve
    (List.pp pp_constr "; ") p.unsolved
    p.recompute
