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
open Scope

(** Logging function for printing. *)
let log_prnt = new_logger 'p' "prnt" "pretty-printing"
let log_prnt = log_prnt.logger

(** Flag controling the printing of the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag controling the printing of implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag controling the printing of implicit arguments. *)
let print_meta_type : bool ref = Console.register_flag "print_meta_type" false

(** Flag controlling the printing of the context in unification. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** [assoc oc a] prints associativity [a] to channel [oc]. *)
let assoc : assoc pp = fun oc assoc ->
  Format.fprintf oc
    (match assoc with
     | Assoc_none -> ""
     | Assoc_left -> "left"
     | Assoc_right -> "right")

(** [hint oc a] prints hint [h] to channel [oc]. *)
let hint : hint pp = fun oc pp_hint ->
  match pp_hint with
  | No_hint -> ()
  | Prefix(n,p,_) -> Format.fprintf oc "prefix %s %f" n p
  | Infix(n,a,p,_) -> Format.fprintf oc "infix %s %a %f" n assoc a p

(** [qualified ss s] prints symbol [s] fully qualified to channel [oc]. *)
let qualified : sig_state -> sym pp = fun _ss oc s ->
  Format.fprintf oc "%a.%s" Files.Path.pp s.sym_path s.sym_name
    (*FIXME: handle aliases. *)

(** Get the printing hint of a symbol. *)
let get_hint : sig_state -> sym -> hint = fun ss s ->
  try SymMap.find s ss.hints with Not_found -> No_hint

(** [pp_symbol oc s] prints the name of the symbol [s] to channel [oc]. *)
let pp_symbol : sig_state -> sym pp = fun ss oc s ->
  if SymMap.mem s ss.hints then Format.pp_print_string oc s.sym_name
  else qualified ss oc s

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let rec pp_meta : sig_state -> meta pp = fun ss oc m ->
  if !print_meta_type then
    Format.fprintf oc "(%s:%a)" (meta_name m) (pp_term ss) !(m.meta_type)
  else
    Format.pp_print_string oc (meta_name m)

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
and pp_term : sig_state -> term pp = fun ss oc t ->
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
          match get_hint ss s with
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
    | Symb(s)     -> pp_symbol ss oc s
    | Meta(m,e)   -> out oc "%a%a" (pp_meta ss) m pp_env e
    | Patt(_,n,e) -> out oc "$%s%a" n pp_env e
    | TEnv(t,e)   -> out oc "$%a%a" pp_term_env t pp_env e
    (* Product and abstraction (only them can be wrapped). *)
    | Abst(a,b)   ->
        if wrap then out oc "(";
        out oc "λ";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then out oc "%a" pp_tvar x else out oc "_";
        if !print_domains then out oc ": %a" (pp `Func) a;
        out oc ", %a" (pp `Func) t;
        if wrap then out oc ")"
    | Prod(a,b)   ->
        if wrap then out oc "(";
        let (x,t) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          out oc "Π%a: %a, %a" pp_tvar x (pp `Func) a (pp `Func) t
        else
          out oc "%a → %a" (pp `Appl) a (pp `Func) t;
        if wrap then out oc ")"
    | LLet(a,t,b) ->
        if wrap then out oc "(";
        let (x,u) = Bindlib.unbind b in
        if Bindlib.binder_occur b then out oc "%a" pp_tvar x else out oc "_";
        if !print_domains then out oc ": %a" (pp `Atom) a;
        out oc " ≔ %a in %a" (pp `Atom) t (pp `Atom) u;
        if wrap then out oc ")"
  in
  pp `Func oc (cleanup t)

(** [pp_rule oc (s,h,r)] prints the rule [r] of symbol [s] to the output
   channel [oc]. *)
let pp_rule : sig_state -> (sym * rule) pp
  = fun ss oc (s,r) ->
  let lhs = Basics.add_args (Symb s) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  Format.fprintf oc "%a ↪ %a" (pp_term ss) lhs (pp_term ss) rhs

(** [pp_ctxt oc ctx] displays context [ctx] if {!val:print_contexts} is
    true, with [ ⊢ ] after; and nothing otherwise. *)
let pp_ctxt : sig_state -> ctxt pp = fun ss oc ctx ->
  if !print_contexts then
    let pp = pp_term ss in
    let pp_ctxt : ctxt pp = fun oc ctx ->
      let pp_e oc (x,a,t) =
        match t with
        | None    -> Format.fprintf oc "%a: %a" pp_tvar x pp a
        | Some(t) -> Format.fprintf oc "%a: %a ≔ %a" pp_tvar x pp a pp t
      in
      if ctx = [] then Format.pp_print_string oc "∅"
      else List.pp pp_e ", " oc (List.rev ctx)
    in
    Format.fprintf oc "%a ⊢ " pp_ctxt ctx

(** [pp_typing oc (c,t,u)] prints the typing constraint [c] to the
    output channel [oc]. *)
let pp_typing : sig_state -> constr pp
  = fun ss oc (ctx, t, u) ->
  Format.fprintf oc "%a%a : %a"
    (pp_ctxt ss) ctx (pp_term ss) t (pp_term ss) u

(** [pp_constr oc c] prints the unification constraints [c] to the
    output channel [oc]. *)
let pp_constr : sig_state -> constr pp
  = fun ss oc (ctx, t, u) ->
  Format.fprintf oc "%a%a ≡ %a"
    (pp_ctxt ss) ctx (pp_term ss) t (pp_term ss) u

(** [pp_constr oc p] prints the unification problem [p] to the
    output channel [oc]. *)
let pp_problem : sig_state -> problem pp = fun ss oc p ->
  Format.fprintf oc "{ to_solve = [%a]; unsolved = [%a]; recompute = %b }"
    (List.pp (pp_constr ss) "; ") p.to_solve
    (List.pp (pp_constr ss) "; ") p.unsolved
    p.recompute

(** Default printing functions (with empty signature state). *)
let empty_sig_state = empty_sig_state (Sign.create [])
let symbol = pp_symbol empty_sig_state
let meta = pp_meta empty_sig_state
let term = pp_term empty_sig_state
let constr = pp_constr empty_sig_state
let rule = pp_rule empty_sig_state
let ctxt = pp_ctxt empty_sig_state
let problem = pp_problem empty_sig_state
