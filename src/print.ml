(** Pretty-printing for the core AST.

    The functions of this module are used for printing terms and other objects
    defined in the {!module:Terms} module.  This is mainly used for displaying
    log messages, and feedback in case of success or error while type-checking
    terms or testing convertibility. *)

open Timed
open Extra
open Terms

(** Flag controling the printing of the domains of λ-abstractions. *)
let print_domains : bool ref = Console.register_flag "print_domains" false

(** Flag controling the printing of implicit arguments. *)
let print_implicits : bool ref = Console.register_flag "print_implicits" false

(** Flag controlling the printing of the context in unification. *)
let print_contexts : bool ref = Console.register_flag "print_contexts" false

(** Flag controling the printing of implicit arguments. *)
let print_meta_type : bool ref = Console.register_flag "print_meta_type" false

(** [pp_symbol h oc s] prints the name of the symbol [s] to channel [oc] using
    the printing hint [h] to decide qualification. *)
let pp_symbol : pp_hint -> sym pp = fun h oc s ->
  match h with
  | Nothing   -> Format.pp_print_string oc s.sym_name
  | Qualified -> Format.fprintf oc "%a.%s" Files.pp_path s.sym_path s.sym_name
  | Alias(a)  -> Format.fprintf oc "%s.%s" a s.sym_name
  | Binary(o) -> Format.fprintf oc "(%s)" o
  | Unary(o)  -> Format.fprintf oc "(%s)" o

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [pp_tevar oc x] prints the term environment variable [x] to the channel
    [oc]. *)
let pp_tevar : tevar pp = fun oc x ->
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
    let args =
      if !print_implicits then args else
      let impl =  match h with Symb(s,_) -> s.sym_impl | _ -> [] in
      let rec filter_impl impl args =
        match (impl, args) with
        | ([]         , _      ) -> args
        | (true ::impl, _::args) -> filter_impl impl args
        | (false::impl, a::args) -> a :: filter_impl impl args
        | (_          , []     ) -> args
      in
      filter_impl impl args
    in
    match (h, args) with
    | (Symb(_,Binary(o)), [l;r]) ->
        if p <> `Func then out oc "(";
        (* Can be improved by looking at symbol priority. *)
        out oc "%a %s %a" (pp `Appl) l o (pp `Appl) r;
        if p <> `Func then out oc ")";
    | (h                , []   ) ->
        pp_head (p <> `Func) oc h
    | (h                , args ) ->
        if p = `Atom then out oc "(";
        pp_head true oc h;
        List.iter (out oc " %a" (pp `Atom)) args;
        if p = `Atom then out oc ")"
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
    | Symb(s,h)   -> pp_symbol h oc s
    | Meta(m,e)   -> out oc "%a%a" pp_meta m pp_env e
    | Patt(_,n,e) -> out oc "&%s%a" n pp_env e
    | TEnv(t,e)   -> out oc "&%a%a" pp_term_env t pp_env e
    (* Product and abstraction (only them can be wrapped). *)
    | Abst(a,t)   ->
        if wrap then out oc "(";
        let pp_arg oc (x,a) =
          if !print_domains then out oc "(%a:%a)" pp_tvar x (pp `Func) a
          else pp_tvar oc x
        in
        let (x,t) = Bindlib.unbind t in
        out oc "λ%a" pp_arg (x,a);
        let rec pp_absts oc t =
          match unfold t with
          | Abst(a,t) -> let (x,t) = Bindlib.unbind t in
                         out oc " %a%a" pp_arg (x,a) pp_absts t
          | _         -> out oc ", %a" (pp `Func) t
        in
        pp_absts oc t;
        if wrap then out oc ")"
    | Prod(a,b)   ->
        if wrap then out oc "(";
        let pp_arg oc (x,a) = out oc "(%a:%a)" pp_tvar x (pp `Func) a in
        let (x,c) = Bindlib.unbind b in
        if Bindlib.binder_occur b then
          begin
            out oc "∀%a" pp_arg (x,a);
            let rec pp_prods oc c =
              match unfold c with
              | Prod(a,b) when Bindlib.binder_occur b ->
                  let (x,b) = Bindlib.unbind b in
                  out oc " %a%a" pp_arg (x,a) pp_prods b
              | _                                      ->
                  out oc ", %a" (pp `Func) c
            in
            pp_prods oc c
          end
        else
          out oc "%a ⇒ %a" (pp `Appl) a (pp `Func) c;
        if wrap then out oc ")"
    | LLet(t,a,u) ->
        if wrap then out oc "(";
        let x, u = Bindlib.unbind u in
        out oc "let %a" pp_tvar x;
        if !print_domains then out oc ":%a" (pp `Atom) a;
        out oc "≔ %a in %a" (pp `Atom) t (pp `Atom) u;
        if wrap then out oc ")"
  in
  pp `Func oc (cleanup t)

(** [pp] is a short synonym of [pp_term]. *)
let pp : term pp = pp_term

(** [pp_rule oc (s,h,r)] prints the rule [r] of symbol [s] (with printing hint
    [h]) to the output channel [oc]. *)
let pp_rule : (sym * pp_hint * rule) pp = fun oc (s,h,r) ->
  let lhs = Basics.add_args (Symb(s,h)) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  Format.fprintf oc "%a → %a" pp lhs pp rhs

(** [pp_hint oc h] prints hint [h] to channel [oc]. *)
let pp_hint : rule pp = fun oc h ->
  let (s, pph) =
    match Unif_hints.atom with
    | Symb(s, pph) -> s, pph
    | _            -> assert false
  in
  pp_rule oc (s, pph, h)

(** [pp oc ctx] prints the context [ctx] to the channel [oc]. *)
let pp_ctxt : ctxt pp = fun oc ctx ->
  let pp_e oc (x,a,t) =
    match t with
    | None    -> Format.fprintf oc "%a : %a" pp_tvar x pp a
    | Some(t) -> Format.fprintf oc "%a : %a ≔ %a" pp_tvar x pp a pp t
  in
  if ctx = [] then Format.pp_print_string oc "∅"
  else List.pp pp_e ", " oc (List.rev ctx)

(** [pp_constr oc (t,u)] prints the unification constraints [(t,u)] to the
    output channel [oc]. *)
let pp_constr : (ctxt * term * term) pp = fun oc (ctx, t, u) ->
  if !print_contexts then Format.fprintf oc "[%a] ⊢ " pp_ctxt ctx;
  Format.fprintf oc "%a ≡ %a" pp t pp u
