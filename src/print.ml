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

(** [pp_symbol h oc s] prints the name of the symbol [s] to channel [oc] using
    the printing hint [h] to decide qualification. *)
let pp_symbol : pp_hint -> sym pp = fun h oc s ->
  match h with
  | Nothing   -> Format.pp_print_string oc s.sym_name
  | Qualified -> Format.fprintf oc "%a.%s" Files.pp_path s.sym_path s.sym_name
  | Alias(a)  -> Format.fprintf oc "%s.%s" a s.sym_name
  | Binary(o) -> Format.fprintf oc "(%s)" o

(** [pp_tvar oc x] prints the term variable [x] to the channel [oc]. *)
let pp_tvar : tvar pp = fun oc x ->
  Format.pp_print_string oc (Bindlib.name_of x)

(** [pp_meta oc m] prints the uninstantiated meta-variable [m] to [oc]. *)
let pp_meta : meta pp = fun oc m ->
  Format.pp_print_string oc (meta_name m)

(** [pp_term oc t] prints the term [t] to the channel [oc]. *)
let pp_term : term pp = fun oc t ->
  let out = Format.fprintf in
  let rec pp (p : [`Func | `Appl | `Atom]) oc t =
    match Basics.get_args t with
    | (Symb(_,Binary(o)), [l;r]) ->
        if p = `Atom then out oc "(";
        (* Can be improved by looking at symbol priority. *)
        out oc "%a %s %a" (pp `Atom) l o (pp `Atom) r;
        if p = `Atom then out oc ")";
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
  in
  pp `Func oc (cleanup t)

(** [pp] is a short synonym of [pp_term]. *)
let pp : term pp = pp_term

(** [pp_rule oc (s,h,r)] prints the rule [r] of symbol [s] (with printing hing
    [h]) to the output channel [oc]. *)
let pp_rule : (sym * pp_hint * rule) pp = fun oc (s,h,r) ->
  let lhs = Basics.add_args (Symb(s,h)) r.lhs in
  let (_, rhs) = Bindlib.unmbind r.rhs in
  Format.fprintf oc "%a → %a" pp lhs pp rhs
