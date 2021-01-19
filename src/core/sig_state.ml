(** Signature state.

   This module provides a record type [sig_state] containing all the
   informations needed for scoping p_terms and printing terms, and functions
   on this type for manipulating it. In particular, it provides functions
   [open_sign], [add_symbol], [add_binop], etc. taking a [sig_state] as
   argument and returning a new [sig_state] as result. These functions call
   the corresponding functions of [Sign] which should not be called directly
   but through the current module only, in order to setup the [sig_state]
   properly. *)

open Lplib.Base
open Lplib.Extra

open Timed
open Console
open Files
open Pos
open Syntax
open Terms
open Sign

(** Pretty-printing information associated to a symbol. *)
type pp_hint =
  | Unqual
  | Prefix of unop
  | Infix of binop
  | Zero
  | Succ
  | Quant

(** [eq_pp_hint h1 h2] says whether [h1] and [h2] are equal, ignoring
   associativity and priorities. *)
let eq_pp_hint : pp_hint eq = fun h1 h2 ->
  match (h1, h2) with
  | (Unqual, Unqual)
  | (Quant, Quant)
  | (Zero, Zero)
  | (Succ, Succ) -> true
  | (Prefix (s1,_,_), Prefix (s2,_,_))
  | (Infix (s1,_,_,_), Infix (s2,_,_,_)) -> s1 = s2
  | (_, _) -> false

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { signature : Sign.t                    (** Current signature.        *)
  ; in_scope  : (sym * Pos.popt) StrMap.t (** Symbols in scope.         *)
  ; aliases   : Path.t StrMap.t           (** Established aliases.      *)
  ; path_map  : string PathMap.t          (** Reverse map of [aliases]. *)
  ; builtins  : sym StrMap.t              (** Builtin symbols.          *)
  ; pp_hints  : pp_hint SymMap.t          (** Printing hints.           *) }

type t = sig_state

(** [create_sign path] creates a signature with path [path] with ghost modules
    as dependencies. *)
let create_sign : Path.t -> Sign.t = fun sign_path ->
  let d = Sign.dummy () in
  { d with sign_path ; sign_deps = ref (PathMap.singleton Unif_rule.path []) }

(** [remove_pp_hint map name pp_hints] removes from [pp_hints] the mapping for
   [s] if [s] is mapped to [name] in [map]. *)
let remove_pp_hint :
      sym StrMap.t -> string -> pp_hint SymMap.t -> pp_hint SymMap.t =
  fun map name pp_hints ->
  try SymMap.remove (StrMap.find name map) pp_hints
  with Not_found -> pp_hints

(** [remove_pp_hint_eq map name h pp_hints] removes from [pp_hints] the
   mapping for [s] if [s] is mapped to [(name,h')] in [map], and [eq_pp_hint h
   h' = true]. *)
let remove_pp_hint_eq :
      (sym * Pos.popt) StrMap.t -> string -> pp_hint -> pp_hint SymMap.t
      -> pp_hint SymMap.t =
  fun in_scope name h pp_hints ->
  try
    let (s,_) = StrMap.find name in_scope in
    let h' = SymMap.find s pp_hints in
    if eq_pp_hint h h' then SymMap.remove s pp_hints else pp_hints
  with Not_found -> pp_hints

(** Symbol properties needed for the signature *)
type sig_symbol =
  { expo   : expo        (** exposition          *)
  ; prop   : prop        (** property            *)
  ; mstrat : match_strat (** strategy            *)
  ; ident  : ident       (** name                *)
  ; typ    : term        (** type                *)
  ; impl   : bool list   (** implicit arguments  *)
  ; def    : term option (** optional definition *) }

(** [add_symbol ss sig_symbol={e,p,st,x,a,impl,def}] generates a new signature
   state from [ss] by creating a new symbol with expo [e], property [p],
   strategy [st], name [x], type [a], implicit arguments [impl] and optional
   definition [t]. This new symbol is returned too. *)
let add_symbol : sig_state -> sig_symbol -> sig_state * sym =
  fun ss {expo=e;prop=p;mstrat=st;ident=x;typ=a;impl;def=t} ->
  let s = Sign.add_symbol ss.signature e p st x a impl in
  begin
    match t with
    | Some t -> s.sym_def := Some (cleanup t)
    | None -> ()
  end;
  let in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope in
  let pp_hints = remove_pp_hint_eq ss.in_scope x.elt Unqual ss.pp_hints in
  let pp_hints = SymMap.add s Unqual pp_hints in
  ({ss with in_scope; pp_hints}, s)

(** [add_unop ss n x] generates a new signature state from [ss] by adding a
    unary operator [x] with name [n]. This name is added to the scope. *)
let add_unop : sig_state -> strloc -> (sym * unop) -> sig_state =
  fun ss name ((sym, unop) as x) ->
  Sign.add_unop ss.signature name.elt x;
  let in_scope = StrMap.add name.elt (sym, name.pos) ss.in_scope in
  let pp_hints =
    let unops = StrMap.map fst !(ss.signature.sign_unops) in
    remove_pp_hint unops name.elt ss.pp_hints
  in
  let pp_hints = SymMap.add sym (Prefix unop) pp_hints in
  {ss with in_scope; pp_hints}

(** [add_binop ss n x] generates a new signature state from [ss] by adding a
    binary operator [x] with name [n]. This name is added to scope. *)
let add_binop : sig_state -> strloc -> (sym * binop) -> sig_state =
  fun ss name ((sym, binop) as x) ->
  Sign.add_binop ss.signature name.elt x;
  let in_scope = StrMap.add name.elt (sym, name.pos) ss.in_scope in
  let pp_hints =
    let binops = StrMap.map fst !(ss.signature.sign_binops) in
    remove_pp_hint binops name.elt ss.pp_hints
  in
  let pp_hints = SymMap.add sym (Infix binop) pp_hints in
  {ss with in_scope; pp_hints}

(** [add_builtin ss n s] generates a new signature state from [ss] by mapping
   the builtin [n] to [s]. *)
let add_builtin : sig_state -> string -> sym -> sig_state = fun ss name sym ->
  Sign.add_builtin ss.signature name sym;
  let builtins = StrMap.add name sym ss.builtins in
  let add_pp_hint hint =
    SymMap.add sym hint (remove_pp_hint ss.builtins name ss.pp_hints)
  in
  let pp_hints =
    match name with
    | "0"  -> add_pp_hint Zero
    | "+1" -> add_pp_hint Succ
    | _    -> ss.pp_hints
  in
  {ss with builtins; pp_hints}

(** [add_quant ss sym] generates a new signature state from [ss] by declaring
   [sym] as quantifier. *)
let add_quant : sig_state -> sym -> sig_state = fun ss sym ->
  Sign.add_quant ss.signature sym;
  {ss with pp_hints = SymMap.add sym Quant ss.pp_hints}

(** [update_pp_hints_from_symbols ss sign pp_hints] generates a new pp_hint
   map from [pp_hints] when adding the symbols of [sign]. *)
let update_pp_hints_from_symbols :
      (sym * Pos.popt) StrMap.t -> Sign.t -> pp_hint SymMap.t
      -> pp_hint SymMap.t =
  fun in_scope sign pp_hints ->
  let fn name (sym,_) pp_hints =
    let h =
      let exception Hint of pp_hint in
      try
        let fn_binop _ (s,binop) =
          if s == sym then raise (Hint (Infix binop))
        in
        StrMap.iter fn_binop !(sign.sign_binops);
        let fn_unop _ (s,unop) =
          if s == sym then raise (Hint (Prefix unop))
        in
        StrMap.iter fn_unop !(sign.sign_unops);
        Unqual
      with Hint h -> h
    in
    SymMap.add sym h (remove_pp_hint_eq in_scope name h pp_hints)
  in
  StrMap.fold fn !(sign.sign_symbols) pp_hints

(** [update_pp_hints_from_builtins old_bm new_bm pp_hints] generates a new
   pp_hint map from [pp_hints] when adding [new_bm] to the builtin map
   [old_bm]. *)
let update_pp_hints_from_builtins
    : sym StrMap.t -> sym StrMap.t -> pp_hint SymMap.t -> pp_hint SymMap.t =
  fun old_bm new_bm pp_hints ->
  let add_hint name h pp_hints =
    try
      let s_new = StrMap.find name new_bm in
      try
        let s_old = StrMap.find name old_bm in
        SymMap.add s_new h (SymMap.remove s_old pp_hints)
      with Not_found -> SymMap.add s_new h pp_hints
    with Not_found -> pp_hints
  in
  add_hint "0" Zero (add_hint "+1" Succ pp_hints)

(** [open_sign ss sign] extends the signature state [ss] with every symbol  of
    the signature [sign].  This has the effect of putting these symbols in the
    scope when (possibly masking symbols with the same name).  Builtin symbols
    are also handled in a similar way. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _key _v1 v2 = Some(v2) in (* hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope !(sign.sign_symbols) in
  let builtins = StrMap.union f ss.builtins !(sign.sign_builtins) in
  (* Bring operators in scope *)
  let open_op k (s, _) ssis = StrMap.add k (s, None) ssis in
  let in_scope = StrMap.fold open_op !(sign.sign_unops) in_scope in
  let in_scope = StrMap.fold open_op !(sign.sign_binops) in_scope in
  let pp_hints = update_pp_hints_from_symbols ss.in_scope sign ss.pp_hints in
  let pp_hints =
    update_pp_hints_from_builtins ss.builtins !(sign.sign_builtins) pp_hints
  in
  {ss with in_scope; builtins; pp_hints}

(** Dummy [sig_state] made from the dummy signature. *)
let dummy : sig_state =
  { signature = Sign.dummy (); in_scope = StrMap.empty; aliases = StrMap.empty
  ; path_map = PathMap.empty; builtins = StrMap.empty
  ; pp_hints = SymMap.empty }

(** [of_sign sign] creates a state from the signature [sign] with ghost
    signatures opened. *)
let of_sign : Sign.t -> sig_state = fun signature ->
  open_sign {dummy with signature} Unif_rule.sign

(** [find_sym ~prt ~prv b st qid] returns the symbol
    corresponding to the qualified identifier [qid]. If [fst qid.elt] is
    empty, we search for the name [snd qid.elt] in the opened modules of [st].
    The boolean [b] only indicates if the error message should mention
    variables, in the case where the module path is empty and the symbol is
    unbound. This is reported using the [Fatal] exception.
    {!constructor:Terms.expo.Protec} symbols from other modules
    are allowed in left-hand side of rewrite rules (only) iff [~prt] is true.
    {!constructor:Terms.expo.Privat} symbols are allowed iff [~prv]
    is [true]. *)
let find_sym : prt:bool -> prv:bool -> bool -> sig_state -> qident -> sym =
  fun ~prt ~prv b st qid ->
  let {elt = (mp, s); pos} = qid in
  let mp = List.map fst mp in
  let s =
    match mp with
    | []                               -> (* Symbol in scope. *)
        begin
          try fst (StrMap.find s st.in_scope) with Not_found ->
          let txt = if b then " or variable" else "" in
          fatal pos "Unbound symbol%s [%s]." txt s
        end
    | [m] when StrMap.mem m st.aliases -> (* Aliased module path. *)
        begin
          (* The signature must be loaded (alias is mapped). *)
          let sign =
            try PathMap.find (StrMap.find m st.aliases) Timed.(!Sign.loaded)
            with _ -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unbound symbol [%a.%s]." Path.pp mp s
        end
    | _                                -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> st.signature.sign_path then
            if not (PathMap.mem mp !(st.signature.sign_deps)) then
              fatal pos "No module [%a] required." Path.pp mp;
          (* The signature must have been loaded. *)
          let sign =
            try PathMap.find mp Timed.(!Sign.loaded)
            with Not_found -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unbound symbol [%a.%s]." Path.pp mp s
        end
  in
  match (prt, prv, s.sym_expo) with
  | (false, _    , Protec) ->
      if s.sym_path = st.signature.sign_path then s else
      (* Fail if symbol is not defined in the current module. *)
      fatal pos "Protected symbol not allowed here."
  | (_    , false, Privat) -> fatal pos "Private symbol not allowed here."
  | _                      -> s
