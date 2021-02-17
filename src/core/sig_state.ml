(** Signature state.

   This module provides a record type [sig_state] containing all the
   informations needed for scoping p_terms and printing terms, and functions
   on this type for manipulating it. In particular, it provides functions
   [open_sign], [add_symbol], [add_binop], etc. taking a [sig_state] as
   argument and returning a new [sig_state] as result. These functions call
   the corresponding functions of [Sign] which should not be called directly
   but through the current module only, in order to setup the [sig_state]
   properly. *)

open Lplib.Extra
open Common
open Error
open Pos
open Timed
open Parsing
open Syntax
open Term
open Sign

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { signature : Sign.t                    (** Current signature.        *)
  ; in_scope  : (sym * Pos.popt) StrMap.t (** Symbols in scope.         *)
  ; alias_path   : Path.t StrMap.t        (** Alias to path map.        *)
  ; path_alias  : string Path.Map.t       (** Path to alias map.        *)
  ; builtins  : sym StrMap.t              (** Builtin symbols.          *)
  ; notations : notation SymMap.t         (** Printing hints.           *) }

type t = sig_state

(** [create_sign path] creates a signature with path [path] with ghost modules
    as dependencies. *)
let create_sign : Path.t -> Sign.t = fun sign_path ->
  let d = Sign.dummy () in
  {d with sign_path; sign_deps = ref (Path.Map.singleton Unif_rule.path [])}

(** [add_symbol ss expo prop mstrat opaq id typ impl def] generates a new
   signature state from [ss] by creating a new symbol with expo [e], property
   [p], strategy [st], name [x], type [a], implicit arguments [impl] and
   optional definition [def]. This new symbol is returned too. *)
let add_symbol : sig_state -> Tags.expo -> Tags.prop -> Tags.match_strat
    -> bool -> strloc -> term -> bool list -> term option -> sig_state * sym =
  fun ss expo prop mstrat opaq id typ impl def ->
  let sym = Sign.add_symbol ss.signature expo prop mstrat opaq id typ impl in
  begin
    match def with
    | Some t -> sym.sym_def := Some (cleanup t)
    | None -> ()
  end;
  let in_scope = StrMap.add id.elt (sym, id.pos) ss.in_scope in
  ({ss with in_scope}, sym)

(** [add_unop ss n x] generates a new signature state from [ss] by adding a
    unary operator [x] with name [n]. This name is added to the scope. *)
let add_unop : sig_state -> strloc -> (sym * unop) -> sig_state =
  fun ss name (sym, unop) ->
  Sign.add_unop ss.signature sym unop;
  let in_scope = StrMap.add name.elt (sym, name.pos) ss.in_scope in
  let notations = SymMap.add sym (Prefix unop) ss.notations in
  {ss with in_scope; notations}

(** [add_binop ss n x] generates a new signature state from [ss] by adding a
    binary operator [x] with name [n]. This name is added to scope. *)
let add_binop : sig_state -> strloc -> (sym * binop) -> sig_state =
  fun ss name (sym, binop) ->
  Sign.add_binop ss.signature sym binop;
  let in_scope = StrMap.add name.elt (sym, name.pos) ss.in_scope in
  let notations = SymMap.add sym (Infix binop) ss.notations in
  {ss with in_scope; notations}

(** [add_builtin ss n s] generates a new signature state from [ss] by mapping
   the builtin [n] to [s]. *)
let add_builtin : sig_state -> string -> sym -> sig_state =
  fun ss builtin sym ->
  Sign.add_builtin ss.signature builtin sym;
  let builtins = StrMap.add builtin sym ss.builtins in
  let notations =
    match builtin with
    | "0"  -> SymMap.add sym Zero ss.notations
    | "+1" -> SymMap.add sym Succ ss.notations
    | _    -> ss.notations
  in
  {ss with builtins; notations}

(** [add_quant ss sym] generates a new signature state from [ss] by declaring
   [sym] as quantifier. *)
let add_quant : sig_state -> sym -> sig_state = fun ss sym ->
  Sign.add_quant ss.signature sym;
  {ss with notations = SymMap.add sym Quant ss.notations}

(** [update_notations_from_builtins old_bm new_bm notmap] generates a new
   notation map from [notmap] when adding [new_bm] to the builtin map
   [old_bm]. *)
let update_notations_from_builtins :
    sym StrMap.t -> sym StrMap.t -> notation SymMap.t -> notation SymMap.t =
  fun old_bm new_bm notmap ->
  let add builtin notation notmap =
    try
      let s_new = StrMap.find builtin new_bm in
      try
        let s_old = StrMap.find builtin old_bm in
        SymMap.add s_new notation (SymMap.remove s_old notmap)
      with Not_found -> SymMap.add s_new notation notmap
    with Not_found -> notmap
  in
  add "0" Zero (add "+1" Succ notmap)

(** [open_sign ss sign] extends the signature state [ss] with every symbol  of
    the signature [sign].  This has the effect of putting these symbols in the
    scope when (possibly masking symbols with the same name).  Builtin symbols
    are also handled in a similar way. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _key _v1 v2 = Some(v2) in (* hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope !(sign.sign_symbols) in
  let builtins = StrMap.union f ss.builtins !(sign.sign_builtins) in
  (* Bring operators in scope *)
  let open_notation s notation in_scope =
    match notation with
    | Sign.Infix (k,_, _, _) -> StrMap.add k (s, None) in_scope
    | Sign.Prefix (k,_,_) -> StrMap.add k (s, None) in_scope
    | _ -> in_scope
  in
  let in_scope = SymMap.fold open_notation !(sign.sign_notations) in_scope in
  let notations =
    SymMap.fold SymMap.add !(sign.sign_notations) ss.notations
  in
  let notations =
    update_notations_from_builtins ss.builtins !(sign.sign_builtins) notations
  in
  {ss with in_scope; builtins; notations}

(** Dummy [sig_state] made from the dummy signature. *)
let dummy : sig_state =
  { signature = Sign.dummy (); in_scope = StrMap.empty;
    alias_path = StrMap.empty; path_alias = Path.Map.empty;
    builtins = StrMap.empty; notations = SymMap.empty }

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
    {!constructor:Term.expo.Protec} symbols from other modules
    are allowed in left-hand side of rewrite rules (only) iff [~prt] is true.
    {!constructor:Term.expo.Privat} symbols are allowed iff [~prv]
    is [true]. *)
let find_sym : prt:bool -> prv:bool -> sig_state -> p_qident -> sym =
  fun ~prt ~prv st {elt = (mp, s); pos} ->
  let pp_uid = Parsing.LpLexer.pp_uid in
  let pp_path = Lplib.List.pp pp_uid "." in
  let s =
    match mp with
    | [] -> (* Symbol in scope. *)
        begin
          try fst (StrMap.find s st.in_scope)
          with Not_found -> fatal pos "Unknown object %a." pp_uid s
        end
    | [m] when StrMap.mem m st.alias_path -> (* Aliased module path. *)
        begin
          (* The signature must be loaded (alias is mapped). *)
          let sign =
            try Path.Map.find (StrMap.find m st.alias_path) !loaded
            with _ -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unknown symbol %a.%a." pp_path mp pp_uid s
        end
    | _  -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> st.signature.sign_path then
            if not (Path.Map.mem mp !(st.signature.sign_deps)) then
              fatal pos "No module [%a] required." pp_path mp;
          (* The signature must have been loaded. *)
          let sign =
            try Path.Map.find mp !loaded
            with Not_found -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unknown symbol %a.%a." pp_path mp pp_uid s
        end
  in
  match (prt, prv, s.sym_expo) with
  | (false, _    , Protec) ->
      if s.sym_path = st.signature.sign_path then s else
      (* Fail if symbol is not defined in the current module. *)
      fatal pos "Protected symbol not allowed here."
  | (_    , false, Privat) -> fatal pos "Private symbol not allowed here."
  | _                      -> s
