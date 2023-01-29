(** Signature state.

   This module provides a record type [sig_state] containing all the
   informations needed for scoping p_terms and printing terms, and functions
   on this type for manipulating it. In particular, it provides functions
   [open_sign], [add_symbol], [add_binop], etc. taking a [sig_state] as
   argument and returning a new [sig_state] as result. These functions call
   the corresponding functions of [Sign] which should not be called directly
   but through the current module only, in order to setup the [sig_state]
   properly. *)

open Lplib open Extra
open Common open Error open Pos
open Timed
open Term
open Sign

(** [create_sign path] creates a signature with path [path] with ghost modules
    as dependencies. *)
let create_sign : Path.t -> Sign.t = fun sign_path ->
  let d = Sign.dummy () in
  let deps = Path.Map.singleton Ghost.sign.sign_path StrMap.empty in
  {d with sign_path; sign_deps = ref deps}

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { signature : Sign.t                    (** Current signature. *)
  ; in_scope  : sym StrMap.t              (** Symbols in scope.  *)
  ; alias_path: Path.t StrMap.t           (** Alias to path map. *)
  ; path_alias: string Path.Map.t         (** Path to alias map. *)
  ; builtins  : sym StrMap.t              (** Builtins. *)
  ; notations : float notation SymMap.t   (** Notations. *)
  ; open_paths : Path.Set.t               (** Open modules. *) }

type t = sig_state

(** Dummy [sig_state]. *)
let dummy : sig_state =
  { signature = Sign.dummy (); in_scope = StrMap.empty;
    alias_path = StrMap.empty; path_alias = Path.Map.empty;
    builtins = StrMap.empty; notations = SymMap.empty;
    open_paths = Path.Set.empty }

(** [add_symbol ss expo prop mstrat opaq id typ impl def] generates a new
   signature state from [ss] by creating a new symbol with expo [e], property
   [p], strategy [st], name [x], type [a], implicit arguments [impl] and
   optional definition [def]. This new symbol is returned too. *)
let add_symbol : sig_state -> expo -> prop -> match_strat
    -> bool -> strloc -> term -> bool list -> term option -> sig_state * sym =
  fun ss expo prop mstrat opaq id typ impl def ->
  let sym =
    Sign.add_symbol ss.signature expo prop mstrat opaq id
      (cleanup typ) impl in
  begin
    match def with
    | Some t when not opaq -> sym.sym_def := Some (cleanup t)
    | _ -> ()
  end;
  let in_scope = StrMap.add id.elt sym ss.in_scope in
  {ss with in_scope}, sym

(** [add_notation ss s n] maps [s] notation to [n] in [ss]. *)
let add_notation : sig_state -> sym -> float notation -> sig_state =
  fun ss s n ->
  if s.sym_path = ss.signature.sign_path then
    Sign.add_notation ss.signature s n;
  {ss with notations = SymMap.update s (Sign.update_notation n) ss.notations}

(** [add_builtin ss n s] generates a new signature state from [ss] by mapping
   the builtin [n] to [s]. *)
let add_builtin : sig_state -> string -> sym -> sig_state =
  fun ss builtin sym ->
  Sign.add_builtin ss.signature builtin sym;
  let builtins = StrMap.add builtin sym ss.builtins in
  let notations = Sign.add_notation_from_builtin builtin sym ss.notations in
  {ss with builtins; notations}

(** [open_sign ss sign] extends the signature state [ss] with every symbol of
   the signature [sign]. This has the effect of putting these symbols in the
   scope when (possibly masking symbols with the same name). Builtins and
   notations are also handled in a similar way. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _key _v1 v2 = Some(v2) in (* hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope !(sign.sign_symbols) in
  let builtins = StrMap.union f ss.builtins !(sign.sign_builtins) in
  let notations = SymMap.union f ss.notations !(sign.sign_notations) in
  let open_paths = Path.Set.add sign.sign_path ss.open_paths in
  {ss with in_scope; builtins; notations; open_paths}

(** [of_sign sign] creates a state from the signature [sign] and open it as
   well as the ghost signatures. *)
let of_sign : Sign.t -> sig_state = fun signature ->
  open_sign (open_sign {dummy with signature} Ghost.sign) signature

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
let find_sym : prt:bool -> prv:bool -> sig_state -> qident loc -> sym =
  fun ~prt ~prv st {elt = (mp, s); pos} ->
  let s =
    match mp with
    | [] -> (* Symbol in scope. *)
        begin
          try StrMap.find s st.in_scope
          with Not_found -> fatal pos "Unknown object %s." s
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
          fatal pos "Unknown symbol %a.%s." Path.pp mp s
        end
    | _  -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> st.signature.sign_path then
            if not (Path.Map.mem mp !(st.signature.sign_deps)) then
              fatal pos "No module [%a] required." Path.pp mp;
          (* The signature must have been loaded. *)
          let sign =
            try Path.Map.find mp !loaded
            with Not_found -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unknown symbol %a.%s." Path.pp mp s
        end
  in
  match (prt, prv, s.sym_expo) with
  | (false, _    , Protec) ->
      if s.sym_path = st.signature.sign_path then s else
      (* Fail if symbol is not defined in the current module. *)
      fatal pos "Protected symbol not allowed here."
  | (_    , false, Privat) -> fatal pos "Private symbol not allowed here."
  | _                      -> s
