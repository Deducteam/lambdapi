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

(** [create_sign path] creates a signature with path [path] and the ghost
    module as dependency. *)
let create_sign : Path.t -> Sign.t = fun sign_path ->
  let sign = Sign.dummy() in
  let dep = {dep_symbols = StrMap.empty; dep_open=true} in
  let deps = Path.Map.singleton Sign.Ghost.path dep in
  {sign with sign_path; sign_deps = ref deps}

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { signature : Sign.t                    (** Current signature. *)
  ; in_scope  : sym StrMap.t              (** Symbols in scope.  *)
  ; alias_path: Path.t StrMap.t           (** Alias to path map. *)
  ; path_alias: string Path.Map.t         (** Path to alias map. *)
  ; builtins  : sym StrMap.t              (** Builtins. *)
  ; open_paths : Path.Set.t               (** Open modules. *) }

type t = sig_state

(** Dummy [sig_state]. *)
let dummy : sig_state =
  { signature = Sign.dummy (); in_scope = StrMap.empty;
    alias_path = StrMap.empty; path_alias = Path.Map.empty;
    builtins = StrMap.empty; open_paths = Path.Set.empty }

(** [add_symbol ss expo prop mstrat opaq id pos typ impl def] generates a new
    signature state from [ss] by creating a new symbol with expo [e], property
    [p], strategy [st], name [x], type [a], implicit arguments [impl] and
    optional definition [def]. [pos] is the position of the declaration
    without its definition. This new symbol is returned too. *)
let add_symbol : sig_state -> expo -> prop -> match_strat
    -> bool -> strloc -> popt -> term -> bool list -> term option ->
    sig_state * sym =
  fun ss expo prop mstrat opaq id pos typ impl def ->
  let sym =
    Sign.add_symbol ss.signature expo prop mstrat opaq id pos typ impl in
  begin
    match def with
    | Some t when not opaq -> sym.sym_def := Some (cleanup t)
    | _ -> ()
  end;
  let in_scope = StrMap.add id.elt sym ss.in_scope in
  {ss with in_scope}, sym

(** [add_builtin ss b s] generates a new signature state from [ss] by mapping
    the builtin string [b] to the symbol [s], and by updating the notation of
    [s] when [b] is a builtin used for printing. *)
let add_builtin : sig_state -> string -> sym -> sig_state =
  fun ss b s ->
  (* Update the notation of [s] if [b] is a builtin used for printing. *)
  let n =
    match b with
    | "nat_zero"  -> Zero
    | "nat_succ" -> Succ !(s.sym_nota)
    | "pos_one"  -> PosOne
    | "pos_double"  -> PosDouble
    | "pos_succ_double"  -> PosSuccDouble
    | "int_zero"  -> IntZero
    | "int_positive"  -> IntPos
    | "int_negative"  -> IntNeg
    | _ -> NoNotation
  in
  begin
    match n with
    | NoNotation -> ()
    | _ -> s.sym_nota := n
  end;
  (* Update the builtins of the current signature. *)
  Sign.add_builtin ss.signature b s;
  (* Update the builtins of the sig_state. *)
  let builtins = StrMap.add b s ss.builtins in
  {ss with builtins}

(** [open_sign ss sign] extends the signature state [ss] with every symbol of
   the signature [sign]. This has the effect of putting these symbols in the
   scope, possibly masking symbols with the same name. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _key _v1 v2 = Some v2 in (* hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope !(sign.sign_symbols) in
  let open_paths = Path.Set.add sign.sign_path ss.open_paths in
  {ss with in_scope; open_paths}

(** [of_sign sign] creates a state from the signature [sign] and open it as
   well as the ghost signature. *)
let of_sign : Sign.t -> sig_state = fun signature ->
  open_sign (open_sign {dummy with signature} Ghost.sign) signature

(** [find_sym] is the type of functions used to return the symbol
    corresponding to a qualified / non qualified name *)
type find_sym = prt:bool -> prv:bool -> sig_state -> qident loc -> sym

(** [find_sym ~prt ~prv b ss qid] returns the symbol corresponding to the
    possibly qualified identifier [qid], or raises [Fatal]. The boolean [b]
    indicates if the error message should mention variables when [qid] is
    unqualified. [~prt] indicates whether {!constructor:Term.expo.Protec}
    symbols from other modules are allowed. [~prv] indicates whether
    {!constructor:Term.expo.Privat} symbols are allowed. *)
let find_sym : find_sym = fun ~prt ~prv ss {elt=(mp,s); pos} ->
  let s =
    match mp with
    | [] -> (* Symbol in scope. *)
        begin
          try StrMap.find s ss.in_scope
          with Not_found -> fatal pos "Unknown object %s." s
        end
    | [m] when StrMap.mem m ss.alias_path -> (* Aliased module path. *)
        begin
          (* The signature must be loaded (alias is mapped). *)
          let sign =
            try Path.Map.find (StrMap.find m ss.alias_path) !loaded
            with _ -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s with Not_found ->
          fatal pos "Unknown symbol %a.%s." Path.pp mp s
        end
    | _  -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> ss.signature.sign_path then
            if not (Path.Map.mem mp !(ss.signature.sign_deps)) then
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
      if s.sym_path = ss.signature.sign_path then s else
      (* Fail if symbol is not defined in the current module. *)
      fatal pos "Protected symbol not allowed here."
  | (_    , false, Privat) -> fatal pos "Private symbol not allowed here."
  | _                      -> s
