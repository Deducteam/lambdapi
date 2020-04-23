(** Signature state. *)

open Timed
open Console
open Extra
open Files
open Pos
open Syntax
open Terms

(** Pretty-printing information associated to a symbol. *)
type hint =
  | No_hint
  | Prefix of unop
  | Infix of binop

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { signature : Sign.t                    (** Current signature.   *)
  ; in_scope  : (sym * Pos.popt) StrMap.t (** Symbols in scope.    *)
  ; aliases   : Path.t StrMap.t           (** Established aliases. *)
  ; builtins  : Sign.builtin_map          (** Builtin symbols.     *)
  ; hints     : hint SymMap.t             (** Printing hints.      *) }

type t = sig_state

(** [init_with sign] creates a state from the signature [sign] with no symbols
   in scope, module aliases, builtins or printing hints. *)
let of_sign : Sign.t -> sig_state = fun sign ->
  { signature = sign
  ; in_scope  = StrMap.empty
  ; aliases   = StrMap.empty
  ; builtins  = StrMap.empty
  ; hints     = SymMap.empty }

(** [empty] state. *)
let empty = of_sign (Sign.create [])

(** Interface for registering and checking builtin symbols. *)
module Builtin :
  sig
    (** [get pos map name] returns the symbol mapped to the “builtin symbol”
       named [name] i n the map [map], which should contain all the builtin
       symbols that are in scope. If the symbol cannot be found then [Fatal]
       is raised. *)
    val get : sig_state -> popt -> string -> sym

    (** [check ss pos name sym] runs the registered check for builtin symbol
       [name] on the symbol [sym] (if such a check has been registered). Note
       that the [bmap] argument is expected to contain the builtin symbols in
       scope, and the [pos] argument is used for error reporting. *)
    val check : sig_state -> popt -> string -> sym -> unit

    (** [register name check] registers the checking function [check], for the
       builtin symbols named [name]. When the check is run, [check] receives
       as argument a position for error reporting as well as the map of every
       builtin symbol in scope. It is expected to raise the [Fatal] exception
       to signal an error. Note that this function should not be called using
       a [name] for which a check has already been registered. *)
    val register : string -> (sig_state -> popt -> sym -> unit) -> unit

    (** [register_expected_type name build pp] registers a checking function
       that checks the type of a symbol defining the builtin [name] against a
       type constructed using the given [build] function. *)
    val register_expected_type
        : term eq -> term pp -> string -> (sig_state -> popt -> term) -> unit
  end =
  struct
    let get ss pos name =
      try StrMap.find name ss.builtins with Not_found ->
        fatal pos "Builtin symbol \"%s\" undefined." name

    (** Hash-table used to record checking functions for builtins. *)
    let htbl : (string, sig_state -> popt -> sym -> unit) Hashtbl.t
      = Hashtbl.create 17

    let check ss pos name sym =
      try (Hashtbl.find htbl name) ss pos sym with Not_found -> ()

    let register name check =
      if Hashtbl.mem htbl name then assert false;
      Hashtbl.add htbl name check

    let register_expected_type eq pp name fn =
      let check ss pos sym =
        let expected = fn ss pos in
        if not (eq !(sym.sym_type) expected) then
          fatal pos "The type of %s is not of the form %a."
            sym.sym_name pp expected
      in
      register name check
  end

(** [remove_hint ss s hints] removes from [hints] the mapping for [s] if
   [s.sym_name] is mapped in [ss.in_scope]. *)
let remove_hint : sig_state -> sym -> hint SymMap.t -> hint SymMap.t
  = fun ss s hints ->
  if StrMap.mem s.sym_name ss.in_scope then SymMap.remove s hints
  else hints

(** [add_symbol ss e p x a impl] adds a symbol in [ss]. *)
let add_symbol
    : sig_state -> expo -> prop -> strloc -> term -> bool list
      -> term option -> sig_state
  = fun ss e p x a impl t ->
  let s = Sign.add_symbol ss.signature e p x a impl in
  begin
    match t with
    | Some t -> s.sym_def := Some(t)
    | None -> ()
  end;
  let hints = SymMap.add s No_hint (remove_hint ss s ss.hints) in
  let in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope in
  {ss with in_scope; hints}

(** [add_unop ss n (s,unop)] declares [n] as prefix and maps it to [s]. *)
let add_unop : sig_state -> string -> (sym * unop) -> sig_state
  = fun ss n (sym, unop) ->
  Sign.add_unop ss.signature n (sym, unop);
  let hints = SymMap.add sym (Prefix unop) (remove_hint ss sym ss.hints) in
  {ss with hints}

(** [add_binop ss n (s,binop)] declares [n] as infix and maps it to [s]. *)
let add_binop : sig_state -> string -> (sym * binop) -> sig_state
  = fun ss n (sym, binop) ->
  Sign.add_binop ss.signature n (sym, binop);
  let hints = SymMap.add sym (Infix binop) (remove_hint ss sym ss.hints) in
  {ss with hints}

(** [add_builtin ss n s] adds builtin [n] and maps it to [s]. *)
let add_builtin : sig_state -> string -> sym -> sig_state = fun ss s sym ->
  Sign.add_builtin ss.signature s sym;
  let builtins = StrMap.add s sym ss.builtins in
  {ss with builtins}

(** [build_hints ss] computes hints from a signature [sign]. *)
let update_hints : sig_state -> Sign.t -> hint SymMap.t = fun ss sign ->
  let fn _ (sym,_) hints =
    let h =
      let exception Hint of hint in
      try
        let fn_binop _ (s,binop) =
          if s == sym then raise (Hint (Infix binop)) in
        StrMap.iter fn_binop !(sign.sign_binops);
        let fn_unop _ (s,unop) =
          if s == sym then raise (Hint (Prefix unop)) in
        StrMap.iter fn_unop !(sign.sign_unops);
        No_hint
      with Hint h -> h
    in
    (* Remove from hints the symbols having a name occurring in the opened
       signature as it gets hidden. *)
    SymMap.add sym h (remove_hint ss sym hints)
  in
  StrMap.fold fn !(sign.sign_symbols) ss.hints

(** [open_sign ss sign] extends the signature state [ss] with every symbol  of
    the signature [sign].  This has the effect of putting these symbols in the
    scope when (possibly masking symbols with the same name).  Builtin symbols
    are also handled in a similar way. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _key _v1 v2 = Some(v2) in (* open signature hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope Sign.(!(sign.sign_symbols)) in
  let builtins = StrMap.union f ss.builtins Sign.(!(sign.sign_builtins)) in
  let hints = update_hints ss sign in
  {ss with in_scope; builtins; hints}

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
let find_sym : prt:bool -> prv:bool -> bool -> sig_state -> qident -> sym
  = fun ~prt ~prv b st qid ->
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
  begin
    match (prt, prv, s.sym_expo) with
    | (false, _    , Protec) ->
        if s.sym_path <> st.signature.sign_path then
          (* Fail if symbol is not defined in the current module. *)
          fatal pos "Protected symbol not allowed here."
    | (_    , false, Privat) ->
        fatal pos "Private symbol not allowed here."
    | _                      -> ()
  end;
  s
