(** Signature state. *)

open Timed
open Console
open Extra
open Files
open Pos
open Syntax
open Terms

(** Pretty-printing information associated to a symbol. *)
type pp_hint =
  | No_hint
  | Prefix of unop
  | Infix of binop

(** State of the signature, including aliasing and accessible symbols. *)
type sig_state =
  { signature : Sign.t                    (** Current signature.   *)
  ; in_scope  : (sym * Pos.popt) StrMap.t (** Symbols in scope.    *)
  ; aliases   : Path.t StrMap.t           (** Established aliases. *)
  ; builtins  : Sign.builtin_map          (** Builtin symbols.     *)
  ; pp_hints  : pp_hint SymMap.t          (** Printing hints.      *) }

type t = sig_state

(** Symbols and signature used for unification rules. *)
module Unif_rule =
  struct

    (** Path of the module. *)
    let path = Path.ghost "unif_rule"

    (** Ghost signature holding the symbols used in unification rules. This
        signature is an automatic dependency of all other signatures, and is
        automatically loaded. *)
    let sign : Sign.t =
      let open Sign in
      let s =
        { sign_path = path; sign_symbols = ref StrMap.empty
        ; sign_deps = ref (PathMap.empty)
        ; sign_builtins = ref StrMap.empty; sign_unops = ref StrMap.empty
        ; sign_binops = ref StrMap.empty; sign_idents = ref StrSet.empty }
      in
      Sign.loaded := Files.PathMap.add path s !(Sign.loaded);
      s

    (** Symbol representing an atomic unification problem. The term [equiv t
        u] represents [t ≡ u]. The left-hand side of a unification rule is
        made of only one unification. *)
    let equiv : sym =
      Sign.add_symbol sign Public Defin (Pos.none "#equiv") Kind []

    (** Holds a list of equivalences. The right-hand side of a unification
        rule is made of such a list, [list (equiv t u) (equiv v w) ...]. *)
    let comma : sym =
      Sign.add_symbol sign Public Defin (Pos.none "#comma") Kind []

    (** Pretty printing hints for symbols [equiv] and [comma]. *)
    let pp_hints : pp_hint SymMap.t =
      let open Stdlib in
      let pth = List.map (fun s -> (s, false)) path in
      let h = Infix("≡", Assoc_none, 1.1, Pos.none (pth, "#equiv")) in
      let res = SymMap.singleton equiv h in
      let h = Infix(",", Assoc_right, 1.0, Pos.none(pth, "#comma")) in
      SymMap.add comma h res

    (** [unpack eqs] transforms a term of the form [t =? u, v =? w, ...]
        into a list [[t =? u; v =? w; ...]]. *)
    let rec unpack : term -> (term * term) list = fun eqs ->
      match Basics.get_args eqs with
      | (Symb(s), [v; w]) ->
          if s == comma then
            match Basics.get_args v with
            | (Symb(e), [t; u]) when e == equiv -> (t, u) :: unpack w
            | _          (* Ill-formed term. *) -> assert false
          else if s == equiv then [(v, w)] else
          assert false (* Ill-formed term. *)
      | _                 -> assert false (* Ill-formed term. *)
end

(** [create_sign path] creates a signature with pervasive modules as
    dependencies. *)
let create_sign : Path.t -> Sign.t = fun sign_path ->
  { sign_path; sign_symbols = ref StrMap.empty
  ; sign_deps = ref (PathMap.singleton Unif_rule.path [])
  ; sign_builtins = ref StrMap.empty; sign_unops = ref StrMap.empty
  ; sign_binops = ref StrMap.empty; sign_idents = ref StrSet.empty }

(** [remove_pp_hint ss s hints] removes from [hints] the mapping for [s] if
   [s.sym_name] is mapped in [ss.in_scope]. *)
let remove_pp_hint :
      sig_state -> sym -> pp_hint SymMap.t -> pp_hint SymMap.t =
  fun ss s pp_hints ->
  if StrMap.mem s.sym_name ss.in_scope then SymMap.remove s pp_hints
  else pp_hints

(** [build_pp_hints ss] computes pp_hints from a signature [sign]. *)
let update_pp_hints : sig_state -> Sign.t -> pp_hint SymMap.t = fun ss sign ->
  let fn _ (sym,_) pp_hints =
    let h =
      let exception Hint of pp_hint in
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
    SymMap.add sym h (remove_pp_hint ss sym pp_hints)
  in
  StrMap.fold fn !(sign.sign_symbols) ss.pp_hints

(** [open_sign ss sign] extends the signature state [ss] with every symbol  of
    the signature [sign].  This has the effect of putting these symbols in the
    scope when (possibly masking symbols with the same name).  Builtin symbols
    are also handled in a similar way. *)
let open_sign : sig_state -> Sign.t -> sig_state = fun ss sign ->
  let f _key _v1 v2 = Some(v2) in (* open signature hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope Sign.(!(sign.sign_symbols)) in
  let builtins = StrMap.union f ss.builtins Sign.(!(sign.sign_builtins)) in
  let pp_hints = update_pp_hints ss sign in
  {ss with in_scope; builtins; pp_hints}

(** [of_sign sign] creates a state from the signature [sign] with ghost
    signatures opened. *)
let of_sign : Sign.t -> sig_state = fun sign ->
  let empty =
    { signature = sign
    ; in_scope  = StrMap.empty
    ; aliases   = StrMap.empty
    ; builtins  = StrMap.empty
    ; pp_hints  = SymMap.empty }
  in
  open_sign empty Unif_rule.sign

(** [empty] state. *)
let empty : sig_state = of_sign (create_sign [])

(** [add_symbol ss e p x a impl] adds a symbol in [ss]. *)
let add_symbol
    : sig_state -> expo -> prop -> strloc -> term -> bool list
      -> term option -> sig_state =
  fun ss e p x a impl t ->
  let s = Sign.add_symbol ss.signature e p x a impl in
  begin
    match t with
    | Some t -> s.sym_def := Some(t)
    | None -> ()
  end;
  let pp_hints = remove_pp_hint ss s ss.pp_hints in
  let pp_hints = SymMap.add s No_hint pp_hints in
  let in_scope = StrMap.add x.elt (s, x.pos) ss.in_scope in
  {ss with in_scope; pp_hints}

(** [add_unop ss n (s,unop)] declares [n] as prefix and maps it to [s]. *)
let add_unop : sig_state -> string -> (sym * unop) -> sig_state =
  fun ss n (sym, unop) ->
  Sign.add_unop ss.signature n (sym, unop);
  let pp_hints = remove_pp_hint ss sym ss.pp_hints in
  let pp_hints = SymMap.add sym (Prefix unop) pp_hints in
  {ss with pp_hints}

(** [add_binop ss n (s,binop)] declares [n] as infix and maps it to [s]. *)
let add_binop : sig_state -> string -> (sym * binop) -> sig_state =
  fun ss n (sym, binop) ->
  Sign.add_binop ss.signature n (sym, binop);
  let pp_hints = remove_pp_hint ss sym ss.pp_hints in
  let pp_hints = SymMap.add sym (Infix binop) pp_hints in
  {ss with pp_hints}

(** [add_builtin ss n s] adds builtin [n] and maps it to [s]. *)
let add_builtin : sig_state -> string -> sym -> sig_state = fun ss s sym ->
  Sign.add_builtin ss.signature s sym;
  let builtins = StrMap.add s sym ss.builtins in
  {ss with builtins}

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
