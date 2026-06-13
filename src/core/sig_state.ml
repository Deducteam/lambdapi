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

(** State of the signature, including aliasing and accessible symbols.
    the tc_solver is an option so that sig_states can be created before
    elpi is initialized. *)
type sig_state =
  { signature      : Sign.t                     (** Current signature. *)
  ; in_scope       : sym StrMap.t               (** Symbols in scope.  *)
  ; alias_path     : Path.t StrMap.t            (** Alias to path map. *)
  ; path_alias     : string Path.Map.t          (** Path to alias map. *)
  ; builtins       : sym StrMap.t                        (** Builtins. *)
  ; active_tc      : SymSet.t                            (** Active TC *)
  ; tc_solver_prog : Elpi.API.Compile.program option     (** TC solver *)
  ; add_tc_instance: sig_state -> popt -> sym ->
    Elpi.API.Compile.program -> Elpi.API.Compile.program (** Self-update   *)
  ; open_paths     : Path.Set.t                          (** Open modules. *)
}

type t = sig_state

(** [get_solver ss pos] accesses the current tc solver of [ss],
    failing if it was not yet initialized *)
let get_solver : sig_state -> popt -> Elpi.API.Compile.program = fun ss pos ->
  match ss.tc_solver_prog with Some p -> p
  | _ -> fatal pos "tc_solver was not initialized"

(** [add_tc ss sym pos] generates a new signature state from [ss]
    by adding [sym] as an active typeclass. *)
let add_tc : sig_state -> sym -> sig_state = fun ss sym ->
  Sign.add_tc ss.signature sym;
  {ss with active_tc = SymSet.add sym ss.active_tc}

  (** [add_tci ss sym pos] generates a new signature state from [ss]
    by compiling [sym] to an instance in its typeclass solver.
    Fails if the solver was not yet initialized or if the conclusion of
    [sym]'s type cannot be recognised as a typeclass *)
let add_tci : sig_state -> sym -> popt -> sig_state = fun ss sym pos ->
  Sign.add_tci ss.signature sym;
  let tc_solver = get_solver ss pos in
  {ss with tc_solver_prog = Some (ss.add_tc_instance ss pos sym tc_solver) }

(** [add_symbol ss expo prop mstrat opaq id pos typ impl def] generates a new
    signature state from [ss] by creating a new symbol with expo [e], property
    [p], strategy [st], name [x], type [a], implicit arguments [impl] and
    optional definition [def]. [pos] is the position of the declaration
    without its definition. This new symbol is returned too. *)
let add_symbol : sig_state -> expo -> prop -> match_strat
    -> bool -> strloc -> popt -> term -> bool list -> bool -> bool ->
    term option -> sig_state * sym =
  fun ss expo prop mstrat opaq id pos typ impl tc tci def ->
  let sym =
    Sign.add_symbol ss.signature expo prop mstrat opaq id pos typ impl in
  begin
    match def with
    | Some t when not opaq -> sym.sym_def := Some (cleanup t)
    | _ -> ()
  end;
  let ss = if tc then add_tc ss sym else ss in
  let ss = if tci then add_tci ss sym pos else ss in
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

(** [open_sign pos ss sign] extends the signature state [ss] with every
   symbol, typeclass and instance of the signature [sign]. This has the effect
   of putting these symbols in the scope, possibly masking symbols with
   the same name. *)
let open_sign : popt -> sig_state -> Sign.t -> sig_state = fun pos ss sign ->
  let f _key _v1 v2 = Some v2 in (* hides previous symbols *)
  let in_scope = StrMap.union f ss.in_scope !(sign.sign_symbols) in
  let open_paths = Path.Set.add sign.sign_path ss.open_paths in
  let active_tc = SymSet.union ss.active_tc !(sign.sign_tc) in
  let ss = {ss with active_tc} in
  let accumulate_all =
    List.fold_right (ss.add_tc_instance ss pos) !(sign.sign_tci)
  in
  let tc_solver_prog = Option.map accumulate_all ss.tc_solver_prog in
  {ss with in_scope; open_paths; tc_solver_prog}

(** [of_sign_and_solver sign solver add_instance] creates a new sig_state
    with tc-solver [solver], self-update function [add_instance], along with
    signature [sign] and open it and the ghost signature as well, assuming
    that [sign] has been created using [Sign.create].
*)
let of_sign_and_solver : Sign.t -> Elpi.API.Compile.program ->
  (t -> popt -> sym -> Elpi.API.Compile.program -> Elpi.API.Compile.program)
  -> sig_state = fun signature prog update ->
  let ss =
    { signature
    ; in_scope = StrMap.empty
    ; alias_path = StrMap.empty
    ; path_alias = Path.Map.empty
    ; builtins = StrMap.empty
    ; active_tc = SymSet.empty
    ; tc_solver_prog = Some prog
    ; add_tc_instance = update
    ; open_paths = Path.Set.empty }
  in
  open_sign None (open_sign None ss Ghost.sign) signature

(** [of_sign sign] creates a new sig_state with signature [sign] and open it
    and the ghost signature as well, assuming that [sign] has been created
    using [Sign.create]. *)
let of_sign : Sign.t -> sig_state = fun signature ->
  let ss =
    { signature
    ; in_scope = StrMap.empty
    ; alias_path = StrMap.empty
    ; path_alias = Path.Map.empty
    ; builtins = StrMap.empty
    ; active_tc = SymSet.empty
    ; tc_solver_prog = None
    ; add_tc_instance = (fun _ pos _ _ -> Common.Error.fatal pos
        "cannot add instance, tc solver was not initialized")
    ; open_paths = Path.Set.empty }
  in
  open_sign None (open_sign None ss Ghost.sign) signature

(** [of_sign_and_solver sign solver add_instance] creates a new sig_state
    with tc-solver [solver] and self-update function [add_instance].
*)
let of_solver : Elpi.API.Compile.program -> (t -> popt -> sym ->
  Elpi.API.Compile.program -> Elpi.API.Compile.program) -> sig_state =
  of_sign_and_solver (Sign.create [])

(** Dummy [sig_state]. *)
let dummy : sig_state = of_sign (Sign.create [])

(** [find_sym] is the type of functions used to return the symbol
    corresponding to a qualified / non qualified name *)
type find_sym = prt:bool -> prv:bool -> sig_state -> qident loc -> sym

(** [find_sym ~prt ~prv b ss qid] returns the symbol corresponding to the
    possibly qualified identifier [qid], or raises [Fatal]. The boolean [b]
    indicates if the error message should mention variables when [qid] is
    unqualified. [~prt] indicates whether [Term.expo.Protec]
    symbols from other modules are allowed. [~prv] indicates whether
    [Term.expo.Privat] symbols are allowed. *)
let find_sym : find_sym = fun ~prt ~prv ss {elt=(mp,s); pos} ->
  let s =
    match mp with
    | [] -> (* Symbol in scope. *)
        begin
          try StrMap.find s ss.in_scope
          with Not_found -> fatal pos "Unknown symbol %s." s
        end
    | [m] when StrMap.mem m ss.alias_path -> (* Aliased module path. *)
        begin
          (* The signature must be loaded (alias is mapped). *)
          let sign =
            try Path.Map.find (StrMap.find m ss.alias_path) !loaded
            with _ -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s
          with Not_found -> fatal pos "Unknown symbol %a.%s." Path.pp mp s
        end
    | _  -> (* Fully-qualified symbol. *)
        begin
          (* Check that the signature was required (or is the current one). *)
          if mp <> ss.signature.sign_path
             && not (Path.Map.mem mp !(ss.signature.sign_deps))
          then fatal pos "No module %a required." Path.pp mp;
          (* The signature must have been loaded. *)
          let sign =
            try Path.Map.find mp !loaded
            with Not_found -> assert false (* Should not happen. *)
          in
          (* Look for the symbol. *)
          try Sign.find sign s
          with Not_found -> fatal pos "Unknown symbol %a.%s." Path.pp mp s
        end
  in
  match (prt, prv, s.sym_expo) with
  | (false, _    , Protec) ->
      if s.sym_path = ss.signature.sign_path then s else
      (* Fail if symbol is not defined in the current module. *)
      fatal pos "Protected symbol not allowed here."
  | (_    , false, Privat) -> fatal pos "Private symbol not allowed here."
  | _                      -> s
