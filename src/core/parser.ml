(** Parsing functions for the Lambdapi syntax based on the Earley library. See
    https://github.com/rlepigre/ocaml-earley/blob/master/README.md for details
    on using the library and its syntax extension. *)

open Earley_core
open Extra
open Syntax
open Files
open Pos

(** {b NOTE} we maintain the invariant that errors reported by the parser have
    a position. To help enforce that, we avoid opening the [Console] module so
    that [Console.fatal] and [Console.fatal_no_pos] are not in scope. To raise
    an error in the parser, only the following function should be used. *)

(** [parser_fatal loc fmt] is a wrapper for [Console.fatal] that enforces that
    the error has an attached source code position. *)
let parser_fatal : Pos.pos -> ('a,'b) Console.koutfmt -> 'a = fun loc fmt ->
  Console.fatal (Some(loc)) fmt

#define LOCATE locate

(** Prefix trees for greedy parsing among a set of string. *)
module Prefix :
  sig
    (** Type of a prefix tree. *)
    type 'a t

    (** [init ()] initializes a new (empty) prefix tree. *)
    val init : unit -> 'a t

    (** [reset t] resets [t] to an empty prefix tree [t]. *)
    val reset : 'a t -> unit

    (** [add k v t] inserts the value [v] with the key [k] (possibly replacing
        a previous value associated to [k]) in the tree [t]. Note that key [k]
        should not be [""], otherwise [Invalid_argument] is raised. *)
    val add : 'a t -> string -> 'a -> unit

    (** [grammar t] is an [Earley] grammar parsing the longest possible prefix
        of the input corresponding to a word of [t]. The corresponding, stored
        value is returned. It fails if no such longest prefix exist. *)
    val grammar : 'a t -> 'a Earley.grammar

    (** Type of a saved prefix tree. Prefix trees are imperative, so they need
        to be manually saved and restored to enforce reentrancy. Note that the
        parser may call itself through dependency loading *)
    type 'a saved

    (** [save t] returns a snapshot of the internal state of [t]. *)
    val save : 'a t -> 'a saved

    (** [restore t s] restores the internal state of [t] as it was at the time
        of calling [save]. *)
    val restore : 'a t -> 'a saved -> unit
  end =
  struct
    type 'a tree = Node of 'a option * (char * 'a tree) list
    type 'a t = 'a tree Stdlib.ref

    let init : unit -> 'a t = fun _ -> ref (Node(None, []))

    let reset : 'a t -> unit = fun t -> t := Node(None, [])

    let add : 'a t -> string -> 'a -> unit = fun t k v ->
      if k = "" then invalid_arg "Prefix.add";
      let rec add i (Node(vo,l)) =
        match try Some(k.[i]) with _ -> None with
        | None    -> Node(Some(v), l)
        | Some(c) ->
            let l =
              try
                let t = List.assoc c l in
                (c, add (i+1) t) :: (List.remove_assoc c l)
              with Not_found -> (c, add (i+1) (Node(None, []))) :: l
            in
            Node(vo, l)
      in
      t := add 0 !t

    let grammar : 'a t -> 'a Earley.grammar = fun t ->
      let fn buf pos =
        let rec fn best (Node(vo,l)) buf pos =
          let best =
            match vo with
            | None    -> best
            | Some(v) -> Some(v,buf,pos)
          in
          try
            let (c, buf, pos) = Input.read buf pos in
            fn best (List.assoc c l) buf pos
          with Not_found ->
            match best with
            | None       -> Earley.give_up ()
            | Some(best) -> best
        in fn None !t buf pos
      in
      Earley.black_box fn Charset.full false "<tree>"

    type 'a saved = 'a tree

    let save : 'a t -> 'a saved = Stdlib.(!)

    let restore : 'a t -> 'a saved -> unit = Stdlib.(:=)
  end

(** Currently defined unary operators. *)
let unops : unop Prefix.t = Prefix.init ()

(** Parser for a unary operator. *)
let unop = Prefix.grammar unops

(** Currently defined binary operators. *)
let binops : binop Prefix.t = Prefix.init ()

(** Parser for a binary operator. *)
let binop = Prefix.grammar binops

(** Currently defined identifiers. *)
let declared_ids : string Prefix.t = Prefix.init ()

(** Parser for a declared identifier. *)
let declared_id = Prefix.grammar declared_ids

(** The following should not appear as substrings of binary operators, as they
    would introduce ambiguity in the parsing. *)
let forbidden_in_ops =
  [ "("; ")"; "."; "λ"; "Π"; "$"; "["; "]"; "{"; "}"; "?"; ":"; "↪"; "⊢"
  ; "→"; "@"; ","; ";"; "\""; "\'"; "≔"; "//"; " "; "\r"; "\n"; "\t"; "\b" ]
  @ List.init 10 string_of_int

(** [get_ops loc p] loads the unary and binary operators associated to  module
    [p] and report possible errors at location [loc].  This operation requires
    the module [p] to be loaded (i.e., compiled). The declared identifiers are
    also retrieved at the same time. *)
let get_ops : Pos.pos -> p_module_path -> unit = fun loc p ->
  let p = List.map fst p in
  let sign =
    try PathMap.find p Timed.(!(Sign.loaded)) with Not_found ->
      parser_fatal loc "Module [%a] not loaded (used for binops)." Path.pp p
  in
  let fn s (_, unop) = Prefix.add unops s unop in
  StrMap.iter fn Timed.(!Sign.(sign.sign_unops));
  let fn s (_, binop) = Prefix.add binops s binop in
  StrMap.iter fn Timed.(!Sign.(sign.sign_binops));
  let fn s = Prefix.add declared_ids s s in
  StrSet.iter fn Timed.(!Sign.(sign.sign_idents))

(** Blank function (for comments and white spaces). *)
let blank = Blanks.line_comments "//"

(** Set of identifier characters. *)
let id_charset = Charset.from_string "a-zA-Z0-9_'"

(** Keyword module. *)
module KW = Keywords.Make(
  struct
    let id_charset = id_charset
    let reserved = []
  end)

(** Reserve ["KIND"] to disallow it as an identifier. *)
let _ = KW.reserve "KIND"

(** Keyword declarations. Keep alphabetical order. *)
let _abort_      = KW.create "abort"
let _admit_      = KW.create "admit"
let _apply_      = KW.create "apply"
let _as_         = KW.create "as"
let _assert_     = KW.create "assert"
let _assertnot_  = KW.create "assertnot"
let _compute_    = KW.create "compute"
let _constant_   = KW.create "constant"
let _definition_ = KW.create "definition"
let _focus_      = KW.create "focus"
let _in_         = KW.create "in"
let _injective_  = KW.create "injective"
let _intro_      = KW.create "assume"
let _let_        = KW.create "let"
let _open_       = KW.create "open"
let _print_      = KW.create "print"
let _private_    = KW.create "private"
let _proof_      = KW.create "proof"
let _proofterm_  = KW.create "proofterm"
let _protected_  = KW.create "protected"
let _qed_        = KW.create "qed"
let _refine_     = KW.create "refine"
let _refl_       = KW.create "reflexivity"
let _require_    = KW.create "require"
let _rewrite_    = KW.create "rewrite"
let _rule_       = KW.create "rule"
let _set_        = KW.create "set"
let _simpl_      = KW.create "simpl"
let _sym_        = KW.create "symmetry"
let _symbol_     = KW.create "symbol"
let _theorem_    = KW.create "theorem"
let _type_       = KW.create "type"
let _TYPE_       = KW.create "TYPE"
let _why3_       = KW.create "why3"
let _wild_       = KW.create "_"
let _with_       = KW.create "with"

(** [sanity_check pos s] checks that the token [s] is appropriate for an infix
    operator or a declared identifier. If it is not the case, then the [Fatal]
    exception is raised. *)
let sanity_check : Pos.pos -> string -> unit = fun loc s ->
  (* Of course, the empty string and keywords are forbidden. *)
  if s = "" then parser_fatal loc "Invalid token (empty).";
  if KW.mem s then parser_fatal loc "Invalid token (reserved).";
  (* We forbid valid (non-escaped) identifiers. *)
  if String.for_all (Charset.mem id_charset) s then
    parser_fatal loc "Invalid token (only identifier characters).";
  (* We also reject symbols with certain substrings. *)
  let check_substring w =
    if String.is_substring w s then
      parser_fatal loc "Invalid token (has [%s] as a substring)." w
  in
  List.iter check_substring forbidden_in_ops

(** Natural number literal. *)
let nat_lit =
  let num_cs = Charset.from_string "0-9" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem num_cs (Input.get buf (pos + !nb)) do incr nb done;
    (int_of_string (String.sub (Input.line buf) pos !nb), buf, pos + !nb)
  in
  Earley.black_box fn num_cs false "<nat>"

(** Floating-point number literal. *)
let float_lit =
  let num_cs = Charset.from_string "0-9" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem num_cs (Input.get buf (pos + !nb)) do incr nb done;
    if Input.get buf (pos + !nb) = '.' then
      begin
        incr nb;
        while Charset.mem num_cs (Input.get buf (pos + !nb)) do incr nb done;
      end;
    (float_of_string (String.sub (Input.line buf) pos !nb), buf, pos + !nb)
  in
  Earley.black_box fn num_cs false "<float>"

(** String literal. *)
let string_lit =
  let body_cs = List.fold_left Charset.del Charset.full ['"'; '\n'] in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem body_cs (Input.get buf (pos + !nb)) do incr nb done;
    if Input.get buf (pos + !nb) <> '"' then Earley.give_up ();
    (String.sub (Input.line buf) (pos+1) (!nb-1), buf, pos + !nb + 1)
  in
  Earley.black_box fn (Charset.singleton '"') false "<string>"

(** Sequence of alphabetical characters. *)
let alpha =
  let alpha = Charset.from_string "a-zA-Z" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem alpha (Input.get buf (pos + !nb)) do incr nb done;
    (String.sub (Input.line buf) pos !nb, buf, pos + !nb)
  in
  Earley.black_box fn alpha false "<alpha>"

(** Regular identifier (regexp ["[a-zA-Z_][a-zA-Z0-9_']*"]). *)
let regular_ident =
  let head_cs = Charset.from_string "a-zA-Z_" in
  let body_cs = Charset.from_string "a-zA-Z0-9_'" in
  let fn buf pos =
    let nb = ref 1 in
    while Charset.mem body_cs (Input.get buf (pos + !nb)) do incr nb done;
    (String.sub (Input.line buf) pos !nb, buf, pos + !nb)
  in
  Earley.black_box fn head_cs false "<r-ident>"

(** [escaped_ident with_delim] is a parser for a single escaped identifier. An
    escaped identifier corresponds to an arbitrary sequence of characters that
    starts with ["{|"], ends with ["|}"], and does not contain ["|}"]. Or said
    otherwise, they are recognised by regexp ["{|\([^|]\|\(|[^}]\)\)|*|}"]. If
    [with_delim] is [true] then the returned string includes both the starting
    and the ending delimitors. They are otherwise omited. *)
let escaped_ident : bool -> string Earley.grammar = fun with_delim ->
  let fn buf pos =
    let s = Buffer.create 20 in
    (* Check start marker. *)
    let (c, buf, pos) = Input.read buf (pos + 1) in
    if c <> '|' then Earley.give_up ();
    if with_delim then Buffer.add_string s "{|";
    (* Accumulate until end marker. *)
    let rec work buf pos =
      let (c, buf, pos) = Input.read buf pos in
      let next_c = Input.get buf pos in
      if c = '|' && next_c = '}' then (buf, pos+1)
      else if c <> '\255' then (Buffer.add_char s c; work buf pos)
      else Earley.give_up ()
    in
    let (buf, pos) = work buf pos in
    if with_delim then Buffer.add_string s "|}";
    (* Return the contents. *)
    (Buffer.contents s, buf, pos)
  in
  let p_name = if with_delim then "{|<e-ident>|}" else "<e-ident>" in
  Earley.black_box fn (Charset.singleton '{') false p_name

let escaped_ident_no_delim = escaped_ident false
let escaped_ident = escaped_ident true

(** Any identifier (regular or escaped). *)
let parser any_ident =
  | id:regular_ident -> KW.check id; id
  | id:escaped_ident -> id
  | id:declared_id   -> id

(** Identifier (regular and non-keyword, or escaped). *)
let parser ident = id:any_ident -> in_pos _loc id

let parser arg_ident =
  | id:ident -> Some(id)
  | _wild_   -> None

(** Metavariable identifier (regular or escaped, prefixed with ['?']). *)
let parser meta =
  | "?" - id:{regular_ident | escaped_ident} ->
      if id = "_" then Earley.give_up (); in_pos _loc id

(** Pattern variable identifier (regular or escaped, prefixed with ['$']). *)
let parser patt =
  | "$" - id:{regular_ident | escaped_ident} ->
      if id = "_" then None else Some(in_pos _loc id)

(** Any path member identifier (escaped idents are stripped). *)
let parser path_elem =
  | id:regular_ident          -> KW.check id; (id, false)
  | id:escaped_ident_no_delim -> (id, true)

(** Module path (dot-separated identifiers. *)
let parser path = m:path_elem ms:{"." path_elem}* $ -> m::ms

(** [qident] parses a single (possibly qualified) identifier. *)
let parser qident = mp:{path_elem "."}* id:any_ident -> in_pos _loc (mp,id)

(** [symtag] parses a single symbol tag. *)
let parser property =
  | _constant_  -> Terms.Const
  | _injective_ -> Terms.Injec

(** [exposition] parses the exposition tag of a symbol.*)
let parser exposition =
  | _protected_ -> Terms.Protec
  | _private_   -> Terms.Privat

(** Priority level for an expression (term or type). *)
type prio = PAtom | PAppl | PUnaO | PBinO | PFunc

(** [term] is a parser for a term. *)
let parser term @(p : prio) =
  (* TYPE constant. *)
  | _TYPE_
      when p >= PAtom -> in_pos _loc P_Type
  (* Variable (or possibly explicitly applied and qualified symbol). *)
  | expl:{"@" -> true}?[false] qid:qident
      when p >= PAtom -> in_pos _loc (P_Iden(qid, expl))
  (* Wildcard. *)
  | _wild_
      when p >= PAtom -> in_pos _loc P_Wild
  (* Metavariable. *)
  | m:meta e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Meta(m, Array.of_list e))
  (* Pattern (LHS) or pattern application (RHS). *)
  | p:patt e:env?[[]]
      when p >= PAtom -> in_pos _loc (P_Patt(p, Array.of_list e))
  (* Parentheses. *)
  | "(" t:(term PFunc) ")"
      when p >= PAtom -> in_pos _loc (P_Wrap(t))
  (* Explicitly given argument. *)
  | "{" t:(term PFunc) "}"
      when p >= PAtom -> in_pos _loc (P_Expl(t))
  (* Application. *)
  | t:(term PAppl) u:(term PAtom)
      when p >= PAppl -> in_pos _loc (P_Appl(t,u))
  (* Implication. *)
  | a:(term PBinO) "→" b:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Impl(a,b))
  (* Products. *)
  | "Π" xs:arg+ "," b:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Prod(xs,b))
  | "Π" xs:arg_ident+ ":" a:(term PFunc) "," b:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Prod([xs,Some(a),false],b))
  (* Abstraction. *)
  | "λ" xs:arg+ "," t:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Abst(xs,t))
  | "λ" xs:arg_ident+ ":" a:(term PFunc) "," t:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_Abst([xs,Some(a),false],t))
  (* Local let. *)
  | _let_ x:ident a:arg* b:{":" (term PFunc)}? "≔" t:(term PFunc) _in_
      u:(term PFunc)
      when p >= PFunc -> in_pos _loc (P_LLet(x,a,b,t,u))
  (* Natural number literal. *)
  | n:nat_lit
      when p >= PAtom -> in_pos _loc (P_NLit(n))
  (* Unary operator. *)
  | u:unop t:(term PUnaO)
      when p >= PUnaO ->
        (* Find out minimum priorities for the operand. *)
        let min_p =
          let (_, p, _) = u in p
        in
        (* Check that priority of operand is above [min_p]. *)
        let _ =
          match t.elt with
          | P_UnaO((_,p,_),_) when p < min_p -> Earley.give_up ()
          | _                                -> ()
        in
        in_pos _loc (P_UnaO(u,t))
  (* Binary operator. *)
  | t:(term PBinO) b:binop
      when p >= PBinO ->>
        (* Find out minimum priorities for left and right operands. *)
        let (min_pl, min_pr) =
          let (_, assoc, p, _) = b in
          let p_plus_epsilon = p +. 1e-6 in
          match assoc with
          | Assoc_none  -> (p_plus_epsilon, p_plus_epsilon)
          | Assoc_left  -> (p             , p_plus_epsilon)
          | Assoc_right -> (p_plus_epsilon, p             )
        in
        (* Check that priority of left operand is above [min_pl]. *)
        let _ =
          match t.elt with
          | P_BinO(_,(_,_,p,_),_) when p < min_pl -> Earley.give_up ()
          | _                                     -> ()
        in
        u:(term PBinO) ->
          (* Check that priority of the right operand is above [min_pr]. *)
          let _ =
            match u.elt with
            | P_BinO(_,(_,_,p,_),_) -> if p < min_pr then Earley.give_up ()
            | _                     -> ()
          in
          in_pos _loc (P_BinO(t,b,u))

(* NOTE on binary operators. To handle infix binary operators, we need to rely
   on a dependent (Earley) grammar. The operands are parsed using the priority
   level [PBinO]. The left operand is parsed first, together with the operator
   to obtain the corresponding priority and associativity parameters.  We then
   check whether the (binary operator) priority level [pl] of the left operand
   satifies the conditions, and reject it early if it does not.  We then parse
   the right operand in a second step, and also check whether it satisfies the
   required condition before accepting the parse tree. *)

(** [env] is a parser for a metavariable environment. *)
and parser env = "[" t:(term PBinO) ts:{"," (term PBinO)}* "]" -> t::ts

(** [arg] parses a single function argument. *)
and parser arg =
  (* Explicit argument without type annotation. *)
  | x:arg_ident                                 -> ([x], None,    false)
  (* Explicit argument with type annotation. *)
  | "(" xs:arg_ident+    ":" a:(term PFunc) ")" -> (xs , Some(a), false)
  (* Implicit argument (with possible type annotation). *)
  | "{" xs:arg_ident+ a:{":" (term PFunc)}? "}" -> (xs , a      , true )

let term = term PFunc

(** [rule] is a parser for a single rewriting rule. *)
let parser rule =
  | l:term "↪" r:term -> Pos.in_pos _loc (l, r)

(** [rw_patt_spec] is a parser for a rewrite pattern specification. *)
let parser rw_patt_spec =
  | t:term                          -> P_rw_Term(t)
  | _in_ t:term                     -> P_rw_InTerm(t)
  | _in_ x:ident _in_ t:term        -> P_rw_InIdInTerm(x,t)
  | x:ident _in_ t:term             -> P_rw_IdInTerm(x,t)
  | u:term _in_ x:ident _in_ t:term -> P_rw_TermInIdInTerm(u,x,t)
  | u:term _as_ x:ident _in_ t:term -> P_rw_TermAsIdInTerm(u,x,t)

(** [rw_patt] is a parser for a (located) rewrite pattern. *)
let parser rw_patt = "[" r:rw_patt_spec "]" -> in_pos _loc r

let parser assert_must_fail =
  | _assert_    -> false
  | _assertnot_ -> true

(** [assertion] parses a single assertion. *)
let parser assertion =
  | t:term ":" a:term -> P_assert_typing(t,a)
  | t:term "≡" u:term -> P_assert_conv(t,u)
  (* FIXME potential conflict with infix "≡". *)

(** [query] parses a query. *)
let parser query =
  | _set_ "verbose" i:nat_lit ->
      Pos.in_pos _loc (P_query_verbose(i))
  | _set_ "debug" b:{'+' -> true | '-' -> false} - s:alpha ->
      Pos.in_pos _loc (P_query_debug(b, s))
  | _set_ "flag" s:string_lit b:{"on" -> true | "off" -> false} ->
      Pos.in_pos _loc (P_query_flag(s, b))
  | mf:assert_must_fail a:assertion ->
      Pos.in_pos _loc (P_query_assert(mf,a))
  | mf:assert_must_fail ps:arg* "⊢" t:term "≡" u:term ->
      let ps_t = Pos.in_pos _loc (P_Abst(ps,t)) in
      let ps_u = Pos.in_pos _loc (P_Abst(ps,u)) in
      let assert_conv = P_assert_conv(ps_t,ps_u) in
      Pos.in_pos _loc (P_query_assert(mf,assert_conv))
  | mf:assert_must_fail ps:arg* "⊢" t:term ":" u:term ->
      let ps_t = Pos.in_pos _loc (P_Abst(ps,t)) in
      let ps_u = Pos.in_pos _loc (P_Prod(ps,u)) in
      let assert_typing = P_assert_typing(ps_t,ps_u) in
      Pos.in_pos _loc (P_query_assert(mf,assert_typing))
  | _type_ t:term ->
      let c = Eval.{strategy = NONE; steps = None} in
      Pos.in_pos _loc (P_query_infer(t,c))
  | _compute_ t:term ->
      let c = Eval.{strategy = SNF; steps = None} in
      Pos.in_pos _loc (P_query_normalize(t,c))
  | _set_ "prover" s:string_lit ->
      Pos.in_pos _loc (P_query_prover(s))
  | _set_ "prover_timeout" n:nat_lit ->
      Pos.in_pos _loc (P_query_prover_timeout(n))

(** [tactic] is a parser for a single tactic. *)
let parser tactic =
  | _refine_ t:term             -> Pos.in_pos _loc (P_tac_refine(t))
  | _intro_ xs:arg_ident+       -> Pos.in_pos _loc (P_tac_intro(xs))
  | _apply_ t:term              -> Pos.in_pos _loc (P_tac_apply(t))
  | _simpl_                     -> Pos.in_pos _loc P_tac_simpl
  | _rewrite_ p:rw_patt? t:term -> Pos.in_pos _loc (P_tac_rewrite(p,t))
  | _refl_                      -> Pos.in_pos _loc P_tac_refl
  | _sym_                       -> Pos.in_pos _loc P_tac_sym
  | i:{_:_focus_ nat_lit}       -> Pos.in_pos _loc (P_tac_focus(i))
  | _print_                     -> Pos.in_pos _loc P_tac_print
  | _proofterm_                 -> Pos.in_pos _loc P_tac_proofterm
  | _why3_ s:string_lit?        -> Pos.in_pos _loc (P_tac_why3(s))
  | q:query                     -> Pos.in_pos _loc (P_tac_query(q))

(** [proof_end] is a parser for a proof terminator. *)
let parser proof_end =
  | _qed_   -> P_proof_qed
  | _admit_ -> P_proof_admit
  | _abort_ -> P_proof_abort

let parser assoc =
  | EMPTY   -> Assoc_none
  | "left"  -> Assoc_left
  | "right" -> Assoc_right

(** [config] parses a single configuration option. *)
let parser config =
  | "builtin" s:string_lit "≔" qid:qident ->
      P_config_builtin(s,qid)
  | "prefix" p:float_lit s:string_lit "≔" qid:qident ->
      let unop = (s, p, qid) in
      sanity_check _loc_s s;
      Prefix.add unops s unop;
      P_config_unop(unop)
  | "infix" a:assoc p:float_lit s:string_lit "≔" qid:qident ->
      let binop = (s, a, p, qid) in
      sanity_check _loc_s s;
      Prefix.add binops s binop;
      P_config_binop(binop)
  | "declared" id:string_lit ->
      sanity_check _loc_id id;
      Prefix.add declared_ids id id;
      P_config_ident(id)

let parser statement =
  _theorem_ s:ident al:arg* ":" a:term _proof_ -> Pos.in_pos _loc (s,al,a)

let parser proof =
  ts:tactic* e:proof_end -> (ts, Pos.in_pos _loc_e e)

(** [!require mp] can be used to require the compilation of a module [mp] when
    it is required as a dependency. This has the effect of importing notations
    exported by that module. The value of [require] is set in [Compile], and a
    reference is used to avoid to avoid cyclic dependencies. *)
let require : (Path.t -> unit) Stdlib.ref = ref (fun _ -> ())

(** [do_require pos path] is a wrapper for [!require path], that takes care of
    possible exceptions. Errors are reported at given position [pos],  keeping
    as much information as possible in the error message. *)
let do_require : Pos.pos -> p_module_path -> unit = fun loc path ->
  let path = List.map fst path in
  let local_fatal fmt =
    let fmt = "Error when loading module [%a].\n" ^^ fmt in
    parser_fatal loc fmt Path.pp path
  in
  (* Saving/restoring parser state here is necessary for reentrancy: [require]
     can call compilation, which in turn can call the parser. *)
  let reentrant_call () =
    let saved_unops = Prefix.save unops in
    let saved_binops  = Prefix.save binops in
    let saved_declared_ids = Prefix.save declared_ids in
    let restore () =
      Prefix.restore unops saved_unops;
      Prefix.restore binops saved_binops;
      Prefix.restore declared_ids saved_declared_ids
    in
    try !require path; restore () with e -> restore (); raise e
  in
  (* We attach our position to errors comming from the outside. *)
  try reentrant_call () with
  | Console.Fatal(None     , msg) -> local_fatal "%s" msg
  | Console.Fatal(Some(pos), msg) -> local_fatal "[%a] %s" Pos.print pos msg
  | e                             -> local_fatal "Uncaught exception: [%s]"
                                       (Printexc.to_string e)

(** [cmd] is a parser for a single command. *)
let parser cmd =
  | _require_ o:{_open_ -> true}?[false] ps:path+
      -> let fn p = do_require _loc p; if o then get_ops _loc p in
         List.iter fn ps; P_require(o,ps)
  | _require_ p:path _as_ n:path_elem
      -> do_require _loc p;
         P_require_as(p, Pos.in_pos _loc_n n)
  | _open_ ps:path+
      -> List.iter (get_ops _loc) ps;
         P_open(ps)
  | e:exposition? p:property? _symbol_ s:ident al:arg* ":" a:term
      -> P_symbol(Option.get Terms.Public e,
                  Option.get Terms.Defin p,s,al,a)
  | _rule_ r:rule rs:{_:_with_ rule}*
      -> P_rules(r::rs)
  | e:exposition? _definition_ s:ident al:arg* ao:{":" term}? "≔" t:term
      -> P_definition(Option.get Terms.Public e,false,s,al,ao,t)
  | e:exposition? st:statement (ts,pe):proof
      -> P_theorem(Option.get Terms.Public e,st,ts,pe)
  | _set_ c:config
      -> P_set(c)
  | q:query
      -> P_query(q)

(** [cmds] is a parser for multiple (located) commands. *)
let parser cmds = {c:cmd -> in_pos _loc c}*

(** [parse_file fname] attempts to parse the file [fname], to obtain a list of
    toplevel commands. In case of failure, a graceful error message containing
    the error position is given through the [Fatal] exception. *)
let parse_file : string -> ast = fun fname ->
  Prefix.reset unops; Prefix.reset binops; Prefix.reset declared_ids;
  try Earley.parse_file cmds blank fname
  with Earley.Parse_error(buf,pos) ->
    let loc = Pos.locate buf pos buf pos in
    parser_fatal loc "Parse error."

(** [parse_string fname str] attempts to parse the string [str] file to obtain
    a list of toplevel commands.  In case of failure, a graceful error message
    containing the error position is given through the [Fatal] exception.  The
    [fname] argument should contain a relevant file name for the error message
    to be constructed. *)
let parse_string : string -> string -> ast = fun fname str ->
  Prefix.reset unops; Prefix.reset binops; Prefix.reset declared_ids;
  try Earley.parse_string ~filename:fname cmds blank str
  with Earley.Parse_error(buf,pos) ->
    let loc = Pos.locate buf pos buf pos in
    parser_fatal loc "Parse error."
