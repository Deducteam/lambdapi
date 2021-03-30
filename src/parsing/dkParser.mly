%{

open! Lplib
open Timed
open Common
open Pos
open Syntax
open DkLexer
open Error
open Core

(** [get_args t] decomposes the parser level term [t] into a spine [(h,args)],
    when [h] is the term at the head of the application and [args] is the list
    of all its arguments.  The arguments are stored together with the position
    of the corresponding application node in the source code. Note that [h] is
    guaranteed not to be a [P_Appl] node. Term constructors with no equivalent
    in the legacy syntax (like binary symbol applications) are not handled. *)
let get_args : p_term -> p_term * (Pos.popt * p_term) list = fun t ->
  let rec get_args acc t =
    match t.elt with
    | P_Appl(u,v) -> get_args ((t.pos,v)::acc) u
    | _           -> (t, acc)
  in get_args [] t

(** [add_args t args] builds the application of the term [t] to the  arguments
    [args]. When [args] is empty, the returned value is exactly [t]. Note that
    this function is the inverse of [get_args] (in some sense). *)
let add_args : p_term -> (Pos.popt * p_term) list -> p_term =
  List.fold_left (fun t (p,u) -> Pos.make p (P_Appl(t,u)))

(** Representation of a reduction rule, with its context. *)
type old_p_rule = ((strloc * p_term option) list * p_term * p_term) Pos.loc

(** [translate_old_rule r] transforms the legacy representation of a rule into
    the new representation. This function will be removed soon. *)
let translate_old_rule : old_p_rule -> p_rule = fun r ->
  let (ctx, lhs, rhs) = r.elt in
  (* Check for (deprecated) annotations in the context. *)
  let get_var (x,ao) =
    let fn a = wrn a.pos "Ignored type annotation." in
    (if !Console.verbose > 1 then Option.iter fn ao); x
  in
  let ctx = List.map get_var ctx in
  let is_pat_var env x =
    not (List.mem x env) && List.exists (fun y -> y.elt = x) ctx
  in
  (* Find the maximum number of arguments a variable is applied to. *)
  let arity = Hashtbl.create 7 in
  let rec compute_arities env t =
    let (h, args) = get_args t in
    let nb_args = List.length args in
    begin
      match h.elt with
      | P_Appl(_,_)       -> assert false (* Cannot happen. *)
      | P_Iden(x,_)       ->
          let (p,x) = x.elt in
          if p = [] && is_pat_var env x then
            begin
              try
                let n = Hashtbl.find arity x in
                if nb_args > n then Hashtbl.replace arity x nb_args
              with Not_found -> Hashtbl.add arity x nb_args
            end
      | P_Wild            -> ()
      | P_Type            -> fatal h.pos "Type in legacy pattern."
      | P_Prod(_,_)       -> fatal h.pos "Product in legacy pattern."
      | P_Abst(xs,t)      ->
          begin
            match xs with
            | [(_       ,Some(a),_)] ->
                fatal a.pos "Annotation in legacy pattern."
            | [([Some x],None   ,_)] ->
                compute_arities (x.elt::env) t
            | [([None  ],None   ,_)] ->
                compute_arities env t
            | _                      -> assert false
          end
      | P_Arro(_,_)       -> fatal h.pos "Implication in legacy pattern."
      | P_LLet(_,_,_,_,_) -> fatal h.pos "Let expression in legacy rule."
      | P_Meta(_,_)       -> assert false
      | P_Patt(_,_)       -> assert false
      | P_NLit(_)         -> assert false
      | P_Wrap(_)         -> assert false
      | P_Expl(_)         -> assert false
    end;
    List.iter (fun (_,t) -> compute_arities env t) args
  in
  compute_arities [] lhs;
  (* Check that all context variables occur in the LHS. *)
  let check_here x =
    try ignore (Hashtbl.find arity x.elt) with Not_found ->
      fatal x.pos "Variable [%s] does not occur in the LHS." x.elt
  in
  List.iter check_here ctx;
  (* Actually process the LHS and RHS. *)
  let rec build env t =
    let (h, lts) = get_args t in
    match h.elt with
    | P_Iden({elt = ([],x); _}, _) when is_pat_var env x ->
        let lts = List.map (fun (p, t) -> (p, build env t)) lts in
        let max = try Hashtbl.find arity x with Not_found -> assert false in
        let k = List.length lts in
        (* Number of η-expansions required. *)
        let nb_exp = if k >= max then 0 else max - k in
        let p = t.pos in
        if nb_exp = 0 then
          (* No η-expansion required (enough arguments). *)
          let (lts1, lts2) = List.cut lts max in
          let ts1 = Array.of_list (List.map snd lts1) in
          let patt = Pos.make p (P_Patt(Some(Pos.make h.pos x), Some ts1)) in
          add_args patt lts2
        else
          (* We need to η-expense (not enough arguments). *)
          let ts = Array.of_list (List.map snd lts) in
          (* Create fresh variables. *)
          let ctx = List.map (fun x -> x.elt) ctx in
          (* Function to create fresh variable names. *)
          let new_var_name : unit -> string =
            let counter = ref (-1) in
            fun () ->
              incr counter;
              while List.mem (Printf.sprintf "v%i" !counter) ctx do
                incr counter
              done;
              Printf.sprintf "v%i" !counter
          in
          let vars = Array.init nb_exp (fun _ -> new_var_name ()) in
          (* Build the pattern. *)
          let fn x = Pos.none (P_Iden(Pos.none ([],x), false)) in
          let args = Array.append ts (Array.map fn vars) in
          let patt = Pos.make p (P_Patt(Some(Pos.make h.pos x), Some args)) in
          (* Build the abstraction. *)
          let xs = Array.map (fun x -> Some(Pos.none x)) vars in
          Pos.make p (P_Abst([Array.to_list xs, None, false], patt))
    | P_Wild when lts = [] && env = []                   -> t
    | P_Wild                                             ->
        let lts = List.map (fun (_, t) -> build env t) lts in
        Pos.make t.pos (P_Patt(None, Some (Array.of_list lts)))
    | _                                                  ->
    match t.elt with
    | P_Iden(_)
    | P_Type
    | P_Wild            -> t
    | P_Prod(xs,b)      ->
        let (x,a) =
          match xs with
          | [([Some x],Some(a),_)] -> (x, build env a)
          | _                      -> assert false (* Unreachable. *)
        in
        let b = build (x.elt::env) b in
        Pos.make t.pos (P_Prod([([Some x],Some(a),false)], b))
    | P_Arro(a,b)       -> Pos.make t.pos (P_Arro(build env a, build env b))
    | P_Abst(xs,u)      ->
        let (x,a) =
          match xs with
          | [([x],ao,_)] -> (x, Option.map (build env) ao)
          | _            -> assert false (* Unreachable. *)
        in
        let u =
          match x with
          | Some(x) -> build (x.elt::env) u
          | None    -> build env u
        in
        Pos.make t.pos (P_Abst([([x],a,false)], u))
    | P_Appl(t1,t2)     -> Pos.make t.pos (P_Appl(build env t1, build env t2))
    | P_Meta(_,_)       -> fatal t.pos "Invalid legacy rule syntax."
    | P_Patt(_,_)       -> fatal h.pos "Pattern in legacy rule."
    | P_LLet(_,_,_,_,_) -> fatal h.pos "Let expression in legacy rule."
    | P_NLit(_)         -> fatal h.pos "Nat literal in legacy rule."
    | P_Wrap(_)         -> fatal h.pos "Wrapping constructor in legacy rule."
    | P_Expl(_)         -> fatal h.pos "Explicit argument in legacy rule."
  in
  (* NOTE the computation order is important for setting arities properly. *)
  let lhs = build [] lhs in
  let rhs = build [] rhs in
  Pos.make r.pos (lhs, rhs)

let build_config : Pos.pos -> string -> string option -> Eval.eval_config =
    fun loc s1 s2o ->
  try
    let config esteps strategy =
      Eval.{strategy; steps=Option.map int_of_string esteps}
    in
    match (s1, s2o) with
    | ("SNF" , io         ) -> config io        SNF
    | ("HNF" , io         ) -> config io        HNF
    | ("WHNF", io         ) -> config io        WHNF
    | (i     , Some "SNF" ) -> config (Some(i)) SNF
    | (i     , Some "HNF" ) -> config (Some(i)) HNF
    | (i     , Some "WHNF") -> config (Some(i)) WHNF
    | (i     , None       ) -> config (Some(i)) NONE
    | (_     , _          ) -> raise Exit (* captured below *)
  with _ -> fatal (Some(loc)) "Invalid command configuration."

%}

// end of file

%token EOF

// keywords in alphabetical order

%token <bool> ASSERT
%token EVAL
%token KW_DEF
%token KW_INJ
%token KW_PRV
%token KW_THM
%token INFER
%token <Path.t> REQUIRE
%token TYPE

// symbols

%token ARROW
%token COLON
%token COMMA
%token DEF
%token DOT
%token EQUAL
%token FATARROW
%token LONGARROW
%token LEFTPAR
%token LEFTSQU
%token RIGHTPAR
%token RIGHTSQU
%token UNDERSCORE

// identifiers

%token <string> UID
%token <Syntax.qident> QID

// start symbol

%start command
%type <Syntax.p_command> command

%right ARROW FATARROW

%%

command:
  | p_sym_mod=modifier* s=UID p_sym_arg=param* COLON a=term DOT
    {
      let p_sym_mod =
        match List.find_opt is_prop p_sym_mod with
        | Some(_) -> p_sym_mod
        | None -> make_pos $loc(s) (P_prop Const) :: p_sym_mod
      in
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_typ = Some a in
      let p_sym_trm = None in
      let p_sym_prf = None in
      let p_sym_def = false in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | p_sym_mod=modifier* KW_DEF s=UID COLON a=term DOT
    {
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_arg = [] in
      let p_sym_typ = Some a in
      let p_sym_trm = None in
      let p_sym_prf = None in
      let p_sym_def = false in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | p_sym_mod=modifier* KW_DEF s=UID COLON a=term DEF t=term DOT
    {
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_arg = [] in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | p_sym_mod=modifier* KW_DEF s=UID DEF t=term DOT
    {
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_arg = [] in
      let p_sym_typ = None in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | p_sym_mod=modifier* KW_DEF s=UID p_sym_arg=param+ COLON a=term
    DEF t=term DOT
    {
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | p_sym_mod=modifier* KW_DEF s=UID p_sym_arg=param+ DEF t=term DOT
    {
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_typ = None in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | p_sym_mod=modifier* KW_THM s=UID COLON a=term DEF t=term DOT
    {
      let p_sym_mod = make_pos $loc(s) P_opaq :: p_sym_mod in
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_arg = [] in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | p_sym_mod=modifier* KW_THM s=UID p_sym_arg=param+ COLON a=term
    DEF t=term DOT
    {
      let p_sym_mod = make_pos $loc(s) P_opaq :: p_sym_mod in
      let p_sym_nam = make_pos $loc(s) s in
      let p_sym_typ = Some a in
      let p_sym_trm = Some t in
      let p_sym_prf = None in
      let p_sym_def = true in
      make_pos $sloc
        (P_symbol {p_sym_mod;p_sym_nam;p_sym_arg;p_sym_typ;p_sym_trm;p_sym_prf
                   ;p_sym_def})
    }
  | rs=rule+ DOT {
      make_pos $sloc (P_rules(List.map translate_old_rule rs))
    }
  | EVAL t=term DOT {
      let c = Eval.{strategy = SNF; steps = None} in
      let q = make_pos $sloc (P_query_normalize(t,c)) in
      make_pos $sloc (P_query q)
    }
  | EVAL c=eval_config t=term DOT {
      let c = if c.strategy=NONE then {c with strategy=SNF} else c in
      let q = make_pos $sloc (P_query_normalize(t, c)) in
      make_pos $sloc (P_query q)
    }
  | INFER t=term DOT {
      let c = Eval.{strategy = NONE; steps = None} in
      let q = make_pos $sloc (P_query_infer(t, c)) in
      make_pos $sloc (P_query q)
    }
  | INFER c=eval_config t=term DOT {
      let q = make_pos $sloc (P_query_infer(t, c)) in
      make_pos $sloc (P_query q)
    }
  | mf=ASSERT t=aterm COLON a=term DOT {
      let q = make_pos $sloc (P_query_assert(mf, P_assert_typing(t,a))) in
      make_pos $sloc (P_query q)
    }
  | mf=ASSERT t=aterm EQUAL u=term DOT {
      let q = make_pos $sloc (P_query_assert(mf, P_assert_conv(t,u))) in
      make_pos $sloc (P_query q)
    }
  | r=REQUIRE DOT { make_pos $sloc (P_require(false, [make_pos $loc(r) r])) }
  | EOF {
      raise End_of_file
    }

eval_config:
  | LEFTSQU s=UID RIGHTSQU
    { build_config (locate $sloc) s None }
  | LEFTSQU s1=UID COMMA s2=UID RIGHTSQU
    { build_config (locate $sloc) s1 (Some s2) }

param:
  | LEFTPAR id=UID COLON te=term RIGHTPAR
    { ([Some (make_pos $loc(id) id)], Some(te), false) }

modifier:
  | KW_PRV { make_pos $sloc (P_expo(Term.Protec)) }
  | KW_INJ { make_pos $sloc (P_prop(Term.Injec)) }

context_item:
  | x=UID ao=option(COLON a=term { a }) { (make_pos $loc(x) x, ao) }

rule:
  | LEFTSQU c=separated_list(COMMA, context_item) RIGHTSQU
    l=term LONGARROW r=term
    { make_pos $sloc (c, l, r) }

sterm:
  | qid=QID { make_pos $sloc (P_Iden(make_pos $sloc qid, false)) }
  | id=UID   { make_pos $sloc (P_Iden(make_pos $sloc ([], id), false)) }
  | UNDERSCORE { make_pos $sloc P_Wild }
  | TYPE    { make_pos $sloc P_Type }
  | LEFTPAR t=term RIGHTPAR { t }

aterm:
  | t=aterm u=sterm { make_pos $sloc (P_Appl(t,u)) }
  | t=sterm         { t }

type_annot:
  | COLON a=aterm { a }

term:
  | t=aterm { t }
  | x=UID COLON a=aterm ARROW b=term {
      let x = make_pos $loc(x) x in
      make_pos $sloc (P_Prod([([Some x], Some(a), false)], b))
    }
  | LEFTPAR x=UID COLON a=aterm RIGHTPAR ARROW b=term {
      let x = make_pos $loc(x) x in
      make_pos $sloc (P_Prod([([Some x], Some(a), false)], b))
    }
  | a=term ARROW b=term {
      make_pos $sloc (P_Arro(a, b))
    }
  | UNDERSCORE a=option(type_annot) FATARROW t=term {
      make_pos $sloc (P_Abst([([None], a, false)], t))
    }
  | x=UID a=option(type_annot) FATARROW t=term {
      let x = make_pos $loc(x) x in
      make_pos $sloc (P_Abst([([Some x], a, false)], t))
    }
%%
