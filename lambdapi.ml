(**** Colorful error / warning messages *************************************)

(* Format transformers (colors). *)
let red fmt = "\027[31m" ^^ fmt ^^ "\027[0m%!"
let gre fmt = "\027[32m" ^^ fmt ^^ "\027[0m%!"
let yel fmt = "\027[33m" ^^ fmt ^^ "\027[0m%!"
let blu fmt = "\027[34m" ^^ fmt ^^ "\027[0m%!"
let mag fmt = "\027[35m" ^^ fmt ^^ "\027[0m%!"
let cya fmt = "\027[36m" ^^ fmt ^^ "\027[0m%!"

(* [r_or_g cond fmt] colors the format [fmt] in green if [cond] is [true], and
   in red otherwise. *)
let r_or_g cond = if cond then gre else red

(* [wrn fmt] prints a yellow warning message with [Printf] format [fmt].  Note
   that the output buffer is flushed by the function. *)
let wrn : ('a, out_channel, unit) format -> 'a =
  fun fmt -> Printf.eprintf (yel fmt)

(* [err fmt] prints a red error message with [Printf] format [fmt].  Note that
   the output buffer is flushed by the function. *)
let err : ('a, out_channel, unit) format -> 'a =
  fun fmt -> Printf.eprintf (red fmt)

(* [fatal fmt] is like [err fmt], but it aborts the program with [exit 1]. *)
let fatal : ('a, out_channel, unit, unit, unit, 'b) format6 -> 'a =
  fun fmt -> Printf.kfprintf (fun _ -> exit 1) stderr (red fmt)

(**** File utilities ********************************************************)

(* Current file name extensions. *)
let src_extension : string = ".dk"
let obj_extension : string = ".dko"

(* [module_path path] computes the module path corresponding to [path],  which
   sould be a relative path to a source file (not using [".."]).  The returned
   module path is formed using the subdirectories and it is  terminated by the
   file name (without extension). Note that the file name sould have extension
   [src_extension]. *)
let module_path : string -> string list = fun fname ->
  if not (Filename.check_suffix fname src_extension) then
    fatal "Invalid extension for %S (expected %S)...\n" fname src_extension;
  let base = Filename.chop_extension (Filename.basename fname) in
  let dir = Filename.dirname fname in
  let rec build_path acc dir =
    let dirbase = Filename.basename dir in
    let dirdir  = Filename.dirname  dir in
    if dirbase = "." then acc else build_path (dirbase::acc) dirdir
  in
  build_path [base] dir

(* [mod_time fname] returns the modification time of file [fname]  represented
   as a [float]. [neg_infinity] is returned if the file does not exist. *)
let mod_time : string -> float = fun fname ->
  if Sys.file_exists fname then Unix.((stat fname).st_mtime) else neg_infinity

(* [binary_time] is the modification time of the compiled program. *)
let binary_time : float = mod_time "/proc/self/exe"

(* [more_recent source target] checks whether the [target] (produced from  the
   [source] file) should be produced again.  This is the case when [source] is
   more recent than [target], or when the binary of the program is more recent
   than [target]. *)
let more_recent : string -> string -> bool = fun source target ->
  let s_time = mod_time source in
  let t_time = mod_time target in
  s_time > t_time || binary_time > t_time

(**** Debugging messages management *****************************************)

(* Various debugging / message flags. *)
let quiet      = ref false
let debug      = ref false
let debug_eval = ref false
let debug_infr = ref false
let debug_patt = ref false
let debug_type = ref false

(* [debug_enabled ()] indicates whether any debugging flag is enabled. *)
let debug_enabled : unit -> bool = fun () ->
  !debug || !debug_eval || !debug_infr || !debug_patt || !debug_type

(* [set_debug str] enables debugging flags according to [str]. *)
let set_debug : string -> unit =
  let enable c =
    match c with
    | 'a' -> debug      := true
    | 'e' -> debug_eval := true
    | 'i' -> debug_infr := true
    | 'p' -> debug_patt := true
    | 't' -> debug_type := true
    | _   -> wrn "Unknown debug flag %C\n" c
  in
  String.iter enable

(* [log name fmt] prints a message in the log with the [Printf] format  [fmt].
   The message is identified with the name (or flag) [name],  and coloured  in
   cyan. Note that the  output buffer is flushed by the  function,  and that a
   newline character ['\n'] is appended to the output. *)
let log : string -> ('a, out_channel, unit) format -> 'a =
  fun name fmt -> Printf.eprintf ((cya "[%s] ") ^^ fmt ^^ "\n%!") name

(* [out fmt] prints an output message with the [Printf] format [fmt]. Note the
   output buffer is flushed by the function, and that the message is displayed
   in magenta whenever a debugging mode is enabled. *)
let out : ('a, out_channel, unit) format -> 'a =
  fun fmt ->
    let fmt = if debug_enabled () then mag fmt else fmt ^^ "%!" in
    if !quiet then Printf.ifprintf stdout fmt else Printf.printf fmt

(**** Abstract syntax of the language ***************************************)

(* Type of terms (and types). *)
type term =
  (* Free variable. *)
  | Vari of term Bindlib.var
  (* "Type" constant. *)
  | Type
  (* "Kind" constant. *)
  | Kind
  (* Symbol (static or definable). *)
  | Symb of symbol
  (* Dependent product. *)
  | Prod of term * (term, term) Bindlib.binder
  (* Abstraction. *)
  | Abst of term * (term, term) Bindlib.binder
  (* Application. *)
  | Appl of bool * term * term
  (* Unification variable. *)
  | Unif of term option ref
  (* Pattern variable. *)
  | PVar of term option ref

(* NOTE: the boolean in application nodes is set to true for rigid terms. They
   are marked as such during evaluation for terms having a  static  symbol  at
   their head. This helps avoiding useless copies. *)

(* Representation of a reduction rule.  The [arity] corresponds to the minimal
   number of arguments that are required for the rule to apply. The definition
   of a rule is split into a left-hand side [lhs] and a right-and sides [rhs].
   The variables of the context are bound on both sides of the rule. Note that
   the left-hand side is given as a list of arguments for the definable symbol
   on which the rule is defined. The symbol is not given in the type of rules,
   as rules will be stored in the definition of symbols. *)
 and rule =
  { lhs   : (term, term list) Bindlib.mbinder
  ; rhs   : (term, term) Bindlib.mbinder
  ; arity : int }

(* NOTE: to check if a rule [r] applies on a term [t] using our representation
   is really easy.  First,  one should substitute the [r.lhs] binder (with the
   [Bindlib.msubst] function) using an array of pattern variables  (which size
   should be [Bindlib.mbinder_arity r.lhs]) to obtain a term list [lhs]. Then,
   to check if [r] applies on a the term [t] (which head should be the symbol)
   one should test equality (with unification) between [lhs] and the arguments
   of [t]. If they are equal then the rule applies and the term obtained after
   the application is computed by substituting [r.rhs] with the same array  of
   pattern variables that was used for [l.rhs] (at this point, all the pattern
   variables should have been instanciated by the equality test). If [lhs] and
   the arguments of [t] are not equal, then the rule does not apply. *)

(**** Symbols (static or definable) *****************************************)

(* Representation of a static symbol. *)
and sym =
  { sym_name  : string
  ; sym_type  : term
  ; sym_path  : string list }

(* Representation of a definable symbol,  which carries its reduction rules in
   a reference. It should be updated to add new rules. *)
and def =
  { def_name  : string
  ; def_type  : term
  ; def_rules : rule list ref
  ; def_path  : string list }

(* NOTE: the [path] that is stored in a symbol corresponds to a "module path".
   The path [["a"; "b"; "f"]] corresponds to file ["a/b/f.lp"].  It is printed
   and read in the source code as ["dira::dirb::file"]. *)

(* Representation of a (static or definable) symbol. *)
and symbol = Sym of sym | Def of def

(* [symbol_type s] returns the type of the given symbol [s]. *)
let symbol_type : symbol -> term =
  fun s ->
    match s with
    | Sym(sym) -> sym.sym_type
    | Def(def) -> def.def_type

(* Reference containing the module path of the current file. It is useful when
   printing symbol names to avoid giving the full path for local symbols. *)
let current_module : string list ref = ref []

(* [symbol_name s] returns the full name of the given symbol [s] (including if
   the symbol does not come from the current module. *)
let symbol_name : symbol -> string = fun s ->
  let (path, name) =
    match s with
    | Sym(sym) -> (sym.sym_path, sym.sym_name)
    | Def(def) -> (def.def_path, def.def_name)
  in
  if path = !current_module then name
  else String.concat "." (path @ [name])

(**** Signature *************************************************************)

module Sign =
  struct
    (* Representation of a signature (roughly, a set of symbols). *)
    type t = { symbols : (string, symbol) Hashtbl.t ; path : string list }

    (* [create path] creates an empty signature with module path [path]. *)
    let create : string list -> t =
      fun path -> { path ; symbols = Hashtbl.create 37 }

    (* [new_static sign name a] creates a new static symbol named [name]  with
       type [a] the signature [sign]. The created symbol is also returned. *)
    let new_static : t -> string -> term -> sym =
      fun sign sym_name sym_type ->
        if Hashtbl.mem sign.symbols sym_name then
          wrn "Redefinition of %s.\n" sym_name;
        let sym_path = sign.path in
        let sym = { sym_name ; sym_type ; sym_path } in
        Hashtbl.add sign.symbols sym_name (Sym(sym)); sym

    (* [new_definable sign name a] creates a new definable symbol (without any
       reduction rule) named [name] with type [a] in the signature [sign]. The
       created symbol is also returned. *)
    let new_definable : t -> string -> term -> def =
      fun sign def_name def_type ->
        if Hashtbl.mem sign.symbols def_name then
          wrn "Redefinition of %s.\n" def_name;
        let def_path = sign.path in
        let def_rules = ref [] in
        let def = { def_name ; def_type ; def_rules ; def_path } in
        Hashtbl.add sign.symbols def_name (Def(def)); def

    (* [find sign name] looks for a symbol named [name] in signature [sign] if
       there is one. The exception [Not_found] is raised if there is none. *)
    let find : t -> string -> symbol =
      fun sign name -> Hashtbl.find sign.symbols name

    (* [write sign file] writes the signature [sign] to the file [fname]. *)
    let write : t -> string -> unit =
      fun sign fname ->
        let oc = open_out fname in
        Marshal.to_channel oc sign [Marshal.Closures];
        close_out oc

    (* [read fname] reads a signature from the file [fname]. *)
    let read : string -> t =
      fun fname ->
        let ic = open_in fname in
        let sign = Marshal.from_channel ic in
        close_in ic; sign
  end

(**** Typing context ********************************************************)

module Ctxt =
  struct
    (* Representation of a typing context, associating a [term] (or type),  to
       the free variables. *)
    type t = (term Bindlib.var * term) list

    (* [empty] is the empty context. *)
    let empty : t = []

    (* [add x a ctx] maps the variable [x] to the type [a] in [ctx]. *)
    let add : term Bindlib.var -> term -> t -> t =
      fun x a ctx -> (x,a)::ctx

    (* [find x ctx] returns the type of variable [x] in the context [ctx] when
       the variable appears inthe context. [Not_found] is raised otherwise. *)
    let find : term Bindlib.var -> t -> term = fun x ctx ->
      snd (List.find (fun (y,_) -> Bindlib.eq_vars x y) ctx)
  end

(**** Unification variables management **************************************)

(* [unfold t] unfolds the toplevel unification / pattern variables in [t]. *)
let rec unfold : term -> term = fun t ->
  match t with
  | Unif({contents = Some(t)}) -> unfold t
  | PVar({contents = Some(t)}) -> unfold t
  | _                          -> t

(* [occurs r t] checks whether the unification variable [r] occurs in [t]. *)
let rec occurs : term option ref -> term -> bool = fun r t ->
  match unfold t with
  | Prod(a,b)   -> occurs r a || occurs r (Bindlib.subst b Kind)
  | Abst(a,t)   -> occurs r a || occurs r (Bindlib.subst t Kind)
  | Appl(n,t,u) -> occurs r t || occurs r u
  | Unif(u)     -> u == r
  | Type        -> false
  | Kind        -> false
  | Vari(_)     -> false
  | Symb(_)     -> false
  | PVar(_)     -> true (* PVar not allowed in Unif *)

(* NOTE: pattern variables prevent unification to ensure that they  cannot  be
   absorbed by unification varialbes (and do not escape rewriting code). *)

(* [unify r t] tries to unify [r] with [t],  and returns a boolean to indicate
   whether it succeeded or not. *)
let unify : term option ref -> term -> bool =
  fun r a ->
    assert (!r = None);
    not (occurs r a) && (r := Some(a); true)

(**** Smart constructors and other Bindlib-related things *******************)

(* Short names for variables and boxed terms. *)
type tvar = term Bindlib.var
type tbox = term Bindlib.bindbox

(* Injection of [Bindlib] variables into terms. *)
let mkfree : tvar -> term =
  fun x -> Vari(x)

(* [_Vari x] injects the free variable [x] into the bindbox, so that it may be
   available for binding. *)
let _Vari : tvar -> tbox =
  Bindlib.box_of_var

(* [_Type] injects the constructor [Type] in the [bindbox] type. *)
let _Type : tbox = Bindlib.box Type

(* [_Kind] injects the constructor [Kind] in the [bindbox] type. *)
let _Kind : tbox = Bindlib.box Kind

(* [_Symb s] injects the constructor [Symb(s)] in the [bindbox] type. *)
let _Symb : symbol -> tbox =
  fun s -> Bindlib.box (Symb(s))

(* [_Symb_find sign name] finds the symbol [s] with the given [name] in [sign]
   and injects the constructor [Symb(s)] into the [bindbox] type.  [Not_found]
   is raised if no such symbol is found. *)
let _Symb_find : Sign.t -> string -> tbox =
  fun sign n -> _Symb (Sign.find sign n)

(* [_Appl t u] lifts the application of [t] and [u] to the [bindbox] type. *)
let _Appl : tbox -> tbox -> tbox =
  Bindlib.box_apply2 (fun t u -> Appl(false,t,u))

(* [_Prod a x f] lifts a dependent product node to the [bindbox] type, given a
   boxed term [a] (the type of the domain),  a prefered name [x] for the bound
   variable, and function [f] to build the [binder] (codomain). *)
let _Prod : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f ->
    let b = Bindlib.vbind mkfree x f in
    Bindlib.box_apply2 (fun a b -> Prod(a,b)) a b

(* [_Abst a x f] lifts an abstraction node to the [bindbox] type, given a term
   [a] (which is the type of the bound variable),  the prefered name [x] to be
   used for the bound variable, and the function [f] to build the [binder]. *)
let _Abst : tbox -> string -> (tvar -> tbox) -> tbox =
  fun a x f ->
    let b = Bindlib.vbind mkfree x f in
    Bindlib.box_apply2 (fun a b -> Abst(a,b)) a b

(* [lift t] lifts a [term] [t] to the [bindbox] type,  thus gathering its free
   variables, making them available for binding.  At the same time,  the names
   of the bound variables are automatically updated by [Bindlib]. *)
let rec lift : term -> tbox = fun t ->
  let lift_binder b x = lift (Bindlib.subst b (mkfree x)) in
  let t = unfold t in
  match t with
  | Vari(x)     -> _Vari x
  | Type        -> _Type
  | Kind        -> _Kind
  | Symb(s)     -> _Symb s
  | Prod(a,b)   -> _Prod (lift a) (Bindlib.binder_name b) (lift_binder b)
  | Abst(a,t)   -> _Abst (lift a) (Bindlib.binder_name t) (lift_binder t)
  | Appl(_,t,u) -> _Appl (lift t) (lift u)
  | Unif(_)     -> Bindlib.box t (* Variable not instanciated. *)
  | PVar(_)     -> Bindlib.box t (* Variable not instanciated. *)

(* [update_names t] updates the names of the bound variables of [t] to prevent
   "visual capture" while printing. Note that with [Bindlib],  real capture is
   not possible as binders are represented as OCaml function (HOAS). *)
let update_names : term -> term = fun t -> Bindlib.unbox (lift t)

(* [get_args t] returns a tuple [(hd,args)] where [hd] if the head of the term
   and [args] its arguments. *)
let get_args : term -> term * term list = fun t ->
  let rec get acc t =
    match unfold t with
    | Appl(_,t,u) -> get (u::acc) t
    | t           -> (t, acc)
  in get [] t

(* [add_args ~rigid hd args] builds the application of a term [hd] to the list
   of its arguments [args] (this is the inverse of [get_args]).  Note that the
   optional [rigid] argument ([false] by default) can be used to mark as rigid
   terms whose head are static symbol, to avoid copying them repeatedly. *)
let add_args : ?rigid:bool -> term -> term list -> term =
  fun ?(rigid=false) t args ->
    let rec add_args t args =
      match args with
      | []      -> t
      | u::args -> add_args (Appl(rigid,t,u)) args
    in add_args t args

(**** Printing functions (should come early for debuging) *******************)

(* [pp_term oc t] pretty-prints the term [t] to the channel [oc]. *)
let pp_term : out_channel -> term -> unit = fun oc t ->
  let pstring = output_string oc in
  let pformat fmt = Printf.fprintf oc fmt in
  let name = Bindlib.name_of in
  let rec print (p : [`Func | `Appl | `Atom]) oc t =
    let t = unfold t in
    match (t, p) with
    (* Atoms are printed inconditonally. *)
    | (Vari(x)  , _    )   -> pstring (name x)
    | (Type     , _    )   -> pstring "Type"
    | (Kind     , _    )   -> pstring "Kind"
    | (Symb(s)  , _    )   -> pstring (symbol_name s)
    | (Unif(_)  , _    )   -> pstring "?"
    | (PVar(_)  , _    )   -> pstring "?"
    (* Applications are printed when priority is above [`Appl]. *)
    | (Appl(_,t,u), `Appl)
    | (Appl(_,t,u), `Func) -> pformat "%a %a" (print `Appl) t (print `Atom) u
    (* Abstractions and products are only printed at priority [`Func]. *)
    | (Abst(a,t), `Func)   ->
        let (x,t) = Bindlib.unbind mkfree t in
        pformat "%s:%a => %a" (name x) (print `Func) a (print `Func) t
    | (Prod(a,b), `Func)   ->
        let (x,c) = Bindlib.unbind mkfree b in
        let x = if Bindlib.binder_occur b then (name x) ^ ":" else "" in
        pformat "%s%a -> %a" x (print `Appl) a (print `Func) c
    (* Anything else needs parentheses. *)
    | (_        , _    )   -> pformat "(%a)" (print `Func) t
  in
  print `Func oc (update_names t)

(* Short synonym for [pp_term]. *)
let pp = pp_term

(* [pp_ctxt oc ctx] pretty-prints the context [ctx] to the channel [oc]. *)
let pp_ctxt : out_channel -> Ctxt.t -> unit = fun oc ctx ->
  let pstring = output_string oc in
  let pformat fmt = Printf.fprintf oc fmt in
  let name = Bindlib.name_of in
  let rec print oc ls =
    match ls with
    | []          -> pstring "∅"
    | [(x,a)]     -> pformat "%s : %a" (name x) pp a
    | (x,a)::ctx  -> pformat "%a, %s : %a" print ctx (name x) pp a
  in print oc ctx

let print_rule : out_channel -> def * rule -> unit = fun oc (def,rule) ->
  let pformat fmt = Printf.fprintf oc fmt in
  let (xs,lhs) = Bindlib.unmbind mkfree rule.lhs in
  let lhs = add_args (Symb(Def def)) lhs in
  let rhs = Bindlib.msubst rule.rhs (Array.map mkfree xs) in
  pformat "%a → %a" pp lhs pp rhs

(**** Strict equality (no conversion) with unification **********************)

(* Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

(* [eq_binder eq b1 b2] tests the equality of two binders by substituting them
   with the same free variable, and testing the equality of the obtained terms
   with the [eq] function. *)
let eq_binder : term eq -> (term, term) Bindlib.binder eq =
  fun eq f g -> f == g ||
    let x = mkfree (Bindlib.new_var mkfree "_eq_binder_") in
    eq (Bindlib.subst f x) (Bindlib.subst g x)

(* [eq t u] tests the equality of the terms [t] and [u]. Pattern variables may
   be instantiated in the process. *)
let eq : ?rewrite: bool -> term -> term -> bool = fun ?(rewrite=false) a b ->
  if !debug then log "equa" "%a =!= %a" pp a pp b;
  let rec eq a b = a == b ||
    match (unfold a, unfold b) with
    | (Vari(x)      , Vari(y)      ) -> Bindlib.eq_vars x y
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Symb(Sym(sa)), Symb(Sym(sb))) -> sa == sb
    | (Symb(Def(sa)), Symb(Def(sb))) -> sa == sb
    | (Prod(a,f)    , Prod(b,g)    ) -> eq a b && eq_binder eq f g
    | (Abst(a,f)    , Abst(b,g)    ) -> eq a b && eq_binder eq f g
    | (Appl(_,t,u)  , Appl(_,f,g)  ) -> eq t f && eq u g
    | (_            , PVar(_)      ) -> assert false
    | (PVar(r)      , b            ) -> assert rewrite; r := Some b; true
    | (Unif(r1)     , Unif(r2)     ) when r1 == r2 -> true
    | (Unif(r)      , b            ) -> unify r b
    | (a            , Unif(r)      ) -> unify r a
    | (_            , _            ) -> false
  in
  let res = eq a b in
  if !debug then log "equa" (r_or_g res "%a =!= %a") pp a pp b; res

(**** Evaluatin function (with rewriting) ***********************************)

(* [match_rules s stk] tries to apply the reduction rules of symbol [s]  using
   the stack [stk]. The possible abstract machine states (see [eval_stk]) with
   which to continue are returned. *)
let match_rules : def -> term list -> (term * term list) list = fun s stk ->
  let nb_args = List.length stk in
  let match_rule acc r =
    (* First check that we have enough arguments. *)
    if r.arity > nb_args then acc else
    (* Substitute the left-hand side of [r] with pattern variables *)
    let new_pvar _ = PVar(ref None) in
    let uvars = Array.init (Bindlib.mbinder_arity r.lhs) new_pvar in
    let lhs = Bindlib.msubst r.lhs uvars in
    if !debug_eval then log "eval" "RULE trying rule [%a]" print_rule (s,r);
    (* Match each argument of the lhs with the terms in the stack. *)
    let rec match_args lhs stk =
      match (lhs, stk) with
      | ([]    , stk   ) -> (Bindlib.msubst r.rhs uvars, stk) :: acc
      | (t::lhs, v::stk) ->
          if eq ~rewrite:true t v then match_args lhs stk else acc
      | (_     , _     ) -> assert false
    in
    match_args lhs stk
  in
  List.fold_left match_rule [] !(s.def_rules)

(* [eval_stk t stk] evaluates the term [t] using the stack [stk], which may be
   seen as a list of arguments for [t]. *)
let rec eval_stk : term -> term list -> term = fun t stk ->
  let t = unfold t in
  match (t, stk) with
  (* Evaluate argument and push it to the stack. *)
  | (Appl(false,f,u), stk    ) -> eval_stk f ((eval_stk u []) :: stk)
  (* Beta. *)
  | (Abst(_,f)      , v::stk ) -> eval_stk (Bindlib.subst f v) stk
  (* Try to rewrite. *)
  | (Symb(Def(s))   , stk    ) ->
      begin
        match match_rules s stk with
        | []          ->
            (* No rule applies. *)
            add_args t stk
        | (t,stk)::rs ->
            (* At least one rule applies. *)
            if !debug_eval && rs <> [] then
              wrn "%i rules apply...\n%!" (List.length rs);
            (* Just use the first one. *)
            eval_stk t stk
      end
  (* The head of the term is rigid, mark it as such. *)
  | (Symb(Sym _)    , stk    ) -> add_args ~rigid:true t stk
  (* This application was marked as rigid. *)
  | (Appl(true ,f,u), stk    ) -> add_args ~rigid:true t stk
  (* In head normal form. *)
  | (t              , stk    ) -> add_args t stk

(* [eval t] returns a weak head normal form of [t].  Note that some  arguments
   are evaluated if they might be used to allow the application of a rewriting
   rule. As their evaluation is kept, so this function does more normalisation
   that the usual weak head normalisation. *)
let eval : term -> term = fun t ->
  if !debug_eval then log "eval" "evaluating %a" pp t;
  let u = eval_stk t [] in
  if !debug_eval then log "eval" "produced %a" pp u; u

(**** Equality modulo conversion ********************************************)

(* Representation of equality constraints. *)
type constrs = (term * term) list

(* If [constraints] is set to [None], then typechecking is in regular mode. If
   it is set to [Some(l)] then it is in constraint mode, which means that when
   equality fails, an equality constraint is added to [constrs] instead of the
   equality function giving up. *)
let constraints = ref None

(* NOTE: constraint mode is only used when type-cheching the left-hand side of
   reduction rules (see function [infer_with_constrs] for mode switching). *)

(* [add_constraint a b] adds an equality constraint between [a] and [b] if the
   program is in regular mode. In this case it returns [true].  If the program
   is in regular mode, then [false] is returned immediately. *)
let add_constraint : term -> term -> bool = fun a b ->
  match !constraints with
  | None    -> false
  | Some(l) -> constraints := Some((eval a, eval b)::l); true

(* [eq_module t u] computes the equality of [t] and [u], modulo the conversion
   rule (i.e., the reduction rules for the definable symbols). Unification can
   be triggered by this function as it calls [eq]. *)
let eq_modulo : term -> term -> bool = fun a b ->
  if !debug then log "equa" "%a == %a" pp a pp b;
  let rec eq_mod a b =
    let a = eval a in
    let b = eval b in
    eq a b ||
    match (a, b) with
    | (Vari(x)      , Vari(y)      ) -> Bindlib.eq_vars x y
    | (Type         , Type         ) -> true
    | (Kind         , Kind         ) -> true
    | (Symb(Sym(sa)), Symb(Sym(sb))) -> sa == sb
    | (Symb(Def(sa)), Symb(Def(sb))) -> sa == sb
    | (Prod(a,f)    , Prod(b,g)    ) -> eq_mod a b && eq_binder eq_mod f g
    | (Abst(a,f)    , Abst(b,g)    ) -> eq_mod a b && eq_binder eq_mod f g
    | (Appl(_,t,u)  , Appl(_,f,g)  ) -> eq_mod t f && eq_mod u g
    | (_            , _            ) -> false
  in
  let res = eq a b || eq_mod a b || add_constraint a b in
  if !debug then log "equa" (r_or_g res "%a == %a") pp a pp b; res

(**** Type inference and type-checking **************************************)

(* [infer sign ctx t] tries to infer a type for the term [t], in context [ctx]
   and with the signature [sign].  The exception [Not_found] is raised when no
   suitable type is found. *)
let rec infer : Sign.t -> Ctxt.t -> term -> term = fun sign ctx t ->
  let rec infer ctx t =
    if !debug_infr then log "INFR" "%a ⊢ %a : ?" pp_ctxt ctx pp t;
    let a =
      match unfold t with
      | Vari(x)     -> Ctxt.find x ctx
      | Type        -> Kind
      | Symb(s)     -> symbol_type s
      | Prod(a,b)   ->
          let (x,bx) = Bindlib.unbind mkfree b in
          begin
            match infer (Ctxt.add x a ctx) bx with
            | Kind -> Kind
            | Type -> Type
            | a    -> err "Type or Kind expected for [%a], found [%a]...\n"
                        pp bx pp a;
                      raise Not_found
          end
      | Abst(a,t)   ->
          let (x,tx) = Bindlib.unbind mkfree t in
          let b = infer (Ctxt.add x a ctx) tx in
          Prod(a, Bindlib.unbox (Bindlib.bind_var x (lift b)))
      | Appl(_,t,u) ->
          begin
            match unfold (infer ctx t) with
            | Prod(a,b) when has_type sign ctx u a -> Bindlib.subst b u
            | Prod(a,_)                            ->
                err "Cannot show [%a : %a]...\n" pp u pp a;
                raise Not_found
            | a                                    ->
                err "Product expected for [%a], found [%a]...\n" pp t pp a;
                raise Not_found
          end
      | Kind        -> assert false
      | Unif(_)     -> assert false
      | PVar(_)     -> assert false
    in
    if !debug_infr then log "INFR" "%a ⊢ %a : %a" pp_ctxt ctx pp t pp a;
    eval a
  in
  if !debug then log "infr" "%a ⊢ %a : ?" pp_ctxt ctx pp t;
  let res = infer ctx t in
  if !debug then log "infr" "%a ⊢ %a : %a" pp_ctxt ctx pp t pp res; res

(* [has_type sign ctx t a] checks whether the term [t] has type [a] in context
   [ctx] and with the signature [sign]. *)
and has_type : Sign.t -> Ctxt.t -> term -> term -> bool = fun sign ctx t a ->
  let rec has_type ctx t a =
    let t = unfold t in
    let a = eval a in
    if !debug_type then log "TYPE" "%a ⊢ %a : %a" pp_ctxt ctx pp t pp a;
    match (t, a) with
    (* Sort *)
    | (Type     , Kind     ) -> true
    (* Variable *)
    | (Vari(x)  , a        ) -> eq_modulo (Ctxt.find x ctx) a
    (* Symbol *)
    | (Symb(s)  , a        ) -> eq_modulo (symbol_type s) a
    (* Product *)
    | (Prod(a,b), Type     ) ->
        let (x,bx) = Bindlib.unbind mkfree b in
        let ctx_x =
          if Bindlib.binder_occur b then Ctxt.add x a ctx else ctx
        in
        has_type ctx a Type && has_type ctx_x bx Type
    (* Product 2 *)
    | (Prod(a,b), Kind     ) ->
        let (x,bx) = Bindlib.unbind mkfree b in
        let ctx_x =
          if Bindlib.binder_occur b then Ctxt.add x a ctx else ctx
        in
        has_type ctx a Type && has_type ctx_x bx Kind
    (* Abstraction and Abstraction 2 *)
    | (Abst(a,t), Prod(c,b)) ->
        let (x,tx) = Bindlib.unbind mkfree t in
        let bx = Bindlib.subst b (mkfree x) in
        let ctx_x = Ctxt.add x a ctx in
        eq_modulo a c && has_type ctx a Type
        && (has_type ctx_x bx Type || has_type ctx_x bx Kind)
        && has_type ctx_x tx bx
    (* Application *)
    | (Appl(_,t,u), b      ) ->
        begin
          match infer sign ctx t with
          | Prod(a,ba) as tt ->
              eq_modulo (Bindlib.subst ba u) b
              && has_type ctx t tt && has_type ctx u a
          | Unif(r)    as tt ->
              let a = Bindlib.box (Unif(ref None)) in
              r := Some (Bindlib.unbox (_Prod a "_" (fun _ -> lift b)));
              has_type ctx t tt && has_type ctx u (Bindlib.unbox a)
          | _                -> false
        end
    (* No rule apply. *)
    | (_        , _        ) -> false
  in
  if !debug then log "type" "%a ⊢ %a : %a" pp_ctxt ctx pp t pp a;
  let res = has_type ctx t a in
  if !debug then log "type" (r_or_g res "%a ⊢ %a : %a") pp_ctxt ctx pp t pp a;
  res

(**** Handling of constraints for typing rewriting rules ********************)

(* [infer_with_constrs sign ctx t] is similar to [infer sign ctx t], but it is
   run in constraint mode (see [constraints]).  In case of success a couple of
   a type and a set of constraints is returned. In case of failure [Not_found]
   is raised. *)
let infer_with_constrs : Sign.t -> Ctxt.t -> term -> term * constrs =
  fun sign ctx t ->
    constraints := Some [];
    let a = infer sign ctx t in
    let cnstrs = match !constraints with Some cs -> cs | None -> [] in
    constraints := None;
    if !debug_patt then
      begin
        log "patt" "inferred type [%a] for [%a]" pp a pp t;
        let fn (x,a) =
          log "patt" "  with\t%s\t: %a" (Bindlib.name_of x) pp a
        in
        List.iter fn ctx;
        let fn (a,b) = log "patt" "  where\t%a == %a" pp a pp b in
        List.iter fn cnstrs
      end;
    (a, cnstrs)

(* [subst_from_constrs cs] builds a //typing substitution// from the  list  of
   constraints [cs].  The returned substitution is given by a couple of arrays
   [(xs,ts)] of the same length. The array [ts] contains the terms that should
   be substituted to the corresponding variables of [xs]. *)
let subst_from_constrs : constrs -> tvar array * term array = fun cs ->
  let rec build_sub acc cs =
    match cs with
    | []        -> acc
    | (a,b)::cs ->
        let (ha,argsa) = get_args a in
        let (hb,argsb) = get_args b in
        match (unfold ha, unfold hb) with
        | (Symb(Sym(sa)), Symb(Sym(sb))) when sa == sb ->
            let cs =
              try List.combine argsa argsb @ cs with Invalid_argument _ -> cs
            in
            build_sub acc cs
        | (Symb(Def(sa)), Symb(Def(sb))) when sa == sb ->
            wrn "%s may not be injective...\n%!" sa.def_name;
            build_sub acc cs
        | (Vari(x)      , _            ) when argsa = [] ->
            build_sub ((x,b)::acc) cs
        | (_            , Vari(x)      ) when argsb = [] ->
            build_sub ((x,a)::acc) cs
        | (a            , b            ) ->
            wrn "Not implemented [%a] [%a]...\n%!" pp a pp b;
            build_sub acc cs
  in
  let sub = build_sub [] cs in
  (Array.of_list (List.map fst sub), Array.of_list (List.map snd sub))

(* [eq_modulo_constrs cs t u] checks if [t] and [u] are equal modulo rewriting
   given a list of constraints [cs] (assumed to be all satisfied). *)
let eq_modulo_constrs : constrs -> term -> term -> bool =
  fun constrs a b -> eq_modulo a b ||
    let (xs,sub) = subst_from_constrs constrs in
    let p = Bindlib.box_pair (lift a) (lift b) in
    let p = Bindlib.unbox (Bindlib.bind_mvar xs p) in
    let (a,b) = Bindlib.msubst p sub in
    eq_modulo a b

(**** Parser for terms (and types) ******************************************)

(* Parser-level representation of terms (and patterns). *)
type p_term =
  | P_Vari of string list * string
  | P_Type
  | P_Prod of string * p_term * p_term
  | P_Abst of string * p_term option * p_term
  | P_Appl of p_term * p_term
  | P_Wild

(* NOTE: the [P_Vari] constructor is used for variables (with an empty  module
   path) and for symbols.  The [P_Wild] corresponds to a wildard,  when a term
   is considered as a pattern. *)

(* [ident] is an atomic parser for an identifier (for example, variable name).
   It accepts (and returns as its semantic value) any non-empty strings formed
   of letters,  decimal digits, and the ['_'] and ['''] characters.  Note that
   ["Type"] and ["_"] are reserved identifiers, and they are thus rejected. *)
let parser ident = id:''[_'a-zA-Z0-9]+'' ->
  if List.mem id ["Type"; "_"] then Earley.give_up (); id

(* [qident] is an atomic parser for a qualified identifier (e.g. an identifier
   that may be preceeded by a module path. The different parts of the path and
   the identifier are build as for [ident] and separated by a ['.']. *)
let parser qident = id:''\([_'a-zA-Z0-9]+[.]\)*[_'a-zA-Z0-9]+'' ->
  let fs = List.rev (String.split_on_char '.' id) in
  let (fs,x) = (List.rev (List.tl fs), List.hd fs) in
  if List.mem id ["Type"; "_"] then Earley.give_up (); (fs,x)

(* [_wild_] is an atomic parser for the special ["_"] identifier. Note that it
   is only accepted if it is not followed by an identifier character. *)
let parser _wild_ = s:''[_][_a-zA-Z0-9]*'' ->
  if s <> "_" then Earley.give_up ()

(* [_Type_] is an atomic parser for the special ["Type"] identifier. Note that
   it is only accepted when it is not followed an identifier character. *)
let parser _Type_ = s:''[T][y][p][e][_a-zA-Z0-9]*'' ->
  if s <> "Type" then Earley.give_up ()

(* [expr p] is a parser for an expression at priority [p]. *)
let parser expr (p : [`Func | `Appl | `Atom]) =
  (* Variable *)
  | (fs,x):qident
      when p = `Atom -> P_Vari(fs,x)
  (* Type constant *)
  | _Type_
      when p = `Atom -> P_Type
  (* Product *)
  | x:{ident ":"}?["_"] a:(expr `Appl) "->" b:(expr `Func)
      when p = `Func -> P_Prod(x,a,b)
  (* Wildcard *)
  | _wild_
      when p = `Atom -> P_Wild
  (* Abstraction *)
  | x:ident a:{":" (expr `Func)}? "=>" t:(expr `Func)
      when p = `Func -> P_Abst(x,a,t)
  (* Application *)
  | t:(expr `Appl) u:(expr `Atom)
      when p = `Appl -> P_Appl(t,u)
  (* Parentheses *)
  | "(" t:(expr `Func) ")"
      when p = `Atom
  (* Coercions *)
  | t:(expr `Appl)
      when p = `Func
  | t:(expr `Atom)
      when p = `Appl

(* [expr] is the entry point of the parser for expressions, including terms as
   well as types and patterns. *)
let expr = expr `Func

(**** Parser for toplevel items *********************************************)

(* Representation of a toplevel item (symbol definition, command, ...). *)
type p_item =
  (* New symbol (static or definable). *)
  | NewSym of bool * string * p_term
  (* New rewriting rules. *)
  | Rules  of ((string * p_term option) list * p_term * p_term) list
  (* New definable symbol with its definition. *)
  | Defin  of string * p_term option * p_term
  (* Commands. *)
  | Check  of p_term * p_term
  | Infer  of p_term
  | Eval   of p_term
  | Conv   of p_term * p_term
  | Name   of string
  | Step   of p_term

(* [ty_ident] is a parser for an (optionally) typed identifier. *)
let parser ty_ident = id:ident a:{":" expr}?

(* [context] is a parser for a rewriting rule context. *)
let parser context = {x:ty_ident xs:{"," ty_ident}* -> x::xs}?[[]]

(* [rule] is a parser for a single rewriting rule. *)
let parser rule = "[" xs:context "]" t:expr "-->" u:expr

(* [def_def] is a parser for one specifc syntax of symbol definition. *)
let parser def_def = xs:{"(" ident ":" expr ")"}* ":=" t:expr ->
  List.fold_right (fun (x,a) t -> P_Abst(x, Some(a), t)) xs t

(* [toplevel] parses a single toplevel item. *)
let parser toplevel =
  | x:ident ":" a:expr                      -> NewSym(false,x,a)
  | "def" x:ident ":" a:expr                -> NewSym(true ,x,a)
  | "def" x:ident ":" a:expr ":=" t:expr    -> Defin(x,Some(a),t)
  | "def" x:ident t:def_def                 -> Defin(x,None   ,t)
  | rs:rule+                                -> Rules(rs)
  | "#CHECK" t:expr "," a:expr              -> Check(t,a)
  | "#INFER" t:expr                         -> Infer(t)
  | "#EVAL" t:expr                          -> Eval(t)
  | "#CONV" t:expr "," u:expr               -> Conv(t,u)
  | "#NAME" id:ident                        -> Name(id)
  | "#STEP" t:expr                          -> Step(t)
  | "#SNF"  t:expr                          -> Eval(t)

(* [full] is the main entry point of the parser. It accepts a list of toplevel
   items, each teminated by a ['.']. *)
let parser full = {l:toplevel "."}*

(**** Main parsing functions ************************************************)

(** Blank function for basic blank characters (' ', '\t', '\r' and '\n')
    and line comments starting with "//". *)
let blank buf pos =
  let rec fn state prev ((buf0, pos0) as curr) =
    let open Input in
    let (c, buf1, pos1) = read buf0 pos0 in
    let next = (buf1, pos1) in
    match (state, c) with
    (* Basic blancs. *)
    | (`Ini, ' '   )
    | (`Ini, '\t'  )
    | (`Ini, '\r'  )
    | (`Ini, '\n'  ) -> fn `Ini curr next
    (* Opening comment. *)
    | (`Ini, '('   ) -> fn `Opn curr next
    | (`Opn, ';'   ) -> fn `Com curr next
    (* Closing comment. *)
    | (`Com, ';'   ) -> fn `Cls curr next
    | (`Cls, ')'   ) -> fn `Ini curr next
    | (`Cls, _     ) -> fn `Com curr next
    (* Other. *)
    | (`Com, '\255') -> fatal "Unclosed comment...\n"
    | (`Com, _     ) -> fn `Com curr next
    | (`Opn, _     ) -> prev
    | (`Ini, _     ) -> curr
  in
  fn `Ini (buf, pos) (buf, pos)

(* [parse_file fname] attempts to parse the file [fname],  to obtain a list of
   toplevel items. In case of failure, a standard parse error message is shown
   and then [exit 1] is called. *)
let parse_file : string -> p_item list =
  Earley.(handle_exception (parse_file full blank))

(**** Earley compilation / module support ***********************************)

(* [!compile_ref modpath] compiles the module corresponding to the module path
   [modpath], if necessary. This function is stored in a reference as we can't
   define it yet (we could alternatively use mutual definitions). *)
let compile_ref : (string list -> Sign.t) ref = ref (fun _ -> assert false)

(* [loaded] is a hashtable associating module paths to signatures. A signature
   will be mapped to a given module path only if it was already compiled. *)
let loaded : (string list, Sign.t) Hashtbl.t = Hashtbl.create 7

(* [load_signature modpath] returns the signature corresponding to the  module
   path [modpath].  Note that compilation may be required if this is the first
   time that the corresponding module is required. *)
let load_signature : string list -> Sign.t = fun modpath ->
  try Hashtbl.find loaded modpath with Not_found ->
    let sign = !compile_ref modpath in
    Hashtbl.add loaded modpath sign; sign

(**** Scoping ***************************************************************)

(* Representation of an environment for variables. *)
type env = (string * tvar) list

(* [scope new_wildcard env sign t] transforms the parsing level term [t]  into
   an actual term, using the free variables of the environement [env], and the
   symbols of the signature [sign].  If a function is given in [new_wildcard],
   then it is called on [P_Wild] nodes. This will only be allowed when reading
   a term as a pattern. *)
let scope : (unit -> tbox) option -> env -> Sign.t -> p_term -> tbox =
  fun new_wildcard vars sign t ->
    let rec scope vars t =
      match t with
      | P_Vari([],x)  ->
          begin
            try Bindlib.box_of_var (List.assoc x vars) with Not_found ->
            try _Symb_find sign x with Not_found ->
            fatal "Unbound variable or symbol %S...\n%!" x
          end
      | P_Vari(fs,x)  ->
          begin
            try _Symb_find (load_signature fs) x with Not_found ->
              let x = String.concat "." (fs @ [x]) in
              fatal "Unbound symbol %S...\n%!" x
          end
      | P_Type        -> _Type
      | P_Prod(x,a,b) ->
          let f v = scope (if x = "_" then vars else (x,v)::vars) b in
          _Prod (scope vars a) x f
      | P_Abst(x,a,t) ->
          let f v = scope ((x,v)::vars) t in
          let a =
            match a with
            | None    -> Bindlib.box (Unif(ref None))
            | Some(a) -> scope vars a
          in
          _Abst a x f
      | P_Appl(t,u)   -> _Appl (scope vars t) (scope vars u)
      | P_Wild        ->
          match new_wildcard with
          | None    -> fatal "\"_\" not allowed in terms...\n"
          | Some(f) -> f ()
    in
    scope vars t

 (* [to_tbox ~vars sign t] is a convenient interface for [scope]. *)
let to_tbox : ?vars:env -> Sign.t -> p_term -> tbox =
  fun ?(vars=[]) sign t -> scope None vars sign t

(* [to_term ~vars sign t] composes [to_tbox] with [Bindlib.unbox]. *)
let to_term : ?vars:env -> Sign.t -> p_term -> term =
  fun ?(vars=[]) sign t -> Bindlib.unbox (scope None vars sign t)

(* Representation of a pattern as a head symbol, list of argument and array of
   variables corresponding to wildcards. *)
type patt = def * tbox list * tvar array

(* [to_patt env sign t] transforms the parsing level term [t] into a  pattern.
   Note that here, [t] may contain wildcards. The function also checks that it
   has a definable symbol as a head term, and gracefully fails otherwise. *)
let to_patt : env -> Sign.t -> p_term -> patt = fun vars sign t ->
  let wildcards = ref [] in
  let counter = ref 0 in
  let new_wildcard () =
    let x = "#" ^ string_of_int !counter ^ "#" in
    let x = Bindlib.new_var mkfree x in
    incr counter; wildcards := x :: !wildcards; Bindlib.box_of_var x
  in
  let t = Bindlib.unbox (scope (Some new_wildcard) vars sign t) in
  let (head, args) = get_args t in
  match head with
  | Symb(Def(s)) -> (s, List.map lift args, Array.of_list !wildcards)
  | Symb(Sym(s)) -> fatal "%s is not a definable symbol...\n" s.sym_name
  | _            -> fatal "%a is not a valid pattern...\n" pp t

(**** Interpretation of commands ********************************************)

(* TODO cleaning and comments from here... *)

let check_rule sign (xs,t,u) =
  let xs = List.map fst xs in (* FIXME keep type annotation. *)
  (* Scoping the LHS and RHS. *)
  let vars = List.map (fun x -> (x, Bindlib.new_var mkfree x)) xs in
  let (s, l, wcs) = to_patt vars sign t in
  let arity = List.length l in
  let l = Bindlib.box_list l in
  let u = to_tbox ~vars sign u in
  (* Building the definition. *)
  let xs = Array.append (Array.of_list (List.map snd vars)) wcs in
  let lhs = Bindlib.unbox (Bindlib.bind_mvar xs l) in
  let rhs = Bindlib.unbox (Bindlib.bind_mvar xs u) in
  (* Constructing the typing context and the terms. *)
  let xs = Array.to_list xs in
  let ctx = List.map (fun x -> (x, Unif(ref None))) xs in
  let u = Bindlib.unbox u in
  (* Check that the LHS is a pattern and build the rule. *)
  let rule = { lhs ; rhs ; arity } in
  let t = add_args (Symb(Def s)) (Bindlib.unbox l) in
  (* Infer the type of the LHS and the constraints. *)
  let (tt, tt_constrs) =
    try infer_with_constrs sign ctx t with Not_found ->
      fatal "Unable to infer the type of [%a]\n" pp t
  in
  (* Infer the type of the RHS and the constraints. *)
  let (tu, tu_constrs) =
    try infer_with_constrs sign ctx u with Not_found ->
      fatal "Unable to infer the type of [%a]\n" pp u
  in
  (* Checking the implication of constraints. *)
  let check_constraint (a,b) =
    if not (eq_modulo_constrs tt_constrs a b) then
      fatal "A constraint is not satisfied...\n"
  in
  List.iter check_constraint tu_constrs;
  (* Checking if the rule is well-typed. *)
  if not (eq_modulo_constrs tt_constrs tt tu) then
    begin
      err "Infered type for LHS: %a\n" pp tt;
      err "Infered type for RHS: %a\n" pp tu;
      fatal "[%a → %a] is ill-typed\n" pp t pp u
    end;
  (s,t,u,rule)

let handle_item : Sign.t -> p_item -> unit = fun sign it ->
  match it with
  | NewSym(d,x,a) ->
      let a = to_term sign a in
      let sort =
        if has_type sign Ctxt.empty a Type then "Type" else
        if has_type sign Ctxt.empty a Kind then "Kind" else
        fatal "%s is neither of type Type nor Kind.\n" x
      in
      let kind = if d then "defi" else "symb" in
      out "(%s) %s : %a (of sort %s)\n" kind x pp a sort;
      if d then ignore (Sign.new_definable sign x a)
      else ignore (Sign.new_static sign x a)
  | Defin(x,a,t) ->
      let t = to_term sign t in
      let a =
        match a with
        | None   -> infer sign Ctxt.empty t
        | Some a -> to_term sign a
      in
      let sort =
        if has_type sign Ctxt.empty a Type then "Type" else
        if has_type sign Ctxt.empty a Kind then "Kind" else
        fatal "%s is neither of type Type nor Kind.\n" x
      in
      out "(defi) %s : %a (of sort %s)\n" x pp a sort;
      if not (has_type sign Ctxt.empty t a) then
        fatal "Cannot type the definition of %s...\n" x;
      let s = Sign.new_definable sign x a in
      out "(rule) %s → %a\n" (symbol_name (Def(s))) pp t;
      let rule =
        let lhs = Bindlib.mbinder_from_fun [||] (fun _ -> []) in
        let rhs = Bindlib.mbinder_from_fun [||] (fun _ -> t) in
        {arity = 0; lhs ; rhs}
      in
      s.def_rules := !(s.def_rules) @ [rule]
  | Rules(rs)     ->
      (* Adding all the rules. *)
      let add_rule (s,t,u,rule) =
        out "  - %a → %a\n" pp t pp u;
        s.def_rules := !(s.def_rules) @ [rule]
      in
      out "(rule) Adding the rules:\n";
      List.iter add_rule (List.map (check_rule sign) rs)
  | Check(t,a)    ->
      let t = to_term sign t in
      let a = to_term sign a in
      if has_type sign Ctxt.empty t a then out "(chck) %a : %a\n" pp t pp a
      else fatal "%a does not have type %a...\n" pp t pp a
  | Infer(t)      ->
      let t = to_term sign t in
      begin
        try out "(infr) %a : %a\n" pp t pp (infer sign Ctxt.empty t)
        with Not_found -> fatal "%a : unable to infer\n%!" pp t
      end
  | Eval(t)       ->
      out "(eval) %a\n" pp (eval (to_term sign t))
  | Conv(t,u)     ->
      let t = to_term sign t in
      let u = to_term sign u in
      if eq_modulo t u then out "(conv) OK\n"
      else fatal "cannot convert %a and %a...\n" pp t pp u
  | Name(_)       -> if !debug then wrn "#NAME directive not implemented.\n"
  | Step(_)       -> if !debug then wrn "#STEP directive not implemented.\n"

(* TODO cleaning and comments until here... *)

(* [handle_file sign fname] parses and interprets the file [fname] with [sign]
   as its signature. All exceptions are handled, and errors lead to (graceful)
   failure of the whole program. *)
let handle_file : Sign.t -> string -> unit = fun sign fname ->
  try List.iter (handle_item sign) (parse_file fname)
  with e -> fatal "Uncaught exception...\n%s\n%!" (Printexc.to_string e)

(**** Main compilation functions ********************************************)

(* [compile force modpath] compiles the file correspinding to the module  path
   [modpath] if it is necessary, or if [force] is [true] ([force] is typically
   used to force the compilation of the files given on the command line). Note
   that the produced signature is registered in [loaded] before being returned
   and it is also stored into an object file. *)
let compile : bool -> string list -> Sign.t = fun force modpath ->
  let base = String.concat "/" modpath in
  let src = base ^ src_extension in
  let obj = base ^ obj_extension in
  if not (Sys.file_exists src) then fatal "File not found: %s\n" src;
  if more_recent src obj || force then
    begin
      out "Loading file [%s]\n%!" src;
      let sign = Sign.create modpath in
      Hashtbl.add loaded modpath sign;
      handle_file sign src;
      Sign.write sign obj;
      out "Done with file [%s]\n%!" src; sign
    end
  else Sign.read obj

(* Setting the compilation function since it is now available. *)
let _ = compile_ref := compile false

(* [compile fname] compile the source file [fname], marking it as the  current
   module (see [current_module]). Note that compilation is forced, even if the
   file has already been compiled. *)
let compile fname =
  let modpath = module_path fname in
  current_module := modpath;
  ignore (compile true modpath)

(**** Main program, handling of command line arguments **********************)

let _ =
  let usage = Sys.argv.(0) ^ " [--debug [a|e|i|p|t]] [--quiet] [FILE] ..." in
  let flags =
    [ "a : general debug informations"
    ; "e : extra debugging informations for equality"
    ; "i : extra debugging informations for inference"
    ; "p : extra debugging informations for patterns"
    ; "t : extra debugging informations for typing" ]
  in
  let flags = List.map (fun s -> String.make 18 ' ' ^ s) flags in
  let flags = String.concat "\n" flags in
  let spec =
    [ ("--debug", Arg.String set_debug, "<str> Set debugging mode:\n" ^ flags)
    ; ("--quiet", Arg.Set quiet       , " Disable output") ]
  in
  let files = ref [] in
  let anon fn = files := fn :: !files in
  Arg.parse (Arg.align spec) anon usage;
  List.iter compile (List.rev !files)
