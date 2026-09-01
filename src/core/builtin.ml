(** Registering and checking builtin symbols. *)

open Lplib open Base open Extra
open Timed
open Common open Error open Pos
open Term
open Sig_state
open Sign

(** [get ss pos path name] returns the symbol mapped to the builtin [name] in
    [path] if any. If the symbol cannot be found then [Fatal] is raised. *)
let get : sig_state -> popt -> Path.t -> string -> sym =
  fun ss pos p s ->
  match p with
  | [] -> (* Symbol in scope. *)
      begin
        try StrMap.find s ss.builtins
        with Not_found -> fatal pos "Unknown builtin \"%s\"." s
      end
  | [m] when StrMap.mem m ss.alias_path -> (* Aliased module path. *)
      begin
        (* The signature must be loaded (alias is mapped). *)
        let sign =
          try Path.Map.find (StrMap.find m ss.alias_path) !loaded
          with _ -> assert false (* Should not happen. *)
        in
        (* Look for the symbol. *)
        try StrMap.find s !(sign.sign_builtins) with Not_found ->
          fatal pos "Unknown builtin \"%a.%s\"." Path.pp p s
      end
  | _  -> (* Fully-qualified symbol. *)
      begin
        (* Check that the signature was required (or is the current one). *)
        if p <> ss.signature.sign_path then
          if not (Path.Map.mem p !(ss.signature.sign_deps)) then
            fatal pos "No module %a required." Path.pp p;
        (* The signature must have been loaded. *)
        let sign =
          try Path.Map.find p !loaded
          with Not_found -> assert false (* Should not happen. *)
        in
        (* Look for the symbol. *)
        try StrMap.find s !(sign.sign_builtins) with Not_found ->
          fatal pos "Unknown builtin \"%a.%s\"." Path.pp p s
      end

(** [get_opt ss name] returns [Some s] where [s] is the symbol mapped to
   the builtin [name], and [None] otherwise. *)
let get_opt : sig_state -> string -> sym option = fun ss name ->
  try Some (StrMap.find name ss.builtins) with Not_found -> None

(** Type of functions checking the validity of a builtin symbol in a given
    signature state. The [pos] argument is used for error reporting. *)
type check = sig_state -> popt -> sym -> unit

let no_check _ _ _ = ()

(** Hash-table used to record checking functions for builtins. *)
let htbl : (string, check) Hashtbl.t = Hashtbl.create 17

(** [check name] returns the registered check function for [name]. *)
let check (name:string): check =
  try Hashtbl.find htbl name
  with Not_found ->
    fatal_msg "Bug: undeclared builtin \"%s\".@." name; assert false

(** [register name check] registers the checking function [check], for the
   builtin symbols named [name]. When the check is run, [check] receives as
   argument a position for error reporting as well as the map of every builtin
   symbol in scope. It is expected to raise the [Fatal] exception to signal an
   error. Note that this function should not be called using a [name] for
   which a check has already been registered. *)
let register (name:string) (check:check): unit =
  if Hashtbl.mem htbl name then
    (fatal_msg "Bug: builtin \"%s\" already declared.@." name; assert false)
  else Hashtbl.add htbl name check

(** [register_expected_type name build pp] registers a checking function that
   checks the type of a symbol defining the builtin [name] against a type
   constructed using the given [build] function. *)
let register_expected_type
    : term eq -> term pp -> string -> (sig_state -> popt -> term) -> unit =
  fun eq pp name mk_type ->
  let check ss pos sym =
    let actual = !(sym.sym_type) in
    let expected = mk_type ss pos in
    if not (eq actual expected) then
      fatal pos "%a is not convertible to %a." pp actual pp expected
  in
  register name check

(** Declare and check the types of builtins. *)
module M = struct

type t = {state:sig_state; pos:popt}

let mk_config ss pos = {state = ss; pos}

let builtin s c = mk_Symb (get c.state c.pos [] s)

(* String builtin. *)
let str = builtin "String"
let _ = register "String" no_check

(* Builtins for decimal notation. *)
let _ =
  register "+1" no_check;
  register "0" no_check;
  register "1" no_check;
  register "2" no_check;
  register "3" no_check;
  register "4" no_check;
  register "5" no_check;
  register "6" no_check;
  register "7" no_check;
  register "8" no_check;
  register "9" no_check;
  register "10" no_check;
  register "+" no_check;
  register "*" no_check;
  register "pos_one" no_check;
  register "pos_double" no_check;
  register "pos_succ_double" no_check;
  register "int_zero" no_check;
  register "int_positive" no_check;
  register "int_negative" no_check;
  register "-" no_check

let typ _c = mk_Type
let arr f g c = mk_Arro(f c, g c)
let app f g c = mk_Appl(f c, g c)
let var x _c = mk_Vari x
let prod f g c = mk_Prod(f c, let x = new_var "x" in bind_var x (g x c))

let apps = List.fold_left app

let register_typ s f =
  register_expected_type (Eval.eq_modulo []) Print.term
    s (fun ss pos -> f (mk_config ss pos))

(* Prop and P builtins. *)
let prop = builtin "Prop"
let prf = builtin "Prf"

let _ =
  register_typ "Prop" typ;
  register_typ "Prf" (arr prop typ)

(* Set and T builtins. *)
let set = builtin "Set"
let elt = app (builtin "El")

let _ =
  register_typ "Set" typ;
  register_typ "El" (arr set typ)

(* Additional builtins for why3 tactic. *)
let _ =
  let unary = arr prop prop in
  let binary = arr prop unary in
  (* Π a:Set, (El a → Prop) → Prop *)
  let quant = prod set (fun a -> arr (arr (elt (var a)) prop) prop) in
  register_typ "bot" prop;
  register_typ "top" prop;
  register_typ "not" unary;
  register_typ "or" binary;
  register_typ "and" binary;
  register_typ "imp" binary;
  register_typ "eqv" binary;
  register_typ "ex" quant;
  register_typ "all" quant

(* Additional builtins for rewrite tactic. *)
let eq = builtin "eq"

let _ =
  (* Π a:Set, El a → El a → Prop *)
  register_typ "eq"
    (prod set (fun a -> arr (elt (var a)) (arr (elt (var a)) prop)));
  (* Π a:Set, Π x:El a, Prf (eq a x x) *)
  register_typ "refl"
    (prod set (fun a ->
         prod (elt (var a)) (fun x ->
             app prf (apps eq [var a; var x; var x]))));
  (* Π a:Set, Π x:El a, Π y:El a, Prf (eq a x y) → Π p:T a → Prop,
     Prf (p y) → Prf (p x) *)
  register_typ "eqind"
    (prod set (fun a ->
         prod (elt (var a)) (fun x ->
             prod (elt (var a)) (fun y ->
                 arr (app prf (apps eq [var a; var x; var y]))
                   (prod (arr (elt (var a)) prop) (fun p ->
                        arr (app prf (app (var p) (var y)))
                          (app prf (app (var p) (var x)))))))))

(* Additional builtins for eval tactic. *)
let tac = builtin "Tactic"
let lvl = builtin "Level"
let univ = app (builtin "Univ")
let eps l u = app (app (builtin "Type") l) u

let _ =
  register_typ "Level" typ;
  register_typ "Univ" (arr lvl typ);
  register_typ "Type" (prod lvl (fun l -> arr (univ (var l)) typ));
  register_typ "Tactic" typ;
  let t1 =
    prod lvl (fun l ->
        prod (univ (var l)) (fun a ->
            arr (eps (var l) (var a)) tac))
  in
  let t2 =
    prod lvl (fun l ->
        prod (univ (var l)) (fun a ->
            arr (arr (eps (var l) (var a)) tac) tac))
  in
  register_typ "admit" tac;
  register_typ "all_hyps" (arr t1 tac);
  register_typ "apply" t1;
  register_typ "assume" (arr str t2);
  register_typ "assumption" tac;
  register_typ "change" t1;
  register_typ "compose" (arr tac (arr tac tac));
  register_typ "fail" tac;
  register_typ "first_hyp" (arr t1 tac);
  register_typ "focus" (arr str tac);
  register_typ "generalize" t1;
  register_typ "have" (arr str t1);
  register_typ "induction" tac;
  register_typ "orelse" (arr tac (arr tac tac));
  register_typ "print" (arr str tac);
  register_typ "refine" (arr str tac);
  register_typ "reflexivity" tac;
  register_typ "remove" t1;
  register_typ "repeat" (arr tac tac);
  register_typ "rewrite" (arr str (arr str t1));
  register_typ "set" (arr str t1);
  register_typ "simplify" tac;
  register_typ "simplify rule off" tac;
  register_typ "solve" tac;
  register_typ "symmetry" tac;
  register_typ "try" (arr tac tac);
  register_typ "why3" tac

end
