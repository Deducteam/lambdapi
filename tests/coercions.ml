open Common
open Parsing
open Core
open Handle

let parse_term s =
  (* A hack to parse a term: wrap term [s] into [compute s;]. *)
  let c = "compute " ^ s ^ ";" in
  let command = (Stream.next (Parser.Lp.parse_string "term" c)) in
  match command.elt with
  | Syntax.P_query {elt=Syntax.P_query_normalize (t, _); _} -> t
  | _ -> assert false

let scope_term ss t =
  Scope.scope_term true ss [] (lazy Lplib.Extra.IntMap.empty) t

(** [compile_ast s ast] compiles abstract syntax tree [ast] using module path
    [s] and returns the signature state.*)
let compile_ast s ast =
  let mp = Path.of_string s in
  Timed.(Sign.loading := mp :: !Sign.loading);
  let sign = Sig_state.create_sign mp in
  let ss = ref (Sig_state.of_sign sign) in
  Timed.(Sign.loaded := Path.Map.add mp sign !Sign.loaded);
  let consume cmd =
    Stdlib.(ss := Command.handle (fun _ -> assert false) !ss cmd)
  in
  Stream.iter consume ast;
  !ss

let simple_coercion = {|
  constant symbol A : TYPE;
  constant symbol a : A;
  constant symbol B : TYPE;
  constant symbol c : A → B;
  constant symbol f : B → B;
|} |> Parser.Lp.parse_string "simple_coercion"

(* The simplest coercion problem possible [a : A == B] with [c : A -> B]
   defined. *)
let simple () =
  let sig_st = compile_ast "simple" simple_coercion in
  let coercion =
    let defn = parse_term "c" |> scope_term sig_st in
    let defn_ty = parse_term "A → B" |> scope_term sig_st in
    Infer.{ name = "a2b"; precoercions = []; source = 1; arity = 0;
            defn; defn_ty }
  in
  let module Infer: Infer.S =
    Infer.Make(struct
      let coercions = [coercion]
      let solve pb = Unif.solve_noexn pb
    end)
  in
  let f_a = parse_term "f a" |> scope_term sig_st in
  let f_a_c = parse_term "f (c a)" |> scope_term sig_st in
  let f_a', _ = Infer.infer [] (Pos.none f_a) in
  Alcotest.(check bool)
    "f a = f (c a)"
    (Rewrite.eq [] f_a' f_a_c) true

let simple = Timed.pure_apply simple

let el_coercion = {|
  constant symbol Set : TYPE;
  injective symbol El : Set → TYPE;
  constant symbol ι : Set;
|} |> Parser.Lp.parse_string "element_coercion"

(* Coercion from value to type [a : Set == TYPE] *)
let element () =
  let sig_st = compile_ast "element" el_coercion in
  let coercion =
    let defn = parse_term "El" |> scope_term sig_st in
    let defn_ty = parse_term "Set → TYPE;" |> scope_term sig_st in
    Infer.{ name = "set2ty"; precoercions = []; source = 1; arity = 0;
            defn; defn_ty }
  in
  let module Infer: Infer.S =
    Infer.Make(struct
      let coercions = [coercion]
      let solve pb = Unif.solve_noexn pb
    end)
  in
  let iota_to_type = parse_term "ι → TYPE" |> scope_term sig_st in
  let el_iota_to_type = parse_term "El ι → TYPE" |> scope_term sig_st in
  let iota_to_type', _ = Infer.infer [] (Pos.none iota_to_type) in
  Alcotest.(check bool)
    "ι → TYPE = El ι → TYPE"
    (Rewrite.eq [] iota_to_type' el_iota_to_type) true

let element = Timed.pure_apply element

let lists_vecs = {|
constant symbol Set : TYPE;
injective symbol El : Set → TYPE;
constant symbol nat : Set;
constant symbol z : El nat;
constant symbol s : El nat → El nat;
constant symbol list : Set → Set;
constant symbol nil (t: Set) : El (list t);
constant symbol cons {t: Set} : El t → El (list t) → El (list t);
symbol length {t: Set}: El (list t) → El nat;
rule @length _ (nil _) ↪ z
with @length _ (@cons _ _ $l) ↪ s (length $l);
constant symbol vec : El nat → Set → Set;
constant symbol vnil (t : Set) : El (vec z t);
constant symbol vcons {t: Set} {n: El nat} :
  El t → El (vec n t) → El (vec (s n) t);

constant symbol lv (l: El (list nat)): El (vec (@length nat l) nat);

constant symbol f_v {t: Set} {n: El nat}: El (vec n t) → El nat;
|} |> Parser.Lp.parse_string "lists_vecs"

let dependent () =
  let sig_st = compile_ast "lists_vecs" lists_vecs in
  let coercion =
    let defn = parse_term "lv" |> scope_term sig_st in
    let defn_ty = parse_term "Π l: El (list nat), El (vec (length l) nat)" |> scope_term sig_st in
    Infer.{ name = "list2vec"; precoercions = []; source = 1; arity = 0; defn; defn_ty }
  in
  let module Infer: Infer.S =
    Infer.Make(struct
      let coercions = [coercion]
      let solve pb = Unif.solve_noexn pb
    end)
  in
  Timed.(Print.print_implicits :=  true);
  let f_v_list = parse_term "f_v (cons z (nil nat))" |> scope_term sig_st in
  let f_v_vec = parse_term "f_v (lv (cons z (nil nat)))" |> scope_term sig_st in
  let f_v_vec, _ = Infer.infer [] (Pos.none f_v_vec) in
  let f_v_list', _ = Infer.infer [] (Pos.none f_v_list) in
  Alcotest.(check bool)
    (Format.asprintf "@[<hov 2>Expected@ %a got@ %a@]"
       Print.pp_term f_v_vec Print.pp_term f_v_list')
    (Eval.eq_modulo [] f_v_list' f_v_vec) true

let dependent = Timed.pure_apply dependent

let _ =
  let open Alcotest in
  run "coercion insertion" [
    ("coercions", [ test_case "simple" `Quick simple
                  ; test_case "value to type" `Quick element
                  ; test_case "dependent" `Quick dependent ] ) ]
