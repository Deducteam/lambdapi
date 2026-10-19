open Core open Term
open Common
open Lplib open Base

type linear_constraint = int array * int

let _void_ =
  create_sym [] Privat (AC true) Eager false (Pos.none "+") None mk_Kind []

let zint = ref _void_
let z0 = ref _void_
let z1 = ref _void_
let zle = ref _void_
let zlt = ref _void_
let zge = ref _void_
let zgt = ref _void_
let zadd = ref _void_
let zmul = ref _void_
let zlt2le = ref _void_    (* ∀ x y, x < y -> x+1 <= y *)
let zge2le = ref _void_    (* ∀ x y, x >= y -> y <= x *)
let zgt2le = ref _void_    (* ∀ x y, x > y -> y+1 <= x *)
let zle_scale = ref _void_ (* ∀ k x y, 0 <= k -> x <= y -> k*x <= k*y *)
let zle_add2 = ref _void_  (* ∀ x1 x2 y1 y2, xi <= yi -> x1+x2 <= y1+y2 *)
let top_i = ref _void_     (* π ⊤ *)

module EMAP = Hashtbl.Make(
  struct
    type t = term
    let equal x y = Term.cmp x y = 0
    let hash = Hashtbl.hash
  end)

let map = EMAP.create 100
let rmap = Hashtbl.create 100
let vnum = ref 0

(** [lia_init ss pos] initializes hash-tables and global symbols *)
let lia_init: Sig_state.t -> Pos.popt -> unit =
  fun ss pos ->
  EMAP.clear map;
  Hashtbl.clear rmap;
  vnum := 0;
  zint := Builtin.get ss pos [] "zint";
  zle := Builtin.get ss pos [] "zle";
  zlt := Builtin.get ss pos [] "zlt";
  zge := Builtin.get ss pos [] "zge";
  zgt := Builtin.get ss pos [] "zgt";
  zadd := Builtin.get ss pos [] "zadd";
  zmul := Builtin.get ss pos [] "zmul";
  zlt2le := Builtin.get ss pos [] "zlt2le"; (* x < y -> x+1 <= y *)
  zge2le := Builtin.get ss pos [] "zge2le"; (* x >= y -> y <= x *)
  zgt2le := Builtin.get ss pos [] "zgt2le"; (* x > y -> y+1 <= x *)
  zle_scale := Builtin.get ss pos [] "zle_scale";  (* x <= y -> k*x <= k*y *)
  zle_add2 := Builtin.get ss pos [] "zle_add2";  (* xi<=yi->x1+x2<=y1+y2 *)
  top_i := Builtin.get ss pos [] "⊤ᵢ"

(** term buildin functions *)
let binop op x y = add_args (mk_Symb op) [x;y]
let mk_add x y = binop !zadd x y
let mk_mul x y = binop !zmul x y
let mk_le x y = binop !zle x y
let mk_incr x = binop !zadd x (mk_Symb !z1)

(** [get_var e] returns the variable number associated to expression [e] *)
let get_var e =
  match EMAP.find_opt map e with
  | Some v -> v
  | None -> ignore (incr vnum);
    EMAP.add map e !vnum; Hashtbl.add rmap !vnum e;
    !vnum

(** an expression is represented by a list of ordered pairs
    (coefficient, variable number). If variable number is 0, the expression
    is a constant. Its value is the coefficient.
*)
type exp = (int * int) list

(** [is_int s] returns true iff [s] is in "'_'[0-9]+" *)
let is_int: string -> bool =
  fun s ->
  String.is_prefix "_" s && try
    ignore (int_of_string (String.sub s 1 (String.length s - 1)));
    true
  with
  | Failure _ -> false

(** [abst_addm e (n,v)] adds monom [n,v] to abstract expression [e] *)
let rec abst_addm: exp -> (int*int) -> exp =
  fun l ((n,v) as x) ->
  match l with
    [] -> [n,v]
  | (m,v')::l when v=v' -> (m+n,v)::l
  | y::l -> y::abst_addm l x

(** [abst_add l1 l2] adds the two abstract expressions [e1] and [e2] *)
let abst_add: exp -> exp -> exp =
  fun e1 e2 -> List.fold_left abst_addm e2 e1

(** [abst_sub e1 e2] computes the difference of two abstract expressions *)
let abst_sub: exp -> exp -> exp =
  fun l1 l2 ->
  let l2 = List.map (fun (n,v) -> (-n,v)) l2 in
  abst_add l1 l2

(** [abst_exp e] converts the term [e] into an abstract expression *)
let rec abst_exp: term -> exp =
  fun e ->
  match unfold e with
  | Appl (Appl(Symb s, l), r) when Sym.compare s !zadd = 0 ->
    abst_add (abst_exp l) (abst_exp r)
  | Appl (Appl(Symb s, l), r) as e when Sym.compare s !zmul = 0 ->
    begin
      let r1 = abst_exp l and r2 = abst_exp r in
      match r1,r2 with
      | [v1,0],[v2,0] -> [v1*v2,0]
      | [v1,0],_ -> List.map (fun (x,y) -> (v1*x,y)) r2
      | _,[v2,0] -> List.map (fun (x,y) -> (v2*x,y)) r1
      | _,_ -> let v = get_var e in [1,v]
    end
  | Symb s when is_int s.sym_name ->
    let s = s.sym_name in
    [int_of_string (String.sub s 1 (String.length s - 1)),0]
  | e -> let v = get_var e in [1,v]

(** [mk_ctr e n] builds a constraint from an abstract expression
    and the number of abstract variables *)
let mk_ctr: exp -> int -> linear_constraint =
  fun e n ->
  let r = Array.make n 0 in
  let c = ref 0 in
  List.iter (fun (n,x) -> if x=0 then c := n else Array.set r (x-1) n) e;
  (r,!c)

(** [mk_ctrs l] builds constraints from all abstracted expressions of [l] *)
let mk_ctrs l = List.map (fun (h,l,r,c) -> (h,l,r,mk_ctr c !vnum)) l

(** proof term builders *)

(** [apply cmp2le x y h] applies the global function [cmp2le] on the 3 given
    arguments. It is une to transform comparisons into <= *)
let apply: sym -> term -> term -> term -> term =
  fun cmp2le x y h -> add_args (mk_Symb cmp2le) [x;y;h]

(** [scale k l r h] with [h:π(l<=r)] returns ([k*l],[k*r],[h'])
  where [h':π(k*l <= k*r)] *)
let scale: term -> term -> term -> term -> term * term * term =
  fun k l r h ->
  let l' = mk_mul k l and r' = mk_mul k r in
  (l',r',add_args (mk_Symb !zle_scale) [k;mk_Symb (!top_i);l;r;h])

(** [le_add2 (x1,y1,h1) (x2,y2,h2)] with [h1:π(x1<=y1] and [h2:π(x2<=y2]
    returns [x1+x2,y1+y2,h] where [h:π(x1+x2<=y1+y2)] *)
let le_add2: (term*term*term) -> (term*term*term) -> (term*term*term) =
  fun (x1,y1,h1) (x2,y2,h2) ->
  mk_add x1 x2, mk_add y1 y2, add_args (mk_Symb !zle_add2) [x1;y1;x2;y2;h1;h2]

(** [get_arith (_,(h,e,_))] where [h:e] returns [Some (l,r,h',abs)]
    where [e <=> l <= r] and [h':π(l<=r)] and [abs] is the abstraction of [e]
    or [None] if the hypothesis is not a supported arithmetic constraint
*)
let get_arith: ('a * (var*term*'b)) -> (term*term*term*exp) option =
  fun (_, (h,p,_)) ->
  let h = mk_Vari h in
  match unfold p with
  | Appl(_, Appl(Appl(Symb s, l), r)) when Sym.compare s !zle = 0 ->
    Some (h, l, r, abst_sub (abst_exp l) (abst_exp r))
  | Appl(_, Appl(Appl(Symb s, l), r)) when Sym.compare s !zge = 0 ->
    Some (apply !zge2le l r h, r, l, abst_sub (abst_exp r) (abst_exp l))
  | Appl(_, Appl(Appl(Symb s, l), r)) when Sym.compare s !zlt = 0 ->
    Some (apply !zlt2le l r h, mk_incr l, r,
          abst_sub (abst_exp (mk_incr l)) (abst_exp r))
  | Appl(_, Appl(Appl(Symb s, l), r)) when Sym.compare s !zgt = 0 ->
    Some (apply !zgt2le l r h, mk_incr r, l,
          abst_sub (abst_exp (mk_incr r)) (abst_exp l))
  | _ -> None

(** pretty-printing functions *)
module PRT = struct
  (* abstract monoms *)
  let elem = fun ppf (n,v) ->
    if v=0 then out ppf "%d" n
    else out ppf "%d * %a" n Raw.term (Hashtbl.find rmap v)

  (* abstracted expression *)
  let exp = fun ppf l -> List.pp elem "+" ppf l

  (* constraint *)
  let ctr = fun ppf (k,c) -> out ppf "%a + %d <= 0" (Array.pp elem "+")
      (Array.mapi (fun i c -> (c,i+1)) k) c
  (* constraint list *)
  let ctrl = fun ppf l -> List.pp ctr ";" ppf l
end
