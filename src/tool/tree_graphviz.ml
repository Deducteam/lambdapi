(** Representation of trees as graphviz files.

   {{:https://graphviz.org}Graphviz} is a graph visualization software. This
   module handles the conversion from {!type:Core.Term.dtree} data structures
   in the [dot] language that can be interpreted by graphviz.

   See the chapter [doc/options.md#printing-decision-trees] of the
   documentation for more information. *)

open Lplib open Base
open Timed
open Core open Term open Tree_type

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa (* Default case *)
  | DotAbst of int
  | DotProd of int
  | DotCons of TC.t
  | DotSuccess
  | DotFailure

(** [to_dot ppf sym] prints a dot graphviz representation of the tree of
   symbol [sym] on [ppf]. Each node of the tree embodies a pattern matrix. The
   label of a node is the column index in the matrix on which the matching is
   performed to give birth to the child node. The label on the edge between a
   node and one of its children represents the term matched to generate the
   next pattern matrix (the one of the child node). *)
let to_dot : Format.formatter -> sym -> unit = fun ppf s ->
  let output_tree ppf tree =
    let dotterm : dot_term pp = fun ppf dh ->
      let var_px = "v" in
      match dh with
      | DotAbst(id)          -> out ppf "λ%s%d" var_px id
      | DotProd(id)          -> out ppf "Π%s%d" var_px id
      | DotDefa              -> out ppf "*"
      | DotCons(Symb(_,n,a)) -> out ppf "%s<sub>%d</sub>" n a
      | DotCons(Vari(i))     -> out ppf "%s%d" var_px i
      | DotCons(Type)        -> out ppf "TYPE"
      | DotSuccess           -> out ppf "✓"
      | DotFailure           -> out ppf "✗"
    in
    let tcstr : tree_cond pp = fun ppf cstr ->
      let ar = Array.pp int " " in
      match cstr with
      | CondNL(i, j) -> out ppf "%d ≡ %d" i j
      | CondFV(i,vs) -> out ppf "%a ⊆ FV(%d)" ar vs i
    in
    let node_count = ref 0 in
    (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
       switch on [u] ({!constructor:None} if default). *)
    let rec write_tree father_l swon t =
      incr node_count;
      match t with
      | Leaf(_,(a,_))                                                    ->
          let _, acte = Bindlib.unmbind a in
          out ppf "@ %d [label=\"%a\"];" !node_count Print.term acte;
          out ppf "@ %d -- %d [label=<%a>];"
            father_l !node_count dotterm swon
      | Node({swap; children; store; abstraction=abs; default; product}) ->
          let tag = !node_count in
          (* Create node *)
          out ppf "@ %d [label=\"%d\"%s];" tag swap
            (if store then " shape=\"box\"" else "");
          (* Create edge *)
          out ppf "@ %d -- %d [label=<%a>];" father_l tag dotterm swon;
          TCMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children;
          Option.iter (fun (x,t) -> write_tree tag (DotAbst(x)) t) abs;
          Option.iter (fun (x,t) -> write_tree tag (DotProd(x)) t) product;
          Option.iter (write_tree tag DotDefa) default
      | Cond({ ok ; cond ; fail })                                       ->
          let tag = !node_count in
          out ppf "@ %d [label=<%a> shape=\"diamond\"];" tag tcstr cond;
          out ppf "@ %d -- %d [label=<%a>];" father_l tag dotterm swon;
          write_tree tag DotSuccess ok;
          write_tree tag DotFailure fail
      | Eos(l,r)                                                         ->
          let tag = !node_count in
          out ppf "@ %d [label=\"\" shape=\"triangle\"];" tag;
          out ppf "@ %d -- %d [label=<%a>];" father_l tag dotterm swon;
          write_tree tag DotFailure l;
          write_tree tag DotSuccess r
      | Fail                                                             ->
          out ppf "@ %d [label=<!>];" !node_count;
          out ppf "@ %d -- %d [label=\"!\"];" father_l !node_count
    in
    out ppf "graph {@[<v>";
    begin
      match tree with
      (* First step must be done to avoid drawing a top node. *)
      | Node{swap; store; children; default; abstraction; product} ->
          out ppf "@ 0 [label=\"%d\"%s];" swap
            (if store then " shape=\"box\"" else "");
          TCMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) children;
          Option.iter (fun (x,t) -> write_tree 0 (DotAbst(x)) t) abstraction;
          Option.iter (fun (x,t) -> write_tree 0 (DotProd(x)) t) product;
          Option.iter (fun t -> write_tree 0 DotDefa t) default
      | Leaf(_) -> ()
      | _       -> assert false
    end;
    out ppf "@.}@\n@?"
  in
  output_tree ppf (Lazy.force (snd !(s.sym_dtree)))
