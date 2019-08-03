(** Representation of trees as graphviz files.

    {{:https://graphviz.org}Graphviz} is a graph visualization software.  This
    module handle the conversion from {!type:Tree.t} data structures files in
    the [dot] language that can be interpreted by graphviz.

    A [dot] file [tree.gv] can be converted to a [png] file [tree.png] using
    [dot -Tpng tree.gv > tree.png].  To output to [tex], one can use
    {{:https://dot2tex.readthedocs.io/}dot2tex}.  For more output formats,
    @see <https://graphviz.gitlab.io/_pages/doc/info/output.html> *)

(** {b Description of output} we remind that trees are interpreted during
    evaluation of terms to get the correct rule to apply.  A node is thus an
    instruction for the evaluation algorithm.  There are three types of
    labeled nodes, labeled edges and leaves.  A node can be
    - a regular node, represented by a circle, whose label indicates on which
      column the next operation to reach the following node will be performed;
    - a store node, represented by a rectangle, which is the same as a regular
      node, except that the term at the index of the label is saved into the
      [vars] array (see {!val:Eval.tree_walk});
    - a conditional node, represented by a diamond, indicating that a
      conditional check shall be performed to reach the next node.

    The label of a node is either
    - [@n] on a regular or storage node if the algorithm inspects the column
      [n] to continue evaluation;
    - [n ≡ m] on a conditional node, meaning that a convertibility check
      between index [n] and index [m] of the [vars] array must be carried out;
    - [xs @ n] on a conditional node, meaning that free variables in [xs] are
      allowed in the term stored at index [n] of the [vars] array.

    The label of an edge is either
    - [*] if the operation to go from a regular or storage node to another
      node is a {!val:Tree.CM.default};
    - [s_n] where [s] is a symbol if the operation to go from a regular or
      storage node to another node is a {!val:Tree.CM.specialize} on symbol
      [s] with arity [n];
    - [λx] if the operation to go from a regular or storage node to another
      node is a specialisation by an abstraction {!val:Tree.CM.abstract};
    - [✓] if the operation to go from a conditional node to another node is
      the assumption of satisfaction of the constraint indicated as label of
      the condition node;
    - [✗] if the operation to go form a conditional node to another node is
      the assumption of failure of satisfaction of the constraint indicated as
      label of the condition node. *)

open Timed
open Extra
open Terms
open Tree_types

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa (* Default case *)
  | DotAbst of tvar
  | DotCons of TC.t
  | DotSuccess
  | DotFailure

(** [to_dot f t] creates a dot graphviz file [f].gv for tree [t].  Each node
    of the tree embodies a pattern matrix.  The label of a node is the
    column index in the matrix on which the matching is performed to give
    birth to the child node.  The label on the edge between a node and one of
    its children represents the term matched to generate the next pattern
    matrix (the one of the child node). *)
let to_dot : string -> sym -> unit = fun fname s ->
  let output_tree oc tree =
    let pp_dotterm : dot_term pp = fun oc dh ->
      let out fmt = Format.fprintf oc fmt in
      match dh with
      | DotAbst(v)           -> out "λ%a" Print.pp_tvar v
      | DotDefa              -> out "*"
      | DotCons(Symb(a,n,_)) -> out "%s<sub>%d</sub>" n a
      | DotCons(Vari(s))     -> out "%s" s
      | DotCons(Abst)        -> assert false
      | DotSuccess           -> out "✓"
      | DotFailure           -> out "✗"
    in
    let pp_tcstr : term tree_constraint pp = fun oc cstr ->
      let out fmt = Format.fprintf oc fmt in
      let pp_ar oc ar =
        Format.pp_print_list Print.pp_tvar oc (Array.to_list ar)
      in
      match cstr with
      | Constr_Eq(i, j) -> out "@%d≡<sub>v</sub>@%d" i j
      | Constr_FV(vs,i) -> out "%a@@<sub>v</sub>%d" pp_ar vs i
    in
    let out fmt = Format.fprintf oc fmt in
    let node_count = ref 0 in
    (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
       switch on [u] ({!constructor:None} if default). *)
    let rec write_tree father_l swon t =
      incr node_count;
      match t with
      | Leaf(_, a)  ->
          let _, acte = Bindlib.unmbind a in
          out "@ %d [label=\"%a\"];" !node_count Print.pp acte;
          out "@ %d -- %d [label=<%a>];" father_l !node_count pp_dotterm swon
      | Node({swap; children; store; abstraction=abs; default}) ->
          let tag = !node_count in
          (* Create node *)
          out "@ %d [label=\"@%d\"%s];" tag swap
            (if store then " shape=\"box\"" else "");
          (* Create edge *)
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          TCMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children;
          Option.iter (fun (v, t) -> write_tree tag (DotAbst(v)) t) abs;
          Option.iter (write_tree tag DotDefa) default
      | Cond({ ok ; cond ; fail }) ->
          let tag = !node_count in
          out "@ %d [label=<%a> shape=\"diamond\"];" tag pp_tcstr cond;
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          write_tree tag DotSuccess ok;
          write_tree tag DotFailure fail
      | Fail        ->
          out "@ %d [label=<!>];" !node_count;
          out "@ %d -- %d [label=\"!\"];" father_l !node_count
    in
    out "graph {@[<v>";
    begin
      match tree with
      (* First step must be done to avoid drawing a top node. *)
      | Node({ swap ; store ; children; default ; abstraction }) ->
          out "@ 0 [label=\"@%d\"%s];" swap
            (if store then " shape=\"box\"" else "");
          TCMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) children;
          Option.iter (fun (v, t) -> write_tree 0 (DotAbst(v)) t) abstraction;
          Option.iter (fun t -> write_tree 0 DotDefa t) default
      | Leaf(_) -> ()
      | _       -> assert false
    end;
    out "@.}@\n@?"
  in
  let tree = Lazy.force (snd !(s.sym_tree)) in
  let oc = open_out fname in
  output_tree (Format.formatter_of_out_channel oc) tree;
  close_out oc

(** [pp o m] prints matrix [m] to out channel [o]. *)
let pp_matrix : Tree.CM.t pp = fun oc m ->
  let open Tree.CM in
  let pp_line oc r =
    Format.fprintf oc "@[<v>@[%a@]@,@[%a@]@,@[%a@]@]" (Array.pp Print.pp " ")
      r.c_lhs Tree.FVCond.pp r.freevars Tree.NLCond.pp r.nonlin
  in
  let out fmt = Format.fprintf oc fmt in
  let l1 = List.map (fun a -> a.arg_path) m.positions in
  let l2 = List.map (fun a -> a.arg_rank) m.positions in
  let pp_path oc l =
    if l = [] then Format.fprintf oc "ε" else
    List.pp (fun oc -> Format.fprintf oc "%d") "." oc (List.rev l)
  in
  out "Positions @@ @[<h>%a@]" (List.pp pp_path ";") l1;
  out " -- Depth: @[<h>%a@]@," (List.pp Format.pp_print_int ";") l2;
  out "{@[<v>@,%a@.@]}" (Format.pp_print_list pp_line) m.clauses
