//////////////////////////////////////////////////////////////////////////////
//                                Comments                                  //
//////////////////////////////////////////////////////////////////////////////

// There are only single-line comments.

// They can contain tags FIXME NOTE TODO

/// Documentation comments start with three slashes, and they can contain
/// “markdown” sytntax.
///
/// Main title
/// ==========
///
/// [website](https://lepigre.fr)
///
/// Important things:
///  - first item,
///  - second item,
///  - last item (**very important**).

//////////////////////////////////////////////////////////////////////////////
//                             Require / Open                               //
//////////////////////////////////////////////////////////////////////////////

// Simple require statement.
require file
require folder.file
require {|.git|}.folder.file // May contain (arbitrary) escaped parts.

// Escaped identifiers cannot contain the sequence “|}”, but they can contain
// “|” and “}” independently.
require folder.{|weir|d}.|}.file
require folder.{|weir|d}.|}
require {|weir|d}.|}

// ( [^|}] | [}] | [|][^}] )* [|]*

// Require and open.
require open file
require open folder.file
require open {|φολδερ|}.file

// Requalifying require statement.
require folder.subfolder.file as m

// Open statement.
open file
open {|φολδερ|}.file
open folder.subfolder.file

// NOTE the following is invalid (keywords are reserved.
//require require.blop
//require blop.require
//require blop.require.blop

// Possible alternative.
require {|require|}.blop
require blop.{|require|}
require blop.{|require|}.blop

//////////////////////////////////////////////////////////////////////////////
//                           Symbol declaration                             //
//////////////////////////////////////////////////////////////////////////////

symbol const Nat : TYPE

symbol {||} : Nat
symbol injective {|this is
a very weird variable name|} : Nat ⇒ Nat

symbol {|test|} : Nat

// symbol test.symbol : Nat

assert zero ?blop[a,b] : Nat

// TODO finish giving examples of every syntactic construct.

definition id_id ≔
  let id = λ x, x in
  id id

rule s (λx, &F[x] x) → &F[zero]
and  s f             → f

definition delta_id ≔
  let delta x = x x in
  let id x = x in
  delta id

theorem add_comm : ∀ m n, eq Nat (add m n) (add n m)
proof
  intro m n
  simpl
  apply h
  refine induction ?zero ?succ
  rewrite [x in add x n] add_assoc
  focus 2
admit

// config naturals Nat zero succ
// 12
