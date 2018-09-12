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


symbol {|this is
a very weird variable name|} : TYPE

symbol {|test|} : Nat

// symbol test.symbol : Nat

assert zero ?blop[a,b] : Nat

// TODO finish giving examples of every syntactic construct.
