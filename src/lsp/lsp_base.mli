(************************************************************************)
(* The λΠ-modulo Interactive Proof Assistant                            *)
(************************************************************************)

(************************************************************************)
(* λΠ-modulo serialization Toplevel                                     *)
(* Copyright 2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Lplib
open Common
open Handle

module J = Yojson.Basic

val std_protocol : bool ref

val snippet_support : bool ref
(** Client supports snippet syntax in [insertText] (LSP
    [textDocument.completion.completionItem.snippetSupport]). Set
    from the [initialize] request's [clientCapabilities]. *)

val hierarchical_symbols : bool ref
(** Client supports hierarchical [DocumentSymbol[]] responses to
    [textDocument/documentSymbol] (LSP
    [textDocument.documentSymbol.hierarchicalDocumentSymbolSupport]).
    When false, fall back to flat [SymbolInformation[]]. *)

val mk_range : Pos.pos -> J.t

val mk_range_of_interval : Range.t -> J.t

val mk_reply : id:int -> result:J.t -> J.t

val mk_error_reply : id:int -> code:int -> msg:string -> J.t
(** JSON-RPC error reply. Codes follow the JSON-RPC 2.0 spec; [-32601]
    is [MethodNotFound]. *)

val mk_diagnostics
  : uri:string
  -> version: int
  -> (Pos.pos * int * string * Goal.info list option) list
  -> J.t

val json_of_goals : ?logs:string -> Goal.info list option -> J.t
