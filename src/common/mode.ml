(** [lsp_mod] indicates whether we are executing the LSP server.
    Constants and rules are indexed automatically only in LSP mode
    and not in check mode *)
let lsp_mod = Stdlib.ref false
