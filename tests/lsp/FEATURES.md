# LSP feature inventory

Snapshot of what the lambdapi LSP implements, what it stubs, and what it
omits — keyed to the LSP specification. Use this as the reference when
planning editor-UX work or picking a next feature. Source of truth is
`src/lsp/lp_lsp.ml` (dispatch + capabilities); when that diverges from
this document, update this document.

Status key: **✅** implemented · **⚠️** partial/stub · **❌** not implemented · **➕** custom extension

## Lifecycle & meta

| Feature | LSP method | Status | Notes |
|---|---|---|---|
| Initialize handshake | `initialize` | ✅ | `lp_lsp.ml` `do_initialize`. Returns static capability set. Reads `clientCapabilities.textDocument.{completion.completionItem.snippetSupport, documentSymbol.hierarchicalDocumentSymbolSupport}`. Applies `Package.apply_config` for `rootUri` and every `workspaceFolders[].uri` so module mappings are live before the first `didOpen`. `initializationOptions` is still ignored. |
| Initialized notification | `initialized` | ⚠️ | NOOP. |
| Shutdown | `shutdown` | ✅ | Replies `null`. |
| Exit | `exit` | ✅ | Hard `exit 0`. |
| Unknown requests | (any unmapped method with `id`) | ✅ | Replies JSON-RPC `-32601 Method not found`. Unknown *notifications* (no `id`) are logged and dropped per spec. |
| Request cancellation | `$/cancelRequest` | ❌ | Single-threaded loop; long requests block. `didChange` notifications are debounced (later edits coalesce older ones for the same URI) but other requests still queue. |
| Progress reporting | `$/progress`, `window/workDoneProgress/*` | ❌ | |
| Log / show messages | `window/logMessage`, `window/showMessage` | ❌ | Server logs to a file (`/tmp/lambdapi_lsp_log.txt`) instead. |
| Telemetry | `telemetry/event` | ❌ | |
| Dynamic capability registration | `client/registerCapability` | ❌ | All capabilities static at init. |
| Configuration pull | `workspace/configuration` | ❌ | |

## Text synchronization

| Feature | LSP method | Status | Notes |
|---|---|---|---|
| Full-document sync | `textDocumentSync: 1` | ✅ | Whole document re-sent and re-checked on every edit. |
| Incremental sync | `textDocumentSync: 2` | ❌ | |
| didOpen | `textDocument/didOpen` | ✅ | Triggers full check; emits diagnostics. |
| didChange | `textDocument/didChange` | ✅ | Reuses full-sync replace; re-checks whole file. **Debounced**: when more `didChange` notifications for the same URI are already queued (peeked via the unbuffered IO reader), the current re-check is skipped — the trailing change triggers it instead. |
| didClose | `textDocument/didClose` | ✅ | Clears both `doc_table` and `completed_table`. |
| willSave | `textDocument/willSave` | ❌ | |
| willSaveWaitUntil | `textDocument/willSaveWaitUntil` | ❌ | |
| didSave | `textDocument/didSave` | ❌ | |

## Language features (per-position)

| Feature | LSP method | Status | Notes |
|---|---|---|---|
| Hover | `textDocument/hover` | ✅ | Plain-string type for symbols; `null` otherwise. |
| Go to definition | `textDocument/definition` | ✅ | Symbols → declaration pos; module paths in `require`/`open` → file start. |
| Go to declaration | `textDocument/declaration` | ❌ | |
| Go to type definition | `textDocument/typeDefinition` | ❌ | |
| Go to implementation | `textDocument/implementation` | ❌ | |
| Find references | `textDocument/references` | ❌ | |
| Document highlight | `textDocument/documentHighlight` | ❌ | |
| Completion | `textDocument/completion` | ✅ | In-scope symbols (no eager `detail`, resolved lazily), 19 hardcoded tactic keywords with snippet `insertText` when the client advertises `snippetSupport`, and visible hypotheses (kind Variable) inside a proof. No prefix awareness after `.`. |
| Completion resolve | `completionItem/resolve` | ✅ | Pretty-prints the symbol type and fills `detail` on the item being highlighted. |
| Signature help | `textDocument/signatureHelp` | ❌ | |
| Code action | `textDocument/codeAction` | ❌ | Explicitly `codeActionProvider: false`. |
| Code action resolve | `codeAction/resolve` | ❌ | |
| Code lens | `textDocument/codeLens` | ❌ | |
| Inlay hint | `textDocument/inlayHint` | ❌ | |
| Semantic tokens | `textDocument/semanticTokens/*` | ❌ | Clients rely on tree-sitter / TextMate grammars. |
| Document symbol | `textDocument/documentSymbol` | ✅ | When the client advertises `hierarchicalDocumentSymbolSupport: true`, returns `DocumentSymbol[]` walked from the AST: `symbol`/`opaque symbol` as Function, `inductive` as Enum with constructors as EnumMember children. Falls back to flat `SymbolInformation[]` (legacy shape) when the cap is absent. |
| Document link | `textDocument/documentLink` | ❌ | |
| Document color | `textDocument/documentColor` | ❌ | |
| Folding range | `textDocument/foldingRange` | ❌ | |
| Selection range | `textDocument/selectionRange` | ❌ | |
| Linked editing range | `textDocument/linkedEditingRange` | ❌ | |
| Moniker | `textDocument/moniker` | ❌ | |
| Call hierarchy | `textDocument/prepareCallHierarchy` | ❌ | |
| Type hierarchy | `textDocument/prepareTypeHierarchy` | ❌ | |
| Inline value | `textDocument/inlineValue` | ❌ | |
| Pull diagnostics | `textDocument/diagnostic` | ❌ | Uses push model only. |

## Formatting & refactoring

| Feature | LSP method | Status | Notes |
|---|---|---|---|
| Document formatting | `textDocument/formatting` | ❌ | |
| Range formatting | `textDocument/rangeFormatting` | ❌ | |
| On-type formatting | `textDocument/onTypeFormatting` | ❌ | |
| Rename | `textDocument/rename` | ❌ | |
| Prepare rename | `textDocument/prepareRename` | ❌ | |

## Diagnostics

| Feature | LSP method | Status | Notes |
|---|---|---|---|
| Publish diagnostics (push) | `textDocument/publishDiagnostics` | ✅ | Emitted on every `didOpen`/`didChange`. Severity 1/2/3/4 (error/warn/info/hint). With `--standard-lsp` off, diagnostics carry an extra `goal_info` field so proof state can be embedded per-sentence. |
| Diagnostic-related information | `DiagnosticRelatedInformation[]` | ❌ | No secondary locations attached to errors. |

## Workspace

| Feature | LSP method | Status | Notes |
|---|---|---|---|
| Workspace symbol | `workspace/symbol` | ❌ | |
| Execute command | `workspace/executeCommand` | ❌ | |
| Apply edit | `workspace/applyEdit` | ❌ | |
| Configuration changed | `workspace/didChangeConfiguration` | ❌ | |
| Workspace folders changed | `workspace/didChangeWorkspaceFolders` | ❌ | |
| Watched files changed | `workspace/didChangeWatchedFiles` | ❌ | |
| Will/did create/rename/delete files | `workspace/{will,did}{Create,Rename,Delete}Files` | ❌ | |
| Refresh requests | `workspace/diagnostic/refresh`, `…/semanticTokens/refresh`, `…/inlayHint/refresh`, `…/codeLens/refresh` | ❌ | |

## Lambdapi-specific extensions

| Feature | Method | Status | Notes |
|---|---|---|---|
| Proof goals at position | `proof/goals` | ➕ | Custom request: `{textDocument, position}` → `{goals, logs}`. Falls back to the closest goal *before* the cursor when asked mid-sentence. Primary API for clients showing live proof state. |
| Embedded goal info in diagnostics | `goal_info` field on each `Diagnostic` | ➕ | Only when `--standard-lsp` is **off**. Carries the same goal-snapshot payload as `proof/goals`, inlined per sentence. Strictly a protocol extension. |
| CLI flags | `--standard-lsp`, `--log-file`, `--lib-root`, `--map-dir` | — | Client launcher toggles. `--standard-lsp` suppresses the two ➕ extensions above. |

## Summary

**Implemented (9 core + 2 custom)**: `initialize`, `shutdown`/`exit`, text sync (full), `publishDiagnostics`, `hover`, `definition`, `documentSymbol`, `completion`, `completionItem/resolve` · `proof/goals`, `goal_info` diagnostic field.

**Glaring gaps given the editor story we want**: `references`, `rename`/`prepareRename`, `semanticTokens`, `signatureHelp`, `codeAction` (e.g. "admit this goal", "intros", "insert tactic skeleton"), `codeLens` (per-theorem "check"/"run"), `inlayHint` (inferred types, implicit args), `foldingRange` (proof blocks).

**Protocol-hygiene issues**: no request cancellation (`didChange` is debounced but other requests still queue); `initialize` still drops `initializationOptions` and most non-feature `clientCapabilities`; no `didSave`.
