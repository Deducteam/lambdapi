# LSP integration tests

End-to-end tests for the lambdapi LSP server. Each test spawns a
`lambdapi lsp` subprocess, speaks JSON-RPC over stdio, and asserts on the
responses.

## Running

From the repository root:

```
make test_lsp                         # runs as part of `make test` too
python3 -m tests.lsp                  # equivalent, more verbose
python3 -m unittest tests.lsp.test_hover -v   # single file
```

The harness prefers a locally-built binary (`_build/install/default/bin/lambdapi`)
over whatever is on `PATH`, so you always test the current tree.

## Environment variables

| Name | Purpose |
|---|---|
| `LAMBDAPI_LIB_ROOT` | override stdlib location (defaults to the opam install) |
| `LSP_TEST_LOG` | when set, pass `--log-file=$LSP_TEST_LOG` to the server |

## Layout

- `client.py`      — JSON-RPC / stdio client (`LSPServer` class)
- `source.py`      — pattern-based position finder for fixtures
- `base.py`        — `LSPTestCase` with per-test server + fixture helpers
- `fixtures/*.lp`  — small focused test documents
- `test_*.py`      — one file per LSP concern (lifecycle, diagnostics, …)

## Requirements

Python ≥ 3.8, stdlib only. No pip packages.
