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

- `__init__.py`    — empty; marks `tests/lsp` as a regular Python package
  so the modules can import each other (`from .base import …`) and the
  suite runs as `python3 -m tests.lsp` on every supported Python
- `__main__.py`    — entry point for `python3 -m tests.lsp`: discovers
  and runs the whole suite
- `base.py`        — `LSPTestCase` with per-test server + fixture helpers
- `client.py`      — JSON-RPC / stdio client (`LSPServer` class)
- `source.py`      — pattern-based position finder for fixtures
- `fixtures/*.lp`  — small focused test documents
- `test_*.py`      — one file per LSP concern (lifecycle, diagnostics, …)

## Requirements

Python ≥ 3.8, stdlib only. No pip packages.
