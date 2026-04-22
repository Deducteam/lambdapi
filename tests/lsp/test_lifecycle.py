"""Basic LSP lifecycle tests: initialize, document open/close, shutdown."""

import os
import unittest

from .base import LSPTestCase, _lambdapi_binary
from .client import LSPServer


def _server_with_stdlib(lib_root):
    map_dirs = []
    stdlib = os.environ.get("LAMBDAPI_LIB_ROOT") or \
        os.path.expanduser("~/.opam/default/lib/lambdapi/lib_root")
    if os.path.isdir(os.path.join(stdlib, "Stdlib")):
        map_dirs.append(f"Stdlib:{os.path.join(stdlib, 'Stdlib')}")
    return LSPServer(lib_root=lib_root, map_dirs=map_dirs,
                     standard_lsp=True, binary=_lambdapi_binary())


class TestInitialize(LSPTestCase):
    """These tests exercise initialize() directly, so they override setUp."""

    def setUp(self):
        self.server = _server_with_stdlib(self.lib_root)
        self.server.start()
        self.addCleanup(self.server.stop)

    def test_returns_capabilities(self):
        result = self.server.initialize()
        self.assertIn("capabilities", result)
        caps = result["capabilities"]
        self.assertEqual(caps.get("textDocumentSync"), 1)
        self.assertTrue(caps.get("documentSymbolProvider"))
        self.assertTrue(caps.get("hoverProvider"))
        self.assertTrue(caps.get("definitionProvider"))

    def test_initialize_with_root_uri(self):
        result = self.server.initialize(
            root_uri=f"file://{self.lib_root}")
        self.assertIn("capabilities", result)


class TestDocumentLifecycle(LSPTestCase):
    """didOpen / didChange / didClose sequence on a clean document."""

    def test_did_open_clean_document(self):
        uri, _text, _src, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags, "simple.lp")
        syms = self.server.document_symbol(uri)
        self.assertIsNotNone(syms)

    def test_did_close_then_server_still_alive(self):
        uri, _, _, _ = self.open_fixture("simple.lp")
        self.server.did_close(uri)
        # Open another doc to confirm the server is still responsive.
        uri2, _, _, _ = self.open_fixture("modifiers.lp")
        syms = self.server.document_symbol(uri2)
        self.assertIsNotNone(syms)

    def test_multiple_documents(self):
        uri1, _, _, d1 = self.open_fixture("simple.lp")
        uri2, _, _, d2 = self.open_fixture("modifiers.lp")
        self.assertNoErrors(d1)
        self.assertNoErrors(d2)
        self.assertIsNotNone(self.server.document_symbol(uri1))
        self.assertIsNotNone(self.server.document_symbol(uri2))


class TestUnknownMethod(LSPTestCase):
    """Unknown methods should not crash the server."""

    def test_unknown_notification_ignored(self):
        self.server.notify("workspace/someUnknownMethod", {})
        # Server still alive afterwards.
        uri, _, _, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags)


if __name__ == "__main__":
    unittest.main()
