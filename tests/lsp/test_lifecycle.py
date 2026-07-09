"""Basic LSP lifecycle tests: initialize, document open/close, shutdown."""

import time
import unittest

from .base import LSPTestCase, _lambdapi_binary, stdlib_map_dir
from .client import LSPServer


def _server_with_stdlib(lib_root):
    map_dirs = [md for md in [stdlib_map_dir()] if md]
    return LSPServer(lib_root=lib_root, map_dirs=map_dirs,
                     standard_lsp=True, binary=_lambdapi_binary())


class TestInitialize(LSPTestCase):
    """Tests that want to drive [initialize] themselves.

    [LSPTestCase.setUp] already performs [initialize] so post-init tests can
    just [open_fixture]. These tests need the un-initialized server, so they
    replace setUp entirely (no [super().setUp()] call)."""

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
        comp = caps.get("completionProvider") or {}
        self.assertTrue(comp.get("resolveProvider"))
        self.assertEqual(comp.get("triggerCharacters"), ["."],
            '"." triggers module-path and qualified-name completion')

    def test_initialize_with_root_uri(self):
        result = self.server.initialize(
            root_uri=f"file://{self.lib_root}")
        self.assertIn("capabilities", result)

    def test_initialize_with_rooturi_and_matching_folder(self):
        """Zed (like many clients) sends BOTH [rootUri] and
        [workspaceFolders] for the same directory. Applying the package
        config twice used to abort initialize with "Module path [...]
        is already mapped." — the client then killed the server and
        retried in a loop."""
        params = {
            "capabilities": {},
            "rootUri": f"file://{self.lib_root}",
            "workspaceFolders": [
                {"uri": f"file://{self.lib_root}", "name": "test"},
            ],
        }
        result = self.server.request("initialize", params)
        self.server.notify("initialized", {})
        self.assertIsNotNone(result,
            "initialize must succeed with duplicated root/folder")
        self.assertIn("capabilities", result)
        # And the workspace still works.
        uri, _, _, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags, "open after duplicated-folder init")

    def test_initialize_with_workspace_folders(self):
        """When the client provides [workspaceFolders] instead of (or in
        addition to) [rootUri], each folder's package config must still
        be applied — otherwise module resolution silently breaks."""
        params = {
            "capabilities": {},
            "workspaceFolders": [
                {"uri": f"file://{self.lib_root}", "name": "test"},
            ],
        }
        result = self.server.request("initialize", params)
        self.server.notify("initialized", {})
        self.assertIn("capabilities", result)
        # Prove the folder actually took effect: opening a fixture that
        # references other fixtures in this root should check cleanly.
        uri, _, _, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags, "open after workspaceFolders init")


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


class TestStringRequestIds(LSPTestCase):
    """JSON-RPC request ids may be strings, not just integers; the
    server must echo them back verbatim instead of failing silently."""

    def test_hover_with_string_id_is_answered(self):
        uri, _text, src, _ = self.open_fixture("simple.lp")
        line, col = src.find(r"rule double zero", "zero")
        msg = self.server.request_with_id(
            "hover-1", "textDocument/hover", {
                "textDocument": {"uri": uri},
                "position": {"line": line, "character": col}})
        self.assertEqual(msg.get("id"), "hover-1",
            f"reply must echo the string id verbatim; got {msg!r}")
        self.assertIn("result", msg)

    def test_unknown_method_with_string_id_gets_error_reply(self):
        msg = self.server.request_with_id(
            "nope-1", "workspace/doesNotExist", {})
        self.assertEqual(msg.get("id"), "nope-1")
        self.assertEqual(msg.get("error", {}).get("code"), -32601,
            f"expected MethodNotFound; got {msg!r}")


class TestShutdownExit(LSPTestCase):
    """shutdown replies null; exit terminates the process."""

    def test_shutdown_then_exit_terminates_process(self):
        # [shutdown] returns null and then [exit] tears the server down.
        self.server.request("shutdown")
        self.server.notify("exit")
        # Give the process a moment to wind down.
        for _ in range(20):
            if self.server._proc.poll() is not None:
                break
            time.sleep(0.05)
        self.assertIsNotNone(self.server._proc.poll(),
            "server should exit after `exit` notification")
        self.assertEqual(self.server._proc.returncode, 0,
            f"expected clean exit; got {self.server._proc.returncode}")


class TestStdinEOF(LSPTestCase):
    """A client that dies without sending [exit] closes the server's
    stdin. The server must terminate on EOF, never linger or spin."""

    def test_stdin_eof_terminates_process(self):
        # Open a document first so EOF can also land while the server
        # is busy checking, not only while blocked reading.
        uri = self.fixture_uri("simple.lp")
        with open(self.fixture_path("simple.lp")) as f:
            self.server.did_open(uri, f.read())
        self.server._proc.stdin.close()
        for _ in range(100):
            if self.server._proc.poll() is not None:
                break
            time.sleep(0.05)
        self.assertIsNotNone(self.server._proc.poll(),
            "server should terminate when its stdin reaches EOF")


class TestServerUnknownRequest(LSPTestCase):
    """Unknown requests must receive a JSON-RPC MethodNotFound reply so
    strict LSP clients don't block waiting for a response."""

    def test_unknown_request_method_not_found(self):
        from .client import LSPError
        with self.assertRaises(LSPError) as ctx:
            self.server.request("workspace/doesNotExist", {})
        msg = str(ctx.exception)
        self.assertNotIn("timeout", msg.lower(),
            f"server should reply with error, not time out: {msg}")
        self.assertIn("Method not found", msg,
            f"expected MethodNotFound message; got {msg}")
        # Server is still alive after rejecting an unknown method.
        uri, _, _, diags = self.open_fixture("simple.lp")
        self.assertNoErrors(diags)

    def test_unknown_notification_no_reply(self):
        """Notifications (no id) must NOT get a reply — sending one back
        would confuse clients that track pending ids."""
        self.server.notify("workspace/doesNotExist", {})
        # Give the server a moment; any reply would be queued as a
        # notification because we never registered an id.
        notifs = self.server.drain_notifications(timeout=0.3)
        # Filter: nothing should have flowed back for that method.
        bad = [n for n in notifs if n.get("method") is None]
        self.assertFalse(bad,
            f"notifications should get no reply; got {bad}")


if __name__ == "__main__":
    unittest.main()
