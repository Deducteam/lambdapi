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

    def test_initialize_with_root_uri(self):
        result = self.server.initialize(
            root_uri=f"file://{self.lib_root}")
        self.assertIn("capabilities", result)

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


class TestClientErrorHandling(unittest.TestCase):
    """Verify the client distinguishes timeout from server-reported error
    at the unit level — a complement to [TestServerUnknownRequest] that
    doesn't depend on server behavior."""

    def test_error_reply_raises_lsp_error(self):
        import queue, threading
        from .client import LSPServer, LSPError
        # Construct a client without starting the subprocess; fake the
        # minimum state [request()] touches on its write path.
        srv = LSPServer(lib_root="/tmp", binary="/bin/true")

        class _DummyStdin:
            def write(self, *_): pass
            def flush(self): pass

        class _DummyProc:
            def __init__(self): self.stdin = _DummyStdin()

        srv._proc = _DummyProc()
        srv.timeout = 2.0

        # Arrange for exactly one request to see an error-shaped reply.
        def inject():
            # Wait until [request()] has registered its reply queue...
            while True:
                with srv._lock:
                    items = list(srv._pending.items())
                if items:
                    break
            mid, q = items[0]
            q.put({"jsonrpc": "2.0", "id": mid,
                   "error": {"code": -32601, "message": "Method not found"}})

        threading.Thread(target=inject, daemon=True).start()
        with self.assertRaises(LSPError) as ctx:
            srv.request("workspace/doesNotExist", {})
        msg = str(ctx.exception)
        self.assertIn("Method not found", msg,
            f"server-reported error message should surface; got {msg!r}")
        self.assertNotIn("timeout", msg.lower(),
            f"error path must not be conflated with timeout; got {msg!r}")

    def test_timeout_raises_with_distinct_marker(self):
        from .client import LSPServer, LSPError

        class _DummyStdin:
            def write(self, *_): pass
            def flush(self): pass

        class _DummyProc:
            def __init__(self): self.stdin = _DummyStdin()

        srv = LSPServer(lib_root="/tmp", binary="/bin/true")
        srv._proc = _DummyProc()
        srv.timeout = 0.2   # force a quick timeout

        with self.assertRaises(LSPError) as ctx:
            srv.request("anything", {})
        self.assertIn("timeout", str(ctx.exception).lower())
        # The timed-out id must be cleaned out of [_pending] so a late
        # reply can't wake a stale queue.
        self.assertEqual(srv._pending, {},
            f"timed-out id should be dropped; got {srv._pending}")


if __name__ == "__main__":
    unittest.main()
