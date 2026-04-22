"""LSP client over JSON-RPC/stdio for testing the lambdapi LSP server.

The client is small by design: it writes framed JSON-RPC to stdin and reads
framed replies / notifications from stdout. stderr is collected in a
background thread and surfaced when the server crashes.

Typical use:

    with LSPServer(lib_root="...") as srv:
        srv.initialize()
        diags = srv.did_open("file:///foo.lp", text)
        resp = srv.hover("file:///foo.lp", line=3, character=10)

All line/character indices follow the LSP convention (0-based).
"""

import json
import os
import queue
import shutil
import subprocess
import threading


class LSPError(Exception):
    """Raised when the server returns an error or times out."""


class LSPServer:
    """A running lambdapi LSP subprocess."""

    def __init__(self, lib_root, map_dirs=None, standard_lsp=True,
                 log_file=None, binary=None, timeout=15.0):
        self.lib_root = lib_root
        self.map_dirs = list(map_dirs or [])
        self.standard_lsp = standard_lsp
        self.log_file = log_file
        self.binary = binary or shutil.which("lambdapi")
        if not self.binary:
            raise LSPError("lambdapi binary not found on PATH")
        self.timeout = timeout
        self._proc = None
        self._stderr = []
        self._notifications = queue.Queue()
        self._pending = {}
        self._next_id = 1
        self._reader_thread = None
        self._stderr_thread = None
        self._stop = threading.Event()

    # --- Process lifecycle ------------------------------------------------

    def start(self):
        cmd = [self.binary, "lsp"]
        if self.standard_lsp:
            cmd.append("--standard-lsp")
        cmd.append(f"--lib-root={self.lib_root}")
        for md in self.map_dirs:
            cmd.append(f"--map-dir={md}")
        if self.log_file:
            cmd.append(f"--log-file={self.log_file}")
        self._proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
        )
        self._reader_thread = threading.Thread(
            target=self._read_stdout, daemon=True)
        self._stderr_thread = threading.Thread(
            target=self._read_stderr, daemon=True)
        self._reader_thread.start()
        self._stderr_thread.start()

    def stop(self):
        self._stop.set()
        if not self._proc:
            return
        if self._proc.poll() is None:
            try:
                self._proc.stdin.close()
            except Exception:
                pass
            try:
                self._proc.terminate()
                self._proc.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self._proc.kill()
                self._proc.wait(timeout=1)
        # Close remaining pipes to suppress ResourceWarning.
        for pipe in (self._proc.stdout, self._proc.stderr, self._proc.stdin):
            try:
                pipe and pipe.close()
            except Exception:
                pass

    def __enter__(self):
        self.start()
        return self

    def __exit__(self, *exc):
        self.stop()

    # --- JSON-RPC framing -------------------------------------------------

    def _write(self, msg):
        body = json.dumps(msg).encode()
        header = f"Content-Length: {len(body)}\r\n\r\n".encode()
        self._proc.stdin.write(header + body)
        self._proc.stdin.flush()

    def _read_stdout(self):
        buf = b""
        while not self._stop.is_set():
            # Read header
            while b"\r\n\r\n" not in buf:
                chunk = self._proc.stdout.read(1)
                if not chunk:
                    return
                buf += chunk
            header, _, buf = buf.partition(b"\r\n\r\n")
            size = None
            for line in header.decode().splitlines():
                if line.lower().startswith("content-length:"):
                    size = int(line.split(":", 1)[1].strip())
            if size is None:
                return
            while len(buf) < size:
                chunk = self._proc.stdout.read(size - len(buf))
                if not chunk:
                    return
                buf += chunk
            body, buf = buf[:size], buf[size:]
            try:
                msg = json.loads(body.decode())
            except json.JSONDecodeError:
                continue
            if "id" in msg and ("result" in msg or "error" in msg):
                # Response to a request
                q = self._pending.pop(msg["id"], None)
                if q is not None:
                    q.put(msg)
            else:
                # Notification (from server to client)
                self._notifications.put(msg)

    def _read_stderr(self):
        for line in self._proc.stderr:
            self._stderr.append(line.decode(errors="replace").rstrip())

    # --- Request / notification -----------------------------------------

    def request(self, method, params=None):
        mid = self._next_id
        self._next_id += 1
        reply = queue.Queue(maxsize=1)
        self._pending[mid] = reply
        self._write({"jsonrpc": "2.0", "id": mid,
                     "method": method, "params": params or {}})
        try:
            msg = reply.get(timeout=self.timeout)
        except queue.Empty:
            raise LSPError(
                f"timeout waiting for {method} (id={mid}); "
                f"stderr={self._stderr[-5:]}")
        if "error" in msg:
            raise LSPError(f"{method}: {msg['error']}")
        return msg.get("result")

    def notify(self, method, params=None):
        self._write({"jsonrpc": "2.0",
                     "method": method, "params": params or {}})

    def drain_notifications(self, timeout=2.0):
        """Collect all notifications that arrive within [timeout] of silence."""
        out = []
        try:
            while True:
                msg = self._notifications.get(timeout=timeout)
                out.append(msg)
                timeout = 0.2  # subsequent reads are quick polls
        except queue.Empty:
            pass
        return out

    # --- Convenience LSP methods ------------------------------------------

    def initialize(self, root_uri=None, capabilities=None):
        params = {"capabilities": capabilities or {}}
        if root_uri is not None:
            params["rootUri"] = root_uri
        result = self.request("initialize", params)
        self.notify("initialized", {})
        return result

    def resolve_completion(self, item):
        return self.request("completionItem/resolve", item)

    def shutdown(self):
        self.request("shutdown")
        self.notify("exit")

    def did_open(self, uri, text, language_id="lp", version=1):
        self.notify("textDocument/didOpen", {
            "textDocument": {"uri": uri, "languageId": language_id,
                             "version": version, "text": text}})

    def did_change(self, uri, text, version):
        self.notify("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": version},
            "contentChanges": [{"text": text}]})

    def did_close(self, uri):
        self.notify("textDocument/didClose", {
            "textDocument": {"uri": uri}})

    def hover(self, uri, line, character):
        return self.request("textDocument/hover", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": character}})

    def definition(self, uri, line, character):
        return self.request("textDocument/definition", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": character}})

    def document_symbol(self, uri):
        return self.request("textDocument/documentSymbol", {
            "textDocument": {"uri": uri}})

    def goals(self, uri, line, character):
        return self.request("proof/goals", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": character}})

    # --- Diagnostics helpers ---------------------------------------------

    def extract_diagnostics(self, notifications, uri=None):
        """Return the latest publishDiagnostics for [uri] (or any URI).

        Each publishDiagnostics notification *supersedes* the previous one
        for the same URI (LSP spec), so the last one wins."""
        latest = {}
        for msg in notifications:
            if msg.get("method") != "textDocument/publishDiagnostics":
                continue
            params = msg.get("params", {})
            u = params.get("uri")
            if uri is not None and u != uri:
                continue
            latest[u] = params.get("diagnostics", [])
        if uri is not None:
            return latest.get(uri, [])
        # If no URI was specified, flatten all latest-per-URI lists.
        out = []
        for v in latest.values():
            out.extend(v)
        return out
