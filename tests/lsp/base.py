"""Shared test base class and fixture helpers."""

import os
import pathlib
import shutil
import tempfile
import unittest

from .client import LSPServer
from .source import SourceFile


HERE = pathlib.Path(__file__).resolve().parent
FIXTURES = HERE / "fixtures"
REPO_ROOT = HERE.parent.parent


def _lambdapi_binary():
    """Prefer a freshly-built local binary over whatever's on PATH."""
    local = REPO_ROOT / "_build" / "install" / "default" / "bin" / "lambdapi"
    if local.exists():
        return str(local)
    return shutil.which("lambdapi")


def _opam_stdlib():
    """Locate the installed lambdapi Stdlib (for --map-dir)."""
    for base in [
        os.environ.get("LAMBDAPI_LIB_ROOT"),
        os.path.expanduser("~/.opam/default/lib/lambdapi/lib_root"),
    ]:
        if base and os.path.isdir(os.path.join(base, "Stdlib")):
            return os.path.join(base, "Stdlib")
    return None


def has_stdlib():
    """True when the opam Stdlib is reachable (for conditional tests)."""
    return _opam_stdlib() is not None


def stdlib_map_dir():
    """[--map-dir] value for Stdlib, or None if not installed."""
    d = _opam_stdlib()
    return f"Stdlib:{d}" if d else None


def requires_stdlib(test):
    """Decorator: skip a test method if Stdlib is not available."""
    return unittest.skipUnless(
        has_stdlib(),
        "lambdapi Stdlib not installed; set LAMBDAPI_LIB_ROOT")(test)


class LSPTestCase(unittest.TestCase):
    """Base class: starts one server per test, exposes helpers."""

    standard_lsp = True
    advertise_snippet_support = False
    advertise_hierarchical_symbols = False
    extra_map_dirs = ()

    @classmethod
    def setUpClass(cls):
        cls._tmpdir = tempfile.TemporaryDirectory(prefix="lptest-")
        cls.lib_root = cls._tmpdir.name
        # Copy fixtures into the lib root so relative references resolve.
        for fixture in FIXTURES.glob("*.lp"):
            dest = pathlib.Path(cls.lib_root) / fixture.name
            dest.write_text(fixture.read_text())
        # A lambdapi.pkg is required for the server to treat the dir as a
        # package root.
        pkg = pathlib.Path(cls.lib_root) / "lambdapi.pkg"
        pkg.write_text("package_name = test\nroot_path = test\n")

    @classmethod
    def tearDownClass(cls):
        cls._tmpdir.cleanup()

    def setUp(self):
        map_dirs = list(self.extra_map_dirs)
        md = stdlib_map_dir()
        if md:
            map_dirs.append(md)
        self.server = LSPServer(
            lib_root=self.lib_root,
            map_dirs=map_dirs,
            standard_lsp=self.standard_lsp,
            log_file=os.environ.get("LSP_TEST_LOG"),
            binary=_lambdapi_binary(),
        )
        self.server.start()
        self.addCleanup(self.server.stop)
        td = {}
        if self.advertise_snippet_support:
            td["completion"] = {"completionItem": {"snippetSupport": True}}
        if self.advertise_hierarchical_symbols:
            td["documentSymbol"] = {
                "hierarchicalDocumentSymbolSupport": True}
        caps = {"textDocument": td} if td else {}
        self.server.initialize(
            root_uri=f"file://{self.lib_root}", capabilities=caps)

    # --- Fixture helpers --------------------------------------------------

    def fixture_path(self, name):
        return os.path.join(self.lib_root, name)

    def fixture_uri(self, name):
        return "file://" + self.fixture_path(name)

    def open_fixture(self, name, wait=True):
        """Open a fixture and return (uri, text, SourceFile, diagnostics)."""
        path = self.fixture_path(name)
        with open(path) as f:
            text = f.read()
        uri = "file://" + path
        self.server.did_open(uri, text)
        diags = []
        if wait:
            notifs = self.server.drain_notifications(timeout=5.0)
            diags = self.server.extract_diagnostics(notifs, uri=uri)
        return uri, text, SourceFile(text), diags

    def open_text(self, name, text, wait=True):
        """Open an inline text as a fresh doc under [name]."""
        path = os.path.join(self.lib_root, name)
        with open(path, "w") as f:
            f.write(text)
        self.addCleanup(lambda: os.path.exists(path) and os.remove(path))
        uri = "file://" + path
        self.server.did_open(uri, text)
        diags = []
        if wait:
            notifs = self.server.drain_notifications(timeout=5.0)
            diags = self.server.extract_diagnostics(notifs, uri=uri)
        return uri, SourceFile(text), diags

    # --- Diagnostic helpers ----------------------------------------------

    @staticmethod
    def errors(diagnostics):
        return [d for d in diagnostics if d.get("severity") == 1]

    @staticmethod
    def hints(diagnostics):
        return [d for d in diagnostics if d.get("severity") == 4]

    def assertNoErrors(self, diagnostics, msg=""):
        errs = self.errors(diagnostics)
        if errs:
            self.fail(
                f"{msg}: {len(errs)} error(s), first: {errs[0].get('message')}"
                if msg else
                f"{len(errs)} error(s), first: {errs[0].get('message')}")

    def assert_server_alive(self):
        """Prove the server can still handle a request (via a real open doc)."""
        uri, _, _, _ = self.open_fixture("simple.lp")
        syms = self.server.document_symbol(uri)
        self.assertIsNotNone(syms)
