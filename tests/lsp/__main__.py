"""Entry point: `python3 -m tests.lsp` runs the whole suite."""

import os
import sys
import unittest


if __name__ == "__main__":
    # Ensure the tests can find each other as a package.
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
    if repo_root not in sys.path:
        sys.path.insert(0, repo_root)

    # Load every tests.lsp.test_* module.
    loader = unittest.TestLoader()
    suite = loader.loadTestsFromNames([
        "tests.lsp.test_lifecycle",
        "tests.lsp.test_diagnostics",
        "tests.lsp.test_hover",
        "tests.lsp.test_definition",
        "tests.lsp.test_incremental",
        "tests.lsp.test_goals",
        "tests.lsp.test_symbols",
        "tests.lsp.test_invariants",
        "tests.lsp.test_bugs_observed",
    ])
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
