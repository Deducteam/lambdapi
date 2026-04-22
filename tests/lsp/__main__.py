"""Entry point: `python3 -m tests.lsp` runs the whole suite."""

import os
import sys
import unittest


if __name__ == "__main__":
    # Ensure the tests can find each other as a package.
    here = os.path.dirname(__file__)
    repo_root = os.path.abspath(os.path.join(here, "..", ".."))
    if repo_root not in sys.path:
        sys.path.insert(0, repo_root)

    loader = unittest.TestLoader()
    suite = loader.discover(start_dir=here, pattern="test_*.py",
                            top_level_dir=repo_root)
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)
    sys.exit(0 if result.wasSuccessful() else 1)
