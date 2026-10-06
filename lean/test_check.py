"""An unsuccessful recheck must never leave an earlier certificate marked PASS."""

from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check
from audit_modules import AuditError


class CheckFailureTests(unittest.TestCase):
    def fixture(self, root):
        (root / "Kneser").mkdir()
        (root / "Kneser" / "Example.lean").write_text("namespace Kneser\nend Kneser\n")
        (root / "audit").mkdir()
        record = root / "audit" / "first-order-result.json"
        record.write_text('{"stale": true}\n')
        return record

    def test_missing_import_revokes_old_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            record = self.fixture(root)
            (root / "Kneser.lean").write_text("")
            with patch.object(check, "__file__", str(root / "check.py")):
                with self.assertRaises(AuditError):
                    check.main()
            self.assertFalse(record.exists())

    def test_failed_build_revokes_old_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            record = self.fixture(root)
            (root / "Kneser.lean").write_text("import Kneser.Example\n")
            with patch.object(check, "__file__", str(root / "check.py")), \
                    patch.object(check.subprocess, "run",
                                 side_effect=subprocess.CalledProcessError(1, ["lake", "build"])):
                with self.assertRaises(subprocess.CalledProcessError):
                    check.main()
            self.assertFalse(record.exists())


if __name__ == "__main__":
    unittest.main()
