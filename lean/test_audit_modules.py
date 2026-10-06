"""Check declaration coverage for the EOF sections used by the project."""
from pathlib import Path
import tempfile
import unittest

from audit_modules import AuditError, collect_declarations


class DeclarationCoverageTests(unittest.TestCase):
    def source(self, text, run):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Example.lean"
            path.write_text(text)
            return run(path)

    def test_anonymous_noncomputable_section_at_eof(self):
        result = self.source(
            "noncomputable section\nnamespace Kneser.Example\n"
            "theorem coefficient' : True := by trivial\n"
            "end Kneser.Example\n", collect_declarations)
        self.assertEqual(result, ["Kneser.Example.coefficient'"])

    def test_unaccounted_named_block_fails_closed(self):
        with self.assertRaises(AuditError):
            self.source("namespace Kneser.Example\ntheorem result : True := by trivial\n",
                        collect_declarations)


if __name__ == "__main__":
    unittest.main()
