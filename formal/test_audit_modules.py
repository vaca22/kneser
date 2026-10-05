"""Offline regression tests for selected-module audit integrity.

Run: python3 -m unittest -v test_audit_modules
By default no Lean process, package download, or project build is performed.
For a real dependency-free Lean fixture, using the installed project toolchain:
KNESER_AUDIT_LEAN_SMOKE=1 python3 -m unittest -v test_audit_modules
"""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest import TestCase, main, skipUnless
from unittest.mock import patch
import json
import os

import audit_modules as audit


class AuditTestCase(TestCase):
    def setUp(self):
        self.temp = TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Kneser").mkdir()
        self.source = self.root / "Kneser" / "Sample.lean"
        self.source.write_text("namespace Kneser\ntheorem verified : True := by trivial\nend Kneser\n")
        self.record = self.root / "audit" / "sample-result.json"
        self.calls = []

    def fake_run(self, command, **kwargs):
        self.calls.append(command)
        if command[1] == "build":
            return SimpleNamespace(returncode=0, stdout="Build completed successfully.\n")
        if command[-1] == "--version":
            return SimpleNamespace(returncode=0, stdout="Lean (version test)\n")
        return SimpleNamespace(returncode=0, stdout="'Kneser.verified' does not depend on any axioms\n")

    def run_audit(self, runner=None):
        with patch.object(audit.subprocess, "run", side_effect=runner or self.fake_run):
            with redirect_stdout(StringIO()):
                return audit.audit_modules(self.root, "sample", ["Sample"])

    def old_success(self):
        self.record.parent.mkdir(exist_ok=True)
        self.record.write_text('{"no_sorryAx": true}\n')

    def test_build_precedes_audit_and_records_provenance(self):
        result = self.run_audit()
        self.assertEqual(self.calls, [
            ["lake", "build", "Kneser.Sample"],
            ["lake", "env", "lean", "--version"],
            ["lake", "env", "lean", "audit/sample-axioms.lean"],
        ])
        self.assertEqual(json.loads(self.record.read_text()), result)
        self.assertEqual(result["sources_sha256"], audit.source_hashes(self.root, [self.source]))
        self.assertTrue(result["selected_modules_built_before_audit"])
        self.assertFalse(result["full_kneser_identity_formalized"])

    def test_build_failure_prevents_axiom_audit_and_removes_old_success(self):
        self.old_success()
        def fail(command, **kwargs):
            self.calls.append(command)
            return SimpleNamespace(returncode=1, stdout="Compile error: changed proof is invalid\n")
        with self.assertRaisesRegex(audit.AuditError, "Command failed"):
            self.run_audit(fail)
        self.assertEqual(self.calls, [["lake", "build", "Kneser.Sample"]])
        self.assertFalse(self.record.exists())
        self.assertIn("changed proof", (self.record.parent / "sample-build.log").read_text())

    def test_changed_source_during_build_is_rejected(self):
        def change(command, **kwargs):
            result = self.fake_run(command, **kwargs)
            if command[1] == "build":
                self.source.write_text(self.source.read_text() + "-- concurrent edit\n")
            return result
        with self.assertRaisesRegex(audit.AuditError, "changed during the build"):
            self.run_audit(change)
        self.assertEqual(len(self.calls), 1)
        self.assertFalse(self.record.exists())

    def test_changed_source_during_axiom_audit_is_rejected(self):
        def change(command, **kwargs):
            result = self.fake_run(command, **kwargs)
            if command[-1].endswith("-axioms.lean"):
                self.source.write_text(self.source.read_text() + "-- concurrent edit\n")
            return result
        with self.assertRaisesRegex(audit.AuditError, "changed during the axiom audit"):
            self.run_audit(change)
        self.assertFalse(self.record.exists())

    def test_sorry_custom_axiom_and_native_reduction_are_rejected(self):
        for axiom in ["sorryAx", "UnprovedAssumption", "Lean.ofReduceBool"]:
            with self.subTest(axiom=axiom):
                self.old_success()
                def axiom_output(command, **kwargs):
                    result = self.fake_run(command, **kwargs)
                    if command[-1].endswith("-axioms.lean"):
                        result.stdout = f"'Kneser.verified' depends on axioms: [propext, {axiom}]\n"
                    return result
                with self.assertRaisesRegex(audit.AuditError, "disallowed axioms"):
                    self.run_audit(axiom_output)
                self.assertFalse(self.record.exists())

    def test_missing_duplicate_and_extra_output_are_rejected(self):
        line = "'Kneser.verified' does not depend on any axioms\n"
        for output in ["", line + line, line + "'Kneser.extra' does not depend on any axioms\n"]:
            with self.subTest(output=output):
                def incomplete(command, **kwargs):
                    result = self.fake_run(command, **kwargs)
                    if command[-1].endswith("-axioms.lean"):
                        result.stdout = output
                    return result
                with self.assertRaisesRegex(audit.AuditError, "exactly once"):
                    self.run_audit(incomplete)
                self.assertFalse(self.record.exists())

    def test_allowed_foundational_axioms_pass(self):
        def foundational(command, **kwargs):
            result = self.fake_run(command, **kwargs)
            if command[-1].endswith("-axioms.lean"):
                result.stdout = "'Kneser.verified' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            return result
        self.assertTrue(self.run_audit(foundational)["no_custom_axioms"])

    def test_apostrophe_names_in_both_lean_output_forms(self):
        self.source.write_text("namespace Kneser\ntheorem verified' : True := by trivial\nend Kneser\n")
        for suffix in ["does not depend on any axioms", "depends on axioms: [propext]"]:
            with self.subTest(suffix=suffix):
                def primed(command, **kwargs):
                    result = self.fake_run(command, **kwargs)
                    if command[-1].endswith("-axioms.lean"):
                        result.stdout = f"'Kneser.verified'' {suffix}\n"
                    return result
                self.assertEqual(self.run_audit(primed)["declarations"], ["Kneser.verified'"])

    def test_nested_namespaces_sections_attributes_and_lemmas(self):
        self.source.write_text('''namespace Kneser
/- outer /- theorem fake : False := sorry -/ lemma also_fake := admit -/
namespace Certificate
section helper
  @[simp] lemma verified' : True := by trivial
end helper
protected theorem another : True := by trivial
end Certificate
@[simp]
theorem _root_.TopLevel : True := by trivial
def description := "theorem fake; axiom fake; sorry"
end Kneser
''')
        self.assertEqual(audit.collect_declarations(self.source), [
            "Kneser.Certificate.verified'", "Kneser.Certificate.another", "TopLevel"])

    def test_forbidden_source_tokens_rejected_before_build(self):
        for token in ["sorry", "admit", "axiom", "native_decide", "unsafe"]:
            with self.subTest(token=token):
                self.source.write_text(f"namespace Kneser\ntheorem x : True := {token}\nend Kneser\n")
                with self.assertRaisesRegex(audit.AuditError, "forbidden source token"):
                    self.run_audit()
        self.assertEqual(self.calls, [])

    def test_unsupported_declaration_syntax_fails_closed(self):
        for declaration in ["private theorem hidden : True := by trivial", "theorem\n  split : True := by trivial",
                            "include h in lemma hidden : True := h", "theorem «quoted name» : True := by trivial"]:
            with self.subTest(declaration=declaration):
                self.source.write_text(f"namespace Kneser\n{declaration}\nend Kneser\n")
                with self.assertRaisesRegex(audit.AuditError, "unsupported theorem/lemma syntax"):
                    self.run_audit()
        self.assertEqual(self.calls, [])

    def test_no_declarations_and_duplicate_declarations_fail(self):
        for source in ["namespace Kneser\nend Kneser\n",
                       "theorem duplicate : True := by trivial\ntheorem duplicate : True := by trivial\n"]:
            with self.subTest(source=source):
                self.source.write_text(source)
                with self.assertRaisesRegex(audit.AuditError, "nonempty set of unique"):
                    self.run_audit()
        self.assertEqual(self.calls, [])

    def test_multiple_declaration_commands_on_same_line_are_rejected(self):
        self.source.write_text("theorem first : True := by trivial; theorem second : True := by trivial\n")
        with self.assertRaisesRegex(audit.AuditError, "multiple theorem/lemma commands"):
            self.run_audit()
        self.assertEqual(self.calls, [])

    def test_malformed_comments_and_scope_fail(self):
        for source in ["/- never closed", 'def s := "never closed', "end Missing\n",
                       "namespace Kneser\nend Different\n", "namespace Kneser\n"]:
            with self.subTest(source=source):
                self.source.write_text(source)
                with self.assertRaises(audit.AuditError):
                    audit.collect_declarations(self.source)

    def test_duplicate_module_requests_are_rejected(self):
        with self.assertRaisesRegex(audit.AuditError, "Duplicate module"):
            audit.audit_modules(self.root, "sample", ["Sample", "Sample"])

    @skipUnless(os.environ.get("KNESER_AUDIT_LEAN_SMOKE") == "1", "opt-in installed Lean fixture")
    def test_real_lean_rebuild_rejects_stale_compiled_proof(self):
        toolchain = Path(__file__).resolve().parent / "lean-toolchain"
        (self.root / "lean-toolchain").write_text(toolchain.read_text())
        (self.root / "lakefile.toml").write_text('name = "auditSmoke"\n[[lean_lib]]\nname = "Kneser"\n')
        with redirect_stdout(StringIO()):
            result = audit.audit_modules(self.root, "sample", ["Sample"])
        self.assertTrue(result["selected_modules_built_before_audit"])
        self.assertTrue(self.record.exists())
        # Keep the compiled True proof, but replace its source with an invalid False proof.
        self.source.write_text("namespace Kneser\ntheorem verified : False := by trivial\nend Kneser\n")
        with self.assertRaisesRegex(audit.AuditError, "Command failed"):
            audit.audit_modules(self.root, "sample", ["Sample"])
        self.assertFalse(self.record.exists())


if __name__ == "__main__":
    main()
