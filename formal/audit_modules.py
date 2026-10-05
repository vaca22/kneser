"""Build and audit selected Kneser modules; never imply a full-project proof.

Declaration discovery supports ordinary named theorem/lemma commands, namespace and
section blocks, attributes, and protected declarations. Unsupported theorem syntax
fails closed instead of silently omitting a declaration. Lean remains the authority
for compilation and axiom dependencies.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IDENT = r"[^\W\d][\w']*"
LEAN_NAME = rf"{IDENT}(?:\.{IDENT})*"


class AuditError(RuntimeError):
    """The requested audit could not establish its advertised evidence."""


def strip_comments_and_strings(text):
    """Mask nested Lean comments and strings while preserving line positions."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "
                i += 1
                if i < len(text):
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    if depth or string:
        raise AuditError("Unterminated Lean comment or string")
    return "".join(out)


def collect_declarations(source):
    """Discover supported theorem and lemma declarations with their actual namespace."""
    code = strip_comments_and_strings(source.read_text())
    forbidden = re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", code)
    if forbidden:
        raise AuditError(f"{source}: forbidden source token {forbidden.group()}")
    declarations = []
    blocks = []  # (written block name, namespace before entry)
    namespace = ""
    for line_number, line in enumerate(code.splitlines(), 1):
        line = line.strip()
        match = re.fullmatch(rf"namespace\s+({LEAN_NAME})", line)
        if match:
            name = match.group(1)
            blocks.append((name, namespace))
            namespace = name.removeprefix("_root_.") if name.startswith("_root_.") else (
                f"{namespace}.{name}" if namespace else name)
            continue
        match = re.fullmatch(rf"(?:noncomputable\s+)?section(?:\s+({LEAN_NAME}))?", line)
        if match:
            blocks.append((match.group(1), namespace))
            continue
        match = re.fullmatch(rf"end(?:\s+({LEAN_NAME}))?", line)
        if match:
            if not blocks:
                raise AuditError(f"{source}:{line_number}: unmatched end")
            block_name, namespace = blocks.pop()
            if match.group(1) and match.group(1) != block_name:
                raise AuditError(f"{source}:{line_number}: mismatched named end")
            continue
        theorem_tokens = re.findall(r"\b(theorem|lemma)\b", line)
        if not theorem_tokens:
            continue
        if len(theorem_tokens) != 1:
            raise AuditError(f"{source}:{line_number}: multiple theorem/lemma commands on one line")
        # Attributes on the same line and on preceding lines are both accepted.
        match = re.match(
            rf"(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+"
            rf"({LEAN_NAME})(?=\s|[:(\[{{]|$)", line)
        if not match:
            raise AuditError(f"{source}:{line_number}: unsupported theorem/lemma syntax")
        name = match.group(1)
        qualified = name.removeprefix("_root_.") if name.startswith("_root_.") else (
            f"{namespace}.{name}" if namespace else name)
        declarations.append(qualified)
    if blocks:
        raise AuditError(f"{source}: unclosed namespace or section")
    return declarations


def source_hashes(root, sources):
    return {str(source.relative_to(root)): hashlib.sha256(source.read_bytes()).hexdigest()
            for source in sources}


def run_logged(command, root, log_path):
    result = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    log_path.write_text(result.stdout)
    if result.returncode:
        raise AuditError(f"Command failed ({result.returncode}): {' '.join(command)}\n"
                         f"See {log_path}\n{result.stdout}")
    return result.stdout


def audit_modules(root, name, modules):
    if not re.fullmatch(r"[a-z][a-z0-9-]*", name):
        raise AuditError("Audit name must match [a-z][a-z0-9-]*")
    if not modules or any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", x) for x in modules):
        raise AuditError("Provide at least one valid module name")
    if len(set(modules)) != len(modules):
        raise AuditError("Duplicate module names")
    audit = root / "audit"
    audit.mkdir(exist_ok=True)
    record_path = audit / (name + "-result.json")
    # A failed rerun must not leave an earlier PASS looking like its result.
    record_path.unlink(missing_ok=True)
    sources = [root / "Kneser" / (module + ".lean") for module in modules]
    before = source_hashes(root, sources)
    declarations = [decl for source in sources for decl in collect_declarations(source)]
    if not declarations or len(set(declarations)) != len(declarations):
        raise AuditError("Expected a nonempty set of unique named declarations")

    build_command = ["lake", "build", *("Kneser." + module for module in modules)]
    run_logged(build_command, root, audit / (name + "-build.log"))
    if source_hashes(root, sources) != before:
        raise AuditError("Selected sources changed during the build; rerun the audit")
    lean_version = run_logged(["lake", "env", "lean", "--version"], root,
                              audit / (name + "-lean-version.log")).strip()
    file = audit / (name + "-axioms.lean")
    file.write_text("".join(f"import Kneser.{module}\n" for module in modules) +
                    "".join(f"#print axioms {decl}\n" for decl in declarations))
    output = run_logged(["lake", "env", "lean", str(file.relative_to(root))], root,
                        audit / (name + "-axioms.log"))
    # Lean identifiers may themselves contain apostrophes (e.g. bound').
    entries = re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", output, re.M)
    empty = re.findall(r"^'(.+)' does not depend on any axioms", output, re.M)
    checked = [decl for decl, _ in entries] + empty
    if len(checked) != len(declarations) or set(checked) != set(declarations):
        raise AuditError("Lean axiom output did not account for every selected declaration exactly once")
    for decl, axioms in entries:
        used = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
        if not used <= ALLOWED_AXIOMS:
            raise AuditError(f"{decl}: disallowed axioms {sorted(used - ALLOWED_AXIOMS)}")
    if source_hashes(root, sources) != before:
        raise AuditError("Selected sources changed during the axiom audit; rerun the audit")
    record = {
        "modules": modules, "checked_theorems": len(declarations), "declarations": declarations,
        "no_sorryAx": True, "no_custom_axioms": True,
        "allowed_foundational_axioms": sorted(ALLOWED_AXIOMS),
        "full_kneser_identity_formalized": False,
        "scope": "Only the listed named theorem/lemma declarations and selected source hashes; "
                 "not a full-project completion audit or a dependency-source snapshot.",
        "sources_sha256": before,
        "lean_version": lean_version,
        "build_command": build_command,
        "selected_modules_built_before_audit": True,
        "selected_sources_unchanged_during_audit": True,
        "declaration_discovery": "Supported named theorem/lemma commands; unsupported syntax fails closed.",
    }
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: {len(declarations)} theorems/lemmas in {len(sources)} built modules; allowed axioms only.")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True)
    parser.add_argument("--module", action="append", required=True)
    args = parser.parse_args()
    try:
        audit_modules(Path(__file__).resolve().parent, args.name, args.module)
    except (AuditError, OSError) as exc:
        parser.exit(1, f"Audit failed: {exc}\n")


if __name__ == "__main__":
    main()
