"""Build every module and audit every named theorem in this standalone project."""

from pathlib import Path
import subprocess

from audit_modules import AuditError, audit_modules


def main():
    root = Path(__file__).resolve().parent
    # A failed whole-project build or import inventory check invalidates any old PASS.
    (root / "audit" / "first-order-result.json").unlink(missing_ok=True)
    sources = sorted((root / "Kneser").glob("*.lean"))
    modules = [source.stem for source in sources]
    imports = [line.removeprefix("import Kneser.")
               for line in (root / "Kneser.lean").read_text().splitlines()
               if line.startswith("import Kneser.")]
    if imports != modules:
        raise AuditError("Kneser.lean must import every source module exactly once, in sorted order")
    subprocess.run(["lake", "build"], cwd=root, check=True)
    audit_modules(root, "first-order", modules)


if __name__ == "__main__":
    main()
