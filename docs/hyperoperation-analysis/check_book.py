"""Check source synchronisation, local links, maths fences and result manifests."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

from build_book import ROOT, assembled_text, chapter_paths


def main():
    paths = chapter_paths()
    assert len(paths) == 14, "Expected preface, twelve chapters and appendix"
    assert (ROOT / "BOOK.md").read_text() == assembled_text(), "Book needs rebuilding"
    failures = []
    markdown_files = list(ROOT.rglob("*.md"))
    for path in markdown_files:
        content = path.read_text()
        if content.count("\\[") != content.count("\\]"):
            failures.append(f"unbalanced math blocks: {path}")
        if content.count("```") % 2:
            failures.append(f"unbalanced code blocks: {path}")
        for match in re.finditer(r"\]\(([^\s)]+)\)", content):
            target = match.group(1)
            if target.startswith(("https://", "http://", "#")):
                continue
            target = target.split("#")[0]
            # This report is created only after all checks succeed below.
            if (path.parent / target).resolve() == ROOT / "validation.json":
                continue
            if target and not (path.parent / target).exists():
                failures.append(f"broken link {path.relative_to(ROOT)} -> {target}")
    manifest = json.loads((ROOT / "source-manifest.json").read_text())
    for rel, expected in manifest["source_sha256"].items():
        assert hashlib.sha256((ROOT / rel).read_bytes()).hexdigest() == expected
    assert hashlib.sha256((ROOT / "BOOK.md").read_bytes()).hexdigest() == manifest["book_sha256"]
    repository = ROOT.parents[1]
    for filename in ("rational-time.json", "linear-response.json", "quantitative-rigidity.json",
                     "complex-rank-geometry.json", "boundary-selected-response.json",
                     "exponential-parameter-family.json", "rank-bands-and-seams.json",
                     "analytic-successor-compactness.json", "bounded-rank-pick.json",
                     "rank-domain-probe.json"):
        result = json.loads((ROOT / "experiments" / filename).read_text())
        assert result["status"] == "PASS"
        if "input_sha256" in result:
            for rel, expected in result["input_sha256"].items():
                assert hashlib.sha256((repository / rel).read_bytes()).hexdigest() == expected, rel
        else:
            script = ROOT / "experiments" / filename.replace("-", "_").replace(".json", ".py")
            assert hashlib.sha256(script.read_bytes()).hexdigest() == result["script_sha256"]
    assert not failures, "\n".join(failures)
    report = {"status": "PASS", "parts": len(paths), "markdown_files": len(markdown_files),
              "book_characters": len((ROOT / "BOOK.md").read_text()),
              "checks": ["source synchronisation", "relative file links", "math/code fences",
                         "chapter/book hashes", "experiment status", "experiment input hashes"]}
    (ROOT / "validation.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    main()
