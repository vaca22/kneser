"""Assemble Markdown chapters, rewriting links relative to the single book."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
LINK = re.compile(r"\]\(([^\s)]+)\)")


def chapter_paths():
    return sorted((ROOT / "chapters").glob("[0-9][0-9]-*.md"))


def assembled_text():
    paths = chapter_paths()
    titles = [p.read_text().splitlines()[0].removeprefix("# ") for p in paths]
    content = ["# 超运算分析学\n\n修订版 v0.8 · 2026-10-05\n\n"
               "本文件由分章源稿生成。研究证明、状态登记与实验数据均有可追踪入口。\n\n"
               "## 目录\n\n"]
    content.append("\n".join(f"- [{title}](#chapter-{p.name[:2]})" for p, title in zip(paths, titles)))
    for path in paths:
        def rewrite(match):
            target = match.group(1)
            if target.startswith(("https://", "http://", "#", "/")):
                return match.group(0)
            local, marker, anchor = target.partition("#")
            resolved = (path.parent / local).resolve()
            relative = os.path.relpath(resolved, ROOT)
            return "](" + relative + (marker + anchor if marker else "") + ")"
        body = LINK.sub(rewrite, path.read_text())
        content.append(f'\n\n---\n\n<a id="chapter-{path.name[:2]}"></a>\n\n{body.rstrip()}\n')
    return "".join(content)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = assembled_text()
    target = ROOT / "BOOK.md"
    if args.check:
        if not target.exists() or target.read_text() != generated:
            raise SystemExit("Book differs from source chapters; run build_book.py")
        print("PASS: book matches chapter sources")
        return
    target.write_text(generated)
    manifest = {
        "version": "v0.8", "date": "2026-10-05", "chapter_count": len(chapter_paths()),
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in chapter_paths()},
        "book_sha256": hashlib.sha256(target.read_bytes()).hexdigest(),
    }
    (ROOT / "source-manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n")
    print(f"Built {target}: {len(chapter_paths())} parts, {len(generated)} characters")


if __name__ == "__main__":
    main()
