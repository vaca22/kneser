#!/bin/sh
# 编译整本书，输出 book.pdf
set -e
cd "$(dirname "$0")"
mkdir -p /tmp/tb-book
tectonic -X compile book.tex --outdir /tmp/tb-book --keep-logs >/tmp/tb-book/build.out 2>&1 || { tail -40 /tmp/tb-book/build.out; exit 1; }
cp /tmp/tb-book/book.pdf book.pdf
echo "undefined refs:"; grep -o "Reference \`[^']*' on page" /tmp/tb-book/book.log | sort -u | head -40 || true
grep -c "Warning" /tmp/tb-book/book.log || true
