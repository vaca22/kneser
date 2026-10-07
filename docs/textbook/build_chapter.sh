#!/bin/sh
# 只编译一章：./build_chapter.sh 3   （或 A、B）。输出在 /tmp/tb-ch$1/
set -e
cd "$(dirname "$0")"
N="$1"
case "$N" in A|B) F="app$N";; *) F=$(printf "ch%02d" "$N");; esac
OUT="/tmp/tb-ch$N"; mkdir -p "$OUT"
W="_wrap_$F.tex"
case "$N" in A|B) PREV=0; APP='\appendix';; *) PREV=$(( $(echo "$N" | sed "s/^0*//") - 1 )); APP='';; esac
cat > "$W" <<TEX
\documentclass[fontset=mac,openany,11pt]{ctexbook}
\input{preamble}
\begin{document}
\mainmatter
\setcounter{chapter}{$PREV}
$APP
\input{chapters/$F}
\input{references}
\end{document}
TEX
tectonic -X compile "$W" --outdir "$OUT" --keep-logs >"$OUT/build.out" 2>&1 || { tail -30 "$OUT/build.out"; rm -f "$W"; exit 1; }
rm -f "$W"
grep -n "^!\|Error" "$OUT/build.out" | head -20 || true
echo "undefined refs:"; grep -o "Reference \`[^']*' on page" "$OUT/_wrap_$F.log" | sort -u | head -40 || true
echo "PDF: $OUT/_wrap_$F.pdf"
