#!/bin/bash
# regen_k11.sh: regenerate the sources of one cell of the kernel-checked 0.8366 certificate with k11export.sh and compare them
# with the shipped ones (k11_sums/SOURCES_SHA256SUMS). extract_mod.txt records extraction times and is not compared.
# usage: bash regen_k11.sh CELL L11DIR GLUEDIR SUMSDIR WORKDIR
#   L11DIR: the L11/ directory of l11_sources.tar.zst; GLUEDIR: k11_glue/ of k11_glue.tar.zst; SUMSDIR: k11_sums/ of k11_sums.tar.zst.
#   k11extract (lake build k11extract, in lean/.lake/build/bin/) must be copied next to this script, with k11export.sh and mkk11.py.
# Prints "P<c>: <n> files identical" or the list of differing files (and exits 1).
set -eu
C=$1; L=$(readlink -f "$2"); G=$(readlink -f "$3"); M=$(readlink -f "$4"); W=$(readlink -f "$5")
T=$(dirname "$(readlink -f "$0")")
[ -f "$T/k11extract" ] || { echo "k11extract not found in $T (copy lean/.lake/build/bin/k11extract there)"; exit 1; }
D=$W/P$C
[ -e "$D" ] && { echo "$D exists: use a fresh WORKDIR"; exit 1; }
mkdir -p "$D/in/L11" "$D/in/glue" "$D/out" "$D/tmp"
(cd "$L" && ls | grep -E "^[BS]${C}(_[0-9]+)?\.lean\$") | while read -r f; do cp "$L/$f" "$D/in/L11/$f"; done
(cd "$G/LebesgueCover/K11" && ls | grep -E "^(H${C}_[0-9]+|G${C})\.lean\$") | while read -r f; do cp "$G/LebesgueCover/K11/$f" "$D/in/glue/$f"; done
tar -czf "$D/cell.tar.gz" -C "$D/in" L11 glue
TMPDIR=$D/tmp bash "$T/k11export.sh" "$C" "$D/cell.tar.gz" "$D/out" > "$D/export.log" 2>&1 || { echo "P$C: export failed, see $D/export.log"; exit 1; }
(cd "$D/out" && find . -type f ! -name extract_mod.txt | sed 's#^\./##' | LC_ALL=C sort | while read -r f; do echo "$(sha256sum < "$f" | cut -c1-64)  P$C/$f"; done) > "$D/regen.sums"
grep "  P$C/" "$M/SOURCES_SHA256SUMS" | grep -v "/extract_mod\.txt\$" | LC_ALL=C sort -k2 > "$D/shipped.sums"
if diff <(LC_ALL=C sort -k2 "$D/regen.sums") "$D/shipped.sums" > "$D/diff.txt"; then
  echo "P$C: $(wc -l < "$D/shipped.sums") files identical"
else
  echo "P$C: differences:"; cat "$D/diff.txt"; exit 1
fi
