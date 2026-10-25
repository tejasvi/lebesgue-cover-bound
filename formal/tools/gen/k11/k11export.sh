#!/bin/bash
# k11export.sh: the generated sources of one cell of the kernel-checked 0.8366 certificate. Cells regenerated with it are
# byte-identical to the shipped sources k11_sources/P<c>.tar.gz, except extract_mod.txt, which records extraction times.
# For each native module of the cell (L11/B<c>.lean, L11/S<c>_<k>.lean, from l11_sources.tar.zst) it runs the extractor
# k11extract (built from lean/tools/K11Extract.lean) with the fixed arguments SPEC, MULTS and ES below, rejects any FAIL or MODERR
# line, and writes the leaf modules with mkk11.py (mode leaves). NPROC/4 extractors (at least 4) run at a time, in a temporary
# directory under TMPDIR. It copies the cell's glue modules H<c>_<k>.lean and G<c>.lean unchanged and writes jobs.tsv, one line per
# module: name, dependencies, estimated GB, estimated seconds, source, olean (leaf modules first, then each H<c>_<k> after its leaf
# modules, then G<c>). The estimates are a scheduling model only: per leaf with m witness points (summed over the fans of a
# combination leaf) 7.30 + 0.0765 m s and 1.36 + 0.0097 m GB for a single fan, 9.75 + 0.1111 m s and 1.81 + 0.0131 m GB for a
# combination; per leaf module 1.3 x the largest leaf's GB + 1 and 1.25 x the summed seconds; per glue module 9 GB and
# 10 + 0.25 s per `theorem walk_ok`.
# Writes OUTDIR/LebK/L11/*.lean, OUTDIR/LebesgueCover/K11/{H<c>_<k>,G<c>}.lean, OUTDIR/jobs.tsv, OUTDIR/extract_mod.txt (the
# last one also records extraction times). k11extract and mkk11.py are taken from this script's directory.
# usage: bash k11export.sh CELL CELLTAR OUTDIR   (CELLTAR: a .tar.gz with L11/B<c>.lean, L11/S<c>_<k>.lean, glue/H<c>_<k>.lean and
# glue/G<c>.lean; tools/gen/k11/regen_k11.sh assembles it from l11_sources.tar.zst and k11_glue.tar.zst)
set -u
C=$1; IN=$2; O=$3; T=$(dirname "$(readlink -f "$0")")
SPEC=256:3000,256:1000,256:300,256:100,1024:10; MULTS=30,10,3,1; ES=16,20,24
X=${TMPDIR:-/tmp}/lebexp_${C}_$$
mkdir -p $X/ext $X/gen $O/LebK/L11 $O/LebesgueCover/K11 || exit 1
tar -xzf "$IN" -C $X || { echo "untar failed"; exit 2; }
ls $X/L11 | grep -E "^[BS]${C}(_[0-9]+)?\.lean\$" | sed 's/\.lean$//' | sort > $X/mods.txt
[ -s $X/mods.txt ] && [ $(grep -c . $X/mods.txt) = $(ls $X/L11 | grep -c .) ] && grep -qx "B$C" $X/mods.txt || { echo "cell $C: module list mismatch"; exit 3; }
one() {
  local M=$1
  echo $X/L11/$M.lean > $X/ext/$M.list
  $T/k11extract $X/ext/$M.list $X/ext/$M.out $SPEC $MULTS $ES > $X/ext/$M.log 2>&1 || { echo "EXTFAIL $M"; return 1; }
  grep -q "^MOD $M.lean " $X/ext/$M.out || { echo "PREPFAIL $M"; return 1; }
  grep -q "FAIL \|MODERR" $X/ext/$M.out && { echo "EXTRACTOR-FAILURE $M"; return 1; }
  python3 -I $T/mkk11.py leaves $X/ext/$M.out $X/L11 $X/gen >> $X/ext/$M.log 2>&1 || { echo "GENFAIL $M: $(tail -c 300 $X/ext/$M.log)"; return 1; }
}
export -f one; export X T SPEC MULTS ES
t0=$(date +%s)
NPX=$(( $(getconf _NPROCESSORS_ONLN) / 4 )); [ $NPX -lt 4 ] && NPX=4
xargs -a $X/mods.txt -P ${LEBEXP_PAR:-$NPX} -I{} bash -c 'one {}' > $X/fail.txt 2>&1; rc=$?
if [ $rc != 0 ] || [ -s $X/fail.txt ]; then echo "cell $C: extraction failed (xargs rc $rc)"; head -n 20 $X/fail.txt; exit 4; fi
find $X/gen/LebK/L11 -name '*.lean' -exec mv -t $O/LebK/L11/ {} +
python3 -I - $C $X $O <<'PYJ' || { echo "cell $C: jobs.tsv failed"; exit 6; }
import os, re, sys, shutil
cell, X, O = int(sys.argv[1]), sys.argv[2], sys.argv[3]
LB = 32
mods = [l.strip() for l in open(os.path.join(X, 'mods.txt')) if l.strip()]
mods.sort(key=lambda t: (t[0] != 'S', int(t.split('_')[1]) if '_' in t else 0))     # export11.py order: S<c>_<k> by k, then B<c>
def leaf_est(kind, m):
    if kind == 'L':
        return 7.30 + 0.0765 * m, 1.36 + 0.0097 * m
    return 9.75 + 0.1111 * m, 1.81 + 0.0131 * m
jobs = []; leafmods_of = {}; mod_lines = []
for t in mods:
    txt = open(os.path.join(X, 'ext', t + '.out')).read()
    mod_lines += [l for l in txt.splitlines() if l.startswith('MOD ')]
    lines = [l for l in txt.splitlines() if l.startswith('L ') or l.startswith('C ')]
    ests = [leaf_est(l[0], sum(int(x) for x in re.findall(r' m=(\d+)', l))) for l in lines]
    names = []
    for j, start in enumerate(range(0, len(lines), LB)):
        e = ests[start:start + LB]; nm = f'{t}_{j}'
        if not os.path.exists(os.path.join(O, 'LebK', 'L11', nm + '.lean')): sys.exit(f'missing generated unit {nm}')
        jobs.append((nm, '-', 1.3 * max(x[1] for x in e) + 1, 1.25 * sum(x[0] for x in e), f'LebK/L11/{nm}.lean', f'LebK/L11/{nm}.olean'))
        names.append(nm)
    if os.path.exists(os.path.join(O, 'LebK', 'L11', f'{t}_{len(names)}.lean')): sys.exit(f'extra generated unit for {t}')
    leafmods_of[t] = names
hs = []
for t in mods:
    if t.startswith('S'):
        h = f'H{t[1:]}'; src = os.path.join(X, 'glue', h + '.lean'); dst = os.path.join(O, 'LebesgueCover', 'K11', h + '.lean')
        shutil.copyfile(src, dst); txt = open(dst).read()
        jobs.append((h, ','.join(leafmods_of[t]) or '-', 9.0, 10 + 0.25 * txt.count('theorem walk_ok'), f'LebesgueCover/K11/{h}.lean', f'LebesgueCover/K11/{h}.olean'))
        hs.append(h)
g = f'G{cell}'; dst = os.path.join(O, 'LebesgueCover', 'K11', g + '.lean')
shutil.copyfile(os.path.join(X, 'glue', g + '.lean'), dst); txt = open(dst).read()
jobs.append((g, ','.join(leafmods_of[f'B{cell}'] + hs) or '-', 9.0, 10 + 0.25 * txt.count('theorem walk_ok'), f'LebesgueCover/K11/{g}.lean', f'LebesgueCover/K11/{g}.olean'))
with open(os.path.join(O, 'jobs.tsv'), 'w') as fh:
    for nm, deps, gb, s, lf, ol in jobs:
        fh.write(f'{nm}\t{deps}\t{gb:.1f}\t{s:.0f}\t{lf}\t{ol}\n')
open(os.path.join(O, 'extract_mod.txt'), 'w').write('\n'.join(mod_lines) + '\n')
print(f'cell {cell}: {len(mods)} native modules, {len(jobs)} jobs ({sum(len(v) for v in leafmods_of.values())} leaf units, {len(hs)} H, 1 G)')
PYJ
echo "cell $C: extraction + generation $(( $(date +%s) - t0 )) s"
case "$X" in */lebexp_${C}_$$) find "$X" -mindepth 1 -type f -delete; find "$X" -depth -type d -empty -delete ;; *) echo "temp dir $X kept (unexpected path)" ;; esac
exit 0
