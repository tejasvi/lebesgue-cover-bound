#!/usr/bin/env python3
"""Build the kernel-checked certificate of the 0.8366 proof (generated modules LebK/L11/*, LebesgueCover/K11/*).

Run in lean/ after the base build (see the README), with the supplement files unpacked into one directory SRC:
  SRC/k11_sources/P<c>.tar.gz   (from k11_sources_00.tar ... k11_sources_15.tar)
  SRC/k11_glue/                 (from k11_glue.tar.zst)
  SRC/k11_sums/                 (from k11_sums.tar.zst)

  python3 ../tools/build_k11.py SRC [--par N] [--mem-gb M] [--shard i/n] [--skip-cells] [--check] [--dry-run]

1. Each cell c: k11_sources/P<c>.tar.gz is unpacked into k11_build/cells/P<c>/ and its files are checked against
   k11_sums/SOURCES_SHA256SUMS. The cell's jobs.tsv lists its modules: leaf modules <M>_<j> (at most 32 leaves of the
   native module M), the subtree modules H<c>_<k> and the cell module G<c>.
2. Every module is compiled in its own single-threaded process, with the command of the original build:
      lean -DElab.async=false -j1 --root=<directory of the source tree> -o <olean> <source>
   LEAN_PATH is `lake env printenv LEAN_PATH`; the .olean files of the generated modules go into .lake/build/lib/lean,
   which they share with the library roots LebK and LebesgueCover. The leaf modules of all cells run first, at most N
   at a time and with the estimated memory of the running ones (column 3 of jobs.tsv, GB) at most M; then the H
   modules; then the G modules. A module whose .olean exists is skipped (rerun to resume).
3. The 64 chunk modules C00..C63 and Root11K are compiled from k11_glue/ (Root11K needs about 240 GB), and the axioms
   of the final theorems are printed (tools/K11Axioms.lean) into k11_build/axioms.txt.
--shard i/n builds the cells c with c mod n = i and stops after step 1-2; collect every .olean under
.lake/build/lib/lean/LebK/L11 and .lake/build/lib/lean/LebesgueCover/K11 on one machine and finish there with
--skip-cells. --check compares each compiled .olean with k11_sums/OLEAN_SHA256SUMS. k11_build/times.txt gets one line
per module: name, exit code, wall seconds, peak RSS (kB)."""
import argparse, hashlib, os, subprocess, sys, tarfile, time

ap = argparse.ArgumentParser()
ap.add_argument('src'); ap.add_argument('--par', type=int, default=os.cpu_count())
ap.add_argument('--mem-gb', type=float, default=None); ap.add_argument('--shard', default='0/1')
ap.add_argument('--skip-cells', action='store_true'); ap.add_argument('--check', action='store_true')
ap.add_argument('--dry-run', action='store_true')
a = ap.parse_args()
SRC = os.path.abspath(a.src); LEAN_DIR = os.getcwd(); W = os.path.join(LEAN_DIR, 'k11_build')
B = os.path.join(LEAN_DIR, '.lake', 'build', 'lib', 'lean')
if a.mem_gb is None:
    kb = int([l for l in open('/proc/meminfo') if l.startswith('MemTotal:')][0].split()[1])
    a.mem_gb = 0.8 * kb / 2 ** 20
si, sn = map(int, a.shard.split('/'))
for d in ('k11_sources', 'k11_glue', 'k11_sums'):
    if not os.path.isdir(os.path.join(SRC, d)): sys.exit(f'missing {SRC}/{d}')
LEAN_PATH = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True, text=True, check=True).stdout.strip()
ENV = dict(os.environ, LEAN_PATH=LEAN_PATH, LEAN_NUM_THREADS='1')
os.makedirs(os.path.join(W, 'cells'), exist_ok=True); os.makedirs(os.path.join(W, 'logs'), exist_ok=True)
olsha = {}
if a.check:
    for l in open(os.path.join(SRC, 'k11_sums', 'OLEAN_SHA256SUMS')):
        h, p = l.split(None, 1); olsha[p.strip()] = h
srcsha = {}
for l in open(os.path.join(SRC, 'k11_sums', 'SOURCES_SHA256SUMS')):
    h, p = l.split(None, 1); c, rest = p.strip().split('/', 1); srcsha.setdefault(int(c[1:]), {})[rest] = h
mism = []

def unpack(c):
    d = os.path.join(W, 'cells', f'P{c}')
    if not os.path.exists(os.path.join(d, '.checked')):
        os.makedirs(d, exist_ok=True)
        with tarfile.open(os.path.join(SRC, 'k11_sources', f'P{c}.tar.gz')) as tf:
            try:
                tf.extractall(d, filter='data')
            except TypeError:                     # Python < 3.12
                tf.extractall(d)
        for rest, h in srcsha[c].items():
            if hashlib.sha256(open(os.path.join(d, rest), 'rb').read()).hexdigest() != h:
                sys.exit(f'P{c}/{rest}: sha256 differs from SOURCES_SHA256SUMS')
        open(os.path.join(d, '.checked'), 'w').close()
    return d

def run(jobs, label):
    """jobs: list of (name, root dir, source relative to root, olean relative to B or None, est_gb, extra lean args)."""
    todo = [j for j in jobs if j[3] is None or not os.path.exists(os.path.join(B, j[3]))]
    print(f'{label}: {len(jobs)} modules, {len(todo)} to compile', flush=True)
    if a.dry_run:
        for j in todo[:3]: print('  cd', j[1], '&&', ' '.join(cmd(j)))
        return
    running, done, nfail = {}, 0, 0
    while todo or running:
        used = sum(r[1][4] for r in running.values())
        while todo and len(running) < a.par and (not running or used + todo[0][4] <= a.mem_gb):
            j = todo.pop(0); used += j[4]
            if j[3]: os.makedirs(os.path.dirname(os.path.join(B, j[3])), exist_ok=True)
            lg = open(os.path.join(W, 'logs', j[0].replace('/', '_') + '.log'), 'w')
            p = subprocess.Popen(cmd(j), cwd=j[1], env=ENV, stdout=lg, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
            running[p.pid] = (p, j, time.time(), lg)
        pid, st, ru = os.wait4(-1, 0)
        if pid not in running: continue
        p, j, t0, lg = running.pop(pid); lg.close(); rc = os.waitstatus_to_exitcode(st)
        with open(os.path.join(W, 'times.txt'), 'a') as fh:
            fh.write(f'{j[0]} {rc} {time.time() - t0:.1f} {ru.ru_maxrss}\n')
        done += 1
        if rc != 0:
            nfail += 1; print(f'  FAILED {j[0]} (exit {rc}), log k11_build/logs/{j[0].replace("/", "_")}.log', flush=True)
        elif a.check and j[3]:
            h = hashlib.sha256(open(os.path.join(B, j[3]), 'rb').read()).hexdigest()
            if olsha.get(j[3]) != h: mism.append(j[3])
    if nfail: sys.exit(f'{label}: {nfail} modules failed')

def cmd(j):
    c = ['lean', '-DElab.async=false', '-j1', f'--root={j[1]}']
    if j[3]: c += ['-o', os.path.join(B, j[3])]
    return c + [j[2]]

if not a.skip_cells:
    cells = [c for c in range(2048) if c % sn == si]
    phase = {'leaf': [], 'H': [], 'G': []}
    for c in cells:
        d = unpack(c)
        for l in open(os.path.join(d, 'jobs.tsv')):
            f = l.rstrip('\n').split('\t')
            if len(f) < 6: continue
            k = 'H' if f[0].startswith('H') else 'G' if f[0].startswith('G') else 'leaf'
            phase[k].append((f[0], d, f[4], f[5], float(f[2])))
    phase['leaf'].sort(key=lambda j: -j[4])          # large modules first
    for k in ('leaf', 'H', 'G'):
        run(phase[k], f'{k} modules of {len(cells)} cells')
    if sn > 1:
        print('shard done'); sys.exit(1 if mism else 0)
G = os.path.join(SRC, 'k11_glue')
run([(f'C{k:02d}', G, f'LebesgueCover/K11/C{k:02d}.lean', f'LebesgueCover/K11/C{k:02d}.olean', 20.0) for k in range(64)], 'chunk modules')
run([('Root11K', G, 'LebesgueCover/K11/Root11K.lean', 'LebesgueCover/K11/Root11K.olean', 240.0)], 'root module')
if not a.dry_run:
    r = subprocess.run(['lean', '-DElab.async=false', '-j1', f'--root={LEAN_DIR}', 'tools/K11Axioms.lean'], cwd=LEAN_DIR, env=ENV,
                       capture_output=True, text=True)
    open(os.path.join(W, 'axioms.txt'), 'w').write(r.stdout + r.stderr)
    print(r.stdout + r.stderr, end='')
if a.check:
    print(f'compiled .olean files differing from OLEAN_SHA256SUMS: {len(mism)}', *mism[:20], sep='\n  ')
