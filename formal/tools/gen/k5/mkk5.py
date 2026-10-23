"""Kernel-checked certificate for M(D, B3, B5) >= 0.8347 (5D, single-fan leaves): Lean modules from a search tree
(s_search3k.py --nocomb output).

Leaf data: the search's float proposal (export_test.propose) made exact (export_test.exact_data) and checked exactly
(exact.leafOK, the Fraction mirror of the checker); a failing leaf is split at the midpoint of its widest relative
coordinate until the halves pass (depth <= 6).
Units: every cell tree is cut into units of at most U delegated items (leaves or sub-units); a unit is a tree walk
with delegated items (code 250), checked by `decide +kernel`, and is good when its items are good (`cellK_good`).
Output under LEANROOT:
  LebK/L/L<m>.lean            core Lean, LB leaves each: namespace LebK.P<g> with lo, hi, wit, cen, beta, sigma and
                              `ok : leafOKF ns3 VQ nu3 tau3 … = true := by decide +kernel`
  LebesgueCover/K3/G<j>.lean  units of the 32 cells of chunk j (bottom-up), cell units C<c>, theorem chunk<j>
  LebesgueCover/K3/Root3Good.lean   root3_good, hull3_geK, weak_main3K, main3K
usage: mkk5.py HEADER SEARCHDIR LEANROOT NPROC [--lb 32] [--units 32] [--cells LIST]"""
import sys, os, json, time, argparse
from fractions import Fraction as Fr
from multiprocessing import Pool
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.environ.get('LEBESGUE_CHECKER', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checker')))   # the paper's checker/ (lbcheck.py)
import exact as EX, export_test as ET
import lbcheck as REL

G = {}

def init(ns, tau_f, cell_w):
    G['ch'] = REL.Checker(ns, tau_f, 1024, 1e-6)
    G.update(VT=EX.vert_table(ns), ns=ns, k=len(ns), tau_f=tau_f, tau=Fr(repr(float(tau_f))), cell_w=cell_w)

def leaf_data(lo, hi):
    ib, Q, z, beta, sigma, mfl = ET.propose(G['ch'], G['k'], np.array([float(x) for x in lo]),
                                            np.array([float(x) for x in hi]), G['tau_f'])
    if len(ib) < 3:
        return None, None
    W, zz, bt, sg = ET.exact_data(ib, Q, z, beta, sigma)
    ok, checks, margin, minrow = EX.leafOK(G['ns'], G['VT'], EX.NU, G['tau'], lo, hi, W, zz, bt, sg, detail=True)
    return ((W, zz, bt, sg) if ok else None), float(margin)

def solve(task):
    """a leaf with exact data, or a split with solved halves (data None: failed at depth 6)."""
    lo, hi, depth = task
    data, margin = leaf_data(lo, hi)
    if data is not None or depth >= 6:
        return dict(k='L', lo=lo, hi=hi, data=data, margin=margin, refined=depth)
    rel = [(hi[a] - lo[a])/G['cell_w'][a] for a in range(len(lo))]
    a = max(range(len(lo)), key=lambda i: rel[i])
    m = (lo[a] + hi[a])/2
    l1, h1 = list(lo), list(hi); h1[a] = m
    l2, h2 = list(lo), list(hi); l2[a] = m
    return dict(k='S', a=a, lo=lo, hi=hi, l=solve((l1, h1, depth + 1)), r=solve((l2, h2, depth + 1)))

def parse(codes, lo, hi):
    """tree from DFS preorder codes (a < d: split coordinate a at the midpoint, lower half first; 254: leaf)."""
    pos = 0
    def rec(lo, hi):
        nonlocal pos
        c = int(codes[pos]); pos += 1
        if c == 254:
            return dict(k='L', lo=lo, hi=hi)
        assert c < len(lo), c
        m = (lo[c] + hi[c])/2
        l1, h1 = list(lo), list(hi); h1[c] = m
        l2, h2 = list(lo), list(hi); l2[c] = m
        left = rec(l1, h1)
        return dict(k='S', a=c, lo=lo, hi=hi, l=left, r=rec(l2, h2))
    t = rec(lo, hi)
    assert pos == len(codes)
    return t

def leaves(n, out):
    if n['k'] == 'L':
        out.append(n)
    else:
        leaves(n['l'], out); leaves(n['r'], out)
    return out

def mark(n, U):
    """items of n walked inline; marks unit roots so that every unit has at most U items."""
    if n['k'] == 'L':
        return 1
    cl, cr = mark(n['l'], U), mark(n['r'], U)
    if cl + cr <= U:
        return cl + cr
    big, small = (n['l'], n['r']) if cl >= cr else (n['r'], n['l'])
    cb, cs = max(cl, cr), min(cl, cr)
    if big['k'] == 'S':
        big['unit'] = True; cb = 1
    if cb + cs > U and small['k'] == 'S':
        small['unit'] = True; cs = 1
    return cb + cs

def units_post(n, out):
    if n['k'] == 'S':
        units_post(n['l'], out); units_post(n['r'], out)
        if n.get('unit'):
            out.append(n)
    return out

def unit_walk(u):
    codes, items = [], []
    def rec(n, top):
        if n['k'] == 'L' or (not top and n.get('unit')):
            codes.append(250); items.append(n); return
        codes.append(n['a']); rec(n['l'], False); rec(n['r'], False)
    rec(u, True)
    return codes, items

def gridcells(sp, lo, hi):
    """`gridCells` of LebFast/Tree.lean."""
    if not sp:
        return [(lo, hi)]
    a = sp[0]; m = (lo[a] + hi[a])/2
    h1 = list(hi); h1[a] = m
    l2 = list(lo); l2[a] = m
    return gridcells(sp[1:], lo, h1) + gridcells(sp[1:], l2, hi)

def q(x):
    x = Fr(x)
    return f'({x.numerator} / {x.denominator} : Rat)' if x.denominator != 1 else f'({x.numerator} : Rat)'

def arr(v):
    return '#[' + ', '.join(q(x) for x in v) + ']'

def leaf_text(n):
    W, z, bt, sg = n['data']
    nm = n['name']
    return '\n'.join([
        f'namespace {nm}',
        f'def lo : Array Rat := {arr(n["lo"])}',
        f'def hi : Array Rat := {arr(n["hi"])}',
        'def wit : List (Nat × (Rat × Rat)) := [' + ', '.join(f'({i}, ({q(p[0])}, {q(p[1])}))' for i, p in W) + ']',
        f'def cen : Rat × Rat := ({q(z[0])}, {q(z[1])})',
        'def beta : Nat → Rat := fun i => match i with' + ''.join(f' | {i} => {q(v)}' for i, v in sorted(bt.items()))
        + ' | _ => 0',
        'def sigma : Nat → Rat := fun a => match a with' + ''.join(f' | {a} => {q(v)}' for a, v in enumerate(sg))
        + ' | _ => 0',
        'theorem ok : leafOKF ns3 VQ nu3 tau3 (fun a => lo.getD a 0) (fun a => hi.getD a 0) wit cen beta sigma = true := by',
        '  decide +kernel',
        f'end {nm}', ''])

def nested(goods):
    s = '.nil'
    for g in reversed(goods):
        s = f'.cons {g} ({s})' if s != '.nil' else f'.cons {g} .nil'
    return s

def unit_text(u):
    codes, items = unit_walk(u)
    refs = [(f'{it["name"]}.lo', f'{it["name"]}.hi', f'(leafF_good vt3 {it["name"]}.ok)') if it['k'] == 'L' else
            (f'{it["uname"]}.lo', f'{it["uname"]}.hi', f'{it["uname"]}.good') for it in items]
    nm = u['uname']
    return '\n'.join([
        f'namespace {nm}',
        f'def lo : Array Rat := {arr(u["lo"])}',
        f'def hi : Array Rat := {arr(u["hi"])}',
        f'theorem walk_ok : (walk ns3 #[] VQ nu3 tau3 {len(codes)} {codes} [] [' + ', '.join(f'({a}, {b})' for a, b, _ in refs)
        + '] lo hi).isSome = true := by',
        '  decide +kernel',
        'theorem good : GoodBox ns3 tau3 (fun i => lo.getD i 0) (fun i => hi.getD i 0) :=',
        f'  cellK_good vt3 ({nested([g for _, _, g in refs])}) walk_ok',
        f'end {nm}', ''])

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('header'); ap.add_argument('searchdir'); ap.add_argument('leanroot'); ap.add_argument('nproc', type=int)
    ap.add_argument('--lb', type=int, default=32); ap.add_argument('--units', type=int, default=32)
    ap.add_argument('--cells', default='')
    a = ap.parse_args()
    t0 = time.time()
    hd = json.load(open(a.header))
    ns, tau_f, s0 = hd['ns'], hd['tau'], hd['split0']
    d = len(s0); assert s0 == [4]*d
    rlo = [Fr(x) for x in hd['lo_exact']]; rhi = [Fr(x) for x in hd['hi_exact']]
    cell_w = [(rhi[i] - rlo[i])/4 for i in range(d)]
    cells = gridcells([i for i in range(d) for _ in range(2)], rlo, rhi)
    nd = list(np.ndindex(*s0))
    for ci, (cl, ch) in enumerate(cells):     # DFS grid order = the search's cell numbering
        assert all(cl[i] == rlo[i] + cell_w[i]*nd[ci][i] and ch[i] == rlo[i] + cell_w[i]*(nd[ci][i] + 1) for i in range(d))
    cis = [int(x) for x in a.cells.split(',')] if a.cells else list(range(len(cells)))
    trees = {ci: parse(np.load(os.path.join(a.searchdir, f'cell{ci:04d}.npy')), cells[ci][0], cells[ci][1]) for ci in cis}
    tasks = []
    for ci in cis:
        for n in leaves(trees[ci], []):
            tasks.append((n['lo'], n['hi'], 0))
    print(json.dumps(dict(stage='parsed', cells=len(cis), leaves=len(tasks), secs=round(time.time() - t0))), flush=True)
    with Pool(a.nproc, initializer=init, initargs=(ns, tau_f, cell_w)) as pool:
        res = pool.map(solve, tasks, chunksize=8)
    print(json.dumps(dict(stage='solved', secs=round(time.time() - t0))), flush=True)
    # substitute the solved leaves
    it = iter(res)
    def subst(n):
        if n['k'] == 'L':
            return next(it)
        n['l'] = subst(n['l']); n['r'] = subst(n['r'])
        return n
    for ci in cis:
        trees[ci] = subst(trees[ci])
    failed = []; refined = 0; nleaf = 0; minmargin = None; mlen = []
    gidx = 0; leafmods = {}
    for ci in cis:
        for n in leaves(trees[ci], []):
            if n['data'] is None:
                failed.append((ci, [str(x) for x in n['lo']], [str(x) for x in n['hi']], n['margin']))
            else:
                minmargin = n['margin'] if minmargin is None else min(minmargin, n['margin'])
                mlen.append(len(n['data'][0]))
            refined += n['refined'] > 0
            n['name'] = f'LebK.P{gidx:05d}'; n['g'] = gidx; n['cell'] = ci
            leafmods.setdefault(gidx // a.lb, []).append(n)
            gidx += 1
        nleaf = gidx
    stats = dict(leaves=nleaf, failed=len(failed), refined_leaves=refined, min_exact_margin=minmargin,
                 witnesses_min=min(mlen) if mlen else None, witnesses_max=max(mlen) if mlen else None,
                 witnesses_mean=sum(mlen)/len(mlen) if mlen else None)
    print(json.dumps(dict(stage='checked', **stats)), flush=True)
    if failed:
        json.dump(failed, open(os.path.join(a.leanroot, 'k5_failed.json'), 'w'))
        print('FAILED leaves: see k5_failed.json; no Lean output written', flush=True)
        sys.exit(1)
    # leaf modules
    os.makedirs(os.path.join(a.leanroot, 'LebK', 'L'), exist_ok=True)
    os.makedirs(os.path.join(a.leanroot, 'LebesgueCover', 'K3'), exist_ok=True)
    hdr = ('import LebFast.Exact\nimport LebFast.VT\nimport LebK.Root3\n\n'
           '/-! Leaves {a}–{b} of the kernel-checked 5D certificate (`M(D, B₃, B₅) ≥ 0.8347`): box, witnesses, centre, '
           '`β`, `σ`, and the leaf check by `decide +kernel`. Generated by gen/k5/mkk5.py. -/\n\n'
           'open LebesgueCover.Fast\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n')
    for m, ls in sorted(leafmods.items()):
        txt = hdr.format(a=ls[0]['g'], b=ls[-1]['g']) + '\n'.join(leaf_text(n) for n in ls)
        open(os.path.join(a.leanroot, 'LebK', 'L', f'L{m:04d}.lean'), 'w').write(txt)
    # units and chunks
    nunits = 0; maxitems = 0
    chunks = {}
    for ci in cis:
        t = trees[ci]
        mark(t, a.units)
        us = units_post(t, []) if t['k'] == 'S' else []
        for k, u in enumerate(us):
            u['uname'] = f'U{ci:04d}_{k:04d}'
        root = dict(t)        # the cell unit: a walk over the cell tree down to its items
        root['unit'] = True; root['uname'] = f'C{ci:04d}'
        cell_units = us + [root]
        for u in cell_units:
            maxitems = max(maxitems, len(unit_walk(u)[1]))
        nunits += len(cell_units)
        chunks.setdefault(ci // 32, []).append((ci, cell_units))
    for j, lst in sorted(chunks.items()):
        mods = sorted({n['g'] // a.lb for ci, _ in lst for n in leaves(trees[ci], [])})
        txt = ('import LebesgueCover.TreeK\n' + ''.join(f'import LebK.L.L{m:04d}\n' for m in mods) + '\n'
               f'/-! Cells {32*j}–{32*j + 31} of the kernel-checked 5D certificate: tree walks with delegated items '
               '(leaves, sub-units) by `decide +kernel`, and the goodness of the cells. Generated by gen/k5/mkk5.py. -/\n\n'
               'open LebesgueCover.Fast LebesgueCover.Cert\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
               'namespace LebesgueCover.K3\n\n')
        txt += '\n'.join(unit_text(u) for ci, cus in lst for u in cus)
        cl = ', '.join(f'(C{ci:04d}.lo, C{ci:04d}.hi)' for ci, _ in lst)
        txt += '\n'.join([
            f'theorem chunk{j:02d} : ∀ c ∈ ((gridCells (gridSplits 5 2) rl3 rh3).drop ({j} * 32)).take 32,',
            '    GoodBox ns3 tau3 (fun i => c.1.getD i 0) (fun i => c.2.getD i 0) := by',
            f'  have e : ((gridCells (gridSplits 5 2) rl3 rh3).drop ({j} * 32)).take 32 = [{cl}] := by',
            '    decide +kernel',
            '  rw [e]',
            f'  exact AllGood.mem ({nested([f"C{ci:04d}.good" for ci, _ in lst])})',
            '', 'end LebesgueCover.K3', ''])
        open(os.path.join(a.leanroot, 'LebesgueCover', 'K3', f'G{j:02d}.lean'), 'w').write(txt)
    if len(cis) == len(cells):
        J = len(chunks)
        txt = ('import LebesgueCover.Main3\n' + ''.join(f'import LebesgueCover.K3.G{j:02d}\n' for j in range(J)) + '\n'
               '/-!\n# `M(D, B₃, B₅) ≥ 0.8347` and `Λ ≥ 0.8347` with a kernel-checked certificate\n\n'
               'The root box is good: its grid of 1024 cells is covered by the chunks (32 cells each). The certificate '
               'modules use `decide +kernel` only.\n-/\n\n'
               'open LebesgueCover.Fast LebesgueCover.Cert\n\nnamespace LebesgueCover.K3\n\n'
               '/-- The root box is good. -/\n'
               'theorem root3_good : GoodBox ns3 tau3 (fun i => rl3.getD i 0) (fun i => rh3.getD i 0) := by\n'
               f'  refine root_good\' (d := 5) (e := 2) (B := 32) (J := {J}) (fun j hj => ?_) (by norm_num)\n'
               '  interval_cases j\n'
               '  exacts [' + ', '.join(f'chunk{j:02d}' for j in range(J)) + ']\n\n'
               '/-- **`M(D, B₃, B₅) ≥ 0.8347`.** -/\n'
               'theorem hull3_geK : Hull3Statement := hull3_of_root_good root3_good\n\n'
               '/-- **`Λ ≥ 0.8347`** for weak universal covers. -/\n'
               'theorem weak_main3K : WeakMain3Statement := weak3_of_hull3 hull3_geK\n\n'
               '/-- **`Λ ≥ 0.8347`.** -/\n'
               'theorem main3K : Main3Statement := main3_of_weak3 weak_main3K\n\n'
               'end LebesgueCover.K3\n')
        open(os.path.join(a.leanroot, 'LebesgueCover', 'K3', 'Root3Good.lean'), 'w').write(txt)
    stats.update(leaf_modules=len(leafmods), chunks=len(chunks), units=nunits, max_items=maxitems,
                 secs=round(time.time() - t0))
    json.dump(stats, open(os.path.join(a.leanroot, 'k5_stats.json'), 'w'))
    print('DONE', json.dumps(stats), flush=True)
