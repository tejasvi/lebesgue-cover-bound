"""Kernel-checked certificate for M(D, B3, B5, B7) >= 0.836 (8D, single-fan leaves): Lean modules from a search tree
(s_search3k.py --nocomb output), chunk by chunk.

Leaf data: the search's float proposal (export_test.propose) made exact (export_test.exact_data) and checked exactly
(exact.leafOK, the Fraction mirror of the checker); a failing leaf is split at the midpoint of its widest relative
coordinate until the halves pass (depth <= 6). The witnesses of a leaf are packed into one natural number (LebK/Decode:
slot j = bits 152 j .. 152 j + 151 holds the body in 4 bits and the two coordinates, each `(|a| 2^8 + e) 2 + sign`).
Units: every cell tree is cut into units of at most U delegated items (leaves or sub-units); a unit is a tree walk with
delegated items (code 250), checked by `decide +kernel`, and is good when its items are good (`cellK_good`).
Output under LEANROOT:
  LebK/L8/L<j>_<m>.lean        core Lean, <= LB leaves of chunk j each: namespace LebK.Q<j>_<i> with lo, hi, wit
                               (packed), cen, beta, sigma and
                               `ok : leafOKF ns4 VQ nu4 tau4 … (unpackW n wit) … = true := by decide +kernel`
  LebesgueCover/K8/G<j>.lean   units of the CB cells of chunk j (bottom-up), cell units C<c>, theorem chunk<j>
  LebesgueCover/K8/Root4Good.lean   root4_good, hull4_geK, weak_mainK, mainK
usage: mkk8.py HEADER SEARCHDIR LEANROOT NPROC [--lb 32] [--units 32] [--chunk 256] [--chunks LIST]"""
import sys, os, json, time, argparse
from fractions import Fraction as Fr
from multiprocessing import Pool
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.environ.get('LEBESGUE_CHECKER', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'checker')))   # the paper's checker/ (lbcheck.py)
import exact as EX, export_test as ET
import lbcheck as REL

sys.set_int_max_str_digits(0)
G = {}
SLOT = 152

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

def encq(x):
    x = Fr(x); d = x.denominator; e = d.bit_length() - 1
    assert d == 1 << e and e < 256, x
    a = abs(x.numerator); assert a < (1 << 64), x
    return (((a << 8) | e) << 1) | (1 if x.numerator < 0 else 0)

def pack(W):
    n = 0
    for i, (b, (x, y)) in enumerate(W):
        assert 0 <= b < 16
        slot = (((encq(x) << 73) | encq(y)) << 4) | b
        assert slot < (1 << SLOT)
        n |= slot << (SLOT * i)
    return n

def decq(c):
    s = c % 2; e = (c // 2) % 256; a = c // 512
    return Fr(-a if s == 1 else a, 1 << e)

def unpack(m, n):
    out = []
    for _ in range(m):
        c = n % (1 << SLOT)
        out.append((c % 16, (decq(c // 16 // (1 << 73)), decq((c // 16) % (1 << 73)))))
        n //= (1 << SLOT)
    return out

def leaf_text(n):
    W, z, bt, sg = n['data']
    P = pack(W)
    assert unpack(len(W), P) == [(int(b), (Fr(x), Fr(y))) for b, (x, y) in W]
    nm = n['name']
    return '\n'.join([
        f'namespace {nm}',
        f'noncomputable def lo : Array Rat := {arr(n["lo"])}',
        f'noncomputable def hi : Array Rat := {arr(n["hi"])}',
        f'noncomputable def wit : Nat := {P}',
        f'noncomputable def cen : Rat × Rat := ({q(z[0])}, {q(z[1])})',
        'noncomputable def beta : Nat → Rat := fun i => match i with'
        + ''.join(f' | {i} => {q(v)}' for i, v in sorted(bt.items())) + ' | _ => 0',
        'noncomputable def sigma : Nat → Rat := fun a => match a with'
        + ''.join(f' | {a} => {q(v)}' for a, v in enumerate(sg)) + ' | _ => 0',
        f'theorem ok : leafOKF ns4 VQ nu4 tau4 (fun a => lo.getD a 0) (fun a => hi.getD a 0) (unpackW {len(W)} wit) cen beta',
        '    sigma = true := by',
        '  decide +kernel',
        f'end {nm}', ''])

def nested(goods):
    s = '.nil'
    for g in reversed(goods):
        s = f'.cons {g} ({s})' if s != '.nil' else f'.cons {g} .nil'
    return s

def unit_text(u):
    codes, items = unit_walk(u)
    refs = [(f'{it["name"]}.lo', f'{it["name"]}.hi', f'(leafF_good vt4 {it["name"]}.ok)') if it['k'] == 'L' else
            (f'{it["uname"]}.lo', f'{it["uname"]}.hi', f'{it["uname"]}.good') for it in items]
    nm = u['uname']
    return '\n'.join([
        f'namespace {nm}',
        f'noncomputable def lo : Array Rat := {arr(u["lo"])}',
        f'noncomputable def hi : Array Rat := {arr(u["hi"])}',
        f'theorem walk_ok : (walk ns4 #[] VQ nu4 tau4 {len(codes)} {codes} [] [' + ', '.join(f'({a}, {b})' for a, b, _ in refs)
        + '] lo hi).isSome = true := by',
        '  decide +kernel',
        'theorem good : GoodBox ns4 tau4 (fun i => lo.getD i 0) (fun i => hi.getD i 0) :=',
        f'  cellK_good vt4 ({nested([g for _, _, g in refs])}) walk_ok',
        f'end {nm}', ''])

LEAF_HDR = ('import LebFast.Exact\nimport LebFast.VT\nimport LebK.Root4\nimport LebK.Decode\n\n'
            '/-! Leaves {a}–{b} of chunk {j} of the kernel-checked 8D certificate (`M(D, B₃, B₅, B₇) ≥ 0.836`): box, packed witnesses, '
            'centre, `β`, `σ`, and the leaf check by `decide +kernel`. Generated by gen/k8/mkk8.py. -/\n\n'
            'open LebesgueCover.Fast\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n')

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('header'); ap.add_argument('searchdir'); ap.add_argument('leanroot'); ap.add_argument('nproc', type=int)
    ap.add_argument('--lb', type=int, default=32); ap.add_argument('--units', type=int, default=32)
    ap.add_argument('--chunk', type=int, default=256); ap.add_argument('--chunks', default='')
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
    CB = a.chunk; J = len(cells) // CB; assert J * CB == len(cells)
    js = [int(x) for x in a.chunks.split(',')] if a.chunks else list(range(J))
    for sub in ('LebK/L8', 'LebesgueCover/K8'):
        os.makedirs(os.path.join(a.leanroot, sub), exist_ok=True)
    gidx = 0; midx = 0; stats = dict(leaves=0, failed=0, refined_leaves=0, units=0, max_items=0, leaf_modules=0)
    minmargin = None; mlen = []; failed = []
    with Pool(a.nproc, initializer=init, initargs=(ns, tau_f, cell_w)) as pool:
        for j in js:
            cis = list(range(j*CB, (j + 1)*CB))
            trees = {ci: parse(np.load(os.path.join(a.searchdir, f'cell{ci:04d}.npy')), cells[ci][0], cells[ci][1]) for ci in cis}
            tasks = [(n['lo'], n['hi'], 0) for ci in cis for n in leaves(trees[ci], [])]
            res = iter(pool.map(solve, tasks, chunksize=4))
            def subst(n):
                if n['k'] == 'L':
                    return next(res)
                n['l'] = subst(n['l']); n['r'] = subst(n['r'])
                return n
            for ci in cis:
                trees[ci] = subst(trees[ci])
            # leaves: names and modules (a module never spans chunks)
            lmods = []; cur = []; chunk_leaves = []
            for ci in cis:
                for n in leaves(trees[ci], []):
                    if n['data'] is None:
                        failed.append((ci, [str(x) for x in n['lo']], [str(x) for x in n['hi']], n['margin']))
                        continue
                    minmargin = n['margin'] if minmargin is None else min(minmargin, n['margin'])
                    mlen.append(len(n['data'][0])); stats['refined_leaves'] += n['refined'] > 0
                    n['name'] = f'LebK.Q{j:03d}_{len(chunk_leaves):05d}'; n['g'] = len(chunk_leaves); gidx += 1
                    chunk_leaves.append(n)
                    if len(cur) == a.lb:
                        lmods.append(cur); cur = []
                    cur.append(n)
            if cur:
                lmods.append(cur)
            if failed:
                break
            mods_of_chunk = []
            for mi, ls in enumerate(lmods):
                txt = LEAF_HDR.format(j=j, a=ls[0]['g'], b=ls[-1]['g']) + '\n'.join(leaf_text(n) for n in ls)
                open(os.path.join(a.leanroot, 'LebK', 'L8', f'L{j:03d}_{mi:03d}.lean'), 'w').write(txt)
                mods_of_chunk.append(f'{j:03d}_{mi:03d}'); midx += 1
            # units of the chunk's cells
            units = []
            for ci in cis:
                t = trees[ci]
                mark(t, a.units)
                us = units_post(t, []) if t['k'] == 'S' else []
                for k, u in enumerate(us):
                    u['uname'] = f'U{ci:05d}_{k:04d}'
                root = dict(t); root['unit'] = True; root['uname'] = f'C{ci:05d}'
                for u in us + [root]:
                    stats['max_items'] = max(stats['max_items'], len(unit_walk(u)[1]))
                units += us + [root]
            stats['units'] += len(units)
            txt = ('import LebesgueCover.K8Base\n' + ''.join(f'import LebK.L8.L{m}\n' for m in mods_of_chunk) + '\n'
                   f'/-! Cells {j*CB}–{(j + 1)*CB - 1} of the kernel-checked 8D certificate: tree walks with delegated items '
                   '(leaves, sub-units) by `decide +kernel`, and the goodness of the cells. Generated by gen/k8/mkk8.py. -/\n\n'
                   'open LebesgueCover.Fast LebesgueCover.Cert\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
                   'namespace LebesgueCover.K8\n\n')
            txt += '\n'.join(unit_text(u) for u in units)
            cl = ', '.join(f'(C{ci:05d}.lo, C{ci:05d}.hi)' for ci in cis)
            txt += '\n'.join([
                f'theorem chunk{j:03d} : ∀ c ∈ ((gridCells (gridSplits {d} 2) rl4 rh4).drop ({j} * {CB})).take {CB},',
                '    GoodBox ns4 tau4 (fun i => c.1.getD i 0) (fun i => c.2.getD i 0) := by',
                f'  have e : ((gridCells (gridSplits {d} 2) rl4 rh4).drop ({j} * {CB})).take {CB} = [{cl}] := by',
                '    decide +kernel',
                '  rw [e]',
                f'  exact AllGood.mem ({nested([f"C{ci:05d}.good" for ci in cis])})',
                '', 'end LebesgueCover.K8', ''])
            open(os.path.join(a.leanroot, 'LebesgueCover', 'K8', f'G{j:03d}.lean'), 'w').write(txt)
            print(json.dumps(dict(chunk=j, leaves=gidx, modules=midx, units=stats['units'],
                                  secs=round(time.time() - t0))), flush=True)
    stats.update(leaves=gidx, failed=len(failed), leaf_modules=midx, min_exact_margin=minmargin,
                 witnesses_min=min(mlen) if mlen else None, witnesses_max=max(mlen) if mlen else None,
                 witnesses_mean=sum(mlen)/len(mlen) if mlen else None, chunks=len(js), secs=round(time.time() - t0))
    if failed:
        json.dump(failed, open(os.path.join(a.leanroot, 'k8_failed.json'), 'w'))
        print('FAILED leaves: see k8_failed.json', flush=True)
        sys.exit(1)
    if len(js) == J:
        txt = ('import LebesgueCover.Main4\n' + ''.join(f'import LebesgueCover.K8.G{j:03d}\n' for j in range(J)) + '\n'
               '/-!\n# `M(D, B₃, B₅, B₇) ≥ 0.836` and `Λ ≥ 0.836` with a kernel-checked certificate\n\n'
               f'The root box is good: its grid of {len(cells)} cells is covered by {J} chunks of {CB} cells. The certificate '
               'modules use `decide +kernel` only.\n-/\n\n'
               'open LebesgueCover.Fast LebesgueCover.Cert\n\nnamespace LebesgueCover.K8\n\n'
               '/-- The root box is good. -/\n'
               'theorem root4_good : GoodBox ns4 tau4 (fun i => rl4.getD i 0) (fun i => rh4.getD i 0) := by\n'
               f'  refine root_good\' (d := {d}) (e := 2) (B := {CB}) (J := {J}) (fun j hj => ?_) (by norm_num)\n'
               '  interval_cases j\n'
               '  exacts [' + ', '.join(f'chunk{j:03d}' for j in range(J)) + ']\n\n'
               '/-- **`M(D, B₃, B₅, B₇) ≥ 0.836`.** -/\n'
               'theorem hull4_geK : Hull4Statement := hull4_of_root_good root4_good\n\n'
               '/-- **`Λ ≥ 0.836`** for weak universal covers. -/\n'
               'theorem weak_mainK : WeakMainStatement := weak_of_hull4 hull4_geK\n\n'
               '/-- **`Λ ≥ 0.836`.** -/\n'
               'theorem mainK : MainStatement := main_of_hull4 hull4_geK\n\n'
               'end LebesgueCover.K8\n')
        open(os.path.join(a.leanroot, 'LebesgueCover', 'K8', 'Root4Good.lean'), 'w').write(txt)
    json.dump(stats, open(os.path.join(a.leanroot, 'k8_stats.json'), 'w'))
    print('DONE', json.dumps(stats), flush=True)
