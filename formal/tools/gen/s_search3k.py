"""11D-capable branch and bound in (t, s) coordinates (s = tan(rho/2)) with the Lean leaf model (gen/leafbound.py),
float; adds combination leaves (several fans on one box, convex weights from an LP; the analogue of Lemma 3.8 of
the paper). Rounds of depth-capped searches with splicing (as s_search2.py).
Codes: 0..d-1 split at the midpoint, 254 = single-fan leaf, 252 = combination leaf (data in the side list).
usage: s_search3k.py OUTDIR NPROC HEADER.json [--cells LIST | --stride K --offset O] [--depth D] [--margin M] [--nocomb]
(s_search3.py with --nocomb: single-fan leaves only, for the kernel-checked certificate)"""
import sys, os, json, time, argparse, pickle, math
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.environ.get('LEBESGUE_CHECKER', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checker')))   # the paper's checker/ (lbcheck.py)
import leafbound as LBd
import s_eval as SE
import s_search as SS
import lbcheck as REL
import highspy, scipy.sparse as sp

G = {}

def init(ns, tau, cell_w, margin, depth, aspect=0.0, nocomb=False):
    G['ch'] = REL.Checker(ns, tau, 1024, 1e-6)
    G.update(ns=ns, k=len(ns), tau=tau, cell_w=np.array(cell_w), margin=margin, depth=depth, aspect=aspect,
             nocomb=nocomb)

def lp_min(cvec, A_ub, b_ub, A_eq, b_eq):
    n = len(cvec); inf = highspy.kHighsInf
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('threads', 1)
    lp = highspy.HighsLp(); lp.num_col_ = n; lp.num_row_ = A_ub.shape[0] + A_eq.shape[0]
    lp.col_cost_ = np.asarray(cvec, float); lp.col_lower_ = np.zeros(n); lp.col_upper_ = np.full(n, inf)
    lp.row_lower_ = np.concatenate([np.full(A_ub.shape[0], -inf), b_eq]); lp.row_upper_ = np.concatenate([b_ub, b_eq])
    A = sp.csc_matrix(np.vstack([A_ub, A_eq]))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = A.indptr; lp.a_matrix_.index_ = A.indices; lp.a_matrix_.value_ = A.data
    h.passModel(lp); h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal: return None
    return np.array(h.getSolution().col_value)

def structure(ch, leaf, cprime, N=1024, eps=1e-6):
    """fan from the support points at the placement cprime (box coordinates), validated on the whole leaf box."""
    k = leaf.k
    c_rho = np.array(cprime, dtype=float).copy()
    for i in range(2, k + 1):
        si = LBd.pidx(i)[0]
        c_rho[si] = 2.0*math.atan(c_rho[si])
    N0, e0 = ch.N, ch.eps
    ch.N, ch.eps = N, eps; ch.th = np.array([2*math.pi*j/N for j in range(N)])
    try:
        ib, Qf = ch.witnesses(c_rho)
    finally:
        ch.N, ch.eps = N0, e0; ch.th = np.array([2*math.pi*j/N0 for j in range(N0)])
    shrink = 1.0 - 2.0**-30
    ib = list(ib); Q = [np.asarray(q)*shrink for q in Qf]
    lbs = LBd.pair_lbs_cheap(leaf, ib, Q, SE.ZS)
    zi = int(np.argmin((lbs <= 1e-13).sum(axis=1))); z = SE.ZS[zi]
    for _ in range(100):
        rows = LBd.pair_lbs_cheap(leaf, ib, Q, z[None, :])[0]
        if not (rows <= 1e-13).any() or len(ib) <= 4: break
        ib, Q = LBd.drop_bad(ib, Q, rows)
    for _ in range(100):
        rows = LBd.fan_rows(leaf, ib, Q, z)
        if not (rows <= 1e-13).any() or len(ib) <= 4: break
        ib, Q = LBd.drop_bad(ib, Q, rows)
    if len(ib) < 3 or (rows <= 1e-13).any() or not LBd.winding_ok(leaf, ib, Q, z):
        return None
    return ib, Q, z

def combination(ch, leaf, c, h, g0y, centre=None, nextra=4, N=1024, eps=1e-6):
    """combination bound over the centre structure and structures at shifted placements; returns (bound, data).
    data: list of (structure, alpha, s, sign vector, weight, N)."""
    k, d = leaf.k, len(c)
    gb = np.zeros(d)
    for i in range(1, k + 1):
        si, tx, ty = LBd.pidx(i)
        a, b, cc, ss = leaf.idx[i]
        gb[tx] += g0y[a]; gb[ty] += g0y[b]
        if si is not None:
            gb[si] += g0y[ss]
    order = np.argsort(-(np.abs(gb)*h))
    specs = [np.zeros(d, dtype=np.int8)]
    for kk in order[:nextra]:
        sv = np.zeros(d, dtype=np.int8); sv[kk] = -int(np.sign(gb[kk])) if gb[kk] != 0 else 1; specs.append(sv)
    sv = -np.sign(gb).astype(np.int8); sv[sv == 0] = 1; specs.append(sv)
    models = []
    for sv in specs:
        if centre is not None and not sv.any() and centre[3] == N:
            st = centre[:3]
        else:
            st = structure(ch, leaf, c + sv*h, N, eps)
        if st is None: continue
        a_, G_, bs, alpha, s = LBd.taylor_form(leaf, *st[:2])
        models.append((a_, G_, st, alpha, s, sv))
    if len(models) < 1: return -np.inf, None
    m = len(models); w = leaf.w; nv = len(w)
    av = np.array([x[0] for x in models]); Gm = np.array([x[1] for x in models])
    cvec = np.concatenate([-av, w])
    A_ub = np.vstack([np.hstack([Gm.T, -np.eye(nv)]), np.hstack([-Gm.T, -np.eye(nv)])])
    xs = lp_min(cvec, A_ub, np.zeros(2*nv), np.concatenate([np.ones(m), np.zeros(nv)])[None, :], np.array([1.0]))
    if xs is None: return -np.inf, None
    lam = np.maximum(xs[:m], 0.0)
    if not lam.sum() > 0: return -np.inf, None
    lam = lam/lam.sum()
    L = float(av @ lam - np.abs(Gm.T @ lam) @ w)
    keep = [j for j in range(m) if lam[j] > 0]
    return L, [(models[j][2], models[j][3], models[j][4], models[j][5], float(lam[j]), N) for j in keep]

def evaluate(ch, k, lo, hi, tau, margin):
    res = SS.evaluate(ch, k, lo, hi, tau)
    if res[0] == 'ok' and res[1] > margin:
        return 'single', res
    if res[3] is not None and not G.get('nocomb'):
        leaf = res[2][0]
        a_, G_, bs, alpha, s = LBd.taylor_form(leaf, res[3][0], res[3][1])
        if a_ - tau > margin:      # the first-order term is the loss: try fans from shifted placements
            F0, g, H, D = LBd.fan_quad(leaf, res[3][0], res[3][1])
            g0y = g + H @ leaf.y0
            c, hh = 0.5*(lo + hi), 0.5*(hi - lo)
            for (N, eps) in ((256, 1e-5), (1024, 1e-6)):
                L, data = combination(ch, leaf, c, hh, g0y, None, 4, N, eps)
                if data is not None and L - tau > margin:
                    return 'comb', (L - tau, data)
                if L - tau < -3e-3: break
    return 'split', res

def split3(k, lo, hi, cell_w, res, tau, margin):
    """split coordinate. When the centre fan itself is below tau + margin (witnesses were dropped because the box
    is too wide for positive fan rows), the loss vector does not see the cause: split the widest relative width."""
    if res[0] == 'low' and res[3] is not None:
        leaf = res[2][0]
        F0, g, H, D = LBd.fan_quad(leaf, res[3][0], res[3][1])
        if F0 + g @ leaf.y0 + 0.5*leaf.y0 @ H @ leaf.y0 - tau <= margin:
            return int(np.argmax((hi - lo)/cell_w))
    a = SS.split_coord(k, lo, hi, cell_w, res)
    asp = G.get('aspect')
    if asp:   # optional guard: never let one coordinate get more than `asp` times thinner than the widest one
        rel = (hi - lo)/cell_w
        if rel[a]*asp < rel.max(): a = int(np.argmax(rel))
    return a

def solve_box(task):
    tid, lo, hi = task
    ch, k, tau, margin, depth, cell_w = G['ch'], G['k'], G['tau'], G['margin'], G['depth'], G['cell_w']
    codes = bytearray(); unres = []; st = dict(single=0, comb=0, nodes=0); minm = None; t0 = time.time(); side = []
    stack = [(np.array(lo), np.array(hi), 0)]
    while stack:
        l, h, dep = stack.pop(); st['nodes'] += 1
        kind, res = evaluate(ch, k, l, h, tau, margin)
        if kind == 'single':
            codes.append(254); st['single'] += 1; minm = res[1] if minm is None else min(minm, res[1]); continue
        if kind == 'comb':
            codes.append(252); st['comb'] += 1; minm = res[0] if minm is None else min(minm, res[0])
            side.append([([int(v) for v in x[3]], x[4], x[5]) for x in res[1]]); continue
        if dep >= depth:
            codes.append(253); unres.append((l.tolist(), h.tolist())); continue
        a = split3(k, l, h, cell_w, res, tau, margin)
        codes.append(a)
        m = 0.5*(l[a] + h[a])
        l2, h2 = l.copy(), h.copy(); l2[a] = m
        l1, h1 = l.copy(), h.copy(); h1[a] = m
        stack.append((l2, h2, dep + 1)); stack.append((l1, h1, dep + 1))
    return tid, bytes(codes), unres, st, minm, time.time() - t0, side

def splice(tid, store):
    """full code array and side list of task tid (sub-tasks spliced in at their 253 placeholders)."""
    codes, nsub, side = store[tid]
    out = bytearray(); sd = []; sub = 0; k = 0
    for c in codes:
        if c == 253:
            c2, s2 = splice(tid + (sub,), store); out += c2; sd += s2; sub += 1
        else:
            out.append(c)
            if c == 252: sd.append(side[k]); k += 1
    assert sub == nsub and k == len(side)
    return bytes(out), sd

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('outdir'); ap.add_argument('nproc', type=int); ap.add_argument('header')
    ap.add_argument('--cells', default=''); ap.add_argument('--stride', type=int, default=1)
    ap.add_argument('--offset', type=int, default=0)
    ap.add_argument('--depth', type=int, default=6); ap.add_argument('--margin', type=float, default=1e-7)
    ap.add_argument('--aspect', type=float, default=0.0)
    ap.add_argument('--dump-from', type=int, default=-1)
    ap.add_argument('--nocomb', action='store_true')
    a = ap.parse_args()
    hd = json.load(open(a.header))
    ns, tau, split0 = hd['ns'], hd['tau'], hd['split0']
    lo, hi = np.array(hd['lo']), np.array(hd['hi'])
    s0 = np.array(split0); cell_w = (hi - lo)/s0
    os.makedirs(a.outdir, exist_ok=True)
    allcells = list(np.ndindex(*split0))
    if a.cells: cis = [int(x) for x in a.cells.split(',')]
    else: cis = list(range(a.offset, len(allcells), a.stride))
    tasks = [((ci,), (lo + (hi - lo)*np.array(allcells[ci])/s0).tolist(),
              (lo + (hi - lo)*(np.array(allcells[ci]) + 1)/s0).tolist()) for ci in cis]
    store = {}; rnd = 0; tot = dict(single=0, comb=0, nodes=0, cpu=0.0); t0 = time.time(); minm = None
    with Pool(a.nproc, initializer=init, initargs=(ns, tau, cell_w.tolist(), a.margin, a.depth, a.aspect, a.nocomb)) as pool:
        while tasks:
            if 0 <= a.dump_from <= rnd and len(tasks) <= 20000:
                json.dump([(list(t), l, h) for t, l, h in tasks], open(os.path.join(a.outdir, f'tasks_r{rnd:02d}.json'), 'w'))
            nxt = []; tr = time.time()
            for tid, codes, unres, st, mm, secs, side in pool.imap_unordered(solve_box, tasks, chunksize=1):
                store[tid] = (codes, len(unres), side)
                nxt += [(tid + (j,), lo_, hi_) for j, (lo_, hi_) in enumerate(unres)]
                for kk in ('single', 'comb', 'nodes'): tot[kk] += st[kk]
                tot['cpu'] += secs
                if mm is not None: minm = mm if minm is None else min(minm, mm)
            print(json.dumps(dict(round=rnd, tasks=len(tasks), unresolved=len(nxt), single=tot['single'],
                                  comb=tot['comb'], nodes=tot['nodes'], cpu=round(tot['cpu']),
                                  wall=round(time.time() - t0), round_wall=round(time.time() - tr),
                                  min_margin=minm)), flush=True)
            tasks = nxt; rnd += 1
    per = {}
    for ci in cis:
        arr, sd = splice((ci,), store)
        arrn = np.frombuffer(arr, dtype=np.uint8)
        np.save(os.path.join(a.outdir, f'cell{ci:04d}.npy'), arrn)
        json.dump(sd, open(os.path.join(a.outdir, f'cell{ci:04d}_side.json'), 'w'))
        per[ci] = dict(nodes=int(len(arrn)), single=int((arrn == 254).sum()), comb=int((arrn == 252).sum()))
    json.dump(dict(header=hd, cells=per, total=tot, min_margin=minm, wall=time.time() - t0),
              open(os.path.join(a.outdir, 'summary.json'), 'w'))
    print('TOTAL', json.dumps(dict(tot, min_margin=minm, wall=round(time.time() - t0))), flush=True)
