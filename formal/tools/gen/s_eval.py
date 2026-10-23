"""Evaluate the Lean leaf check (float model, gen/leafbound.py) on every leaf of a published certificate tree,
reinterpreted in (t, s) coordinates (s = tan(rho/2); root s-ranges [0, S]; same codes, exact midpoint splits).
Not a proof.  usage: s_eval.py CERTDIR NPROC OUT NSUB S2 [S3]"""
import sys, os, json, math, time
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.environ.get('LEBESGUE_CHECKER', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checker')))   # the paper's checker/ (lbcheck.py)
import leafbound as LBd
import lbcheck as REL   # release checker: used ONLY for its float witness heuristic (untrusted data generation)

ZS = np.array([(0.0, 0.0)] + [(0.12*math.cos(a*math.pi/4), 0.12*math.sin(a*math.pi/4)) for a in range(8)])

def root_box(meta, S):
    lo = np.array(meta['lo'], dtype=float); hi = np.array(meta['hi'], dtype=float)
    k = len(meta['ns'])
    for i in range(2, k + 1):
        si = LBd.pidx(i)[0]
        lo[si] = 0.0; hi[si] = S[i - 2]
    return lo, hi

def leaves(certdir, part, meta, S):
    codes = np.load(os.path.join(certdir, f'part{part:04d}.npy'))
    lo, hi = root_box(meta, S)
    s0 = np.array(meta['split0'])
    cells = list(np.ndindex(*meta['split0']))[part::meta['nparts']]
    pos = 0
    for ci, cell in enumerate(cells):
        cl = lo + (hi - lo)*np.array(cell)/s0; chh = lo + (hi - lo)*(np.array(cell) + 1)/s0
        stack = [(cl, chh, 0)]
        while stack:
            l, h, dep = stack.pop()
            code = int(codes[pos]); pos += 1
            if code >= 254:
                yield code, l, h, dep, ci
            else:
                m = 0.5*(l[code] + h[code])
                l2, h2 = l.copy(), h.copy(); l2[code] = m
                l1, h1 = l.copy(), h.copy(); h1[code] = m
                stack.append((l2, h2, dep + 1)); stack.append((l1, h1, dep + 1))

def witnesses_at(ch, leaf, N, eps):
    """release heuristic at the centre placement (angles from the exact centre rotations)."""
    k = leaf.k
    c_rho = leaf.c.copy()
    for i in range(2, k + 1):
        c_rho[LBd.pidx(i)[0]] = leaf.rho(i)
    N0, e0 = ch.N, ch.eps
    ch.N, ch.eps = N, eps; ch.th = np.array([2*math.pi*j/N for j in range(N)])
    try:
        ib, Qf = ch.witnesses(c_rho)
    finally:
        ch.N, ch.eps = N0, e0; ch.th = np.array([2*math.pi*j/N0 for j in range(N0)])
    shrink = 1.0 - 2.0**-30
    return list(ib), [np.asarray(q)*shrink for q in Qf]

def check_leaf(ch, k, lo, hi, tau):
    leaf = LBd.Leaf(k, lo, hi)
    best = None
    for (N, eps) in ((256, 1e-5), (1024, 1e-6)):
        ib, Q = witnesses_at(ch, leaf, N, eps)
        # fan centre: fewest failing rows
        zb = None
        for z in ZS:
            nb = int((LBd.fan_rows(leaf, ib, Q, z) <= 1e-13).sum())
            if zb is None or nb < zb[0]: zb = (nb, z)
            if nb == 0: break
        z = zb[1]
        ib2, Q2 = list(ib), list(Q)
        for _ in range(600):
            rows = LBd.fan_rows(leaf, ib2, Q2, z)
            bad = np.nonzero(rows <= 1e-13)[0]
            if len(bad) == 0 or len(ib2) <= 4: break
            j = int(bad[0]); j2 = (j + 1) % len(ib2); drop = j2 if ib2[j2] != 0 else j
            del ib2[drop]; del Q2[drop]
        rows = LBd.fan_rows(leaf, ib2, Q2, z)
        if len(ib2) < 3 or (rows <= 1e-13).any():
            res = ('fan', -1.0, len(ib2))
        elif not LBd.winding_ok(leaf, ib2, Q2, z):
            res = ('wind', -1.0, len(ib2))
        else:
            b, alpha, s = LBd.leaf_bound(leaf, ib2, Q2)
            res = ('ok' if b > tau else 'low', b - tau, len(ib2))
        if best is None or res[1] > best[1]: best = res
        if best[0] == 'ok' and best[1] > 1e-7: break
    return best

def run(args):
    certdir, part, sub, nsub, S = args
    meta = json.load(open(os.path.join(certdir, f'part{part:04d}.json')))
    k = len(meta['ns']); tau = meta['tau']
    ch = REL.Checker(meta['ns'], meta['tau'], meta['N'], meta['eps'])
    n = 0; nfail = 0; fails = []; minm = None; t0 = time.time(); ms = []
    for code, l, h, dep, ci in leaves(certdir, part, meta, S):
        if ci % nsub != sub: continue
        if code != 254:
            fails.append(('code255', dep, l.tolist(), h.tolist())); continue
        st, mg, m = check_leaf(ch, k, l, h, tau)
        n += 1; ms.append(m)
        if minm is None or mg < minm: minm = mg
        if st != 'ok':
            nfail += 1; fails.append((st, dep, mg, l.tolist(), h.tolist()))
    return dict(part=part, sub=sub, leaves=n, fails=nfail, min_margin=minm, secs=time.time() - t0,
                m_mean=float(np.mean(ms)) if ms else 0.0, fail_list=fails)

if __name__ == '__main__':
    certdir, nproc, out, nsub = sys.argv[1], int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    S = [float(x) for x in sys.argv[5:]]
    m0 = json.load(open(os.path.join(certdir, 'part0000.json')))
    tasks = [(certdir, p, sb, nsub, S) for p in range(m0['nparts']) for sb in range(nsub)]
    with Pool(nproc) as pool, open(out, 'w') as f:
        for res in pool.imap_unordered(run, tasks):
            f.write(json.dumps(res) + '\n'); f.flush()
