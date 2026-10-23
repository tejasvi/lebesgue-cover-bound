"""Branch and bound in (t, s) coordinates (s = tan(rho/2)) with the Lean leaf model (gen/leafbound.py), float.
Writes a certificate tree in the format of the published certificates (header JSON + uint8 code array per part):
codes 0..d-1 = split at the midpoint of that coordinate, 254 = leaf closed by the fan bound.
usage: s_search.py OUTDIR NPROC NPARTS ns(comma) tau "lo;hi" (or 'paper:CERTDIR') S2 [S3] [--margin M] [--maxdepth D]"""
import sys, os, json, math, time, argparse
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.environ.get('LEBESGUE_CHECKER', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checker')))   # the paper's checker/ (lbcheck.py)
import leafbound as LBd
import s_eval as SE
import lbcheck as REL

def evaluate(ch, k, lo, hi, tau, slack=3e-5):
    """(status, margin, (leaf, loss_y)) for the box; fast screening with cheap pair bounds."""
    leaf = LBd.Leaf(k, lo, hi)
    best = None
    for (N, eps) in ((256, 1e-5), (1024, 1e-6)):
        ib, Q = SE.witnesses_at(ch, leaf, N, eps)
        lbs = LBd.pair_lbs_cheap(leaf, ib, Q, SE.ZS)
        zi = int(np.argmin((lbs <= 1e-13).sum(axis=1))); z = SE.ZS[zi]
        ib2, Q2 = list(ib), list(Q)
        for _ in range(100):
            rows = LBd.pair_lbs_cheap(leaf, ib2, Q2, z[None, :])[0]
            if not (rows <= 1e-13).any() or len(ib2) <= 4: break
            ib2, Q2 = LBd.drop_bad(ib2, Q2, rows)
        for _ in range(100):
            rows = LBd.fan_rows(leaf, ib2, Q2, z)
            if not (rows <= 1e-13).any() or len(ib2) <= 4: break
            ib2, Q2 = LBd.drop_bad(ib2, Q2, rows)
        if len(ib2) < 3 or (rows <= 1e-13).any() or not LBd.winding_ok(leaf, ib2, Q2, z):
            res = ('fan', -1.0, None, None)
        else:
            b, alpha, s = LBd.leaf_bound(leaf, ib2, Q2)
            F0, g, H, D = LBd.fan_quad(leaf, ib2, Q2)
            loss_y = np.abs(g + H @ leaf.y0)*leaf.w + 0.5*s
            res = ('ok' if b > tau else 'low', b - tau, (leaf, loss_y), (ib2, Q2, z, alpha, s, D))
        if best is None or res[1] > best[1]: best = res
        if best[0] == 'ok' or best[1] < -slack: break
    return best

def split_coord(k, lo, hi, cell_w, res):
    """coordinate to split: largest loss (mapped from y to box coordinates) or widest relative width."""
    d = len(lo)
    rel = (hi - lo)/cell_w
    if res[2] is None:
        return int(np.argmax(rel))
    leaf, loss_y = res[2]
    loss = np.zeros(d)
    for i in range(1, k + 1):
        si, tx, ty = LBd.pidx(i)
        a, b, cc, ss = leaf.idx[i]
        loss[tx] += loss_y[a]; loss[ty] += loss_y[b]
        if si is not None:
            loss[si] += loss_y[cc] + loss_y[ss]
    if loss.max() <= 0:
        return int(np.argmax(rel))
    return int(np.argmax(loss))

def run_part(args):
    outdir, part, nparts, ns, tau, lo, hi, split0, margin, maxdepth = args
    k = len(ns)
    ch = REL.Checker(ns, tau, 1024, 1e-6)
    lo = np.array(lo); hi = np.array(hi); s0 = np.array(split0)
    cell_w = (hi - lo)/s0
    cells = list(np.ndindex(*split0))[part::nparts]
    codes = bytearray(); t0 = time.time(); nleaf = 0; nnode = 0; minm = None; maxd = 0; nfail = 0
    for cell in cells:
        cl = lo + (hi - lo)*np.array(cell)/s0; chh = lo + (hi - lo)*(np.array(cell) + 1)/s0
        stack = [(cl, chh, 0)]
        while stack:
            l, h, dep = stack.pop()
            nnode += 1
            res = evaluate(ch, k, l, h, tau)
            if res[0] == 'ok' and res[1] > margin:
                codes.append(254); nleaf += 1
                minm = res[1] if minm is None else min(minm, res[1]); maxd = max(maxd, dep)
                continue
            if dep >= maxdepth:
                codes.append(253); nfail += 1   # unresolved (never in a final certificate)
                continue
            a = split_coord(k, l, h, cell_w, res)
            codes.append(a)
            m = 0.5*(l[a] + h[a])
            l2, h2 = l.copy(), h.copy(); l2[a] = m
            l1, h1 = l.copy(), h.copy(); h1[a] = m
            stack.append((l2, h2, dep + 1)); stack.append((l1, h1, dep + 1))
    np.save(os.path.join(outdir, f'part{part:04d}.npy'), np.frombuffer(bytes(codes), dtype=np.uint8))
    meta = dict(ns=ns, tau=tau, part=part, nparts=nparts, split0=list(split0), lo=list(map(float, lo)),
                hi=list(map(float, hi)), coords='t,s (s = tan(rho/2))', margin=margin, nodes=nnode, leaves=nleaf,
                unresolved=nfail, minL_margin=minm, maxdepth=maxd, secs=time.time() - t0)
    json.dump(meta, open(os.path.join(outdir, f'part{part:04d}.json'), 'w'))
    return meta

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('outdir'); ap.add_argument('nproc', type=int); ap.add_argument('nparts', type=int)
    ap.add_argument('paper_certdir'); ap.add_argument('S', type=float, nargs='+')
    ap.add_argument('--margin', type=float, default=1e-7); ap.add_argument('--maxdepth', type=int, default=60)
    a = ap.parse_args()
    m0 = json.load(open(os.path.join(a.paper_certdir, 'part0000.json')))
    lo, hi = SE.root_box(m0, a.S)
    os.makedirs(a.outdir, exist_ok=True)
    tasks = [(a.outdir, p, a.nparts, m0['ns'], m0['tau'], lo.tolist(), hi.tolist(), m0['split0'], a.margin, a.maxdepth)
             for p in range(a.nparts)]
    tot = dict(nodes=0, leaves=0, unresolved=0)
    with Pool(a.nproc) as pool:
        for meta in pool.imap_unordered(run_part, tasks):
            for kk in tot: tot[kk] += meta[kk]
            print(json.dumps({kk: meta[kk] for kk in ('part', 'nodes', 'leaves', 'unresolved', 'minL_margin', 'maxdepth', 'secs')}), flush=True)
    print('TOTAL', json.dumps(tot), flush=True)
