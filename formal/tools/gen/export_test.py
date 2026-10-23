"""Exact re-check (Fraction mirror of the Lean checker) of leaves of a search certificate (s_search.py output),
with the data proposed by the float pipeline.  Optionally writes a Lean test file with `#eval leafOK ...` for
some leaves.  usage: export_test.py CERTDIR PART NLEAVES [LEANOUT]"""
import sys, os, json, math, time
from fractions import Fraction as Fr
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.environ.get('LEBESGUE_CHECKER', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'checker')))   # the paper's checker/ (lbcheck.py)
import leafbound as LBd, s_eval as SE, exact as EX
import lbcheck as REL

def leaves_exact(certdir, part):
    meta = json.load(open(os.path.join(certdir, f'part{part:04d}.json')))
    codes = np.load(os.path.join(certdir, f'part{part:04d}.npy'))
    lo = [Fr(x) for x in meta['lo']]; hi = [Fr(x) for x in meta['hi']]
    s0 = meta['split0']; d = len(lo)
    cells = list(np.ndindex(*s0))[part::meta['nparts']]
    pos = 0
    for cell in cells:
        cl = [lo[a] + (hi[a] - lo[a])*cell[a]/s0[a] for a in range(d)]
        chh = [lo[a] + (hi[a] - lo[a])*(cell[a] + 1)/s0[a] for a in range(d)]
        stack = [(cl, chh)]
        while stack:
            l, h = stack.pop()
            code = int(codes[pos]); pos += 1
            if code >= 253:
                yield code, l, h
            else:
                m = (l[code] + h[code])/2
                l2, h2 = list(l), list(h); l2[code] = m
                l1, h1 = list(l), list(h); h1[code] = m
                stack.append((l2, h2)); stack.append((l1, h1))
    assert pos == len(codes)

def propose(ch, k, lo_f, hi_f, tau):
    """float pipeline: exactly the search's evaluate() (fast screening), returning its data."""
    import s_search as SS
    res = SS.evaluate(ch, k, lo_f, hi_f, tau)
    if res[3] is None:
        return [], [], np.zeros(2), {}, [0.0]*(4*k - 2), res[1]
    ib2, Q2, z, alpha, s, D = res[3]
    leaf = res[2][0]
    beta = {i: (alpha - 1.0)*D.get(i, 0.0) for i in range(2, k + 1)}
    sigma = [s[a]/leaf.w[a]**2 if leaf.w[a] > 0 else 0.0 for a in range(leaf.nv)]
    return ib2, Q2, z, beta, sigma, res[1]

def exact_data(ib, Q, z, beta, sigma):
    W = [(int(i), (EX.fr(q[0]), EX.fr(q[1]))) for i, q in zip(ib, Q)]
    zz = (EX.fr(z[0]), EX.fr(z[1]))
    bt = {i: EX.dyadic_near(v) for i, v in beta.items()}
    sg = [EX.dyadic_up(v*(1 + 1e-6) + 1e-12) for v in sigma]
    return W, zz, bt, sg

def lean_q(x):
    x = Fr(x)
    return f'({x.numerator} / {x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'

def lean_leaf(name, ns, tau, lo, hi, W, z, beta, sigma):
    k = len(ns); nv = 4*k - 2
    lines = [f'def {name}_lo : ℕ → ℚ := fun a => match a with']
    lines += [f'  | {a} => {lean_q(v)}' for a, v in enumerate(lo)] + ['  | _ => 0']
    lines += [f'def {name}_hi : ℕ → ℚ := fun a => match a with']
    lines += [f'  | {a} => {lean_q(v)}' for a, v in enumerate(hi)] + ['  | _ => 0']
    lines += [f'def {name}_W : List Wit := [']
    lines += [',\n'.join(f'  ⟨{i}, ({lean_q(q[0])}, {lean_q(q[1])})⟩' for i, q in W)] + [']']
    lines += [f'def {name}_z : ℚ × ℚ := ({lean_q(z[0])}, {lean_q(z[1])})']
    lines += [f'def {name}_beta : ℕ → ℚ := fun i => match i with']
    lines += [f'  | {i} => {lean_q(v)}' for i, v in beta.items()] + ['  | _ => 0']
    lines += [f'def {name}_sigma : ℕ → ℚ := fun a => match a with']
    lines += [f'  | {a} => {lean_q(v)}' for a, v in enumerate(sigma)] + ['  | _ => 0']
    lines += [f'#eval leafOK {ns} vt ({lean_q(tau)}) {name}_lo {name}_hi {name}_W {name}_z {name}_beta {name}_sigma']
    return '\n'.join(lines)

def lean_vt(VT, nu):
    lines = ['def vt : VertTable where', '  V := fun n l => match n, l with']
    lines += [f'    | {n}, {l} => ({lean_q(v[0])}, {lean_q(v[1])})' for (n, l), v in sorted(VT.items())]
    lines += ['    | _, _ => (0, 0)', f'  ν := {lean_q(nu)}']
    return '\n'.join(lines)

if __name__ == '__main__':
    certdir, part, nleaves = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    leanout = sys.argv[4] if len(sys.argv) > 4 else None
    meta = json.load(open(os.path.join(certdir, f'part{part:04d}.json')))
    ns = meta['ns']; k = len(ns); tau_f = meta['tau']; tau = Fr(repr(float(tau_f)))
    ch = REL.Checker(ns, tau_f, 1024, 1e-6)
    VT = EX.vert_table(ns)
    out = []; t0 = time.time(); nok = 0; n = 0
    lean_parts = []
    for code, lo, hi in leaves_exact(certdir, part):
        if code != 254: continue
        lo_f = np.array([float(x) for x in lo]); hi_f = np.array([float(x) for x in hi])
        ib, Q, z, beta, sigma, mfl = propose(ch, k, lo_f, hi_f, tau_f)
        W, zz, bt, sg = exact_data(ib, Q, z, beta, sigma)
        t1 = time.time()
        ok, checks, margin, minrow = EX.leafOK(ns, VT, EX.NU, tau, lo, hi, W, zz, bt, sg, detail=True)
        te = time.time() - t1
        n += 1; nok += ok
        print(json.dumps(dict(ok=ok, float_margin=mfl, exact_margin=float(margin), failed=[c[0] for c in checks if not c[1]],
                              m=len(W), exact_secs=round(te, 3))), flush=True)
        if leanout and len(lean_parts) < 3:
            lean_parts.append(lean_leaf(f'leaf{n}', ns, tau, lo, hi, W, zz, bt, sg))
        if n >= nleaves: break
    print('SUMMARY', n, 'ok', nok, 'secs', round(time.time() - t0, 1), flush=True)
    if leanout:
        hdr = 'import LebesgueCover.Checker\nopen LebesgueCover.Cert\n\n' + lean_vt(VT, EX.NU) + '\n\n'
        open(leanout, 'w').write(hdr + '\n\n'.join(lean_parts) + '\n')
