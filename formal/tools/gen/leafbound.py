"""Float model of the Lean leaf check in (t, s) coordinates, s = tan(rho/2) (not a proof; the exact check is separate).

Box coordinates: k = 2: (t1x, t1y, s2, t2x, t2y); k = 3: (t1x, t1y, s2, t2x, t2y, s3, t3x, t3y).
Rotation of body i >= 2 on a leaf: R(u(s)) = R(M) R(delta), M = u(s_m), u(s) = ((1 - s^2), 2 s)/(1 + s^2);
C = cos(delta) - 1 in [-Cmax, 0], S = sin(delta) in [-Smax, Smax] with Cmax, Smax the exact values at the endpoints.
Witness positions are affine in y = (dt_1, [dt_i, C_i, S_i]_{i>=2}); the fan area F and the fan determinants are exact
quadratics in y; F gets the identity beta_i (2 C_i + C_i^2 + S_i^2) = 0 added (beta chosen from a small scan).
Leaf passes if: fan determinants > 0 on the y-box; winding certificate at the centre; F lower bound > tau.
"""
import math
import numpy as np

def u_of(s):
    d = 1.0 + s*s
    return np.array([(1.0 - s*s)/d, 2.0*s/d])

def rotm(u):
    return np.array([[u[0], -u[1]], [u[1], u[0]]])

def Jv(v):
    return np.array([-v[1], v[0]])

def det2(a, b):
    return a[0]*b[1] - a[1]*b[0]

def layout(k):
    """index tuples per body: body 1 -> (dtx, dty, None, None); body i >= 2 -> (dtx, dty, C, S)."""
    idx = {1: (0, 1, None, None)}
    nv = 2
    for i in range(2, k + 1):
        idx[i] = (nv, nv + 1, nv + 2, nv + 3); nv += 4
    return idx, nv

def pidx(i):
    """coordinates of body i in the box vector: (s, tx, ty) (s = None for body 1)."""
    if i == 1:
        return (None, 0, 1)
    b = 2 + 3*(i - 2)
    return (b, b + 1, b + 2)

def rot_ranges(s_lo, s_hi):
    """centre M = u(s_m) and exact ranges Cmax, Smax of C = cos(delta) - 1, S = sin(delta) over s in [s_lo, s_hi]."""
    s_m = 0.5*(s_lo + s_hi)
    M = u_of(s_m)
    Cmax = 0.0; Smax = 0.0
    for s in (s_lo, s_hi):
        us = u_of(s)
        Cmax = max(Cmax, 1.0 - float(M @ us))
        Smax = max(Smax, abs(det2(M, us)))
    return s_m, M, Cmax, Smax

class Leaf:
    """y-coordinates and witness linearization for a box (lo, hi)."""
    def __init__(self, k, lo, hi):
        self.k = k
        self.idx, self.nv = layout(k)
        self.c = 0.5*(lo + hi); self.h = 0.5*(hi - lo)
        self.M = {}; self.t = {0: np.zeros(2)}
        self.y0 = np.zeros(self.nv); self.w = np.zeros(self.nv)
        for i in range(1, k + 1):
            si, tx, ty = pidx(i)
            a, b, cc, ss = self.idx[i]
            self.t[i] = np.array([self.c[tx], self.c[ty]])
            self.w[a] = self.h[tx]; self.w[b] = self.h[ty]
            if si is None:
                self.M[i] = np.array([1.0, 0.0])
            else:
                s_m, M, Cmax, Smax = rot_ranges(lo[si], hi[si])
                self.M[i] = M
                self.y0[cc] = -0.5*Cmax; self.w[cc] = 0.5*Cmax
                self.w[ss] = Smax
        self.M[0] = np.array([1.0, 0.0])

    def rho(self, i):
        """rotation angle at the centre (for the float witness heuristic)."""
        return math.atan2(self.M[i][1], self.M[i][0])

    def lin(self, i, q):
        """x = X0 + L y for a witness (i, q)."""
        L = np.zeros((2, self.nv))
        if i == 0:
            return np.array(q, dtype=float), L
        a_ = rotm(self.M[i]) @ q
        X0 = a_ + self.t[i]
        ia, ib, cc, ss = self.idx[i]
        L[:, ia] = [1.0, 0.0]; L[:, ib] = [0.0, 1.0]
        if cc is not None:
            L[:, cc] = a_; L[:, ss] = Jv(a_)
        return X0, L

JP = np.array([[0.0, 1.0], [-1.0, 0.0]])   # det(a, b) = a^T JP b

def quad_det(X0, L, Y0, Mm):
    """det(X0 + L y, Y0 + M y) = c0 + g.y + y^T A y (A not symmetric)."""
    c0 = X0 @ JP @ Y0
    g = X0 @ JP @ Mm + L.T @ JP @ Y0
    A = L.T @ JP @ Mm
    return c0, g, A

def quad_lower(c0, g, A, y0, w):
    """lower bound of c0 + g.y + y^T A y over the box y0 + [-w, w] (absolute values for the quadratic part)."""
    val = c0 + g @ y0 + y0 @ A @ y0
    gy = g + (A + A.T) @ y0
    return val - float(np.abs(gy) @ w) - float(w @ np.abs(A) @ w)

def stack_lin(leaf, ib, Q):
    """arrays X0 (m, 2), L (m, 2, nv) for the witness list."""
    m = len(ib)
    X0 = np.zeros((m, 2)); L = np.zeros((m, 2, leaf.nv))
    for j, (i, q) in enumerate(zip(ib, Q)):
        X0[j], L[j] = leaf.lin(i, q)
    return X0, L

def fan_rows(leaf, ib, Q, z, lin=None):
    """per consecutive pair: lower bound of det(x_j - z, x_{j+1} - z) on the box (vectorized)."""
    X0, L = lin if lin is not None else stack_lin(leaf, ib, Q)
    P = X0 - z; P2 = np.roll(P, -1, axis=0); L2 = np.roll(L, -1, axis=0)
    c0 = np.einsum('ma,ab,mb->m', P, JP, P2)
    g = np.einsum('ma,ab,mbn->mn', P, JP, L2) + np.einsum('man,ab,mb->mn', L, JP, P2)
    A = np.einsum('man,ab,mbk->mnk', L, JP, L2)
    y0, w = leaf.y0, leaf.w
    val = c0 + g @ y0 + np.einsum('n,mnk,k->m', y0, A, y0)
    gy = g + np.einsum('mnk,k->mn', A + np.transpose(A, (0, 2, 1)), y0)
    return val - np.abs(gy) @ w - np.einsum('n,mnk,k->m', w, np.abs(A), w)

def pair_lbs_cheap(leaf, ib, Q, zs):
    """fast norm-based lower bounds (paper's Lemma 3.6(b)-style) of det(x_j - z, x_{j+1} - z) on the box, for
    several fan centres at once; used only to choose z and drop witnesses (the final check uses fan_rows)."""
    k = leaf.k
    ib = np.asarray(ib); Q = np.asarray(Q)
    # angular radius of the rotation range and translation radius per body
    a = np.zeros(k + 1); dt = np.zeros(k + 1)
    for i in range(1, k + 1):
        aa, bb, cc, ss = leaf.idx[i]
        dt[i] = math.hypot(leaf.w[aa], leaf.w[bb])
        if cc is not None:
            a[i] = math.hypot(leaf.w[ss], 2*leaf.w[cc])
    X0 = np.zeros((len(ib), 2))
    for j, (i, q) in enumerate(zip(ib, Q)):
        X0[j] = leaf.lin(int(i), q)[0]
    ib2 = np.roll(ib, -1); Q2 = np.roll(Q, -1, axis=0); X2 = np.roll(X0, -1, axis=0)
    same = ib == ib2
    nq = np.linalg.norm(Q, axis=1); nq2 = np.linalg.norm(Q2, axis=1)
    dX = nq*a[ib] + dt[ib]; dX2 = nq2*a[ib2] + dt[ib2]
    wq = np.linalg.norm(Q2 - Q, axis=1)
    out = np.empty((len(zs), len(ib)))
    tt = np.array([leaf.t[i] for i in range(k + 1)])
    for zi, z in enumerate(zs):
        A = X0 - z; B = X2 - z
        d0 = A[:, 0]*B[:, 1] - A[:, 1]*B[:, 0]
        tz = np.linalg.norm(tt[ib] - z, axis=1)
        vs = wq*(dt[ib]*(1 + a[ib]) + tz*a[ib])
        vt = dX*(np.linalg.norm(B, axis=1) + dX2) + np.linalg.norm(A, axis=1)*dX2
        out[zi] = d0 - 1.05*np.where(same, vs, vt)
    return out

def drop_bad(ib, Q, rows):
    """drop, for every bad row j (non-adjacent greedy), witness j+1 (or j if j+1 is a disk witness)."""
    m = len(ib)
    bad = np.nonzero(rows <= 1e-13)[0]
    dropset = set()
    for j in bad:
        j2 = (j + 1) % m
        dr = j2 if ib[j2] != 0 else j
        if dr in dropset or (dr - 1) % m in dropset or (dr + 1) % m in dropset:
            continue
        dropset.add(dr)
    keep = [t for t in range(m) if t not in dropset]
    return [ib[t] for t in keep], [Q[t] for t in keep]

def winding_ok(leaf, ib, Q, z):
    """certificate at the centre (y = 0 placement): all det > 0 and sum of angle upper bounds < 4 pi, with
    theta <= min(det/dot, pi/2) if dot > 0, theta <= pi/2 - dot/det if dot <= 0."""
    m = len(ib)
    X = [leaf.lin(i, q)[0] - z for i, q in zip(ib, Q)]
    tot = 0.0
    for j in range(m):
        a = X[j]; b = X[(j + 1) % m]
        d = det2(a, b); dt = float(a @ b)
        if d <= 0:
            return False
        tot += min(d/dt, 0.5*3.1416) if dt > 0 else min(3.1416, 0.5*3.1416 - dt/d)
    return tot < 4*3.1415 - 1e-9

def fan_quad(leaf, ib, Q):
    """F = (1/2) sum det(x_j, x_{j+1}) = F0 + g.y + (1/2) y^T H y; also D_i (coefficient of 2C+C^2+S^2)."""
    X0, L = stack_lin(leaf, ib, Q)
    X2 = np.roll(X0, -1, axis=0); L2 = np.roll(L, -1, axis=0)
    F0 = 0.5*float(np.einsum('ma,ab,mb->', X0, JP, X2))
    g = 0.5*(np.einsum('ma,ab,mbn->n', X0, JP, L2) + np.einsum('man,ab,mb->n', L, JP, X2))
    A = 0.5*np.einsum('man,ab,mbk->nk', L, JP, L2)
    H = A + A.T
    D = {}
    m = len(ib)
    for j in range(m):
        j2 = (j + 1) % m
        if ib[j] == ib[j2] and ib[j] >= 2:
            R = rotm(leaf.M[ib[j]])
            D[ib[j]] = D.get(ib[j], 0.0) + 0.5*det2(R @ Q[j], R @ Q[j2])
    return F0, g, H, D

def shift_bound(Mw):
    """-(1/2) sum s_a for a diagonal shift with Mw + diag(s) >= 0 (best of two cheap choices); returns (value, s)."""
    n = Mw.shape[0]
    lam = float(np.linalg.eigvalsh(Mw)[0])
    best = (0.5*min(0.0, lam)*n, np.full(n, max(0.0, -lam)))
    # Jacobi-type scaling
    d = np.sqrt(np.maximum(np.abs(Mw).sum(axis=1), 1e-300))
    Md = Mw/np.outer(d, d)
    lamd = float(np.linalg.eigvalsh(Md)[0])
    if lamd < 0:
        s2 = -lamd*d*d
        v = -0.5*float(s2.sum())
        if v > best[0]:
            best = (v, s2)
    return best

def leaf_bound(leaf, ib, Q, alphas=(0.0, 0.5, 1.0, 1.5, 2.0)):
    """best lower bound of F over the box (float), with the beta (2C+C^2+S^2) scan."""
    F0, g, H, D = fan_quad(leaf, ib, Q)
    y0, w = leaf.y0, leaf.w
    best = None
    for alpha in alphas:
        g2 = g.copy(); H2 = H.copy()
        for i in range(2, leaf.k + 1):
            beta = (alpha - 1.0)*D.get(i, 0.0)
            a, b, cc, ss = leaf.idx[i]
            g2[cc] += 2*beta; H2[cc, cc] += 2*beta; H2[ss, ss] += 2*beta
        Qy0 = F0 + g2 @ y0 + 0.5*y0 @ H2 @ y0
        gy = g2 + H2 @ y0
        Mw = np.diag(w) @ H2 @ np.diag(w)
        sv, s = shift_bound(Mw)
        b = Qy0 - float(np.abs(gy) @ w) + sv
        if best is None or b > best[0]:
            best = (b, alpha, s)
    return best


def taylor_form(leaf, ib, Q, alphas=(0.0, 0.5, 1.0, 1.5, 2.0)):
    """per-fan affine minorant on the box: F(y) >= a + G.(y - y0) with a = F(y0) - (1/2) sum s_a (PSD shift);
    beta (alpha) chosen to maximize the single-fan bound. Returns (a, G, b_single, alpha, s)."""
    F0, g, H, D = fan_quad(leaf, ib, Q)
    y0, w = leaf.y0, leaf.w
    best = None
    for alpha in alphas:
        g2 = g.copy(); H2 = H.copy()
        for i in range(2, leaf.k + 1):
            beta = (alpha - 1.0)*D.get(i, 0.0)
            a, b, cc, ss = leaf.idx[i]
            g2[cc] += 2*beta; H2[cc, cc] += 2*beta; H2[ss, ss] += 2*beta
        Qy0 = F0 + g2 @ y0 + 0.5*y0 @ H2 @ y0
        gy = g2 + H2 @ y0
        Mw = np.diag(w) @ H2 @ np.diag(w)
        sv, s = shift_bound(Mw)
        bsingle = Qy0 - float(np.abs(gy) @ w) + sv
        if best is None or bsingle > best[2]:
            best = (Qy0 + sv, gy, bsingle, alpha, s)
    return best
