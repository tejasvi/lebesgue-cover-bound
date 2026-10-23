"""Exact (Fraction) mirror of the Lean reference checker LebesgueCover/Checker.lean, and the data exporter.

The float pipeline (leafbound.py, release witness heuristic) proposes data; this module turns it into exact data
(dyadic rationals) and runs exactly the checks of `leafOK`.  Every function here mirrors the Lean definition of
the same name.
"""
import math
from fractions import Fraction as Fr
import numpy as np

# ---------------- rational helpers (Checker.lean) ----------------
def cuQ(s): return (1 - s*s)/(1 + s*s)
def suQ(s): return 2*s/(1 + s*s)
def det2(a, b): return a[0]*b[1] - a[1]*b[0]
def dot2(a, b): return a[0]*b[0] + a[1]*b[1]
def rot2(u, q): return (u[0]*q[0] - u[1]*q[1], u[1]*q[0] + u[0]*q[1])
def J2(q): return (-q[1], q[0])
def uQ(s): return (cuQ(s), suQ(s))

def yTx(i): return 0 if i == 1 else 4*i - 6
def yTy(i): return 1 if i == 1 else 4*i - 5
def yC(i): return 4*i - 4
def yS(i): return 4*i - 3
def bTx(i): return 0 if i == 1 else 3*i - 3
def bTy(i): return 1 if i == 1 else 3*i - 2
def bS(i): return 3*i - 4

def body_box(lo, hi, i):
    """(tc, ht, M, Cmax, Smax, sOK)"""
    if i == 0:
        return ((Fr(0), Fr(0)), (Fr(0), Fr(0)), (Fr(1), Fr(0)), Fr(0), Fr(0), True)
    tc = ((lo[bTx(i)] + hi[bTx(i)])/2, (lo[bTy(i)] + hi[bTy(i)])/2)
    ht = ((hi[bTx(i)] - lo[bTx(i)])/2, (hi[bTy(i)] - lo[bTy(i)])/2)
    if i == 1:
        return (tc, ht, (Fr(1), Fr(0)), Fr(0), Fr(0), True)
    sl, sh = lo[bS(i)], hi[bS(i)]
    m = (sl + sh)/2
    M = uQ(m)
    Cmax = max(1 - dot2(M, uQ(sl)), 1 - dot2(M, uQ(sh)))
    Smax = max(abs(det2(M, uQ(sl))), abs(det2(M, uQ(sh))))
    return (tc, ht, M, Cmax, Smax, (0 <= sl and sl <= sh and sh <= 1))

def witX0(bb, w):
    i, q = w
    if i == 0: return q
    tc, ht, M, Cmax, Smax, ok = bb[i]
    a = rot2(M, q)
    return (a[0] + tc[0], a[1] + tc[1])

def witL(bb, w, v):
    i, q = w
    if i == 0: return (Fr(0), Fr(0))
    a = rot2(bb[i][2], q)
    if v == yTx(i): return (Fr(1), Fr(0))
    if v == yTy(i): return (Fr(0), Fr(1))
    if i >= 2 and v == yC(i): return a
    if i >= 2 and v == yS(i): return J2(a)
    return (Fr(0), Fr(0))

def yBody(v): return 1 if v < 2 else (v + 6)//4
def yKind(v): return v if v < 2 else (v + 6) % 4
def yCentre(bb, v): return -bb[yBody(v)][3]/2 if yKind(v) == 2 else Fr(0)
def yHalf(bb, v):
    tc, ht, M, Cmax, Smax, ok = bb[yBody(v)]
    kd = yKind(v)
    return [ht[0], ht[1], Cmax/2, Smax][kd]

def quadLowerAbs(nv, c0, g, A, y0, w):
    R = range(nv)
    val = c0 + sum(g[a]*y0[a] for a in R) + sum(A[a][b]*y0[a]*y0[b] for a in R for b in R)
    val -= sum(abs(g[a] + sum((A[a][b] + A[b][a])*y0[b] for b in R))*w[a] for a in R)
    val -= sum(abs(A[a][b])*w[a]*w[b] for a in R for b in R)
    return val

def cycPairs(W):
    return [] if not W else list(zip(W, W[1:] + W[:1]))

def fanRow(nv, bb, z, w, w2):
    P0 = witX0(bb, w); Q0 = witX0(bb, w2)
    P = (P0[0] - z[0], P0[1] - z[1]); Q = (Q0[0] - z[0], Q0[1] - z[1])
    L = [witL(bb, w, v) for v in range(nv)]; M = [witL(bb, w2, v) for v in range(nv)]
    c0 = det2(P, Q)
    g = [det2(P, M[a]) + det2(L[a], Q) for a in range(nv)]
    A = [[det2(L[a], M[b]) for b in range(nv)] for a in range(nv)]
    y0 = [yCentre(bb, v) for v in range(nv)]; wv = [yHalf(bb, v) for v in range(nv)]
    return quadLowerAbs(nv, c0, g, A, y0, wv)

PILO = Fr(31415, 10000); PIHI = Fr(31416, 10000)

def windOK(bb, z, W):
    tot = Fr(0)
    for w, w2 in cycPairs(W):
        P0 = witX0(bb, w); Q0 = witX0(bb, w2)
        P = (P0[0] - z[0], P0[1] - z[1]); Q = (Q0[0] - z[0], Q0[1] - z[1])
        d = det2(P, Q)
        if not d > 0: return False
        dt = dot2(P, Q)
        tot += min(d/dt, PIHI/2) if dt > 0 else min(PIHI, PIHI/2 - dt/d)
    return tot < 4*PILO

def fanQuad(nv, bb, W, beta):
    prs = cycPairs(W)
    F0 = sum(det2(witX0(bb, w), witX0(bb, w2)) for w, w2 in prs)/2
    g = [Fr(0)]*nv; H = [[Fr(0)]*nv for _ in range(nv)]
    for w, w2 in prs:
        P0 = witX0(bb, w); Q0 = witX0(bb, w2)
        L = [witL(bb, w, v) for v in range(nv)]; M = [witL(bb, w2, v) for v in range(nv)]
        for a in range(nv):
            g[a] += (det2(P0, M[a]) + det2(L[a], Q0))/2
            for b in range(nv):
                H[a][b] += (det2(L[a], M[b]) + det2(L[b], M[a]))/2
    for a in range(nv):
        if yKind(a) == 2:
            g[a] += 2*beta.get(yBody(a), Fr(0))
        if yKind(a) in (2, 3):
            H[a][a] += 2*beta.get(yBody(a), Fr(0))
    return F0, g, H

def ldl(n, N):
    L = [[Fr(0)]*n for _ in range(n)]; D = [Fr(0)]*n
    for a in range(n):
        for b in range(a):
            s = N[a][b]
            for c in range(b):
                s -= L[a][c]*L[b][c]*D[c]
            L[a][b] = Fr(0) if D[b] == 0 else s/D[b]
        s = N[a][a]
        for c in range(a):
            s -= L[a][c]*L[a][c]*D[c]
        D[a] = s; L[a][a] = Fr(1)
    return L, D

def psdOK(n, N):
    L, D = ldl(n, N)
    if any(d < 0 for d in D): return False
    for a in range(n):
        for b in range(n):
            if N[a][b] != sum(L[a][c]*D[c]*L[b][c] for c in range(n)): return False
    return True

def fanLower(nv, bb, F0, g, H, sigma):
    y0 = [yCentre(bb, v) for v in range(nv)]; w = [yHalf(bb, v) for v in range(nv)]
    R = range(nv)
    return (F0 + sum(g[a]*y0[a] for a in R) + sum(H[a][b]*y0[a]*y0[b] for a in R for b in R)/2
            - sum(abs(g[a] + sum(H[a][b]*y0[b] for b in R))*w[a] for a in R)
            - sum(sigma[a]*w[a]**2 for a in R)/2)

def memOK(ns, VT, nu, w):
    i, q = w
    if i == 0: return dot2(q, q) <= Fr(1, 4)
    n = ns[i - 1]
    for l in range(n):
        V = VT[(n, l)]
        d = (q[0] - V[0], q[1] - V[1])
        if not dot2(d, d) <= (1 - nu)**2: return False
    return True

def leafOK(ns, VT, nu, tau, lo, hi, W, z, beta, sigma, detail=False):
    k = len(ns); nv = 4*k - 2
    bb = [body_box(lo, hi, i) for i in range(k + 1)]
    checks = []
    checks.append(('sOK', all(bb[i][5] for i in range(k + 1))))
    checks.append(('k', k >= 2)); checks.append(('m', len(W) >= 3))
    checks.append(('mem', all(w[0] <= k and memOK(ns, VT, nu, w) for w in W)))
    checks.append(('z', dot2(z, z) < Fr(1, 4)))
    rows = [fanRow(nv, bb, z, w, w2) for w, w2 in cycPairs(W)]
    checks.append(('fan', all(r > 0 for r in rows)))
    checks.append(('wind', windOK(bb, z, W)))
    checks.append(('sigma', all(sigma[a] >= 0 for a in range(nv))))
    F0, g, H = fanQuad(nv, bb, W, beta)
    N = [[H[a][b] + (sigma[a] if a == b else 0) for b in range(nv)] for a in range(nv)]
    checks.append(('psd', psdOK(nv, N)))
    val = fanLower(nv, bb, F0, g, H, sigma)
    checks.append(('bound', tau < val))
    ok = all(c[1] for c in checks)
    if detail:
        return ok, checks, val - tau, min(rows) if rows else None
    return ok

# ---------------- vertex table ----------------
VT_PREC = 40
def vert_table(ns):
    """dyadic approximations (2^-40) of V_{n,l} = R_n (cos(2 pi l/n), sin(2 pi l/n)); computed with mpmath."""
    import mpmath
    mpmath.mp.prec = 200
    VT = {}
    for n in ns:
        R = 1/(2*mpmath.cos(mpmath.pi/(2*n)))
        for l in range(n):
            x = R*mpmath.cos(2*mpmath.pi*l/n); y = R*mpmath.sin(2*mpmath.pi*l/n)
            VT[(n, l)] = (Fr(int(mpmath.nint(x*2**VT_PREC)), 2**VT_PREC), Fr(int(mpmath.nint(y*2**VT_PREC)), 2**VT_PREC))
    return VT
NU = Fr(1, 2**36)

def fr(x):
    """exact value of a double."""
    return Fr(float(x))

def dyadic_up(x, bits=40):
    return Fr(math.ceil(float(x)*2**bits), 2**bits)

def dyadic_near(x, bits=40):
    return Fr(round(float(x)*2**bits), 2**bits)
