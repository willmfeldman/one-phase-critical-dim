#!/usr/bin/env python3
"""Exact checker for m-dimensional certificates.

Independent of the numeric search: it does NOT import engine.py or search.py, and it
does not trust any floating-point output.  It reads a certificate file (JSON, all numbers
exact rationals written as strings), rebuilds the interior polynomial I and the boundary
polynomial S in exact rational arithmetic (sympy polynomial rings over QQ), and checks:

  (B) boundary:  S >= delta on all boundary data (g = 0, |p| = 1, Ap = lam p, lam < 0),
  (I) interior:  I - eps (z^2 + |l|^2) >= 0 on all data with chi = 1 - |p|^2 - g^2 >= 0,
                 via one of
                   - 'constant': the quadratic form does not depend on (p, g) after fixing a
                     representative A of the single O(m)-orbit (m = 2); exact LDL^T;
                   - 'sos': a Putinar certificate for diagonal A = diag(alpha) (m = 3):
                       Q - eps E - eta I = sum_k B_k^T G_k B_k + chi sum_k B'_k^T G'_k B'_k + R
                     modulo the circle relation h(alpha) = |alpha|^2 - 1 = 0, every G exactly
                     positive definite (LDL^T over QQ), and an exact rational bound
                     ||R(x)||_op <= max row sum of |coefficients| < eta on the domain.
  (S) structure: P has positive g-degree in every term, all terms are O(m)-equivariant graph
                 monomials (no Levi-Civita), U and K have an even number of p's.

Certificate JSON (full specification in README.md, section "Certificate format"):
  {"m": 3, "a": "11/20", "eps": "...", "delta": "...",
   "terms": [{"F": "U", "coef": "1/4", "h": 0, "scal": [["s",1]], "pairs": [[0,1,1]],
              "legs": [[0,0],[1,1]]}, ...],
   "interior": {"method": "sos", "eta": "...", "blocks": [...]}  # or {"method": "constant", ...}
  }
Term semantics: coef * g^h * prod(scal) * prod_pairs (A^k)_{ab} * prod_legs (A^k p)_a, where
('s',k) = p.A^k p and ('t',k) = tr A^k; free slots 0..r-1 with r = 0,2,4,1,1 for f,U,K,M,P and
slot orders (), (j,k), (l,i,j,k), (l), (l).

Usage:  python exact_check.py CERT.json
"""

import itertools
import json
import sys
import time
from fractions import Fraction as Fr

import numpy as np
import sympy
from sympy import QQ
from sympy.polys.rings import ring

RANK = {"f": 0, "U": 2, "K": 4, "M": 1, "P": 1}


# ---------------------------------------------------------------------------
# rational basis of STF^3(R^m), split by sign-flip parity classes
# ---------------------------------------------------------------------------

def stf3_rational_basis(m):
    """List of rational tensors (numpy object arrays m x m x m of Fractions) spanning
    STF^3(R^m); each has a definite parity under the coordinate sign flips."""
    idx = [t for t in itertools.combinations_with_replacement(range(m), 3)]
    classes = {}
    for t in idx:
        par = tuple(sum(1 for x in t if x == i) % 2 for i in range(m))
        classes.setdefault(par, []).append(t)
    basis = []
    for par in sorted(classes):
        ts = classes[par]
        # unknowns: values S_t of the symmetric tensor on sorted index t
        # trace conditions: for each i, sum_j S_{sort(i,j,j)} = 0
        rows = []
        for i in range(m):
            row = [0] * len(ts)
            hit = False
            for j in range(m):
                tt = tuple(sorted((i, j, j)))
                if tt in ts:
                    row[ts.index(tt)] += 1
                    hit = True
            if hit:
                rows.append(row)
        M = sympy.Matrix(rows) if rows else sympy.zeros(0, len(ts))
        ns = M.nullspace() if rows else [sympy.eye(len(ts))[:, k] for k in range(len(ts))]
        for vec in ns:
            # clear denominators for readability
            den = sympy.ilcm(1, 1, *[sympy.fraction(x)[1] for x in vec])
            vec = vec * den
            T = np.empty((m, m, m), dtype=object)
            T[...] = Fr(0)
            for val, t in zip(vec, ts):
                for perm in set(itertools.permutations(t)):
                    T[perm] = Fr(int(val))
            basis.append((par, T))
    # sanity: symmetric, trace-free, linearly independent, of dimension C(m+2,3) - m
    for _, T in basis:
        for ind in itertools.product(range(m), repeat=3):
            for perm in itertools.permutations(ind):
                assert T[ind] == T[perm]
        for i in range(m):
            assert sum(T[i, j, j] for j in range(m)) == 0
    Mat = sympy.Matrix([[T[ind] for ind in itertools.product(range(m), repeat=3)] for _, T in basis])
    from math import comb
    assert Mat.rank() == len(basis) == comb(m + 2, 3) - m
    return basis


# ---------------------------------------------------------------------------
# exact construction of I and S
# ---------------------------------------------------------------------------

class Exact:
    def __init__(self, m, nX):
        self.m = m
        names = [f"a{i}{j}" for i in range(m) for j in range(i, m)]
        names += [f"p{i}" for i in range(m)] + ["g", "w", "z"]
        names += [f"l{i}" for i in range(m)] + [f"x{s}" for s in range(nX)]
        names += [f"al{i}" for i in range(m)]
        self.R, *gens = ring(",".join(names), QQ)
        self.gen = dict(zip(names, gens))
        G = self.gen
        self.Aij = {}
        A = np.empty((m, m), dtype=object)
        for i in range(m):
            for j in range(i, m):
                A[i, j] = A[j, i] = G[f"a{i}{j}"]
                self.Aij[(i, j)] = G[f"a{i}{j}"]
        self.A = A
        self.p = np.array([G[f"p{i}"] for i in range(m)], dtype=object)
        self.g, self.w, self.z = G["g"], G["w"], G["z"]
        self.l = np.array([G[f"l{i}"] for i in range(m)], dtype=object)
        self.xi = [G[f"x{s}"] for s in range(nX)]
        self.zero = self.R(0)
        self.one = self.R(1)

    def mat_pow(self, k):
        m = self.m
        P = np.empty((m, m), dtype=object)
        for i in range(m):
            for j in range(m):
                P[i, j] = self.one if i == j else self.zero
        for _ in range(k):
            P = matmul(P, self.A, self.zero)
        return P

    def term_tensor(self, t, r):
        """Tensor (object array, shape (m,)*r) of one certificate term."""
        m = self.m
        coef = QQ(Fr(t["coef"]).numerator, Fr(t["coef"]).denominator)
        sc = self.R(coef) * self.g ** int(t["h"])
        for kind, k in t["scal"]:
            Ak = self.mat_pow(int(k))
            if kind == "s":
                sc *= sum(self.p[i] * Ak[i, j] * self.p[j] for i in range(m) for j in range(m))
            elif kind == "t":
                sc *= sum(Ak[i, i] for i in range(m))
            else:
                raise ValueError(kind)
        slots_seen = []
        pairs = [(int(a), int(b), int(k)) for a, b, k in t["pairs"]]
        legs = [(int(a), int(k)) for a, k in t["legs"]]
        for a, b, k in pairs:
            slots_seen += [a, b]
        for a, k in legs:
            slots_seen.append(a)
        assert sorted(slots_seen) == list(range(r)), ("each free slot exactly once", t)
        pw = {k: self.mat_pow(k) for k in set([k for _, _, k in pairs] + [k for _, k in legs])}
        vec = {k: matvec(pw[k], self.p, self.zero) for k in set(k for _, k in legs)}
        T = np.empty((m,) * r, dtype=object) if r else None
        if r == 0:
            return sc
        for ind in itertools.product(range(m), repeat=r):
            v = sc
            for a, b, k in pairs:
                v = v * pw[k][ind[a], ind[b]]
            for a, k in legs:
                v = v * vec[k][ind[a]]
            T[ind] = v
        return T

    def family(self, cert, F):
        r = RANK[F]
        tot = None
        for t in cert["terms"]:
            if t["F"] != F:
                continue
            T = self.term_tensor(t, r)
            tot = T if tot is None else tot + T
        if tot is None:
            if r == 0:
                return self.zero
            tot = np.empty((self.m,) * r, dtype=object)
            tot[...] = self.zero
        return tot


def matmul(P, Q, zero):
    m = P.shape[0]
    out = np.empty((m, m), dtype=object)
    for i in range(m):
        for j in range(m):
            s = zero
            for k in range(m):
                s = s + P[i, k] * Q[k, j]
            out[i, j] = s
    return out


def matvec(P, v, zero):
    m = P.shape[0]
    return np.array([sum((P[i, k] * v[k] for k in range(m)), zero) for i in range(m)], dtype=object)


def build_interior(cert, ex, Xb):
    """Exact I as a ring element, for general symmetric A (entries a_ij)."""
    m = ex.m
    a = Fr(cert["a"])
    aQ = ex.R(QQ(a.numerator, a.denominator))
    beta2 = Fr(m - 1, 2) ** 2
    b2 = ex.R(QQ(beta2.numerator, beta2.denominator))
    A, p, g, w, z, l = ex.A, ex.p, ex.g, ex.w, ex.z, ex.l
    zero = ex.zero
    # X from the rational basis
    X = np.empty((m, m, m), dtype=object)
    for ind in itertools.product(range(m), repeat=3):
        X[ind] = sum((ex.xi[s] * QQ(T[ind].numerator, T[ind].denominator)
                      for s, (_, T) in enumerate(Xb) if T[ind] != 0), zero)
    q = np.array([sum((X[l_, i, j] * A[i, j] for i in range(m) for j in range(m)), zero)
                  for l_ in range(m)], dtype=object)
    dA = {}
    for (i, j), aij in ex.Aij.items():
        dA[(i, j)] = [X[l_, i, j] - q[l_] * A[i, j] for l_ in range(m)]
    dp = [[w * A[l_, i] - (g * z if i == l_ else zero) for i in range(m)] for l_ in range(m)]
    dg = [z * p[l_] for l_ in range(m)]

    def D(F, l_):
        out = zero
        for (i, j), aij in ex.Aij.items():
            out = out + F.diff(aij) * dA[(i, j)][l_]
        for i in range(m):
            out = out + F.diff(p[i]) * dp[l_][i]
        out = out + F.diff(g) * dg[l_]
        return out

    f = ex.family(cert, "f")
    U = ex.family(cert, "U")
    K = ex.family(cert, "K")
    M = ex.family(cert, "M")
    P = ex.family(cert, "P")
    C = np.empty((m,) * 4, dtype=object)
    for ind in itertools.product(range(m), repeat=4):
        l_, i, j, k = ind
        C[ind] = K[l_, i, j, k] - K[i, l_, j, k]
    two_a = 2 * aQ
    I = zero
    # z^2 [ m U:A + C(dA + dA) - beta2 f ]
    zz = sum((m * U[j, k] * A[j, k] for j in range(m) for k in range(m)), zero)
    for l_, i, j, k in itertools.product(range(m), repeat=4):
        if C[l_, i, j, k] == 0:
            continue
        t = zero
        if l_ == j:
            t = t + A[i, k]
        if l_ == k:
            t = t + A[i, j]
        zz = zz + C[l_, i, j, k] * t
    zz = zz - b2 * f
    I = I + z ** 2 * zz
    # [D_l G_lijk + (2a-1) q_l G_lijk] X_ijk,  G_lijk = d_li U_jk + C_lijk
    for i, j, k in itertools.product(range(m), repeat=3):
        if X[i, j, k] == 0:
            continue
        coef = D(U[j, k], i) + (two_a - 1) * q[i] * U[j, k]
        for l_ in range(m):
            if C[l_, i, j, k] != 0:
                coef = coef + D(C[l_, i, j, k], l_) + (two_a - 1) * q[l_] * C[l_, i, j, k]
        I = I + coef * X[i, j, k]
    # w [ D_l M_l + (2a+1) q_l M_l ] + z [ D_l P_l + 2a q_l P_l ]
    I = I + w * sum((D(M[l_], l_) + (two_a + 1) * q[l_] * M[l_] for l_ in range(m)), zero)
    I = I + z * sum((D(P[l_], l_) + two_a * q[l_] * P[l_] for l_ in range(m)), zero)
    # f|l|^2 - (D_l f + 2a q_l f) l_l
    I = I + f * sum((l[i] ** 2 for i in range(m)), zero)
    I = I - sum(((D(f, l_) + two_a * q[l_] * f) * l[l_] for l_ in range(m)), zero)
    return I


def build_boundary(cert, ex):
    """Exact S for general symmetric A and vector p (to be specialized by the caller)."""
    m = ex.m
    A, p = ex.A, ex.p
    zero = ex.zero
    lam = sum((p[i] * A[i, j] * p[j] for i in range(m) for j in range(m)), zero)
    A2 = matmul(A, A, zero)
    S0 = np.empty((m, m), dtype=object)
    for i in range(m):
        for j in range(m):
            S0[i, j] = lam * A[i, j] - A2[i, j]
    V = np.empty((m, m, m), dtype=object)
    for i, j, k in itertools.product(range(m), repeat=3):
        V[i, j, k] = p[i] * S0[j, k] + p[j] * S0[k, i] + p[k] * S0[i, j] + p[i] * p[j] * p[k]
    f = ex.family(cert, "f")
    U = ex.family(cert, "U")
    K = ex.family(cert, "K")
    M = ex.family(cert, "M")
    S = -lam * f
    S = S + sum((U[j, k] * (S0[j, k] + p[j] * p[k]) for j in range(m) for k in range(m)), zero)
    for l_, i, j, k in itertools.product(range(m), repeat=4):
        c = K[l_, i, j, k] - K[i, l_, j, k]
        if c != 0:
            S = S + c * p[l_] * V[i, j, k]
    S = S + sum((p[l_] * M[l_] for l_ in range(m)), zero)
    return S


# ---------------------------------------------------------------------------
# small exact polynomial arithmetic on dicts {exponent tuple: Fraction}
# ---------------------------------------------------------------------------

def padd(P, Q_, c=Fr(1)):
    out = dict(P)
    for e, v in Q_.items():
        nv = out.get(e, Fr(0)) + c * v
        if nv:
            out[e] = nv
        else:
            out.pop(e, None)
    return out


def pmul(P, Q_):
    out = {}
    for e1, v1 in P.items():
        for e2, v2 in Q_.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            nv = out.get(e, Fr(0)) + v1 * v2
            if nv:
                out[e] = nv
            else:
                out.pop(e)
    return out


def reduce_circle3(P):
    """Normal form modulo h = al1^2 + al2^2 + (al1+al2)^2 - 1 (variables ordered
    (al1, al2, ...)): replace al2^2 by (1 - 2 al1^2 - 2 al1 al2)/2 until al2-degree <= 1."""
    P = dict(P)
    while True:
        hi = {e: v for e, v in P.items() if e[1] >= 2}
        if not hi:
            return P
        for e, v in hi.items():
            del P[e]
            base = list(e)
            base[1] -= 2
            for de, dv in (((0, 0), Fr(1, 2)), ((2, 0), Fr(-1)), ((1, 1), Fr(-1))):
                ne = list(base)
                ne[0] += de[0]
                ne[1] += de[1]
                ne = tuple(ne)
                nv = P.get(ne, Fr(0)) + v * dv
                if nv:
                    P[ne] = nv
                else:
                    P.pop(ne, None)


def ring_to_dict(poly, ex, var_names):
    """Convert a ring element in the given variables (all others must be absent)."""
    idx = [ex.R.gens.index(ex.gen[n]) for n in var_names]
    out = {}
    for mon, c in poly.terms():
        for k, e in enumerate(mon):
            if e and k not in idx:
                raise ValueError("unexpected variable " + str(ex.R.gens[k]))
        key = tuple(mon[k] for k in idx)
        out[key] = out.get(key, Fr(0)) + Fr(int(c.numerator), int(c.denominator))
    return {k: v for k, v in out.items() if v}


# ---------------------------------------------------------------------------
# exact PSD test (LDL^T over QQ)
# ---------------------------------------------------------------------------

def ldl_psd(M, strict=False):
    """Return (ok, min_pivot).  Exact symmetric Gaussian elimination; zero pivots are
    allowed (non-strict) only if the whole remaining row vanishes."""
    n = len(M)
    A = [list(map(Fr, row)) for row in M]
    minp = None
    for k in range(n):
        piv = A[k][k]
        minp = piv if minp is None else min(minp, piv)
        if piv < 0:
            return False, piv
        if piv == 0:
            if strict or any(A[k][j] != 0 for j in range(k + 1, n)):
                return False, piv
            continue
        for i in range(k + 1, n):
            if A[i][k] == 0:
                continue
            r = A[i][k] / piv
            Ai, Ak = A[i], A[k]
            for j in range(k + 1, n):
                if Ak[j]:
                    Ai[j] -= r * Ak[j]
    return True, minp


# ---------------------------------------------------------------------------
# checks
# ---------------------------------------------------------------------------

def structural_checks(cert):
    m = cert["m"]
    msgs = []
    for t in cert["terms"]:
        F = t["F"]
        r = RANK[F]
        npp = len(t["legs"]) + 2 * sum(1 for s in t["scal"] if s[0] == "s")
        if F in ("U", "K"):
            assert npp % 2 == 0, ("U,K even in p", t)
        if F == "P":
            assert int(t["h"]) > 0, ("P vanishes at g = 0", t)
        for s in t["scal"]:
            assert s[0] in ("s", "t")
        for a, b, k in t["pairs"]:
            assert 0 <= a < r and 0 <= b < r and a != b
    msgs.append(f"structure: {len(cert['terms'])} terms; every term is an O({m})-equivariant "
                f"graph monomial; U,K even in p; P has g-degree >= 1 in every term")
    return msgs


def interior_matrix(cert, verbose=True):
    """Exact quadratic-form matrix Q of I in v = (w, z, l, xi), with A replaced by a
    representative: m = 2 -> the rational matrix [[1/2,1/2],[1/2,-1/2]];
    m = 3 -> diag(al1, al2, -al1-al2).  Entries: dicts over (al1, al2, p.., g) (m=3) or
    (p.., g) (m=2)."""
    m = cert["m"]
    Xb = stf3_rational_basis(m)
    nX = len(Xb)
    ex = Exact(m, nX)
    t0 = time.time()
    I = build_interior(cert, ex, Xb)
    if verbose:
        print(f"  built I exactly: {len(I.terms())} terms ({time.time() - t0:.1f}s)")
    G = ex.gen
    subs = []
    if m == 2:
        rep = {(0, 0): QQ(1, 2), (0, 1): QQ(1, 2), (1, 1): QQ(-1, 2)}
        for (i, j), aij in ex.Aij.items():
            subs.append((aij, ex.R(rep[(i, j)])))
        xvars = [f"p{i}" for i in range(m)] + ["g"]
    elif m == 3:
        al = [G["al0"], G["al1"], -G["al0"] - G["al1"]]
        for (i, j), aij in ex.Aij.items():
            subs.append((aij, al[i] if i == j else ex.zero))
        xvars = ["al0", "al1"] + [f"p{i}" for i in range(m)] + ["g"]
    else:
        raise NotImplementedError
    Id = I.compose(subs)
    vnames = ["w", "z"] + [f"l{i}" for i in range(m)] + [f"x{s}" for s in range(nX)]
    vidx = [ex.R.gens.index(G[n]) for n in vnames]
    V = len(vnames)
    Q = [[{} for _ in range(V)] for _ in range(V)]
    xidx = [ex.R.gens.index(G[n]) for n in xvars]
    for mon, c in Id.terms():
        vdeg = [mon[k] for k in vidx]
        assert sum(vdeg) == 2, "I must be homogeneous of degree 2 in (w,z,l,X)"
        others = [k for k, e in enumerate(mon) if e and k not in vidx and k not in xidx]
        assert not others
        pos = [i for i, d in enumerate(vdeg) for _ in range(d)]
        key = tuple(mon[k] for k in xidx)
        val = Fr(int(c.numerator), int(c.denominator))
        u, v = pos
        if u == v:
            Q[u][u][key] = Q[u][u].get(key, Fr(0)) + val
        else:
            Q[u][v][key] = Q[u][v].get(key, Fr(0)) + val / 2
            Q[v][u][key] = Q[v][u].get(key, Fr(0)) + val / 2
    if m == 3:
        Q = [[reduce_circle3(e) for e in row] for row in Q]
    Q = [[{k: v for k, v in e.items() if v} for e in row] for row in Q]
    parities = vparities(m, Xb)
    return Q, vnames, xvars, parities


def vparities(m, Xb):
    """Characters of the v-coordinates under sign flips (s_1..s_m) and the g-flip."""
    out = [tuple([0] * m + [0]), tuple([0] * m + [1])]  # w, z
    for i in range(m):
        e = [0] * m + [0]
        e[i] = 1
        out.append(tuple(e))
    for par, _ in Xb:
        out.append(tuple(list(par) + [0]))
    return out


def check_interior(cert, verbose=True):
    m = cert["m"]
    eps = Fr(cert["eps"])
    Q, vnames, xvars, _ = interior_matrix(cert, verbose)
    V = len(vnames)
    meth = cert["interior"]["method"]
    # target T = Q - eps E
    T = [[dict(e) for e in row] for row in Q]
    zero_key = tuple([0] * len(xvars))
    for i, n in enumerate(vnames):
        if n == "z" or n.startswith("l"):
            T[i][i] = padd(T[i][i], {zero_key: Fr(1)}, -eps)
    if meth == "constant":
        for row in T:
            for e in row:
                assert all(k == zero_key for k in e), "form depends on (p,g): 'constant' invalid"
        M = [[T[i][j].get(zero_key, Fr(0)) for j in range(V)] for i in range(V)]
        ok, minp = ldl_psd(M)
        return ok, {"method": "constant", "V": V, "ldl_ok": ok, "min_pivot": str(minp),
                    "matrix": [[str(x) for x in row] for row in M]}
    assert meth == "sos" and m == 3
    eta = Fr(cert["interior"]["eta"])
    for i in range(V):
        T[i][i] = padd(T[i][i], {zero_key: Fr(1)}, -eta)
    nvar = len(xvars)  # (al0, al1, p0, p1, p2, g)
    chi = {zero_key: Fr(1)}
    for k in range(2, nvar):
        e = [0] * nvar
        e[k] = 2
        chi[tuple(e)] = Fr(-1)
    S = [[{} for _ in range(V)] for _ in range(V)]
    info = {"method": "sos", "eta": str(eta), "blocks": 0, "gram_dims": [], "min_pivots": []}
    t0 = time.time()
    for blk in cert["interior"]["blocks"]:
        basis = [(tuple(b[0]), int(b[1])) for b in blk["basis"]]  # (x-exponent, v-index)
        Gm = [[Fr(x) for x in row] for row in blk["gram"]]
        ok, minp = ldl_psd(Gm, strict=True)
        if not ok:
            return False, {"error": "Gram block not positive definite", "block": info["blocks"]}
        info["blocks"] += 1
        info["gram_dims"].append(len(basis))
        info["min_pivots"].append(float(minp))
        acc = [[{} for _ in range(V)] for _ in range(V)]
        for r_, (er, mu) in enumerate(basis):
            for s_, (es, nu) in enumerate(basis):
                c = Gm[r_][s_]
                if c == 0:
                    continue
                e = tuple(x + y for x, y in zip(er, es))
                acc[mu][nu][e] = acc[mu][nu].get(e, Fr(0)) + c
        mult = chi if blk["mult"] == "chi" else {zero_key: Fr(1)}
        for mu in range(V):
            for nu in range(V):
                if acc[mu][nu]:
                    S[mu][nu] = padd(S[mu][nu], pmul(acc[mu][nu], mult))
    S = [[reduce_circle3(e) for e in row] for row in S]
    # residual R = T - S (mod h); exact bound of ||R||_op by max row sum of |coefficients|
    rows = []
    maxabs = Fr(0)
    nterms = 0
    for mu in range(V):
        rs = Fr(0)
        for nu in range(V):
            Rm = padd(T[mu][nu], S[mu][nu], Fr(-1))
            nterms += len(Rm)
            for k, v in Rm.items():
                rs += abs(v)
                maxabs = max(maxabs, abs(v))
        rows.append(rs)
    bound = max(rows)
    info.update({"residual_terms": nterms, "residual_max_coef": float(maxabs),
                 "residual_rowsum_bound": str(bound), "residual_bound_float": float(bound),
                 "bound_lt_eta": bound < eta, "time_sos_check": time.time() - t0})
    # monomial bound used: |al0|,|al1| <= 1 (|alpha_i|^2 <= 2/3 on the circle), |p_i|,|g| <= 1.
    return bound < eta, info


def check_boundary(cert, verbose=True):
    m = cert["m"]
    delta = Fr(cert["delta"])
    Xb = stf3_rational_basis(m)
    ex = Exact(m, len(Xb))
    S = build_boundary(cert, ex)
    G = ex.gen
    xs = [G[f"al{i}"] for i in range(m - 1)]
    lam = -sum(xs, ex.zero)
    subs = []
    diag = xs + [lam]
    for (i, j), aij in ex.Aij.items():
        subs.append((aij, diag[i] if i == j else ex.zero))
    for i in range(m):
        subs.append((ex.p[i], ex.one if i == m - 1 else ex.zero))
    Sd = S.compose(subs)
    sx = sympy.symbols(f"x0:{m - 1}")
    expr = sum(sympy.Rational(int(c.numerator), int(c.denominator))
               * sympy.prod([sx[k] ** mon[ex.R.gens.index(xs[k])] for k in range(m - 1)])
               for mon, c in Sd.terms())
    if m == 2:
        # x0 = -lam > 0 with 2 x0^2 = 1:  x0 = 1/sqrt(2)
        val = sympy.nsimplify(sympy.expand(expr.subs(sx[0], 1 / sympy.sqrt(2))))
        ok = bool(sympy.simplify(val - sympy.Rational(delta.numerator, delta.denominator)) >= 0)
        return ok, {"S_exact": str(val), "delta": str(delta), "S_float": float(val)}
    if m == 3:
        x0, x1 = sx
        sym_ok = sympy.expand(expr - expr.subs({x0: x1, x1: x0}, simultaneous=True)) == 0
        s, e2 = sympy.symbols("s e2")
        # express in e1 = x0 + x1 = s and e2 = x0 x1 (symmetric reduction)
        from sympy.polys.polyfuncs import symmetrize
        sf = symmetrize(sympy.expand(expr), x0, x1, formal=True)
        poly_e, remainder, gens_defs = sf[0], sf[1], sf[2]
        assert remainder == 0
        # gens_defs: [(s1, x0 + x1), (s2, x0*x1)]
        s1, s2 = gens_defs[0][0], gens_defs[1][0]
        # on |A| = 1:  x0^2 + x1^2 + s^2 = 1  =>  e2 = s^2 - 1/2
        Ps = sympy.Poly(sympy.expand(poly_e.subs({s1: s, s2: s ** 2 - sympy.Rational(1, 2)})), s)
        Pd = Ps - sympy.Rational(delta.numerator, delta.denominator)
        smax_upper = sympy.Rational(8165, 10000)  # > sqrt(2/3) = 0.81649658...
        assert smax_upper ** 2 > sympy.Rational(2, 3)
        nroots = Pd.count_roots(0, smax_upper)
        val0 = Pd.eval(0)
        ok = sym_ok and nroots == 0 and val0 > 0
        # report exact min over a fine grid for information
        grid = [Ps.eval(sympy.Rational(k, 1000)) for k in range(0, 817)]
        return ok, {"symmetric_in_x0_x1": sym_ok, "S_of_s": str(Ps.as_expr()),
                    "roots_of_S-delta_in_[0,0.8165]": int(nroots), "S(0)-delta": str(val0),
                    "S_min_on_grid": float(min(grid)), "delta": str(delta)}
    raise NotImplementedError


def main(path):
    cert = json.load(open(path))
    t0 = time.time()
    print(f"exact check of {path}: m = {cert['m']}, a = {cert['a']}, eps = {cert['eps']}, "
          f"delta = {cert['delta']}")
    a = Fr(cert["a"])
    assert Fr(1, 2) < a < 1, "need 1/2 < a < 1 (weighted Bochner absorption)"
    for msg in structural_checks(cert):
        print("  " + msg)
    okb, infob = check_boundary(cert)
    print(f"  boundary: {'PASS' if okb else 'FAIL'}  {json.dumps(infob)}")
    oki, infoi = check_interior(cert)
    short = {k: v for k, v in infoi.items() if k != "matrix"}
    print(f"  interior: {'PASS' if oki else 'FAIL'}  {json.dumps(short)}")
    if "matrix" in infoi:
        print("  interior matrix (Q - eps E):")
        for row in infoi["matrix"]:
            print("    " + " ".join(f"{x:>8}" for x in row))
    ok = okb and oki
    print(f"RESULT: {'ACCEPTED' if ok else 'REJECTED'}  ({time.time() - t0:.1f}s)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
