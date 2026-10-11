#!/usr/bin/env python3
"""Numeric Putinar/SOS fit for the m = 3 interior inequality, and certificate writer.

Input: a search result (search.py --out), rounded here to rationals with denominator
--den.  Output: a certificate JSON for exact_check.py containing the rational terms and
rational Gram blocks.

Target (exact, from exact_check.interior_matrix):  T(x) = Q(x) - eps E - eta I, with
x = (al0, al1, p0, p1, p2, g), A = diag(al0, al1, -al0-al1), reduced modulo the circle
relation h = 0.  We look for
     T = sum_k B_k^T G_k B_k + chi * sum_k B'_k^T G'_k B'_k    (mod h)
with basis elements b(x) e_mu, b an alpha-monomial in normal form (al1-degree <= 1,
degree <= dal) times a (p,g)-monomial of degree <= dpg (dpg_chi for the chi part).
The Gram matrices are block diagonal by the character of b(x) e_mu under the sign
flips p_i -> -p_i (with l_i, X) and the (g,z) flip; this is no loss by averaging.
We maximize the smallest eigenvalue margin mu of all blocks, so that rounding to
rationals keeps them positive definite.

Usage:
  python sos_fit.py certs/m3_search.json --den 1000 --eps 1/50 --eta 1/1000 --out certs/m3_cert.json
"""

import argparse
import itertools
import json
import os
import sys
import time
from fractions import Fraction as Fr

import numpy as np
import scipy.sparse as sp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import exact_check as X  # noqa: E402


def rational_terms(search, den):
    terms = []
    for (F, r, h, scal, pairs, legs), c in zip(search["basis"], search["c"]):
        q = Fr(round(c * den), den)
        if F == "f":
            q = Fr(1)  # normalization
        if q == 0:
            continue
        terms.append({"F": F, "coef": str(q), "h": h, "scal": scal, "pairs": pairs, "legs": legs})
    return terms


def alpha_monos(d):
    return [(i, j) for j in (0, 1) for i in range(d + 1) if i + j <= d]


def pg_monos(d, n=4):
    out = []
    for tot in range(d + 1):
        for e in itertools.product(range(tot + 1), repeat=n):
            if sum(e) == tot:
                out.append(e)
    return out


def character(xe, mu, vpar):
    # xe = (al0, al1, p0, p1, p2, g)
    xc = tuple([xe[2] % 2, xe[3] % 2, xe[4] % 2, xe[5] % 2])
    return tuple((a + b) % 2 for a, b in zip(xc, vpar[mu]))


def nf_cache():
    cache = {}

    def nf(e):
        if e not in cache:
            cache[e] = X.reduce_circle3({e: Fr(1)})
        return cache[e]
    return nf


def fit(cert, eps, eta, dal=2, dpg=1, dal_chi=2, dpg_chi=0, verbose=True):
    import clarabel
    t0 = time.time()
    Q, vnames, xvars, vpar = X.interior_matrix(cert, verbose)
    V = len(vnames)
    nvar = len(xvars)
    zero_key = tuple([0] * nvar)
    T = [[dict(e) for e in row] for row in Q]
    for i, n in enumerate(vnames):
        if n == "z" or n.startswith("l"):
            T[i][i] = X.padd(T[i][i], {zero_key: Fr(1)}, -eps)
        T[i][i] = X.padd(T[i][i], {zero_key: Fr(1)}, -eta)
    chi = {zero_key: Fr(1)}
    for k in range(2, nvar):
        e = [0] * nvar
        e[k] = 2
        chi[tuple(e)] = Fr(-1)
    nf = nf_cache()

    def make_basis(da, dp):
        B = []
        for am in alpha_monos(da):
            for pm in pg_monos(dp):
                for mu in range(V):
                    B.append((am + pm, mu))
        blocks = {}
        for b in B:
            blocks.setdefault(character(b[0], b[1], vpar), []).append(b)
        return [blocks[k] for k in sorted(blocks)]

    groups = [("one", blk) for blk in make_basis(dal, dpg)]
    groups += [("chi", blk) for blk in make_basis(dal_chi, dpg_chi)]
    # variable layout: svec of each block (upper triangle by columns, off-diag sqrt2-scaled)
    col_of = []
    ncol = 0
    for mult, blk in groups:
        n = len(blk)
        idx = {}
        for j in range(n):
            for i in range(j + 1):
                idx[(i, j)] = ncol
                ncol += 1
        col_of.append(idx)
    # equations: key (mu, nu, xexp) with mu <= nu
    eq_index = {}
    rows, cols, vals = [], [], []

    def eq(key):
        if key not in eq_index:
            eq_index[key] = len(eq_index)
        return eq_index[key]
    r2 = np.sqrt(2.0)
    for gi, (mult, blk) in enumerate(groups):
        mpoly = chi if mult == "chi" else {zero_key: Fr(1)}
        n = len(blk)
        for j in range(n):
            for i in range(j + 1):
                (ei, mi), (ej, mj) = blk[i], blk[j]
                e = tuple(a + b for a, b in zip(ei, ej))
                prod = {}
                for me, mc in mpoly.items():
                    ee = tuple(a + b for a, b in zip(e, me))
                    for ke, kc in nf(ee).items():
                        prod[ke] = prod.get(ke, Fr(0)) + mc * kc
                # contribution of G_ij (and G_ji) to entry (mi, mj) of the matrix SOS
                # entry (mu,nu) with mu<=nu collects G_rs b_r b_s with (mu_r,mu_s)=(mu,nu) or (nu,mu)
                mu, nu = min(mi, mj), max(mi, mj)
                if i == j:
                    w = 1.0  # G_ii, svec value = G_ii
                else:
                    # G_ij appears as (i,j) and (j,i); if mi == mj both land on the diagonal entry
                    # (factor 2); otherwise one lands on (mu,nu) and one on (nu,mu): we write the
                    # equation for the upper entry, which receives exactly one of them.
                    w = (2.0 if mi == mj else 1.0) / r2
                c = col_of[gi][(i, j)]
                for ke, kc in prod.items():
                    if kc:
                        rows.append(eq((mu, nu, ke)))
                        cols.append(c)
                        vals.append(w * float(kc))
    # right-hand side
    for mu in range(V):
        for nu in range(mu, V):
            for ke in T[mu][nu]:
                eq((mu, nu, ke))
    neq = len(eq_index)
    b_eq = np.zeros(neq)
    for (mu, nu, ke), r in eq_index.items():
        b_eq[r] = float(T[mu][nu].get(ke, Fr(0)))
    nx = ncol + 1  # + margin variable
    Aeq = sp.csc_matrix((vals, (rows, cols)), shape=(neq, nx))
    # PSD: s = svec(G_k) - m svec(I) in PSD  <=>  -x_G + m svec(I) + s = 0
    Arows, cones = [Aeq], [clarabel.ZeroConeT(neq)]
    bvec = [b_eq]
    for gi, (mult, blk) in enumerate(groups):
        n = len(blk)
        k = n * (n + 1) // 2
        cidx = [col_of[gi][(i, j)] for j in range(n) for i in range(j + 1)]
        isv = np.array([1.0 if i == j else 0.0 for j in range(n) for i in range(j + 1)])
        M = sp.lil_matrix((k, nx))
        for r_, c in enumerate(cidx):
            M[r_, c] = -1.0
        M[:, nx - 1] = isv[:, None]
        Arows.append(M.tocsc())
        bvec.append(np.zeros(k))
        cones.append(clarabel.PSDTriangleConeT(n))
    # cap the margin variable to keep the problem bounded: m <= 1
    capr = sp.csc_matrix(([1.0], ([0], [nx - 1])), shape=(1, nx))
    Arows.append(capr); bvec.append(np.array([1.0])); cones.append(clarabel.NonnegativeConeT(1))
    A = sp.vstack(Arows).tocsc()
    b = np.concatenate(bvec)
    q = np.zeros(nx); q[-1] = -1.0
    st = clarabel.DefaultSettings(); st.verbose = False; st.max_iter = 500
    st.tol_gap_abs = 1e-10; st.tol_gap_rel = 1e-10; st.tol_feas = 1e-10
    if verbose:
        print(f"  SOS: {len(groups)} blocks, sizes {sorted(len(b_) for _, b_ in groups)}, "
              f"{ncol} Gram unknowns, {neq} equations")
    ts = time.time()
    sol = clarabel.DefaultSolver(sp.csc_matrix((nx, nx)), q, A, b, cones, st).solve()
    x = np.array(sol.x)
    if verbose:
        print(f"  SOS solve: {sol.status}, margin mu = {x[-1]:.3e} ({time.time() - ts:.1f}s); "
              f"eq residual {np.abs(Aeq @ x - b_eq).max():.2e}")
    # unpack Gram blocks
    grams = []
    for gi, (mult, blk) in enumerate(groups):
        n = len(blk)
        G = np.zeros((n, n))
        for j in range(n):
            for i in range(j + 1):
                v = x[col_of[gi][(i, j)]]
                if i == j:
                    G[i, i] = v
                else:
                    G[i, j] = G[j, i] = v / r2
        grams.append((mult, blk, G))
    return grams, float(x[-1]), str(sol.status), time.time() - t0


def to_rational(G, den):
    n = G.shape[0]
    return [[str(Fr(int(round(G[i, j] * den)), den)) for j in range(n)] for i in range(n)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("search")
    ap.add_argument("--den", type=int, default=1000, help="denominator for ansatz coefficients")
    ap.add_argument("--gden", type=int, default=10 ** 9, help="denominator for Gram entries")
    ap.add_argument("--eps", default="1/50")
    ap.add_argument("--eta", default="1/1000")
    ap.add_argument("--delta", default="1/100")
    ap.add_argument("--dal", type=int, default=2)
    ap.add_argument("--dpg", type=int, default=1)
    ap.add_argument("--dal-chi", type=int, default=2)
    ap.add_argument("--dpg-chi", type=int, default=0)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    search = json.load(open(args.search))
    cert = {"m": search["m"], "a": str(Fr(search["a"]).limit_denominator(1000)),
            "eps": args.eps, "delta": args.delta,
            "comment": "generated by sos_fit.py from " + os.path.basename(args.search),
            "terms": rational_terms(search, args.den)}
    eps, eta = Fr(args.eps), Fr(args.eta)
    grams, mu, status, tt = fit(cert, eps, eta, args.dal, args.dpg, args.dal_chi, args.dpg_chi)
    blocks = []
    for mult, blk, G in grams:
        blocks.append({"mult": mult, "basis": [[list(e), mu_] for e, mu_ in blk],
                       "gram": to_rational(G, args.gden)})
    cert["interior"] = {"method": "sos", "eta": str(eta), "sos_margin_float": mu,
                        "solver_status": status, "fit_time_s": tt,
                        "degrees": {"dal": args.dal, "dpg": args.dpg, "dal_chi": args.dal_chi,
                                    "dpg_chi": args.dpg_chi},
                        "blocks": blocks}
    with open(args.out, "w") as fh:
        json.dump(cert, fh)
    print(f"wrote {args.out} ({tt:.1f}s)")


if __name__ == "__main__":
    main()
