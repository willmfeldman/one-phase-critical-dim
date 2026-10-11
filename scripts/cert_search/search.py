#!/usr/bin/env python3
"""Sampled-SDP search for m-dimensional certificates.

For an equivariant polynomial ansatz (see engine.py) the unknown coefficients c enter
the interior form I and the boundary value S linearly.  We solve

    maximize t   s.t.  Q(x_i; c) - t (z^2 + |l|^2)  PSD   (x_i interior samples)
                       S(y_j; c) >= t                       (y_j boundary samples)
                       mean_i f(x_i; c) = 1,   |c|_inf <= cmax

by a cutting-plane loop: solve on an active set, evaluate the minimum eigenvalue on a
dense validation set, add the worst points, repeat.  A positive optimum on the dense
set is numerical evidence only; exact_check.py decides.

Usage examples:
  python search.py --m 3 --a 0.6 --spec f:0,0,3 U:0,0,3 K:0,0,2
  python search.py --m 3 --a 0.6 --spec f:2,2,2 U:2,2,2 K:0,0,1 M:3,2,2 P:1,1,1 --out sol.json
A spec entry F:pdeg,gdeg,Adeg bounds the degree in p, in g and in A of family F.
"""

import argparse
import json
import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import engine as E  # noqa: E402

RANK = {"f": 0, "U": 2, "K": 4, "M": 1, "P": 1}
GPAR = {"f": 0, "U": 0, "K": 0, "M": 0, "P": 1}


def build_basis(m, spec, kmax=None):
    basis = []
    for F, (pd, gd, ad) in spec.items():
        monos = E.enumerate_monos(m, RANK[F], pd, gd, ad, GPAR[F], kmax)
        if F == "P":
            monos = [mo for mo in monos if mo.h > 0]
        basis += [(F, mo) for mo in monos]
    return basis


def contributions(m, basis, A, p, g, Ab, pb, a, beta2, kmax, L):
    """Interior forms (nb, N, V, V) and boundary values (nb, Nb)."""
    ia = E.InteriorAssembler(L, A, p, g, a, beta2, kmax)
    ba = E.BoundaryAssembler(Ab, pb, kmax) if Ab is not None else None
    Qs, Ss, fs = [], [], []
    for F, mo in basis:
        fn = (lambda c, mo=mo: E.eval_mono(mo, c))
        Qs.append(ia.form(F, fn))
        Ss.append(ba.value(F, fn) if ba is not None else None)
        fs.append(E.eval_mono(mo, ia.jet.base) if F == "f" else np.zeros(len(A)))
    return np.array(Qs), (np.array(Ss) if ba is not None else None), np.array(fs)


def prune(m, basis, a, beta2, kmax, L, seed=7, tol=1e-9):
    """Remove ansatz elements whose effect (on I and S) is linearly dependent."""
    rng = np.random.default_rng(seed)
    n = 40
    A = rng.normal(size=(n, m, m)); A = A + np.swapaxes(A, 1, 2)
    A -= np.einsum("nii->n", A)[:, None, None] * np.eye(m) / m
    A /= np.linalg.norm(A, axis=(1, 2))[:, None, None]
    pg = rng.normal(size=(n, m + 1)) * 0.5
    Ab, pb = E.boundary_samples(m, 25)
    Q, S, _ = contributions(m, basis, A, pg[:, :m], pg[:, m], Ab, pb, a, beta2, kmax, L)
    iu = np.triu_indices(L.V)
    M = np.concatenate([Q[:, :, iu[0], iu[1]].reshape(len(basis), -1), S], axis=1)
    norms = np.linalg.norm(M, axis=1)
    keep0 = [i for i in range(len(basis)) if norms[i] > tol]
    from scipy.linalg import qr
    Mk = M[keep0] / norms[keep0][:, None]
    _, R, piv = qr(Mk.T, pivoting=True, mode="economic")
    d = np.abs(np.diag(R))
    rank = int(np.sum(d > 1e-8 * d[0]))
    keep = sorted(keep0[i] for i in piv[:rank])
    return [basis[i] for i in keep]


def svec_index(V):
    """Clarabel svec order: upper triangle by columns, off-diagonals scaled by sqrt 2."""
    ii, jj, sc = [], [], []
    for j in range(V):
        for i in range(j + 1):
            ii.append(i); jj.append(j); sc.append(1.0 if i == j else np.sqrt(2.0))
    return np.array(ii), np.array(jj), np.array(sc)


def solve_sdp(Qa, Sa, fa, Ezl, cmax, solver=None, verbose=False, return_duals=False, eta=0.0):
    """maximize t s.t. Q_i(c) - t Ezl PSD, S_j(c) >= t, mean f = 1, |c| <= cmax.
    Direct Clarabel call; x = (c, t)."""
    import clarabel
    import scipy.sparse as sp
    nb, N, V, _ = Qa.shape
    nx = nb + 1
    ii, jj, sc = svec_index(V)
    rows_A, rows_b, cones = [], [], []
    # zero cone: mean f = 1
    rows_A.append(sp.csr_matrix(np.append(fa.mean(axis=1), 0.0)[None]))
    rows_b.append(np.array([1.0]))
    cones.append(clarabel.ZeroConeT(1))
    # nonnegative: S_j c - t >= 0 ; cmax -+ c >= 0
    nn = []
    if Sa is not None and Sa.shape[1]:
        nn.append(np.hstack([-Sa.T, np.ones((Sa.shape[1], 1))]))
    I = np.eye(nb)
    nn.append(np.hstack([I, np.zeros((nb, 1))]))
    nn.append(np.hstack([-I, np.zeros((nb, 1))]))
    nnA = np.vstack(nn)
    nnb = np.zeros(nnA.shape[0]); nnb[-2 * nb:] = cmax
    rows_A.append(sp.csr_matrix(nnA)); rows_b.append(nnb)
    cones.append(clarabel.NonnegativeConeT(nnA.shape[0]))
    # PSD blocks: s = -(sum_b c_b svec Q_b - t svec E) = b - A x, b = 0
    Esv = Ezl[ii, jj] * sc
    Isv = np.eye(V)[ii, jj] * sc  # reserved margin eta * I on all of v
    blk = Qa[:, :, ii, jj] * sc  # (nb, N, nsv)
    for i in range(N):
        Ai = np.hstack([-blk[:, i, :].T, Esv[:, None]])
        rows_A.append(sp.csr_matrix(Ai)); rows_b.append(-eta * Isv)
        cones.append(clarabel.PSDTriangleConeT(V))
    A = sp.vstack(rows_A).tocsc()
    b = np.concatenate(rows_b)
    q = np.zeros(nx); q[-1] = -1.0
    st = clarabel.DefaultSettings(); st.verbose = verbose
    st.max_iter = 400
    s = clarabel.DefaultSolver(sp.csc_matrix((nx, nx)), q, A, b, cones, st)
    sol = s.solve()
    x = np.array(sol.x)
    status = str(sol.status)
    if return_duals:
        return x[:nb], x[nb], status, np.array(sol.z)
    return x[:nb], x[nb], status


def evaluate(m, basis, cvec, A, p, g, Ab, pb, a, beta2, kmax, L, chunk=4000):
    """Min eigenvalue of I - t... (returns min eig of Q - 0*Ezl per point,
    min eig of Q restricted with Ezl subtracted is handled by caller) and S."""
    fams = {}
    for (F, mo), c in zip(basis, cvec):
        if abs(c) > 0:
            fams.setdefault(F, []).append((c, mo))
    eigs = []
    for s in range(0, len(A), chunk):
        ia = E.InteriorAssembler(L, A[s:s + chunk], p[s:s + chunk], g[s:s + chunk], a, beta2, kmax)
        Q = sum(ia.form(F, lambda cc, F=F: E.eval_combo(fams[F], cc)) for F in fams)
        eigs.append(Q)
    Q = np.concatenate(eigs)
    S = None
    if Ab is not None:
        ba = E.BoundaryAssembler(Ab, pb, kmax)
        S = sum(ba.value(F, lambda cc, F=F: E.eval_combo(fams[F], cc)) for F in fams)
    return Q, S


def margin(Q, Ezl):
    """Largest t with Q - t Ezl PSD, per point (generalized: via bisection-free
    formula using eigen of Q - t Ezl is not linear; we report min eig of Q - eps Ezl
    for eps given separately).  Here: min eigenvalue of Q itself on the complement
    plus the Ezl block, computed as min generalized margin by bisection."""
    lo, hi = -10.0, 10.0
    for _ in range(50):
        mid = 0.5 * (lo + hi)
        ok = np.linalg.eigvalsh(Q - mid * Ezl)[:, 0] >= -1e-12
        if ok.all():
            lo = mid
        else:
            hi = mid
    return lo


def pointwise_margin(Q, Ezl, iters=40):
    lo = np.full(len(Q), -10.0)
    hi = np.full(len(Q), 10.0)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        ok = np.linalg.eigvalsh(Q - mid[:, None, None] * Ezl[None])[:, 0] >= -1e-12
        lo = np.where(ok, mid, lo)
        hi = np.where(ok, hi, mid)
    return lo


def parse_spec(items):
    spec = {}
    for it in items:
        F, rest = it.split(":")
        spec[F] = tuple(int(x) for x in rest.split(","))
    return spec


def run(m, a, spec, n_eig=31, n_ball=400, n_init=150, rounds=12, add=60, cmax=1e3,
        solver="CLARABEL", kmax=None, seed=0, verbose=True, out=None, eta=0.0):
    beta2 = ((m - 1) / 2) ** 2
    kmax = (m - 1) if kmax is None else kmax
    L = E.Layout(m)
    t0 = time.time()
    basis = build_basis(m, spec, kmax)
    nb0 = len(basis)
    basis = prune(m, basis, a, beta2, kmax, L)
    if verbose:
        counts = {F: sum(1 for b in basis if b[0] == F) for F in RANK}
        print(f"m={m} a={a} spec={spec}: basis {nb0} -> {len(basis)} after pruning {counts}"
              f" ({time.time() - t0:.1f}s)", flush=True)
    A, p, g = E.interior_samples(m, n_eig if m > 2 else 1, n_ball, seed)
    Ab, pb = E.boundary_samples(m, 201)
    rng = np.random.default_rng(seed + 1)
    active = list(rng.choice(len(A), size=min(n_init, len(A)), replace=False))
    # always include p = 0, g = 0 points and the sphere |p|^2+g^2 = 1 extreme points
    active = sorted(set(active) | set(np.where(np.abs(p).sum(1) + np.abs(g) < 1e-12)[0]))
    _, Sb, _ = contributions(m, basis, A[:1], p[:1], g[:1], Ab, pb, a, beta2, kmax, L)
    hist = []
    best = None
    for rd in range(rounds):
        Qa, _, fa = contributions(m, basis, A[active], p[active], g[active], None, None, a, beta2, kmax, L)
        ts = time.time()
        cvec, t, status = solve_sdp(Qa, Sb, fa, L.Ezl, cmax, solver, eta=eta)
        if cvec is None:
            print("  solver failed:", status)
            break
        Q, S = evaluate(m, basis, cvec, A, p, g, Ab, pb, a, beta2, kmax, L)
        marg = pointwise_margin(Q - eta * np.eye(L.V)[None], L.Ezl)
        worst = np.argsort(marg)[:add]
        hist.append((rd, len(active), float(t), float(marg.min()), float(S.min())))
        if verbose:
            print(f"  round {rd}: active {len(active)}  sdp t={t:.5f} ({status}, {time.time() - ts:.1f}s)"
                  f"  dense min margin {marg.min():.5f}  min S {S.min():.5f}", flush=True)
        best = (cvec, t, marg.min(), S.min())
        new = [i for i in worst if i not in set(active) and marg[i] < t - 1e-6]
        if not new:
            break
        active = sorted(set(active) | set(int(i) for i in new))
    res = {"m": m, "a": a, "eta": eta, "spec": {k: list(v) for k, v in spec.items()}, "kmax": kmax,
           "basis": [[F, mo.rank, mo.h, [list(s) for s in mo.scal], [list(x) for x in mo.pairs],
                      [list(x) for x in mo.legs]] for F, mo in basis],
           "c": [float(x) for x in best[0]] if best else None,
           "t_sdp": best[1] if best else None, "dense_margin": best[2] if best else None,
           "dense_minS": best[3] if best else None, "history": hist,
           "time": time.time() - t0}
    if out:
        with open(out, "w") as fh:
            json.dump(res, fh, indent=1)
    if verbose:
        print(f"  done in {res['time']:.1f}s", flush=True)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, required=True)
    ap.add_argument("--a", type=float, default=0.6)
    ap.add_argument("--spec", nargs="+", required=True)
    ap.add_argument("--n-eig", type=int, default=31)
    ap.add_argument("--n-ball", type=int, default=400)
    ap.add_argument("--rounds", type=int, default=12)
    ap.add_argument("--kmax", type=int, default=None)
    ap.add_argument("--cmax", type=float, default=1e3)
    ap.add_argument("--solver", default="CLARABEL")
    ap.add_argument("--out", default=None)
    ap.add_argument("--eta", type=float, default=0.0)
    args = ap.parse_args()
    run(args.m, args.a, parse_spec(args.spec), n_eig=args.n_eig, n_ball=args.n_ball,
        rounds=args.rounds, kmax=args.kmax, cmax=args.cmax, solver=args.solver, out=args.out, eta=args.eta)


if __name__ == "__main__":
    main()
