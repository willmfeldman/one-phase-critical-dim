#!/usr/bin/env python3
"""Consistency checks between the exact checker and the numeric engine, and negative
controls for the exact checker.

  1. For a certificate file, the exact interior polynomial I (exact_check.build_interior,
     general symmetric A) and the numeric engine (engine.py, validated against the paper's
     m = 5 data in selftest.py) agree at random points, including non-diagonal A.
  2. Exact O(m)-equivariance spot check: I(R.data) = I(data) in exact rational arithmetic
     for a rational orthogonal R (Cayley transform) at random rational points.
  3. Exact U = A identity: I = m z^2 + |X|^2 + (2a-2)|q|^2.
  4. Negative controls: perturbed certificates must be REJECTED.

Usage: python crosscheck.py certs/m3_cert.json
"""

import copy
import io
import itertools
import json
import os
import sys
from contextlib import redirect_stdout
from fractions import Fraction as Fr

import numpy as np
import sympy

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import engine as E  # noqa: E402
import exact_check as X  # noqa: E402


def setup(cert):
    m = cert["m"]
    Xb = X.stf3_rational_basis(m)
    ex = X.Exact(m, len(Xb))
    I = X.build_interior(cert, ex, Xb)
    return m, Xb, ex, I


def point_subs(ex, Xb, A, p, g, w, z, l, xi):
    m = ex.m
    G = ex.gen
    vals = {}
    for i in range(m):
        for j in range(i, m):
            vals[G[f"a{i}{j}"]] = A[i][j]
    for i in range(m):
        vals[G[f"p{i}"]] = p[i]
        vals[G[f"l{i}"]] = l[i]
    vals[G["g"]], vals[G["w"]], vals[G["z"]] = g, w, z
    for s in range(len(Xb)):
        vals[G[f"x{s}"]] = xi[s]
    return vals


def eval_exact(I, ex, vals):
    pts = [vals.get(gn, 0) for gn in ex.R.gens]
    return I(*[sympy.Rational(x.numerator, x.denominator) if isinstance(x, Fr) else x for x in pts])


def check_engine_agreement(cert, n=5, seed=3):
    m, Xb, ex, I = setup(cert)
    rng = np.random.default_rng(seed)
    terms = {}
    for t in cert["terms"]:
        mono = E.Mono(X.RANK[t["F"]], int(t["h"]), tuple(tuple(s) for s in t["scal"]),
                      tuple(tuple(x) for x in t["pairs"]), tuple(tuple(x) for x in t["legs"]))
        terms.setdefault(t["F"], []).append((float(Fr(t["coef"])), mono))
    L = E.Layout(m)
    maxerr = 0.0
    for _ in range(n):
        A = rng.normal(size=(m, m)); A = A + A.T; A -= np.trace(A) / m * np.eye(m)
        A /= np.linalg.norm(A)
        pg = rng.normal(size=m + 1); pg *= 0.9 * rng.uniform() / np.linalg.norm(pg)
        p, g = pg[:m], pg[m]
        w, z = rng.normal(), rng.normal()
        l = rng.normal(size=m)
        xi = rng.normal(size=len(Xb))
        Xt = sum(xi[s] * np.array(Xb[s][1], dtype=float) for s in range(len(Xb)))
        # exact polynomial evaluated in floats (rationalized inputs)
        fr = lambda x: Fr(float(x))
        vals = point_subs(ex, Xb, [[fr(A[i, j]) for j in range(m)] for i in range(m)],
                          [fr(x) for x in p], fr(g), fr(w), fr(z), [fr(x) for x in l],
                          [fr(x) for x in xi])
        ve = float(eval_exact(I, ex, vals))
        ia = E.InteriorAssembler(L, A[None], p[None], np.array([g]), float(Fr(cert["a"])),
                                 ((m - 1) / 2) ** 2, m)
        Q = sum(ia.form(F, lambda c, F=F: E.eval_combo(terms[F], c)) for F in terms)[0]
        v = np.concatenate([[w, z], l, np.einsum("sijk,ijk->s", L.E, Xt)])
        vn = v @ Q @ v
        maxerr = max(maxerr, abs(ve - vn) / (1 + abs(vn)))
    print(f"[1] exact I vs numeric engine at {n} random non-diagonal points: max rel err {maxerr:.2e}")
    return maxerr < 1e-9


def cayley(m):
    S = sympy.zeros(m, m)
    vals = [sympy.Rational(1, 2), sympy.Rational(-1, 3), sympy.Rational(2, 5)]
    k = 0
    for i in range(m):
        for j in range(i + 1, m):
            S[i, j] = vals[k % 3]; S[j, i] = -vals[k % 3]; k += 1
    R = (sympy.eye(m) - S) * (sympy.eye(m) + S).inv()
    assert sympy.simplify(R * R.T - sympy.eye(m)) == sympy.zeros(m, m)
    return R


def check_equivariance(cert, n=2, seed=5):
    m, Xb, ex, I = setup(cert)
    R = cayley(m)
    rng = np.random.default_rng(seed)
    Ebasis = sympy.Matrix([[sympy.Rational(T[idx].numerator, T[idx].denominator)
                            for (_, T) in Xb] for idx in itertools.product(range(m), repeat=3)])
    ok = True
    for _ in range(n):
        rq = lambda: sympy.Rational(int(rng.integers(-9, 10)), int(rng.integers(1, 10)))
        A = sympy.zeros(m, m)
        for i in range(m):
            for j in range(i, m):
                A[i, j] = A[j, i] = rq()
        A -= A.trace() / m * sympy.eye(m)
        p = sympy.Matrix([rq() for _ in range(m)]); l = sympy.Matrix([rq() for _ in range(m)])
        g, w, z = rq(), rq(), rq()
        xi = sympy.Matrix([rq() for _ in range(len(Xb))])
        Xv = Ebasis * xi
        # rotate X
        Xt = {idx: Xv[k] for k, idx in enumerate(itertools.product(range(m), repeat=3))}
        Xr = []
        for idx in itertools.product(range(m), repeat=3):
            s = 0
            for jdx in itertools.product(range(m), repeat=3):
                s += R[idx[0], jdx[0]] * R[idx[1], jdx[1]] * R[idx[2], jdx[2]] * Xt[jdx]
            Xr.append(s)
        xir = (Ebasis.T * Ebasis).inv() * Ebasis.T * sympy.Matrix(Xr)
        assert Ebasis * xir == sympy.Matrix(Xr)
        Ar, pr, lr = R * A * R.T, R * p, R * l

        def val(A_, p_, l_, xi_):
            G = ex.gen
            sub = {}
            for i in range(m):
                for j in range(i, m):
                    sub[G[f"a{i}{j}"]] = A_[i, j]
                sub[G[f"p{i}"]] = p_[i]; sub[G[f"l{i}"]] = l_[i]
            sub[G["g"]], sub[G["w"]], sub[G["z"]] = g, w, z
            for s in range(len(Xb)):
                sub[G[f"x{s}"]] = xi_[s]
            return I(*[sub.get(gn, 0) for gn in ex.R.gens])
        v0, v1 = val(A, p, l, xi), val(Ar, pr, lr, xir)
        ok &= (v0 == v1)
    print(f"[2] exact O({m}) equivariance under a rational rotation at {n} rational points: {ok}")
    return ok


def check_UA(m):
    cert = {"m": m, "a": "3/5", "terms": [{"F": "U", "coef": "1", "h": 0, "scal": [],
                                           "pairs": [[0, 1, 1]], "legs": []}]}
    m, Xb, ex, I = setup(cert)
    A, z = ex.A, ex.z
    Xt = np.empty((m, m, m), dtype=object)
    for idx in itertools.product(range(m), repeat=3):
        Xt[idx] = sum((ex.xi[s] * sympy.QQ(T[idx].numerator, T[idx].denominator)
                       for s, (_, T) in enumerate(Xb) if T[idx] != 0), ex.zero)
    q = [sum((Xt[l_, i, j] * A[i, j] for i in range(m) for j in range(m)), ex.zero) for l_ in range(m)]
    X2 = sum((Xt[idx] ** 2 for idx in itertools.product(range(m), repeat=3)), ex.zero)
    A2 = sum((A[i, j] ** 2 for i in range(m) for j in range(m)), ex.zero)
    expect = m * z ** 2 * A2 + X2 + (2 * sympy.QQ(3, 5) - 2) * sum((x ** 2 for x in q), ex.zero) * A2
    # I is exact as a polynomial without using |A| = 1; the identity holds with |A|^2 factors
    # on the constraint set.  Compare after substituting a rational unit-norm diagonal-free A
    # is not possible in general, so compare the difference modulo (|A|^2 - 1) numerically
    # at random points with |A| = 1.
    rng = np.random.default_rng(1)
    diff = I - expect
    worst = 0.0
    for _ in range(5):
        Am = rng.normal(size=(m, m)); Am = Am + Am.T; Am -= np.trace(Am) / m * np.eye(m)
        Am /= np.linalg.norm(Am)
        pts = []
        for gn in ex.R.gens:
            name = str(gn)
            if name.startswith("a") and not name.startswith("al"):
                pts.append(float(Am[int(name[1]), int(name[2])]))
            else:
                pts.append(float(rng.normal()))
        worst = max(worst, abs(float(diff(*pts))))
    print(f"[3] exact U = A row vs m z^2 + |X|^2 + (2a-2)|q|^2 (m={m}), max |diff| at |A|=1: {worst:.2e}")
    return worst < 1e-9


def negative_controls(path):
    cert = json.load(open(path))
    results = []
    variants = []
    m = cert["m"]
    # values chosen so that each variant violates a true inequality (m = 2: interior needs
    # c >= a / (2 (1 - eps)) for U = cA, and S = (1 - 2c)/sqrt 2 = 0.1414 for c = 2/5)
    bad_a, bad_delta, bad_eps = ("9/10", "1/5", "1/2") if m == 2 else ("7/10", "1/10", "1/10")
    c1 = copy.deepcopy(cert); c1["a"] = bad_a; variants.append((f"a = {bad_a} with same data", c1))
    if m == 3:
        c2 = copy.deepcopy(cert)
        for t in c2["terms"]:
            if t["F"] == "M":
                t["coef"] = "0"
        variants.append(("M set to 0", c2))
    c3 = copy.deepcopy(cert); c3["delta"] = bad_delta; variants.append((f"delta = {bad_delta}", c3))
    c4 = copy.deepcopy(cert); c4["eps"] = bad_eps; variants.append((f"eps = {bad_eps}", c4))
    if cert["m"] == 2:
        c5 = copy.deepcopy(cert)
        c5["terms"][1]["coef"] = "1/5"; variants.append(("U = A/5 (interior should fail)", c5))
        c6 = copy.deepcopy(cert)
        c6["terms"][1]["coef"] = "3/5"; variants.append(("U = 3A/5 (boundary should fail)", c6))
    tmp = os.path.join(os.path.dirname(os.path.abspath(path)), "_neg.json")
    for name, c in variants:
        json.dump(c, open(tmp, "w"))
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = X.main(tmp)
        out = buf.getvalue().strip().splitlines()[-1]
        results.append(rc != 0)
        print(f"[4] negative control '{name}': {'REJECTED (good)' if rc else 'ACCEPTED (BAD)'}")
    os.remove(tmp)
    return all(results)


if __name__ == "__main__":
    path = sys.argv[1]
    cert = json.load(open(path))
    ok = check_engine_agreement(cert)
    ok &= check_equivariance(cert)
    ok &= check_UA(cert["m"])
    ok &= negative_controls(path)
    print("crosscheck", "OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)
