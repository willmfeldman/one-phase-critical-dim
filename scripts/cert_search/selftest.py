#!/usr/bin/env python3
"""Self-tests of the numeric engine.

1. The single row U = A gives  m z^2 + |X|^2 + (2a-2)|q|^2  in the interior and
   2 lam - tr A^3 on the boundary (the preprint's computation for this row, with 5
   replaced by m).
2. Regression at m = 5: the preprint's m = 5 certificate (Table I, embedded in
   paper_table1_m5.py), assembled by the GENERIC-m code of engine.py with beta^2 = 4,
   satisfies I - eps_*(z^2+|l|^2) >= 0 and S >= delta_* at random points.  This
   validates the assembly conventions (slot orders, C = K - K^(12), the D_l rules, the
   q coefficients) against independently published data.
"""

import os
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import engine as E  # noqa: E402


def rand_points(m, N, rng):
    A = rng.normal(size=(N, m, m))
    A = A + np.swapaxes(A, 1, 2)
    A -= np.einsum("nii->n", A)[:, None, None] * np.eye(m) / m
    A /= np.linalg.norm(A, axis=(1, 2))[:, None, None]
    pg = rng.normal(size=(N, m + 1))
    pg /= np.linalg.norm(pg, axis=1, keepdims=True)
    pg *= rng.uniform(size=(N, 1)) ** (1 / (m + 1))
    return A, pg[:, :m], pg[:, m]


def test_U_equals_A(m, a=0.6):
    rng = np.random.default_rng(5)
    L = E.Layout(m)
    A, p, g = rand_points(m, 7, rng)
    ia = E.InteriorAssembler(L, A, p, g, a, ((m - 1) / 2) ** 2, m)
    mono = E.Mono(2, 0, (), ((0, 1, 1),), ())
    Q = ia.form("U", lambda c: E.eval_mono(mono, c))
    # expected: m z^2 + |X|^2 + (2a-2)|q|^2
    Qe = np.zeros_like(Q)
    Qe[:, 1, 1] = m
    for s in range(L.nX):
        Qe[:, 2 + m + s, 2 + m + s] += 1
    Qe += (2 * a - 2) * np.einsum("nlu,nlv->nuv", ia.qv, ia.qv)
    err_i = np.abs(Q - Qe).max()
    # boundary
    Ab, pb = E.boundary_samples(m, 9)
    ba = E.BoundaryAssembler(Ab, pb, m)
    S = ba.value("U", lambda c: E.eval_mono(mono, c))
    tr3 = np.einsum("nij,njk,nki->n", Ab, Ab, Ab)
    err_b = np.abs(S - (2 * ba.lam - tr3)).max()
    print(f"[U=A, m={m}] interior err {err_i:.2e}, boundary err {err_b:.2e}")
    assert err_i < 1e-9 and err_b < 1e-12


def decode_word(word, r):
    trip = [word[i:i + 3] for i in range(0, len(word), 3)]
    h, b, j = (int(c) for c in trip[0])
    assert j == 0
    scal, pairs, legs = [("t", 3)] * b, [], []
    for t in trip[1:]:
        u, v, k = int(t[0]), int(t[1]), int(t[2])
        if u == 5 and v == 5:
            scal.append(("s", k))
        elif u == 5 or v == 5:
            legs.append((v if u == 5 else u, k))
        else:
            assert u < r and v < r and u != v
            pairs.append((min(u, v), max(u, v), k))
    return E.Mono(r, h, tuple(scal), tuple(pairs), tuple(legs))


def test_paper_m5(N=400):
    import paper_table1_m5 as T1
    table1 = T1.entries()
    Q = T1.Q
    a, eps, delta = (n / d for n, d in (T1.A_EXP, T1.EPS_STAR, T1.DELTA_STAR))
    ranks = {"f": 0, "U": 2, "K": 4, "M": 1, "P": 1}
    combos = {F: [] for F in ranks}
    for F, word, c in table1:
        combos[F].append((c / Q, decode_word(word, ranks[F])))
    m = 5
    rng = np.random.default_rng(11)
    L = E.Layout(m)
    A, p, g = rand_points(m, N, rng)
    # include points on the sphere |p|^2 + g^2 = 1 and at p = 0
    p[: N // 4] /= np.sqrt(np.sum(p[: N // 4] ** 2, 1) + g[: N // 4] ** 2)[:, None]
    g[: N // 4] /= 1.0
    t0 = time.time()
    ia = E.InteriorAssembler(L, A, p, g, a, 4.0, 6)
    Qf = sum(ia.form(F, lambda c, F=F: E.eval_combo(combos[F], c)) for F in ranks)
    Qm = Qf - eps * L.Ezl[None]
    mins = np.linalg.eigvalsh(Qm)[:, 0]
    print(f"[paper m=5] interior: min eig of I - eps*(z^2+|l|^2) over {N} pts = {mins.min():.3e}"
          f"  ({time.time() - t0:.1f}s)")
    # boundary at random boundary configurations (non-diagonal: rotate)
    Ab, pb = E.boundary_samples(m, 3000)
    ba = E.BoundaryAssembler(Ab, pb, 6)
    S = sum(ba.value(F, lambda c, F=F: E.eval_combo(combos[F], c)) for F in ranks)
    print(f"[paper m=5] boundary: min S over {len(S)} pts = {S.min():.6f} (delta_* = {delta:.6f})")
    # P vanishes at g = 0
    assert all(mono.h > 0 for _, mono in combos["P"])
    assert mins.min() > -1e-9 and S.min() >= delta - 1e-12


if __name__ == "__main__":
    for m in (2, 3, 4, 5):
        test_U_equals_A(m)
    test_paper_m5()
    print("selftest OK")
