#!/usr/bin/env python3
"""Export the m = 3 interior sum-of-squares certificate as Lean data.

Input: a certificate JSON with an "sos" interior (default certs/m3a2950_cert.json).
Output: Lean data modules under OnePhaseDimension/LowDim/SOS/Data/.

The exported identity, in the polynomial ring Q[al0, al1, p0, p1, p2, g, v0..v11], is

  S Q - S eps E - S eta I = sum_k mult_k sum_{r,s} S' (L_k L_k^T)_{rs} b_r b_s + S R + h S Mult,

where
  * Q is the quadratic form of the interior expression at A = diag(al0, al1, -al0-al1) in
    v = (w, z, l0, l1, l2, xi0..xi6), NOT reduced modulo h (so that it is the polynomial a
    Lean-side computation of the interior expression produces);
  * E = z^2 + |l|^2, I = |v|^2, h = al0^2 + al1^2 + (al0+al1)^2 - 1;
  * mult_k is 1 or chi = 1 - |p|^2 - g^2, b_r = x^{e_r} v_{mu_r} (the block basis);
  * L_k is an integer lower-triangular matrix, round(2^K chol(G_k)), so that
    (L L^T) / 4^K approximates the certificate Gram matrix G_k; S' = S / 4^K;
  * R is the remainder of the division by h (al1-degree <= 1) and Mult the quotient;
  * S is the least common denominator.

Python is an untrusted oracle here: every identity and bound is re-checked in Lean by kernel
computation. This script only re-checks the identity exactly, as a sanity check.

Key encoding (shared with the Lean side): a monomial x^e v_mu v_nu (mu <= nu) is the natural
number (12 mu + nu) * 16^6 + sum_i e_i 16^i, variables x = (al0, al1, p0, p1, p2, g).

Usage: python -I export_lean.py [CERT.json] [--K 40] [--out DIR] [--dry]
"""

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np  # noqa: E402

import exact_check as ec  # noqa: E402

NV = 12
NX = 6
B = 16
XB = B ** NX


def key(mu, nu, e):
    if mu > nu:
        mu, nu = nu, mu
    assert all(0 <= d < B for d in e) and 0 <= nu < NV
    c = sum(d * B ** i for i, d in enumerate(e))
    return (NV * mu + nu) * XB + c


def code(e):
    return sum(d * B ** i for i, d in enumerate(e))


def add_to(P, k, c):
    nv = P.get(k, Fr(0)) + c
    if nv:
        P[k] = nv
    else:
        P.pop(k, None)


def unreduced_Q(cert):
    """The quadratic-form matrix of the interior expression at diagonal A, without the
    reduction modulo h that exact_check applies."""
    saved = ec.reduce_circle3
    ec.reduce_circle3 = lambda P: dict(P)
    try:
        Q, vnames, xvars, _ = ec.interior_matrix(cert, verbose=False)
    finally:
        ec.reduce_circle3 = saved
    assert vnames == ["w", "z", "l0", "l1", "l2"] + [f"x{s}" for s in range(7)]
    assert xvars == ["al0", "al1", "p0", "p1", "p2", "g"]
    return Q


def sym_poly(Q):
    """Q as a polynomial in v: {(mu, nu, e): coeff}, mu <= nu."""
    P = {}
    for mu in range(NV):
        for nu in range(NV):
            for e, c in Q[mu][nu].items():
                a, b = min(mu, nu), max(mu, nu)
                add_to(P, (a, b, e), c)
    return P


def divide_h(D):
    """D = h * Mult + R with R of al1-degree <= 1; h = 2 al1^2 + 2 al0 al1 + 2 al0^2 - 1."""
    D = dict(D)
    Mult = {}
    while True:
        hi = [k for k in D if k[2][1] >= 2]
        if not hi:
            return Mult, D
        top = max(k[2][1] for k in hi)
        for k in [k for k in hi if k[2][1] == top]:
            c = D[k]
            mu, nu, e = k
            q = list(e)
            q[1] -= 2
            q = tuple(q)
            qc = c / 2
            add_to(Mult, (mu, nu, q), qc)
            # subtract qc * x^q * h
            for de, dc in (((0, 2), 2), ((1, 1), 2), ((2, 0), 2), ((0, 0), -1)):
                ne = list(q)
                ne[0] += de[0]
                ne[1] += de[1]
                add_to(D, (mu, nu, tuple(ne)), -qc * dc)
            assert k not in D


def hmul(Mult):
    out = {}
    for (mu, nu, e), c in Mult.items():
        for de, dc in (((0, 2), 2), ((1, 1), 2), ((2, 0), 2), ((0, 0), -1)):
            ne = list(e)
            ne[0] += de[0]
            ne[1] += de[1]
            add_to(out, (mu, nu, tuple(ne)), c * dc)
    return out


CHI = [((0, 0, 0, 0, 0, 0), 1), ((0, 0, 2, 0, 0, 0), -1), ((0, 0, 0, 2, 0, 0), -1),
       ((0, 0, 0, 0, 2, 0), -1), ((0, 0, 0, 0, 0, 2), -1)]
ONE = [((0, 0, 0, 0, 0, 0), 1)]


def cholesky_int(G, K):
    Gf = np.array([[float(x) for x in row] for row in G])
    L = np.linalg.cholesky(Gf)
    n = len(G)
    Li = [[int(round(L[i, j] * 2 ** K)) for j in range(i + 1)] for i in range(n)]
    return Li


def gram_int(Li):
    n = len(Li)
    N = [[0] * n for _ in range(n)]
    for r in range(n):
        for s in range(n):
            N[r][s] = sum(a * b for a, b in zip(Li[r], Li[s]))
    return N


def lean_int(c):
    c = int(c)
    return f".ofNat {c}" if c >= 0 else f".negSucc {-c - 1}"


def wrap_items(items, indent="  ", width=100):
    """Join items with ", " into lines of at most `width` characters (a trailing comma on
    every line but the last)."""
    lines, cur = [], indent
    for i, it in enumerate(items):
        piece = it + ("," if i < len(items) - 1 else "")
        if cur.strip() and len(cur) + 1 + len(piece) > width:
            lines.append(cur.rstrip())
            cur = indent
        cur += ("" if cur == indent else " ") + piece
    if cur.strip():
        lines.append(cur.rstrip())
    return lines


def wrap_text(text, width=100):
    words, lines, cur = text.split(" "), [], ""
    for w in words:
        if cur and len(cur) + 1 + len(w) > width:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + " " + w) if cur else w
    lines.append(cur)
    return "\n".join(lines)


def poly_lines(P):
    return wrap_items([f"({k}, {lean_int(c)})" for k, c in sorted(P.items())])


HEADER = """/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

{imports}

/-!
# {title}

{doc}

Generated by `scripts/cert_search/export_lean.py` from
`{cert}`; do not edit by hand.
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS.Data
"""

FOOTER = "\nend OnePhaseDimension.LowDim.SOS.Data\n"


def write_poly_module(path, name, title, doc, P, cert_name, imports="public import Mathlib.Init"):
    lines = poly_lines(P)
    body = [HEADER.format(imports=imports, title=title, doc=wrap_text(doc), cert=cert_name)]
    body.append("set_option maxRecDepth 100000 in")
    body.append(f"/-- {title} ({len(P)} terms). -/")
    body.append(f"def {name} : List (Nat × Int) := [")
    body.append("\n".join(lines))
    body.append("]")
    body.append(FOOTER)
    text = "\n".join(body)
    with open(path, "w") as f:
        f.write(text)
    return text.count("\n")


def main():
    ap = argparse.ArgumentParser()
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("cert", nargs="?", default=os.path.join(here, "certs", "m3a2950_cert.json"))
    ap.add_argument("--K", type=int, default=40)
    ap.add_argument("--out", default=os.path.join(here, "..", "..", "OnePhaseDimension", "LowDim",
                                                  "SOS", "Data"))
    ap.add_argument("--dry", action="store_true")
    args = ap.parse_args()
    t0 = time.time()
    cert = json.load(open(args.cert))
    assert cert["m"] == 3 and cert["interior"]["method"] == "sos"
    eps = Fr(cert["eps"])
    eta = Fr(cert["interior"]["eta"])
    K = args.K
    Q = unreduced_Q(cert)
    Qp = sym_poly(Q)
    z6 = (0,) * NX
    # T = Q - eps E - eta I
    T = dict(Qp)
    for mu in range(NV):
        c = eta + (eps if mu in (1, 2, 3, 4) else 0)
        add_to(T, (mu, mu, z6), -c)
    # SOS part
    blocks = []
    Ssum = {}
    for blk in cert["interior"]["blocks"]:
        basis = [(tuple(b[0]), int(b[1])) for b in blk["basis"]]
        G = [[Fr(x) for x in row] for row in blk["gram"]]
        Li = cholesky_int(G, K)
        N = gram_int(Li)
        mult = CHI if blk["mult"] == "chi" else ONE
        for r, (er, mr) in enumerate(basis):
            for s, (es, ms) in enumerate(basis):
                if N[r][s] == 0:
                    continue
                for em, sg in mult:
                    e = tuple(a + b + c for a, b, c in zip(er, es, em))
                    a, b = min(mr, ms), max(mr, ms)
                    add_to(Ssum, (a, b, e), Fr(sg * N[r][s], 4 ** K))
        blocks.append((blk["mult"], basis, Li))
    D = dict(T)
    for k, c in Ssum.items():
        add_to(D, k, -c)
    Mult, R = divide_h(D)
    # exact sanity check: T = Ssum + R + h Mult
    chk = dict(Ssum)
    for k, c in R.items():
        add_to(chk, k, c)
    for k, c in hmul(Mult).items():
        add_to(chk, k, c)
    for k, c in T.items():
        add_to(chk, k, -c)
    assert not chk, "identity failed"
    rsum = sum(abs(c) for c in R.values())
    dens = [c.denominator for P in (Qp, R, Mult) for c in P.values()]
    S = math.lcm(4 ** K, eps.denominator, eta.denominator, *dens)
    Sp = S // 4 ** K
    assert S % 4 ** K == 0 and (S * eps).denominator == 1 and (S * eta).denominator == 1
    maxdeg = [max(k[2][i] for P in (Qp, R, Mult) for k in P) for i in range(NX)]
    print(f"Q terms {len(Qp)}, Ssum terms {len(Ssum)}, R terms {len(R)}, Mult terms {len(Mult)}")
    print(f"sum |R| = {float(rsum):.3e} (eta = {float(eta)}), bound ok: {rsum < eta}")
    print(f"max x-degrees {maxdeg}; S = {S} ({len(str(S))} digits), S' = {Sp}")
    print(f"max |L| = {max(abs(x) for _, _, Li in blocks for row in Li for x in row)}")
    print(f"time {time.time() - t0:.1f}s")
    assert rsum < eta
    if args.dry:
        return 0
    out = os.path.abspath(args.out)
    os.makedirs(out, exist_ok=True)
    cert_name = "scripts/cert_search/certs/" + os.path.basename(args.cert)

    def kp(P):
        return {key(mu, nu, e): c * S for (mu, nu, e), c in P.items()}

    for c in list(kp(Qp).values()) + list(kp(R).values()) + list(kp(Mult).values()):
        assert c.denominator == 1
    n = write_poly_module(os.path.join(out, "QForm.lean"), "qPoly",
                          "The scaled interior form at diagonal `A`",
                          "`S · Q`, the quadratic form of the interior expression at "
                          "`A = diag(α₀, α₁, -α₀-α₁)`, in the packed key encoding of "
                          "`OnePhaseDimension.LowDim.SOS.dataMono`.", kp(Qp), cert_name)
    print("QForm.lean lines", n)
    n = write_poly_module(os.path.join(out, "Residual.lean"), "residualPoly",
                          "The scaled residual", "`S · R`, the remainder of the certificate "
                          "identity (degree at most one in `α₁`).", kp(R), cert_name)
    print("Residual.lean lines", n)
    # Mult may be long: split into parts of at most 3000 terms
    items = sorted(kp(Mult).items())
    parts = [dict(items[i:i + 3000]) for i in range(0, len(items), 3000)]
    for j, part in enumerate(parts):
        n = write_poly_module(os.path.join(out, f"Mult{j}.lean"), f"multPoly{j}",
                              f"The scaled multiplier of the circle relation, part {j}",
                              "`S · Mult`, the multiplier of `h = α₀² + α₁² + (α₀+α₁)² - 1` "
                              "in the certificate identity.", part, cert_name)
        print(f"Mult{j}.lean lines", n)
    # blocks: one module per group of blocks, keeping files small
    groups = []
    cur, size = [], 0
    for i, b in enumerate(blocks):
        sz = sum(len(row) for row in b[2])
        if cur and size + sz > 1600:
            groups.append(cur)
            cur, size = [], 0
        cur.append(i)
        size += sz
    if cur:
        groups.append(cur)
    for gi, grp in enumerate(groups):
        body = [HEADER.format(imports="public import Mathlib.Init",
                              title=f"Cholesky factors of the Gram blocks, group {gi}",
                              doc=wrap_text("Each block is its multiplier flag (`true` for `χ`), and its "
                                  "rows `(monomial code, v-index, row of L)`."),
                              cert=cert_name)]
        for i in grp:
            mult, basis, Li = blocks[i]
            body.append(f"/-- Gram block {i} (size {len(basis)}, multiplier "
                        f"{'χ' if mult == 'chi' else '1'}). -/")
            body.append(f"def block{i:02d} : Bool × List (Nat × Nat × List Int) :=")
            body.append(f"  ({str(mult == 'chi').lower()}, [")
            rows = []
            for j, ((e, mu), row) in enumerate(zip(basis, Li)):
                items = [lean_int(x) for x in row]
                items[0] = f"({code(e)}, {mu}, [" + items[0]
                items[-1] += "])" + ("," if j < len(basis) - 1 else "")
                rows += wrap_items(items, indent="  ")
            body.append("\n".join(rows))
            body.append("])\n")
        body.append(FOOTER)
        with open(os.path.join(out, f"Blocks{gi}.lean"), "w") as f:
            f.write("\n".join(body))
        print(f"Blocks{gi}.lean blocks {grp}")
    with open(os.path.join(out, "Scale.lean"), "w") as f:
        f.write(HEADER.format(imports="public import Mathlib.Init", title="Scale factors",
                              doc="The common denominator `S` and `S' = S / 4^K`.",
                              cert=cert_name))
        f.write(f"\n/-- The common denominator `S`. -/\ndef scale : Nat := {S}\n")
        f.write(f"\n/-- `S' = S / 4^{K}`, the scale of the Gram blocks `L Lᵀ`. -/\n"
                f"def gramScale : Nat := {Sp}\n")
        f.write(FOOTER)
    print(f"done {time.time() - t0:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
