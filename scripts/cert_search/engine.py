"""Numeric engine for the m-dimensional certificate search.

Everything here is floating point and is used only to *search*.  The exact
checker (exact_check.py) is written independently and does not import this
module.

Conventions (explained in README.md, section "Conventions"):
  data      A in STF^2(R^m), |A| = 1;  p in R^m;  g in R;  chi = 1 - |p|^2 - g^2 >= 0
  free      v = (w, z, l_0..l_{m-1}, xi_0..xi_{nX-1}),  X = sum_s xi_s E_s  (E_s an
            orthonormal basis of STF^3(R^m)),  q_l = X_lij A_ij
  D_l       D_l A_ij = X_lij - q_l A_ij,  D_l p_i = w A_li - g z delta_li,  D_l g = z p_l
  interior  I = z^2 [ m U:A + C_lijk (d_lj A_ik + d_lk A_ij) - beta2 f ]
              + [ D_l G_lijk + (2a-1) q_l G_lijk ] X_ijk
              + w [ D_l M_l + (2a+1) q_l M_l ] + z [ D_l P_l + 2a q_l P_l ]
              + f |l|^2 - (D_l f + 2a q_l f) l_l ,
            G_lijk = d_li U_jk + C_lijk,  C = K - K^(12).
  boundary  S = -lam f + U:(S0 + pp) + C_lijk p_l V_ijk + p.M   (g = 0, |p| = 1, Ap = lam p)

Tensor monomials ("graph monomials") are encoded as
    Mono(rank, h, scal, pairs, legs)
  h      power of g
  scal   tuple of ('s', k) = p.A^k p   and ('t', k) = tr A^k   (a multiset)
  pairs  tuple of (a, b, k): factor (A^k)_{ab} on free slots a < b
  legs   tuple of (a, k): factor (A^k p)_a on free slot a
Every free slot 0..rank-1 occurs exactly once in pairs/legs.  These are O(m)
equivariant (O(m) acts on slots, on p and by conjugation on A), with no
Levi-Civita tensor.
"""

from __future__ import annotations

import itertools
from collections import namedtuple

import numpy as np

Mono = namedtuple("Mono", "rank h scal pairs legs")

# ---------------------------------------------------------------------------
# linear algebra helpers
# ---------------------------------------------------------------------------


def sym3_tf_projector(m):
    """Matrix (m^3 x m^3) of the orthogonal projection onto STF^3(R^m)."""
    n = m ** 3
    P = np.zeros((n, n))
    for col in range(n):
        T = np.zeros(n)
        T[col] = 1.0
        T = T.reshape(m, m, m)
        S = sum(T.transpose(p) for p in itertools.permutations(range(3))) / 6.0
        v = np.einsum("iik->k", S)  # Tr_12
        J = (np.einsum("ij,k->ijk", np.eye(m), v) + np.einsum("ik,j->ijk", np.eye(m), v)
             + np.einsum("jk,i->ijk", np.eye(m), v))
        F = S - J / (m + 2)
        P[:, col] = F.reshape(-1)
    return P


def stf3_basis(m):
    """Orthonormal basis of STF^3(R^m) as array (nX, m, m, m)."""
    P = sym3_tf_projector(m)
    ev, V = np.linalg.eigh(P)
    idx = np.where(ev > 0.5)[0]
    E = V[:, idx].T.reshape(len(idx), m, m, m)
    return E


def sym_index_pairs(m):
    return [(a, b) for a in range(m) for b in range(a, m)]


# ---------------------------------------------------------------------------
# basis enumeration
# ---------------------------------------------------------------------------


def _matchings(slots):
    """All partial matchings of a list of slots: yields (pairs, singles)."""
    slots = list(slots)
    if not slots:
        yield [], []
        return
    a = slots[0]
    rest = slots[1:]
    # a single
    for pr, sg in _matchings(rest):
        yield pr, [a] + sg
    # a paired with some b
    for i, b in enumerate(rest):
        rest2 = rest[:i] + rest[i + 1:]
        for pr, sg in _matchings(rest2):
            yield [(a, b)] + pr, sg


def scalar_monomials(m, max_pdeg, max_Adeg, kmax):
    """Multisets of ('s',k) (p-degree 2, A-degree k) and ('t',k) (k>=3)."""
    gens = [("s", k) for k in range(kmax + 1)] + [("t", k) for k in range(3, m + 1)]
    out = []

    def rec(i, cur, pdeg, adeg):
        if i == len(gens):
            out.append((tuple(cur), pdeg, adeg))
            return
        kind, k = gens[i]
        dp = 2 if kind == "s" else 0
        e = 0
        while True:
            if pdeg + e * dp > max_pdeg or adeg + e * k > max_Adeg:
                break
            if kind == "t" and k == 0:
                break
            rec(i + 1, cur + [gens[i]] * e, pdeg + e * dp, adeg + e * k)
            e += 1
            if dp == 0 and k == 0:
                break
    rec(0, [], 0, 0)
    return out


def enumerate_monos(m, rank, max_pdeg, max_gdeg, max_Adeg, g_parity, kmax=None):
    """All graph monomials of a given rank within degree bounds.

    g_parity: 0 -> even powers of g only, 1 -> odd powers only, None -> all.
    kmax: largest power of A on an edge (default m-1, by Cayley-Hamilton).
    """
    if kmax is None:
        kmax = m - 1
    res = []
    scal = scalar_monomials(m, max_pdeg, max_Adeg, kmax)
    for pairs, singles in _matchings(range(rank)):
        for kp in itertools.product(range(kmax + 1), repeat=len(pairs)):
            for kl in itertools.product(range(kmax + 1), repeat=len(singles)):
                pdeg0 = len(singles)
                adeg0 = sum(kp) + sum(kl)
                if pdeg0 > max_pdeg or adeg0 > max_Adeg:
                    continue
                for sc, pd, ad in scal:
                    if pdeg0 + pd > max_pdeg or adeg0 + ad > max_Adeg:
                        continue
                    for h in range(max_gdeg + 1):
                        if g_parity is not None and h % 2 != g_parity:
                            continue
                        res.append(Mono(rank, h, sc,
                                        tuple((a, b, k) for (a, b), k in zip(pairs, kp)),
                                        tuple((a, k) for a, k in zip(singles, kl))))
    return res


# ---------------------------------------------------------------------------
# batched evaluation
# ---------------------------------------------------------------------------


class Ctx:
    """Precomputed powers for a batch of data points (possibly complex)."""

    def __init__(self, A, p, g, kmax):
        self.A, self.p, self.g = A, p, g
        N, m, _ = A.shape
        self.m = m
        I = np.broadcast_to(np.eye(m, dtype=A.dtype), (N, m, m))
        pw = [np.array(I)]
        for _ in range(max(kmax, m)):
            pw.append(np.einsum("nij,njk->nik", pw[-1], A))
        self.pw = pw
        self.vec = [np.einsum("nij,nj->ni", P, p) for P in pw]
        self._s = {}
        self._t = {}

    def s(self, k):
        if k not in self._s:
            self._s[k] = np.einsum("ni,ni->n", self.p, self.vec[k])
        return self._s[k]

    def t(self, k):
        if k not in self._t:
            self._t[k] = np.einsum("nii->n", self.pw[k])
        return self._t[k]


_LET = "abcdefghij"


def eval_mono(mono, ctx):
    """Value of a monomial: array (N,) + (m,)*rank."""
    N = ctx.A.shape[0]
    sc = ctx.g ** mono.h if mono.h else np.ones(N, dtype=ctx.A.dtype)
    for kind, k in mono.scal:
        sc = sc * (ctx.s(k) if kind == "s" else ctx.t(k))
    if mono.rank == 0:
        return sc
    ops, subs = [sc], ["n"]
    for a, b, k in mono.pairs:
        ops.append(ctx.pw[k])
        subs.append("n" + _LET[a] + _LET[b])
    for a, k in mono.legs:
        ops.append(ctx.vec[k])
        subs.append("n" + _LET[a])
    out = "n" + _LET[: mono.rank]
    return np.einsum(",".join(subs) + "->" + out, *ops)


def eval_combo(combo, ctx):
    """combo: list of (coef, Mono) of equal rank."""
    tot = None
    for c, mono in combo:
        v = c * eval_mono(mono, ctx)
        tot = v if tot is None else tot + v
    return tot


class Jet:
    """Value and first derivatives (complex step) of tensor functions at points."""

    H = 1e-30

    def __init__(self, A, p, g, kmax):
        N, m, _ = A.shape
        self.m, self.N = m, N
        self.idx = sym_index_pairs(m)
        Ac, pc, gc = A.astype(complex), p.astype(complex), g.astype(complex)
        self.base = Ctx(A, p, g, kmax)
        self.dA = []
        for a, b in self.idx:
            E = np.zeros((m, m))
            E[a, b] = E[b, a] = 1.0
            self.dA.append(Ctx(Ac + 1j * self.H * E, pc, gc, kmax))
        self.dp = []
        for i in range(m):
            e = np.zeros(m)
            e[i] = 1.0
            self.dp.append(Ctx(Ac, pc + 1j * self.H * e, gc, kmax))
        self.dg = Ctx(Ac, pc, gc + 1j * self.H, kmax)

    def jet(self, f):
        """f: callable ctx -> array.  Returns (val, dA (N,nsym,...), dp (N,m,...), dg)."""
        val = f(self.base)
        dA = np.stack([f(c).imag / self.H for c in self.dA], axis=1)
        dp = np.stack([f(c).imag / self.H for c in self.dp], axis=1)
        dg = f(self.dg).imag / self.H
        return val, dA, dp, dg


# ---------------------------------------------------------------------------
# assembly of interior quadratic forms and boundary values
# ---------------------------------------------------------------------------


class Layout:
    def __init__(self, m):
        self.m = m
        self.E = stf3_basis(m)
        self.nX = self.E.shape[0]
        self.V = 2 + m + self.nX
        V = self.V
        self.wv = np.zeros(V); self.wv[0] = 1
        self.zv = np.zeros(V); self.zv[1] = 1
        self.lv = np.zeros((m, V))
        for i in range(m):
            self.lv[i, 2 + i] = 1
        self.Xv = np.zeros((m, m, m, V))
        for s in range(self.nX):
            self.Xv[..., 2 + m + s] = self.E[s]
        # the positive form E_zl = z^2 + |l|^2
        self.Ezl = np.zeros((V, V))
        self.Ezl[1, 1] = 1
        for i in range(m):
            self.Ezl[2 + i, 2 + i] = 1


class InteriorAssembler:
    """Computes, at a batch of points, the quadratic form (N,V,V) contributed by
    one ansatz element of each family."""

    def __init__(self, layout, A, p, g, a, beta2, kmax):
        self.L = layout
        m = layout.m
        self.m, self.a, self.beta2 = m, a, beta2
        self.A, self.p, self.g = A, p, g
        N = A.shape[0]
        self.N = N
        self.jet = Jet(A, p, g, kmax)
        L = layout
        self.qv = np.einsum("lijv,nij->nlv", L.Xv, A)
        dA_full = L.Xv[None] - self.qv[:, :, None, None, :] * A[:, None, :, :, None]
        self.dA = np.stack([dA_full[:, :, a_, b_, :] for a_, b_ in self.jet.idx], axis=2)  # (N,l,nsym,V)
        eye = np.eye(m)
        self.dp = (A[:, :, :, None] * L.wv[None, None, None, :]
                   - g[:, None, None, None] * eye[None, :, :, None] * L.zv[None, None, None, :])  # (N,l,i,V)
        self.dg = p[:, :, None] * L.zv[None, None, :]  # (N,l,V)

    def D(self, f):
        """Return (val, DF) with DF[..., l, V] the derivation applied to f."""
        val, dA, dp, dg = self.jet.jet(f)
        r = val.ndim - 1
        sl = _LET[:r]
        DF = (np.einsum(f"ns{sl},nlsv->n{sl}lv", dA, self.dA)
              + np.einsum(f"ni{sl},nliv->n{sl}lv", dp, self.dp)
              + np.einsum(f"n{sl},nlv->n{sl}lv", dg, self.dg))
        return val, DF

    @staticmethod
    def _sym(B):
        return 0.5 * (B + np.swapaxes(B, -1, -2))

    def form_f(self, f):
        L, a = self.L, self.a
        val, DF = self.D(f)  # val (N,), DF (N,l,V)
        Q = -self.beta2 * val[:, None, None] * np.outer(L.zv, L.zv)[None]
        Q = Q + val[:, None, None] * np.einsum("lu,lv->uv", L.lv, L.lv)[None]
        lin = DF + 2 * a * self.qv * val[:, None, None]  # (N,l,V)
        Q = Q - self._sym(np.einsum("nlu,lv->nuv", lin, L.lv))
        return Q

    def form_U(self, f):
        L, a, m = self.L, self.a, self.m
        val, DF = self.D(f)  # val (N,j,k), DF (N,j,k,l,V)
        zz = m * np.einsum("njk,njk->n", val, self.A)
        Q = zz[:, None, None] * np.outer(L.zv, L.zv)[None]
        B = np.einsum("njkiu,ijkv->nuv", DF, L.Xv)
        B = B + (2 * a - 1) * np.einsum("niu,njk,ijkv->nuv", self.qv, val, L.Xv)
        return Q + self._sym(B)

    def form_K(self, f):
        """f returns K (rank 4); C = K - K^(12) is formed here."""
        L, a = self.L, self.a

        def fc(ctx):
            K = f(ctx)
            return K - np.swapaxes(K, 1, 2)
        val, DF = self.D(fc)  # val (N,l,i,j,k), DF (N,l,i,j,k,l',V)
        eye = np.eye(self.m)
        T = np.einsum("lj,nik->nlijk", eye, self.A) + np.einsum("lk,nij->nlijk", eye, self.A)
        zz = np.einsum("nlijk,nlijk->n", val, T)
        Q = zz[:, None, None] * np.outer(L.zv, L.zv)[None]
        DC = np.einsum("nlijklu->nijku", DF)
        B = np.einsum("nijku,ijkv->nuv", DC, L.Xv)
        B = B + (2 * a - 1) * np.einsum("nlu,nlijk,ijkv->nuv", self.qv, val, L.Xv)
        return Q + self._sym(B)

    def form_M(self, f):
        L, a = self.L, self.a
        val, DF = self.D(f)  # (N,l), (N,l,l',V)
        lin = np.einsum("nllu->nu", DF) + (2 * a + 1) * np.einsum("nlu,nl->nu", self.qv, val)
        return self._sym(np.einsum("nu,v->nuv", lin, L.wv))

    def form_P(self, f):
        L, a = self.L, self.a
        val, DF = self.D(f)
        lin = np.einsum("nllu->nu", DF) + 2 * a * np.einsum("nlu,nl->nu", self.qv, val)
        return self._sym(np.einsum("nu,v->nuv", lin, L.zv))

    def form(self, fam, f):
        return {"f": self.form_f, "U": self.form_U, "K": self.form_K,
                "M": self.form_M, "P": self.form_P}[fam](f)


class BoundaryAssembler:
    """Boundary polynomial S at points (A diagonal-or-not, p unit eigenvector,
    lam < 0, g = 0)."""

    def __init__(self, A, p, kmax):
        N, m, _ = A.shape
        self.m = m
        self.A, self.p = A, p
        self.lam = np.einsum("ni,nij,nj->n", p, A, p)
        self.ctx = Ctx(A, p, np.zeros(N), kmax)
        A2 = np.einsum("nij,njk->nik", A, A)
        S0 = self.lam[:, None, None] * A - A2
        self.S0pp = S0 + np.einsum("ni,nj->nij", p, p)
        self.V = (np.einsum("ni,njk->nijk", p, S0) + np.einsum("nj,nki->nijk", p, S0)
                  + np.einsum("nk,nij->nijk", p, S0) + np.einsum("ni,nj,nk->nijk", p, p, p))

    def value(self, fam, f):
        val = f(self.ctx)
        if fam == "f":
            return -self.lam * val
        if fam == "U":
            return np.einsum("njk,njk->n", val, self.S0pp)
        if fam == "K":
            C = val - np.swapaxes(val, 1, 2)
            return np.einsum("nlijk,nl,nijk->n", C, self.p, self.V)
        if fam == "M":
            return np.einsum("nl,nl->n", val, self.p)
        if fam == "P":
            return np.zeros(self.A.shape[0])  # P vanishes at g = 0 by construction
        raise ValueError(fam)


# ---------------------------------------------------------------------------
# sample points
# ---------------------------------------------------------------------------


def unit_stf_from_eigs(alpha):
    """Diagonal unit trace-free matrices from eigenvalue rows (N,m)."""
    al = alpha - alpha.mean(axis=1, keepdims=True)
    al = al / np.linalg.norm(al, axis=1, keepdims=True)
    N, m = al.shape
    A = np.zeros((N, m, m))
    for i in range(m):
        A[:, i, i] = al[:, i]
    return A


def eig_chamber(m, n, rng=None):
    """Sorted eigenvalue vectors of unit STF matrices covering the Weyl chamber."""
    if m == 2:
        return np.tile(np.array([[1.0, -1.0]]) / np.sqrt(2), (1, 1))
    if m == 3:
        phi = np.linspace(0, np.pi / 3, n)
        u = np.array([2, -1, -1]) / np.sqrt(6)
        v = np.array([0, 1, -1]) / np.sqrt(2)
        return np.cos(phi)[:, None] * u + np.sin(phi)[:, None] * v
    rng = rng or np.random.default_rng(0)
    al = rng.normal(size=(n, m))
    al -= al.mean(axis=1, keepdims=True)
    al /= np.linalg.norm(al, axis=1, keepdims=True)
    return -np.sort(-al, axis=1)


def ball_points(dim, n, rng, octant=True):
    """Points in the closed unit ball of R^dim: shells plus random fill."""
    pts = [np.zeros(dim)]
    radii = [0.3, 0.6, 0.85, 1.0]
    for r in radii:
        d = rng.normal(size=(n // (len(radii) + 1), dim))
        d /= np.linalg.norm(d, axis=1, keepdims=True)
        pts.extend(r * d)
    d = rng.normal(size=(n - len(pts), dim))
    d /= np.linalg.norm(d, axis=1, keepdims=True)
    rad = rng.uniform(size=(len(d), 1)) ** (1.0 / dim)
    pts.extend(rad * d)
    # coordinate axes and diagonals on the sphere
    for i in range(dim):
        e = np.zeros(dim); e[i] = 1
        pts.append(e)
    pts = np.array(pts)
    if octant:
        pts = np.abs(pts)
    return pts


def interior_samples(m, n_eig, n_ball, seed=0):
    rng = np.random.default_rng(seed)
    al = eig_chamber(m, n_eig, rng)
    B = ball_points(m + 1, n_ball, rng)  # (p, g) with p >= 0, g >= 0
    AA, PP, GG = [], [], []
    for row in al:
        A = unit_stf_from_eigs(row[None])[0]
        for b in B:
            AA.append(A); PP.append(b[:m]); GG.append(b[m])
    return np.array(AA), np.array(PP), np.array(GG)


def boundary_samples(m, n):
    """A = diag(x_1..x_{m-1}, lam), p = e_m, lam < 0 (including lam -> 0)."""
    if m == 2:
        A = np.diag([1.0, -1.0]) / np.sqrt(2)
        p = np.array([0.0, 1.0])
        return A[None], p[None]
    rng = np.random.default_rng(1)
    if m == 3:
        # x1 + x2 = s, x1 x2 = s^2 - 1/2, s in (0, sqrt(2/3)]
        s = np.linspace(0.0, np.sqrt(2 / 3), n)
        disc = np.maximum(s ** 2 - 4 * (s ** 2 - 0.5), 0)
        x1 = (s + np.sqrt(disc)) / 2
        x2 = (s - np.sqrt(disc)) / 2
        lam = -s
        al = np.stack([x1, x2, lam], axis=1)
    else:
        x = rng.normal(size=(n, m - 1))
        lam = -np.abs(x.sum(axis=1, keepdims=True))
        al = np.concatenate([x, lam], axis=1)
        al -= 0  # trace: lam = -sum x
        al[:, -1] = -al[:, :-1].sum(axis=1)
        al = al[al[:, -1] < 0]
        al /= np.linalg.norm(al, axis=1, keepdims=True)
    N = al.shape[0]
    A = np.zeros((N, m, m))
    for i in range(m):
        A[:, i, i] = al[:, i]
    p = np.zeros((N, m)); p[:, -1] = 1
    return A, p
