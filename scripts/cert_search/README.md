# cert_search: universal certificates in low dimension

This directory contains the search for, and an exact verification of, the universal
algebraic certificates that run the preprint's flux/stability argument (OpenAI, "The
critical dimension for one-phase Bernoulli minimizers", 2026) in tangent dimension
m = d − 1 ∈ {2, 3}, that is, for minimizers in ℝ³ and ℝ⁴. The preprint gives such a
certificate for m = 5 (its Table I); the ones here are new and much smaller.

**Role in the formalization.** The correctness of the Lean development does not depend on
this code. For m = 3 the certificate is exported to Lean data (`export_lean.py`) and every
identity and bound is re-checked there by kernel computation; for m = 2 the Lean proof is a
short hand proof. The Python code documents where the certificates came from and gives an
independent exact check outside Lean.

## Results

| m (d) | certificate | a | ε | δ | exact check |
|---|---|---|---|---|---|
| 2 (3) | `certs/m2_cert.json`: f = 1, U = (2/5)A, K = M = P = 0 | 3/5 | 1/10 | 1/10 | ACCEPTED |
| 3 (4) | `certs/m3a2950_cert.json` (**used by Lean**): f = 1, U with 8 terms (p-degree ≤ 2, A-degree ≤ 2), M = (39/500)p + (69/500)Ap, K = P = 0 | 29/50 | 1/50 | 1/100 | ACCEPTED |
| 3 (4) | `certs/m3_cert.json` (first certificate found): same ansatz, M = (39/1000)p + (141/1000)Ap | 11/20 | 1/50 | 1/100 | ACCEPTED |

Notes on the table.

- **m = 3.** The two m = 3 certificates use the same 11-term ansatz and differ only in the
  exponent a and the coefficients. The first search was run at a = 11/20. It was then
  repeated at a = 29/50, the exponent of the preprint, so that the rest of the argument
  (where a enters) can be reused unchanged in every dimension. The Lean data in
  `OnePhaseDimension/LowDim/SOS/Data/` is generated from `certs/m3a2950_cert.json`, whose
  coefficients are
  U = (197/1000) p⊗p − (27/200) p⊗Ap + (429/1000) Ap⊗Ap
      + (527/1000 − (173/500) p·Ap − (1/1000)|p|²) A + (49/250 − (17/40)|p|²) A².
  `certs/m3_cert.json` is kept as a second, independent example.
- **m = 2.** The plain choice U = cA works for every a ∈ (1/2, 1) as long as
  a/2 < c < 1/2. This is a short hand computation: in two dimensions |q|² = |X|²/2,
  completing the square in ℓ leaves (ca − a²/(2(1−ε)))|X|², and on the boundary
  tr A³ = 0, so 𝓢 = (1 − 2c)/√2. The JSON certificate is at a = 3/5; the Lean proof
  (`OnePhaseDimension/LowDim/CertificateTwo.lean`) is this hand proof at a = 29/50.
- In both dimensions the scalar is the plain power h = w^a. Neither K nor P is needed. For
  m = 3 the plain choice U = cA provably fails (the interior needs 3c > 1, the boundary
  needs c ≤ 2/7), and the dependence of U on p = ∇g, together with a nonzero M, repairs it.

## Conventions

Notation follows the preprint, with 5 replaced by m. On a spherical domain Ω ⊂ Sᵐ,
g satisfies Δg = −mg, p = ∇g, T = ∇²g + g·Id, B = ∇T and w = |T|.

**Data.** A = T/w is a symmetric trace-free m × m matrix with |A| = 1; p ∈ ℝᵐ; g ∈ ℝ;
and χ = 1 − |p|² − g² ≥ 0.

**Free variables.** v = (w, z, ℓ₀, …, ℓ_{m−1}, ξ₀, …, ξ_{nX−1}), where
X = B/w = Σ ξ_s E_s for a basis E_s of the symmetric trace-free 3-tensors STF³(ℝᵐ)
(nX = C(m+2, 3) − m, so V = 6 coordinates for m = 2 and V = 12 for m = 3), and
q_l = X_lij A_ij.

**Derivation.** D_l A_ij = X_lij − q_l A_ij, D_l p_i = w A_li − g z δ_li and
D_l g = z p_l. It satisfies D_l(tr A) = 0 and D_l|A|² = 0.

**Ansatz.** The certificate consists of five tensor fields of (A, p, g): a scalar f, a
symmetric 2-tensor U (slots (j,k)), a 4-tensor K (slots (l,i,j,k)), and vectors M and P
(slot (l)). From them, C = K − K^(12) and G_lijk = δ_li U_jk + C_lijk, as in the preprint.
The flux field is Z_l = w^{2a}(G_lijk X_ijk + w M_l + P_l) and h = w^a √f.

**Interior polynomial.** With β² = ((m−1)/2)²,

    𝓘 = z² [ m U:A + C_lijk (δ_lj A_ik + δ_lk A_ij) − β² f ]
        + [ D_l G_lijk + (2a−1) q_l G_lijk ] X_ijk
        + w [ D_l M_l + (2a+1) q_l M_l ] + z [ D_l P_l + 2a q_l P_l ]
        + f |ℓ|² − (D_l f + 2a q_l f) ℓ_l .

It is a quadratic form Q in v, with coefficients polynomial in (A, p, g). The interior
condition is 𝓘 ≥ ε(z² + |ℓ|²) for all unit A, all v and all (p, g) with χ ≥ 0.

**Boundary polynomial.** At g = 0, |p| = 1 and Ap = λp with λ < 0,

    𝓢 = −λ f + U:(S₀ + p⊗p) + C_lijk p_l V_ijk + p·M ,

as in the preprint (P vanishes at g = 0 and U, K are even in p). The boundary condition is
𝓢 ≥ δ. After a rotation, p = e_m and A = diag(x₁, …, x_{m−1}, λ) with λ = −Σx.

**Exponent.** 1/2 < a < 1.

**Graph monomials.** The fields are linear combinations of O(m)-equivariant monomials

    g^h · Π (p·A^k p) · Π tr A^k · Π_pairs (A^k)_ab · Π_legs (A^k p)_a ,

in which every free slot occurs exactly once among the pairs and legs. No Levi-Civita
tensor is used. By Cayley–Hamilton, k ≤ m − 1. In the code a monomial is
`Mono(rank, h, scal, pairs, legs)`, with `scal` a multiset of `('s', k)` = p·A^k p and
`('t', k)` = tr A^k, `pairs` a tuple of `(a, b, k)` with a < b, and `legs` a tuple of
`(a, k)`.

**Parity.** Without loss of generality (by averaging), f, U, K, M are even in g and P is odd
in g; U and K are even in p and M, P are odd in p (this follows from −I ∈ O(m)). The search
imposes both.

## Certificate format

`certs/*_cert.json`. Every number is an exact rational written as a string.

- **Header:** `m`, `a`, `eps`, `delta`, and a free-text `comment`.
- **`terms`:** a list of objects `{F, coef, h, scal, pairs, legs}` with F ∈ {f, U, K, M, P}.
  The value of a term is

      coef · g^h · Π_{(s,k) ∈ scal} p·A^k p · Π_{(t,k) ∈ scal} tr A^k
           · Π_{(a,b,k) ∈ pairs} (A^k)_ab · Π_{(a,k) ∈ legs} (A^k p)_a ,

  with free slots 0, …, r−1, where r = 0, 2, 4, 1, 1 for f, U, K, M, P, and slot orders
  (), (j,k), (l,i,j,k), (l), (l).
- **`interior`:**
  - m = 2: `{"method": "constant"}`.
  - m = 3: `{"method": "sos", "eta": ..., "blocks": [...]}` (plus informational fields
    from the fit). Each block is `{mult, basis, gram}` with `mult` ∈ {"one", "chi"}; each
    `basis` entry `[[e_α0, e_α1, e_p0, e_p1, e_p2, e_g], μ]` stands for the monomial
    α₀^{e_α0} α₁^{e_α1} p₀^{e_p0} p₁^{e_p1} p₂^{e_p2} g^{e_g} times the coordinate v_μ;
    `gram` is a symmetric rational matrix. The claim is

        Q − εE − ηI = Σ_k B_kᵀ G_k B_k + χ Σ_k B′_kᵀ G′_k B′_k + R   (mod h)

    at A = diag(α₀, α₁, −α₀−α₁), where E = z² + |ℓ|², I = |v|²,
    h = α₀² + α₁² + (α₀+α₁)² − 1, the blocks with `mult` = "chi" are multiplied by χ,
    and the remainder R is small enough that ‖R‖ < η on the domain.
- **Coordinates.** v is ordered (w, z, ℓ₀, …, ℓ_{m−1}, ξ₀, …, ξ_{nX−1}), and ξ refers to
  the rational STF³ basis produced by `exact_check.stf3_rational_basis(m)`. That basis is
  deterministic (parity classes in sorted order, sympy nullspace vectors with denominators
  cleared), and the Gram data are tied to it.

**Why diagonal A suffices.** Each term is a full contraction of copies of δ, A and p with
free slots, so F(OAOᵀ, Op, g) = O^{⊗r} F(A, p, g) for O ∈ O(m), and D_l is equivariant.
Hence 𝓘 at (A, p, g, v) equals 𝓘 at (OᵀAO, Oᵀp, g, Oᵀ·v), and one may take A diagonal.
`crosscheck.py` confirms this for the implementation by an exact spot check.

## Files

| file | role |
|---|---|
| `engine.py` | Numeric engine for general m. It enumerates O(m)-equivariant graph monomials, evaluates them in batches with complex-step derivatives, and assembles the interior quadratic form 𝓘 in v and the boundary value 𝓢. Used for the search only. |
| `search.py` | Sampled-SDP search with a cutting-plane loop: solve on an active set of sample points, validate on a dense grid, add the worst points. Calls Clarabel directly. The unknowns are the ansatz coefficients; it maximizes t subject to Q − t(z² + \|ℓ\|²) − ηI ⪰ 0 at the samples and 𝓢 ≥ t, normalized by mean f = 1. Samples use the reduced domain: A diagonal with sorted eigenvalues, p in the closed positive octant, g ≥ 0, \|p\|² + g² ≤ 1. |
| `scan.py` | Batch runs of `search.run` over ansatz specs at a fixed exponent a. |
| `sos_fit.py` | m = 3 only. Rounds a search result to rationals (denominator 1000) and solves the Putinar/SOS problem numerically for Q − εE − ηI, with Gram matrices block-diagonal by sign-flip characters. Writes the certificate JSON with rational Gram blocks. |
| `exact_check.py` | **Exact checker.** It does not import `engine`, `search` or `sos_fit` and trusts no floating-point output. It rebuilds 𝓘 and 𝓢 from the certificate terms in sympy polynomial rings over ℚ, with a general symmetric A and its own chain rule for D_l, then runs the checks listed below. |
| `crosscheck.py` | Cross-checks the exact checker: exact 𝓘 agrees with the numeric engine at random non-diagonal points; exact O(m)-equivariance under a rational rotation; the row U = A gives m z² + \|X\|² + (2a−2)\|q\|²; perturbed certificates (negative controls) must be rejected. |
| `selftest.py` | Engine self-tests: the row U = A for m = 2, …, 5, and a regression against the preprint's m = 5 certificate assembled by the generic-m code (β² = 4). |
| `paper_table1_m5.py` | The preprint's Table I (coefficients of its m = 5 certificate), copied verbatim; used only by `selftest.py`. |
| `export_lean.py` | Exports the m = 3 interior SOS certificate as Lean data (`OnePhaseDimension/LowDim/SOS/Data/*.lean`), with integer Cholesky factors of the Gram matrices, the exact remainder and the multiplier of h; re-checks the exported identity exactly. |
| `boundary_reduce.py` | Reduces the m = 3 boundary polynomial of `m3a2950_cert.json` at diagonal A to a quartic in s = −λ (Gröbner basis over ℚ); the computation behind the Lean lemma `Gen.boundaryPolyThree_diag3`. |
| `boundary_sos.py` | Exploratory floating-point search (cvxpy) for a Positivstellensatz certificate of that quartic on 0 ≤ s ≤ √(2/3); rounded by hand to the certificate in `Gen.boundaryQuartic_ge`. |
| `certs/m2_cert.json` | m = 2 certificate. |
| `certs/m3a2950_cert.json` | m = 3 certificate at a = 29/50; the source of the Lean data. |
| `certs/m3a2950_search.json` | Search output it was rounded from. |
| `certs/m3_cert.json`, `certs/m3_search.json` | m = 3 certificate at a = 11/20 and its search output. |
| `transcripts/` | Outputs of `exact_check.py` (`exact_check_m2.txt`, `exact_check_m3.txt`, `exact_check_m3a2950.txt`), `crosscheck.py` (`crosscheck_m2.txt`, `crosscheck_m3.txt`) and `selftest.py` (`selftest.txt`). |
| `requirements.txt` | Pinned Python packages. |

### Checks in `exact_check.py`

- **Structure:** each term is an O(m)-equivariant graph monomial in which every free slot
  occurs once; U and K are even in p; every P term has positive g-degree; 1/2 < a < 1. The
  rational STF³ basis is checked to be symmetric, trace-free, of the right rank and
  linearly independent, and 𝓘 is checked to be homogeneous of degree 2 in v.
- **Interior, m = 2:** evaluate at the rational representative A = [[1/2,1/2],[1/2,−1/2]]
  of the single O(2)-orbit of unit symmetric trace-free matrices. The checker confirms
  that the form does not depend on (p, g) and runs an exact LDLᵀ of Q − εE.
- **Interior, m = 3:** evaluate at A = diag(α₀, α₁, −α₀−α₁) and reduce modulo h to the
  normal form of α₁-degree ≤ 1. It checks that
  - every Gram block is positive definite (exact LDLᵀ over ℚ);
  - the residual R = Q − εE − ηI − Σ BᵀGB − χ Σ B′ᵀG′B′ satisfies
    max-row-sum Σ|coeff| < η. On the domain |α_i|² ≤ 2/3 and |p_i|, |g| ≤ 1, so every
    monomial is at most 1 in absolute value and this bounds ‖R(x)‖_op; hence
    Q − εE ⪰ (η − ‖R‖)I ⪰ 0.
- **Boundary:** take A = diag(x₁, …, x_{m−1}, λ) with p = e_m and g = 0.
  - m = 2: x₁ = −λ = 1/√2, a single configuration; compute 𝓢 exactly in ℚ(√2).
  - m = 3: with s = −λ, x₁ + x₂ = s and x₁x₂ = s² − 1/2, and real roots force s² ≤ 2/3.
    The checker verifies that 𝓢 is symmetric in x₁, x₂, reduces it to a univariate
    polynomial in s, and uses exact Sturm counting to show that 𝓢 − δ has no root on
    [0, 0.8165] ⊃ [0, √(2/3)].

## How to reproduce

From the repository root:

```sh
python3 -m venv .venv && .venv/bin/pip install -r scripts/cert_search/requirements.txt
cd scripts/cert_search
PY=../../.venv/bin/python
$PY selftest.py                                   # a few seconds
$PY exact_check.py certs/m2_cert.json             # < 1 s
$PY exact_check.py certs/m3a2950_cert.json        # a few seconds
$PY exact_check.py certs/m3_cert.json             # a few seconds
$PY crosscheck.py certs/m2_cert.json
$PY crosscheck.py certs/m3a2950_cert.json         # under a minute
$PY crosscheck.py certs/m3_cert.json
```

Regenerating the certificates (the search and the fit are floating point; the exact check
is what matters):

```sh
# m = 3 at a = 29/50 (the certificate used by Lean)
$PY search.py --m 3 --a 0.58 --spec f:0,0,0 U:2,0,2 M:1,0,1 --n-ball 250 --n-eig 41 --eta 0.005 --out certs/m3a2950_search.json
$PY sos_fit.py certs/m3a2950_search.json --out certs/m3a2950_cert.json
# m = 3 at a = 11/20
$PY search.py --m 3 --a 0.55 --spec f:0,0,0 U:2,0,2 M:1,0,1 --n-ball 250 --n-eig 41 --eta 0.005 --out certs/m3_search.json
$PY sos_fit.py certs/m3_search.json --out certs/m3_cert.json
# m = 2 search
$PY search.py --m 2 --a 0.6 --spec f:0,0,0 U:0,0,1
```

A spec entry `F:pdeg,gdeg,Adeg` bounds the degree of family F in p, in g and in A.
Floating-point details make regeneration reproducible only up to small differences: a
re-run of the a = 29/50 search and fit gave the same rounded coefficients (with the slots
of one U term listed in the opposite order) and different Gram matrices, and the result
was again ACCEPTED by `exact_check.py`.

Export to Lean (overwrites `OnePhaseDimension/LowDim/SOS/Data/*.lean`; use `--dry` to
only run the exact re-check of the identity, or `--out DIR` to write elsewhere):

```sh
$PY export_lean.py certs/m3a2950_cert.json
```

The integer Cholesky factors are computed by rounding a floating-point Cholesky
factorization, so a re-export on another machine may differ from the committed Lean data
in the last unit of a few entries (and correspondingly in the remainder and multiplier).
Any such output is an equally valid input for Lean, which checks the identity and the
residual bound itself.

## Dependencies

- Python 3.14, in a virtual environment (`.venv/` is git-ignored).
- numpy, scipy, sympy, clarabel; cvxpy (with scs) is used only by `boundary_sos.py`.
  All versions are pinned in `requirements.txt`.
- The SDPs in `search.py` and `sos_fit.py` are solved by Clarabel through its Python API,
  with the PSD cones in svec form.
- Reference timings (m = 3): search about 35–105 s (4 cutting-plane rounds, about 350 active
  points, dense set 41 × 255); SOS fit about 30 s (19 blocks, 5180 Gram unknowns, 1440
  equations); exact check a few seconds.
