/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The universal algebraic certificate

All tensors are over `ℝ⁵`, written as plain functions `Fin 5 → … → ℝ`, with explicit index sums;
squared norms are sums of squares of entries (`sq1`, `sq2`), never the sup norm of the function
space. Data: `A` a symmetric trace-free matrix with `|A|² = 1`, `X` a symmetric trace-free
three-tensor, `p, ℓ ∈ ℝ⁵`, `g, w, z ∈ ℝ` (with no sign conditions on `w, z`), and
`q_l = X_{lij} A_{ij}`. The derivation `D_l` acts on functions of `(A, p, g)` by
`D_l A_{ij} = X_{lij} - q_l A_{ij}`, `D_l p_i = w A_{li} - g z δ_{li}`, `D_l g = z p_l`.

`CertificateStatement` asserts that there are smooth coefficient maps `f, U_{jk}, K_{lijk}, M_l,
P_l` of `(A, p, g)`, orthogonally equivariant with `f` invariant, `U, K` even in `p`, `P = 0` at
`g = 0`, such that with `C_{lijk} = K_{lijk} - K_{iljk}` and `G_{lijk} = δ_{li} U_{jk} + C_{lijk}`,

  `𝓘 = z²[5 U_{jk}A_{jk} + C_{lijk}(δ_{lj}A_{ik} + δ_{lk}A_{ij}) - 4f]`
    `+ [D_l G_{lijk} + (2a-1) q_l G_{lijk}] X_{ijk} + w [D_l M_l + (2a+1) q_l M_l]`
    `+ z [D_l P_l + 2a q_l P_l] + f|ℓ|² - (D_l f + 2a q_l f) ℓ_l ≥ ε* (z² + |ℓ|²)`

whenever `g² + |p|² ≤ 1`, `f ≥ ε*` there, and on the boundary data (`g = 0`, `|p| = 1`,
`Ap = λp`, `λ < 0`, `S₀ = λA - A²`,
`V_{ijk} = p_i S₀_{jk} + p_j S₀_{ki} + p_k S₀_{ij} + p_i p_j p_k`)

  `𝓢 = -λ f + U_{jk}(S₀ + p ⊗ p)_{jk} + C_{lijk} p_l V_{ijk} + p_l M_l ≥ δ*`.

The constants are `a = 29/50`, `ε* = 438907/12000000`, `δ* = 6984137359/31250000000`.

## Differences from the source

* The 2026-09-24 version states the certificate with explicit rational tensor polynomials (its
  Table I). We state it existentially over smooth coefficient maps with the properties above; the
  tabulated polynomials are the witness. Equivariance, evenness and `P = 0` at `g = 0` are
  required on the whole space.
* The 2026-09-24 version defines `D_l` as a formal derivation on tensor polynomials in
  `A, p, g, δ`. We use the directional derivative `fderiv` along the generator vector
  `(D_l A, D_l p, D_l g)`; on polynomial maps the two agree.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace OnePhaseDimension

/-- Vectors in `ℝ⁵`. -/
abbrev Ten1 := Fin 5 → ℝ
/-- Two-tensors on `ℝ⁵`. -/
abbrev Ten2 := Fin 5 → Fin 5 → ℝ
/-- Three-tensors on `ℝ⁵`. -/
abbrev Ten3 := Fin 5 → Fin 5 → Fin 5 → ℝ
/-- Four-tensors on `ℝ⁵`. -/
abbrev Ten4 := Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ

/-- The Kronecker delta. -/
def kron (i j : Fin 5) : ℝ := if i = j then 1 else 0

/-- The exponent `a = 29/50`. -/
def aExp : ℝ := 29 / 50
/-- The interior constant `ε* = 438907/12000000`. -/
def εStar : ℝ := 438907 / 12000000
/-- The boundary constant `δ* = 6984137359/31250000000`. -/
def δStar : ℝ := 6984137359 / 31250000000

theorem εStar_pos : 0 < εStar := by norm_num [εStar]

theorem δStar_pos : 0 < δStar := by norm_num [δStar]

theorem one_half_lt_aExp : 1 / 2 < aExp := by norm_num [aExp]

theorem aExp_lt_one : aExp < 1 := by norm_num [aExp]

/-- Squared norm of a vector. -/
def sq1 (p : Ten1) : ℝ := ∑ i, p i ^ 2
/-- Squared norm of a two-tensor, `|A|² = ∑ᵢⱼ A_{ij}²`. -/
def sq2 (A : Ten2) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- A symmetric two-tensor. -/
def IsSymm2 (A : Ten2) : Prop := ∀ i j, A i j = A j i
/-- A symmetric trace-free two-tensor. -/
def IsSTF2 (A : Ten2) : Prop := IsSymm2 A ∧ ∑ i, A i i = 0
/-- A fully symmetric trace-free three-tensor. -/
def IsSTF3 (X : Ten3) : Prop :=
  (∀ i j k, X i j k = X j i k) ∧ (∀ i j k, X i j k = X i k j) ∧ ∀ k, ∑ i, X i i k = 0

/-- `O` is orthogonal: `Oᵀ O = 1`. -/
def IsOrth5 (O : Ten2) : Prop := ∀ i j, ∑ k, O k i * O k j = kron i j

/-- Action of `O` on vectors. -/
def act1 (O : Ten2) (p : Ten1) : Ten1 := fun i ↦ ∑ a, O i a * p a
/-- Action of `O` on two-tensors, `O A Oᵀ`. -/
def act2 (O : Ten2) (A : Ten2) : Ten2 := fun i j ↦ ∑ a, ∑ b, O i a * O j b * A a b
/-- Action of `O` on four-tensors. -/
def act4 (O : Ten2) (K : Ten4) : Ten4 := fun i j k l ↦
  ∑ a, ∑ b, ∑ c, ∑ e, O i a * O j b * O k c * O l e * K a b c e

/-- The certificate data: functions of `(A, p, g)`. -/
structure Coeffs where
  /-- The scalar coefficient `f`. -/
  f : Ten2 × Ten1 × ℝ → ℝ
  /-- The two-tensor coefficient `U_{jk}`. -/
  U : Ten2 × Ten1 × ℝ → Ten2
  /-- The four-tensor coefficient `K_{lijk}`. -/
  K : Ten2 × Ten1 × ℝ → Ten4
  /-- The vector coefficient `M_l`. -/
  M : Ten2 × Ten1 × ℝ → Ten1
  /-- The vector coefficient `P_l`. -/
  P : Ten2 × Ten1 × ℝ → Ten1

/-- `q_l = X_{lij} A_{ij}`. -/
def qVec (X : Ten3) (A : Ten2) (l : Fin 5) : ℝ := ∑ i, ∑ j, X l i j * A i j

/-- The generator of `D_l` at `(A, p, g)`:
`D_l A_{ij} = X_{lij} − q_l A_{ij}`, `D_l p_i = w A_{li} − g z δ_{li}`, `D_l g = z p_l`. -/
def gen (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (l : Fin 5) : Ten2 × Ten1 × ℝ :=
  (fun i j ↦ X l i j - qVec X A l * A i j,
    fun i ↦ w * A l i - g * z * kron l i,
    z * p l)

/-- `D_l F` at `(A, p, g)`: the derivative of `F` along the generator. -/
def Dl {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Ten2 × Ten1 × ℝ → W)
    (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (l : Fin 5) : W :=
  fderiv ℝ F (A, p, g) (gen A X p g w z l)

namespace Coeffs

variable (c : Coeffs)

/-- `C_{lijk} = K_{lijk} − K_{iljk}`. -/
def C (x : Ten2 × Ten1 × ℝ) (l i j k : Fin 5) : ℝ := c.K x l i j k - c.K x i l j k

/-- `G_{lijk} = δ_{li} U_{jk} + C_{lijk}`. -/
def G (x : Ten2 × Ten1 × ℝ) (l i j k : Fin 5) : ℝ := kron l i * c.U x j k + c.C x l i j k

/-- `z² [5 U_{jk} A_{jk} + C_{lijk}(δ_{lj} A_{ik} + δ_{lk} A_{ij}) − 4 f]`. -/
def termZ (A : Ten2) (p : Ten1) (g z : ℝ) : ℝ :=
  z ^ 2 * (5 * ∑ j, ∑ k, c.U (A, p, g) j k * A j k
    + ∑ l, ∑ i, ∑ j, ∑ k, c.C (A, p, g) l i j k * (kron l j * A i k + kron l k * A i j)
    - 4 * c.f (A, p, g))

/-- `[D_l G_{lijk} + (2a − 1) q_l G_{lijk}] X_{ijk}`. -/
def termG (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) : ℝ :=
  ∑ l, ∑ i, ∑ j, ∑ k,
    (Dl (fun y ↦ c.G y l i j k) A X p g w z l
      + (2 * aExp - 1) * qVec X A l * c.G (A, p, g) l i j k) * X i j k

/-- `w [D_l M_l + (2a + 1) q_l M_l]`. -/
def termM (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) : ℝ :=
  w * ∑ l, (Dl (fun y ↦ c.M y l) A X p g w z l + (2 * aExp + 1) * qVec X A l * c.M (A, p, g) l)

/-- `z [D_l P_l + 2a q_l P_l]`. -/
def termP (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) : ℝ :=
  z * ∑ l, (Dl (fun y ↦ c.P y l) A X p g w z l + 2 * aExp * qVec X A l * c.P (A, p, g) l)

/-- `f |ℓ|² − (D_l f + 2a q_l f) ℓ_l`. -/
def termF (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (ℓ : Ten1) : ℝ :=
  c.f (A, p, g) * sq1 ℓ
    - ∑ l, (Dl c.f A X p g w z l + 2 * aExp * qVec X A l * c.f (A, p, g)) * ℓ l

/-- The interior expression `𝓘`. -/
def interiorExpr (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (ℓ : Ten1) : ℝ :=
  c.termZ A p g z + c.termG A X p g w z + c.termM A X p g w z + c.termP A X p g w z
    + c.termF A X p g w z ℓ

/-- `S₀ = λ A − A²`. -/
def bdryS0 (A : Ten2) (lam : ℝ) : Ten2 := fun i j ↦ lam * A i j - ∑ k, A i k * A k j

/-- `V_{ijk} = p_i S₀_{jk} + p_j S₀_{ki} + p_k S₀_{ij} + p_i p_j p_k`. -/
def bdryV (A : Ten2) (p : Ten1) (lam : ℝ) : Ten3 := fun i j k ↦
  p i * bdryS0 A lam j k + p j * bdryS0 A lam k i + p k * bdryS0 A lam i j + p i * p j * p k

/-- The boundary expression `𝓢` at `g = 0`. -/
def boundaryExpr (A : Ten2) (p : Ten1) (lam : ℝ) : ℝ :=
  -lam * c.f (A, p, 0)
    + ∑ j, ∑ k, c.U (A, p, 0) j k * (bdryS0 A lam j k + p j * p k)
    + ∑ l, ∑ i, ∑ j, ∑ k, c.C (A, p, 0) l i j k * p l * bdryV A p lam i j k
    + ∑ l, p l * c.M (A, p, 0) l

end Coeffs

/-- The certificate properties. -/
structure CertificateHolds (c : Coeffs) : Prop where
  /-- `f` is smooth. -/
  smooth_f : ContDiff ℝ ∞ c.f
  /-- `U` is smooth. -/
  smooth_U : ContDiff ℝ ∞ c.U
  /-- `K` is smooth. -/
  smooth_K : ContDiff ℝ ∞ c.K
  /-- `M` is smooth. -/
  smooth_M : ContDiff ℝ ∞ c.M
  /-- `P` is smooth. -/
  smooth_P : ContDiff ℝ ∞ c.P
  /-- `f` is orthogonally invariant. -/
  equiv_f : ∀ O, IsOrth5 O → ∀ A p g, c.f (act2 O A, act1 O p, g) = c.f (A, p, g)
  /-- `U` is orthogonally equivariant. -/
  equiv_U : ∀ O, IsOrth5 O → ∀ A p g, c.U (act2 O A, act1 O p, g) = act2 O (c.U (A, p, g))
  /-- `K` is orthogonally equivariant. -/
  equiv_K : ∀ O, IsOrth5 O → ∀ A p g, c.K (act2 O A, act1 O p, g) = act4 O (c.K (A, p, g))
  /-- `M` is orthogonally equivariant. -/
  equiv_M : ∀ O, IsOrth5 O → ∀ A p g, c.M (act2 O A, act1 O p, g) = act1 O (c.M (A, p, g))
  /-- `P` is orthogonally equivariant. -/
  equiv_P : ∀ O, IsOrth5 O → ∀ A p g, c.P (act2 O A, act1 O p, g) = act1 O (c.P (A, p, g))
  /-- `U` is even in `p`. -/
  even_U : ∀ A p g, c.U (A, -p, g) = c.U (A, p, g)
  /-- `K` is even in `p`. -/
  even_K : ∀ A p g, c.K (A, -p, g) = c.K (A, p, g)
  /-- `P = 0` when `g = 0`. -/
  P_g_zero : ∀ A p, c.P (A, p, 0) = 0
  /-- The interior inequality `𝓘 ≥ ε* (z² + |ℓ|²)`. -/
  interior : ∀ A X p g w z ℓ, IsSTF2 A → sq2 A = 1 → IsSTF3 X → g ^ 2 + sq1 p ≤ 1 →
    εStar * (z ^ 2 + sq1 ℓ) ≤ c.interiorExpr A X p g w z ℓ
  /-- The lower bound `f ≥ ε*`. -/
  f_ge : ∀ A p g, IsSTF2 A → sq2 A = 1 → g ^ 2 + sq1 p ≤ 1 → εStar ≤ c.f (A, p, g)
  /-- The boundary inequality `𝓢 ≥ δ*` for every eigenpair `Ap = λp`, `|p| = 1`, `λ < 0`. -/
  boundary : ∀ A p (lam : ℝ), IsSTF2 A → sq2 A = 1 → sq1 p = 1 →
    (∀ i, ∑ j, A i j * p j = lam * p i) → lam < 0 → δStar ≤ c.boundaryExpr A p lam

/-- The universal certificate: some smooth coefficient data satisfies all the properties. -/
def CertificateStatement : Prop := ∃ c : Coeffs, CertificateHolds c

end OnePhaseDimension
