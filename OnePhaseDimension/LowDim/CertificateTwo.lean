/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import OnePhaseDimension.Statements.CertificateGen

/-!
# The algebraic certificate on `ℝ²`

We prove `Gen.CertificateStatement 2` with `ε = δ = 1/10` and the coefficients
`f = 1`, `U(A, p, g) = (2/5) A`, `K = M = P = 0`.

With `c = 2/5`, `a = 29/50` and `q_l = X_{lij} A_{ij}`, the interior expression is

  `𝓘 = z² (2c|A|² − 1/4) + c|X|² + (2a − 2) c |q|² + |ℓ|² − 2a q·ℓ`.

On `ℝ²`, write `A = [[α, β], [β, −α]]` and let `s = X₁₁₁`, `t = X₁₁₂`; the symmetric
trace-free three-tensor `X` is determined by `s, t`, and `|X|² = 4(s² + t²)`,
`|q|² = 4(α² + β²)(s² + t²)`. Hence `|X|² = 2|q|²` when `|A|² = 1`, and

  `𝓘 − ε(z² + |ℓ|²) = (9/20) z² + (9/10)|ℓ − (29/45) q|² + (203/2250)|q|²`.

On the boundary, `tr A³ = 0` and `p·Ap = λ`, so `𝓢 = −λ(1 − 2c) = −λ/5`; moreover
`A² = (1/2) I`, so `λ² = 1/2` and `𝓢 = √2/10 ≥ 1/10`.

## Main statements

* `Gen.certificateTwoCoeffs`: the coefficient data.
* `Gen.certificateTwoCoeffs_holds`: these coefficients satisfy the certificate properties with
  `ε = δ = 1/10`.
* `Gen.certificateStatement_two`: the certificate on `ℝ²`.
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Gen

/-- The certificate coefficients on `ℝ²`: `f = 1`, `U(A, p, g) = (2/5) A`, `K = M = P = 0`. -/
def certificateTwoCoeffs : Coeffs 2 where
  f := fun _ ↦ 1
  U := fun x ↦ (2 / 5 : ℝ) • x.1
  K := fun _ ↦ 0
  M := fun _ ↦ 0
  P := fun _ ↦ 0

namespace CertificateTwo

/-- The entry `(j, k)` of the matrix component, as a continuous linear map. -/
def entryCLM (j k : Fin 2) : (Ten2 2 × Ten1 2 × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Ten2 2) (Ten1 2 × ℝ)))

lemma Dl_G (A : Ten2 2) (X : Ten3 2) (p : Ten1 2) (g w z : ℝ) (l l' i j k : Fin 2) :
    Dl (fun y ↦ certificateTwoCoeffs.G y l i j k) A X p g w z l' =
      kron l i * (2 / 5) * (X l' j k - qVec X A l' * A j k) := by
  have hfun : (fun y ↦ certificateTwoCoeffs.G y l i j k) =
      ⇑((kron l i * (2 / 5)) • entryCLM j k) := by
    funext y
    simp [Coeffs.G, Coeffs.C, certificateTwoCoeffs, entryCLM]
    ring
  rw [Dl, hfun, ContinuousLinearMap.fderiv]
  simp [entryCLM, gen]

lemma Dl_f (A : Ten2 2) (X : Ten3 2) (p : Ten1 2) (g w z : ℝ) (l : Fin 2) :
    Dl certificateTwoCoeffs.f A X p g w z l = 0 := by
  simp [Dl, certificateTwoCoeffs]

lemma Dl_M (A : Ten2 2) (X : Ten3 2) (p : Ten1 2) (g w z : ℝ) (l : Fin 2) :
    Dl (fun y ↦ certificateTwoCoeffs.M y l) A X p g w z l = 0 := by
  simp [Dl, certificateTwoCoeffs]

lemma Dl_P (A : Ten2 2) (X : Ten3 2) (p : Ten1 2) (g w z : ℝ) (l : Fin 2) :
    Dl (fun y ↦ certificateTwoCoeffs.P y l) A X p g w z l = 0 := by
  simp [Dl, certificateTwoCoeffs]

/-- The interior inequality on `ℝ²`. -/
theorem interior (A : Ten2 2) (X : Ten3 2) (p : Ten1 2) (g w z : ℝ) (ℓ : Ten1 2)
    (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) :
    1 / 10 * (z ^ 2 + sq1 ℓ) ≤ certificateTwoCoeffs.interiorExpr A X p g w z ℓ := by
  obtain ⟨hAs, hAt⟩ := hA
  obtain ⟨hX1, hX2, hX3⟩ := hX
  have hA10 : A 1 0 = A 0 1 := hAs 1 0
  have hA11 : A 1 1 = -A 0 0 := by simp [Fin.sum_univ_two] at hAt; linarith
  have hX010 : X 0 1 0 = X 0 0 1 := hX2 0 1 0
  have hX100 : X 1 0 0 = X 0 0 1 := by rw [hX1 1 0 0, hX2 0 1 0]
  have h3 := hX3 0
  have h4 := hX3 1
  simp only [Fin.sum_univ_two] at h3 h4
  have hX110 : X 1 1 0 = -X 0 0 0 := by linarith
  have hX011 : X 0 1 1 = -X 0 0 0 := by rw [hX2 0 1 1, ← hX1 1 0 1, hX2 1 0 1]; linarith
  have hX101 : X 1 0 1 = -X 0 0 0 := by rw [hX2 1 0 1]; linarith
  have hX111 : X 1 1 1 = -X 0 0 1 := by linarith
  have hS : 2 * A 0 0 ^ 2 + 2 * A 0 1 ^ 2 = 1 := by
    simp only [sq2, Fin.sum_univ_two, hA10, hA11] at hA1
    linarith
  have e1 : (2 * A 0 0 ^ 2 + 2 * A 0 1 ^ 2 - 1) * z ^ 2 = 0 := by rw [hS]; ring
  have e2 : (2 * A 0 0 ^ 2 + 2 * A 0 1 ^ 2 - 1) * (X 0 0 0 ^ 2 + X 0 0 1 ^ 2) = 0 := by
    rw [hS]; ring
  simp only [Coeffs.interiorExpr, Coeffs.termZ, Coeffs.termG, Coeffs.termM, Coeffs.termP,
    Coeffs.termF, Dl_G, Dl_f, Dl_M, Dl_P]
  simp [Fin.sum_univ_two, Coeffs.G, Coeffs.C, certificateTwoCoeffs, kron, qVec, sq1,
    hardyConst, aExp, hA10, hA11, hX010, hX100, hX110, hX011, hX101, hX111]
  nlinarith [sq_nonneg (ℓ 0 - 29 / 45 * (2 * (X 0 0 0 * A 0 0 + X 0 0 1 * A 0 1))),
    sq_nonneg (ℓ 1 - 29 / 45 * (2 * (X 0 0 1 * A 0 0 - X 0 0 0 * A 0 1))), sq_nonneg z,
    sq_nonneg (X 0 0 0 * A 0 0 + X 0 0 1 * A 0 1), sq_nonneg (X 0 0 1 * A 0 0 - X 0 0 0 * A 0 1)]

/-- The boundary inequality on `ℝ²`. -/
theorem boundary (A : Ten2 2) (p : Ten1 2) (lam : ℝ) (hA : IsSTF2 A) (hA1 : sq2 A = 1)
    (hp : sq1 p = 1) (hev : ∀ i, ∑ j, A i j * p j = lam * p i) (hlam : lam < 0) :
    1 / 10 ≤ certificateTwoCoeffs.boundaryExpr A p lam := by
  obtain ⟨hAs, hAt⟩ := hA
  have hA10 : A 1 0 = A 0 1 := hAs 1 0
  have hA11 : A 1 1 = -A 0 0 := by simp [Fin.sum_univ_two] at hAt; linarith
  have hS : 2 * A 0 0 ^ 2 + 2 * A 0 1 ^ 2 = 1 := by
    simp only [sq2, Fin.sum_univ_two, hA10, hA11] at hA1
    linarith
  have hP : p 0 ^ 2 + p 1 ^ 2 = 1 := by simpa [sq1, Fin.sum_univ_two] using hp
  have e0 : A 0 0 * p 0 + A 0 1 * p 1 = lam * p 0 := by
    simpa [Fin.sum_univ_two] using hev 0
  have e1 : A 0 1 * p 0 - A 0 0 * p 1 = lam * p 1 := by
    have := hev 1
    simp only [Fin.sum_univ_two, hA10, hA11] at this
    linarith
  have hlam2 : lam ^ 2 = 1 / 2 := by
    linear_combination (-lam ^ 2 + A 0 0 ^ 2 + A 0 1 ^ 2) * hP
      - (A 0 0 * p 0 + A 0 1 * p 1 + lam * p 0) * e0
      - (A 0 1 * p 0 - A 0 0 * p 1 + lam * p 1) * e1 + 1 / 2 * hS
  have hhalf : 1 / 2 ≤ -lam := by nlinarith
  have hval : certificateTwoCoeffs.boundaryExpr A p lam = -lam / 5 := by
    simp [Coeffs.boundaryExpr, Coeffs.bdryS0, Coeffs.C, Fin.sum_univ_two,
      certificateTwoCoeffs, hA10, hA11]
    linear_combination (2 / 5) * (lam * hS + p 0 * e0 + p 1 * e1 + lam * hP)
  rw [hval]
  linarith

end CertificateTwo

open CertificateTwo in
/-- The coefficients `f = 1`, `U = (2/5) A`, `K = M = P = 0` satisfy the certificate properties
on `ℝ²` with `ε = δ = 1/10`. -/
theorem certificateTwoCoeffs_holds :
    CertificateHolds 2 (1 / 10) (1 / 10) certificateTwoCoeffs where
  smooth_f := contDiff_const
  smooth_U := ContDiff.const_smul _ contDiff_fst
  smooth_K := contDiff_const
  smooth_M := contDiff_const
  smooth_P := contDiff_const
  equiv_f _ _ _ _ _ := rfl
  equiv_U O _ A p g := by
    funext i j
    simp [certificateTwoCoeffs, act2]
    ring_nf
  equiv_K O _ A p g := by
    funext i j k l
    simp [certificateTwoCoeffs, act4]
  equiv_M O _ A p g := by
    funext i
    simp [certificateTwoCoeffs, act1]
  equiv_P O _ A p g := by
    funext i
    simp [certificateTwoCoeffs, act1]
  even_U _ _ _ := rfl
  even_K _ _ _ := rfl
  P_g_zero _ _ := rfl
  interior A X p g w z ℓ hA hA1 hX _ := interior A X p g w z ℓ hA hA1 hX
  f_ge _ _ _ _ _ _ := by norm_num [certificateTwoCoeffs]
  boundary A p lam hA hA1 hp hev hlam := boundary A p lam hA hA1 hp hev hlam

/-- The algebraic certificate on `ℝ²`. -/
theorem certificateStatement_two : CertificateStatement 2 :=
  ⟨1 / 10, 1 / 10, by norm_num, by norm_num, certificateTwoCoeffs, certificateTwoCoeffs_holds⟩

end OnePhaseDimension.Gen
