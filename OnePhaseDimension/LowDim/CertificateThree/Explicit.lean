/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.CertificateThree.Coeffs
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The explicit interior and boundary polynomials of the certificate in `ℝ³`

For the coefficient data `certThreeCoeffs` the derivation `D_l`, defined through `fderiv` along
the generator `(X_l − q_l A, w A_{l·} − g z δ_{l·}, z p_l)`, is computed by the product rule.
For a direction `(E, v)` in the `(A, p)` variables the directional derivatives of `U` and `M` are
`coeffUDir A p E v` and `coeffMDir A p E v` (the coefficients do not depend on `g`). Substituting
them into the interior expression `𝓘` and the boundary expression `𝓢` gives explicit polynomials
`interiorPolyThree` and `boundaryPolyThree` in the entries of `(A, X, p, g, w, z, ℓ)` and
`(A, p, λ)`, written with sums over `Fin 3`; unfolding the tensor operations and
`Fin.sum_univ_three` turns them into polynomials in the entries.

## Main statements

* `Gen.certThree_Dl_G`, `Gen.certThree_Dl_M`: the explicit derivatives.
* `Gen.certThree_interiorExpr_eq`: `𝓘 = interiorPolyThree`.
* `Gen.certThree_boundaryExpr_eq`: `𝓢 = boundaryPolyThree`.
* `Gen.certThree_holds_of`: the certificate properties follow from the two polynomial
  inequalities.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace OnePhaseDimension.Gen

namespace CertThree

variable {m : ℕ}

/-! ### Directional derivatives of the coefficients -/

/-- The derivative of `Ap` in the direction `(E, v)`: `Ep + Av`. -/
def matVecDir (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) : Ten1 m :=
  matVec E p + matVec A v

/-- The derivative of `p · Ap` in the direction `(E, v)`: `v · Ap + p · (Ep + Av)`. -/
def quadFormDir (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) : ℝ :=
  dot v (matVec A p) + dot p (matVecDir A p E v)

/-- The derivative of `U` in the direction `(E, v)` of `(A, p)`. -/
def coeffUDir (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) : Ten2 m :=
  (197 / 1000 : ℝ) • (outer v p + outer p v)
    - (27 / 200 : ℝ) • (outer v (matVec A p) + outer p (matVecDir A p E v))
    + (429 / 1000 : ℝ) • (outer (matVecDir A p E v) (matVec A p)
      + outer (matVec A p) (matVecDir A p E v))
    + (527 / 1000 - 173 / 500 * quadForm A p - 1 / 1000 * sq1 p) • E
    - (173 / 500 * quadFormDir A p E v + 1 / 1000 * (2 * dot p v)) • A
    + (49 / 250 - 17 / 40 * sq1 p) • (matMul E A + matMul A E)
    - (17 / 40 * (2 * dot p v)) • matMul A A

/-- The derivative of `M` in the direction `(E, v)` of `(A, p)`. -/
def coeffMDir (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) : Ten1 m :=
  (39 / 500 : ℝ) • v + (69 / 500 : ℝ) • matVecDir A p E v

/-! ### Product rules along a curve -/

section Curve

variable {A : ℝ → Ten2 m} {p u : ℝ → Ten1 m} {A' : Ten2 m} {p' u' : Ten1 m} {t₀ : ℝ}

theorem hasDerivAt_dot (hp : ∀ i, HasDerivAt (fun t ↦ p t i) (p' i) t₀)
    (hu : ∀ i, HasDerivAt (fun t ↦ u t i) (u' i) t₀) :
    HasDerivAt (fun t ↦ dot (p t) (u t)) (dot p' (u t₀) + dot (p t₀) u') t₀ := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ (hp i).mul (hu i)
  refine h.congr_deriv ?_
  simp [dot, Finset.sum_add_distrib]

theorem hasDerivAt_sq1 (hp : ∀ i, HasDerivAt (fun t ↦ p t i) (p' i) t₀) :
    HasDerivAt (fun t ↦ sq1 (p t)) (2 * dot (p t₀) p') t₀ := by
  simp only [sq1_eq_dot]
  refine (hasDerivAt_dot hp hp).congr_deriv ?_
  simp only [dot]
  rw [mul_comm 2, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem hasDerivAt_matVec (hA : ∀ i j, HasDerivAt (fun t ↦ A t i j) (A' i j) t₀)
    (hp : ∀ i, HasDerivAt (fun t ↦ p t i) (p' i) t₀) (i : Fin m) :
    HasDerivAt (fun t ↦ matVec (A t) (p t) i) (matVecDir (A t₀) (p t₀) A' p' i) t₀ := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun a _ ↦ (hA i a).mul (hp a)
  refine h.congr_deriv ?_
  simp [matVecDir, matVec, Finset.sum_add_distrib]

theorem hasDerivAt_matMul (hA : ∀ i j, HasDerivAt (fun t ↦ A t i j) (A' i j) t₀) (i j : Fin m) :
    HasDerivAt (fun t ↦ matMul (A t) (A t) i j)
      ((matMul A' (A t₀) + matMul (A t₀) A') i j) t₀ := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun a _ ↦ (hA i a).mul (hA a j)
  refine h.congr_deriv ?_
  simp [matMul, Finset.sum_add_distrib]

theorem hasDerivAt_quadForm (hA : ∀ i j, HasDerivAt (fun t ↦ A t i j) (A' i j) t₀)
    (hp : ∀ i, HasDerivAt (fun t ↦ p t i) (p' i) t₀) :
    HasDerivAt (fun t ↦ quadForm (A t) (p t)) (quadFormDir (A t₀) (p t₀) A' p') t₀ :=
  hasDerivAt_dot hp (hasDerivAt_matVec hA hp)

theorem hasDerivAt_coeffU_apply (hA : ∀ i j, HasDerivAt (fun t ↦ A t i j) (A' i j) t₀)
    (hp : ∀ i, HasDerivAt (fun t ↦ p t i) (p' i) t₀) (j k : Fin m) :
    HasDerivAt (fun t ↦ coeffU (A t) (p t) j k) (coeffUDir (A t₀) (p t₀) A' p' j k) t₀ := by
  have hmv := hasDerivAt_matVec hA hp
  have hq := hasDerivAt_quadForm hA hp
  have hs := hasDerivAt_sq1 hp
  have hmm := hasDerivAt_matMul hA j k
  simp only [coeffU_apply]
  have h1 := ((hp j).fun_mul (hp k)).const_mul (197 / 1000 : ℝ)
  have h2 := ((hp j).fun_mul (hmv k)).const_mul (27 / 200 : ℝ)
  have h3 := ((hmv j).fun_mul (hmv k)).const_mul (429 / 1000 : ℝ)
  have h4 := ((((hasDerivAt_const t₀ (527 / 1000 : ℝ)).fun_sub
    (hq.const_mul (173 / 500 : ℝ))).fun_sub (hs.const_mul (1 / 1000 : ℝ))).fun_mul (hA j k))
  have h5 := ((hasDerivAt_const t₀ (49 / 250 : ℝ)).fun_sub
    (hs.const_mul (17 / 40 : ℝ))).fun_mul hmm
  have h := (((h1.fun_sub h2).fun_add h3).fun_add h4).fun_add h5
  refine h.congr_deriv ?_
  simp only [coeffUDir, outer, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    matVecDir]
  ring

theorem hasDerivAt_coeffM_apply (hA : ∀ i j, HasDerivAt (fun t ↦ A t i j) (A' i j) t₀)
    (hp : ∀ i, HasDerivAt (fun t ↦ p t i) (p' i) t₀) (l : Fin m) :
    HasDerivAt (fun t ↦ coeffM (A t) (p t) l) (coeffMDir (A t₀) (p t₀) A' p' l) t₀ := by
  simp only [coeffM_apply]
  refine (((hp l).const_mul (39 / 500 : ℝ)).add
    ((hasDerivAt_matVec hA hp l).const_mul (69 / 500 : ℝ))).congr_deriv ?_
  simp [coeffMDir]

end Curve

/-! ### Derivatives along lines and `D_l` -/

theorem hasDerivAt_line_fst (x d : Ten2 m × Ten1 m × ℝ) (a b : Fin m) :
    HasDerivAt (fun t : ℝ ↦ (x + t • d).1 a b) (d.1 a b) 0 := by
  simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d.1 a b)).const_add (x.1 a b)

theorem hasDerivAt_line_snd (x d : Ten2 m × Ten1 m × ℝ) (a : Fin m) :
    HasDerivAt (fun t : ℝ ↦ (x + t • d).2.1 a) (d.2.1 a) 0 := by
  simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d.2.1 a)).const_add (x.2.1 a)

/-- `D_l F` is the derivative of `F` along the line through `(A, p, g)` in the direction of the
generator, for `F` differentiable at `(A, p, g)`. -/
theorem Dl_eq_of_hasDerivAt {F : Ten2 m × Ten1 m × ℝ → ℝ} {A : Ten2 m} {X : Ten3 m}
    {p : Ten1 m} {g w z : ℝ} {l : Fin m} {F' : ℝ} (hF : DifferentiableAt ℝ F (A, p, g))
    (h : HasDerivAt (fun t : ℝ ↦ F ((A, p, g) + t • gen A X p g w z l)) F' 0) :
    Dl F A X p g w z l = F' := by
  rw [Dl, ← DifferentiableAt.lineDeriv_eq_fderiv (𝕜 := ℝ) hF]
  exact HasLineDerivAt.lineDeriv (show HasLineDerivAt ℝ F F' (A, p, g) (gen A X p g w z l) from h)

/-- `D_l` of an entry of `U` at `(A, p, g)` is the derivative of `U` in the direction
`(X_l − q_l A, w A_{l·} − g z δ_{l·})`. -/
theorem Dl_coeffU_apply (A : Ten2 m) (X : Ten3 m) (p : Ten1 m) (g w z : ℝ) (l j k : Fin m) :
    Dl (fun y ↦ coeffU y.1 y.2.1 j k) A X p g w z l
      = coeffUDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) j k := by
  refine Dl_eq_of_hasDerivAt
    ((contDiff_coeffU_apply j k).differentiable (by simp)).differentiableAt ?_
  have h := hasDerivAt_coeffU_apply (A := fun t ↦ ((A, p, g) + t • gen A X p g w z l).1)
    (p := fun t ↦ ((A, p, g) + t • gen A X p g w z l).2.1)
    (hasDerivAt_line_fst _ _) (hasDerivAt_line_snd _ _) j k
  simpa [gen] using h

theorem Dl_coeffM_apply (A : Ten2 m) (X : Ten3 m) (p : Ten1 m) (g w z : ℝ) (l : Fin m) :
    Dl (fun y ↦ coeffM y.1 y.2.1 l) A X p g w z l
      = coeffMDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) l := by
  refine Dl_eq_of_hasDerivAt
    ((contDiff_coeffM_apply l).differentiable (by simp)).differentiableAt ?_
  have h := hasDerivAt_coeffM_apply (A := fun t ↦ ((A, p, g) + t • gen A X p g w z l).1)
    (p := fun t ↦ ((A, p, g) + t • gen A X p g w z l).2.1)
    (hasDerivAt_line_fst _ _) (hasDerivAt_line_snd _ _) l
  simpa [gen] using h

theorem sum_kron_mul (l : Fin m) (Φ : Fin m → ℝ) : ∑ i, kron l i * Φ i = Φ l := by
  simp [kron]

end CertThree

open CertThree

/-! ### The explicit derivatives for `certThreeCoeffs` -/

theorem certThree_G (y : Ten2 3 × Ten1 3 × ℝ) (l i j k : Fin 3) :
    certThreeCoeffs.G y l i j k = kron l i * coeffU y.1 y.2.1 j k := by
  simp [Coeffs.G, Coeffs.C, certThreeCoeffs]

/-- `D_l G_{lijk} = δ_{li} D_l U_{jk}` with the explicit derivative of `U`. -/
theorem certThree_Dl_G (A : Ten2 3) (X : Ten3 3) (p : Ten1 3) (g w z : ℝ) (l i j k : Fin 3) :
    Dl (fun y ↦ certThreeCoeffs.G y l i j k) A X p g w z l
      = kron l i * coeffUDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) j k := by
  simp only [certThree_G]
  rw [Dl, fderiv_const_mul
    ((contDiff_coeffU_apply j k).differentiable (by simp)).differentiableAt (kron l i)]
  rw [← Dl_coeffU_apply A X p g w z l j k]
  rfl

theorem certThree_Dl_M (A : Ten2 3) (X : Ten3 3) (p : Ten1 3) (g w z : ℝ) (l : Fin 3) :
    Dl (fun y ↦ certThreeCoeffs.M y l) A X p g w z l
      = coeffMDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) l :=
  Dl_coeffM_apply A X p g w z l

theorem certThree_Dl_P (A : Ten2 3) (X : Ten3 3) (p : Ten1 3) (g w z : ℝ) (l : Fin 3) :
    Dl (fun y ↦ certThreeCoeffs.P y l) A X p g w z l = 0 := by
  simp [Dl, certThreeCoeffs]

theorem certThree_Dl_f (A : Ten2 3) (X : Ten3 3) (p : Ten1 3) (g w z : ℝ) (l : Fin 3) :
    Dl certThreeCoeffs.f A X p g w z l = 0 := by
  simp [Dl, certThreeCoeffs]

/-! ### The explicit polynomials -/

/-- The interior polynomial of the certificate in `ℝ³` (with `a = 29/50`, so `2a − 1 = 4/25`,
`2a + 1 = 54/25`, `2a = 29/25`, and `m = 3`, `β² = 1`):

  `z² (3 U_{jk} A_{jk} − 1) + ∑_{l,j,k} (D_l U_{jk} + 4/25 q_l U_{jk}) X_{ljk}`
    `+ w ∑_l (D_l M_l + 54/25 q_l M_l) + |ℓ|² − ∑_l 29/25 q_l ℓ_l`,

with `D_l U = coeffUDir A p E v`, `D_l M = coeffMDir A p E v` in the direction
`E = X_l − q_l A`, `v = w A_{l·} − g z δ_{l·}`. -/
def interiorPolyThree (A : Ten2 3) (X : Ten3 3) (p : Ten1 3) (g w z : ℝ) (ℓ : Ten1 3) : ℝ :=
  z ^ 2 * (3 * ∑ j, ∑ k, coeffU A p j k * A j k - 1)
    + ∑ l, ∑ j, ∑ k,
        (coeffUDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
            (fun a ↦ w * A l a - g * z * kron l a) j k
          + 4 / 25 * qVec X A l * coeffU A p j k) * X l j k
    + w * ∑ l, (coeffMDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
            (fun a ↦ w * A l a - g * z * kron l a) l
          + 54 / 25 * qVec X A l * coeffM A p l)
    + sq1 ℓ - ∑ l, 29 / 25 * qVec X A l * ℓ l

/-- The boundary polynomial of the certificate in `ℝ³`:
`−λ + U_{jk}(λ A_{jk} − (A²)_{jk} + p_j p_k) + p_l M_l` at `g = 0`. -/
def boundaryPolyThree (A : Ten2 3) (p : Ten1 3) (lam : ℝ) : ℝ :=
  -lam + ∑ j, ∑ k, coeffU A p j k * (lam * A j k - ∑ a, A j a * A a k + p j * p k)
    + ∑ l, p l * coeffM A p l

theorem aExp_eq : aExp = 29 / 50 := rfl

theorem hardyConst_three : hardyConst 3 = 1 := by norm_num [hardyConst]

theorem certThree_interiorExpr_eq (A : Ten2 3) (X : Ten3 3) (p : Ten1 3) (g w z : ℝ)
    (ℓ : Ten1 3) :
    certThreeCoeffs.interiorExpr A X p g w z ℓ = interiorPolyThree A X p g w z ℓ := by
  have hZ : certThreeCoeffs.termZ A p g z = z ^ 2 * (3 * ∑ j, ∑ k, coeffU A p j k * A j k - 1) := by
    simp [Coeffs.termZ, Coeffs.C, certThreeCoeffs, hardyConst_three]
  have hG : certThreeCoeffs.termG A X p g w z = ∑ l, ∑ j, ∑ k,
      (coeffUDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) j k
        + 4 / 25 * qVec X A l * coeffU A p j k) * X l j k := by
    unfold Coeffs.termG
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    have h : ∀ i, ∑ j, ∑ k, (Dl (fun y ↦ certThreeCoeffs.G y l i j k) A X p g w z l
          + (2 * aExp - 1) * qVec X A l * certThreeCoeffs.G (A, p, g) l i j k) * X i j k
        = kron l i * ∑ j, ∑ k, (coeffUDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
            (fun a ↦ w * A l a - g * z * kron l a) j k
          + 4 / 25 * qVec X A l * coeffU A p j k) * X i j k := fun i ↦ by
      simp only [certThree_Dl_G]
      simp only [certThree_G, Finset.mul_sum, aExp_eq]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    simp only [h]
    exact sum_kron_mul l _
  have hM : certThreeCoeffs.termM A X p g w z = w * ∑ l,
      (coeffMDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) l
        + 54 / 25 * qVec X A l * coeffM A p l) := by
    simp only [Coeffs.termM, certThree_Dl_M, aExp_eq]
    congr 1
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [certThreeCoeffs]
    ring
  have hP : certThreeCoeffs.termP A X p g w z = 0 := by
    simp [Coeffs.termP, Dl, certThreeCoeffs]
  have hF : certThreeCoeffs.termF A X p g w z ℓ = sq1 ℓ - ∑ l, 29 / 25 * qVec X A l * ℓ l := by
    simp only [Coeffs.termF, certThree_Dl_f, aExp_eq]
    simp only [certThreeCoeffs]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun l _ ↦ ?_
      ring
  rw [Coeffs.interiorExpr, hZ, hG, hM, hP, hF, interiorPolyThree]
  ring

theorem certThree_boundaryExpr_eq (A : Ten2 3) (p : Ten1 3) (lam : ℝ) :
    certThreeCoeffs.boundaryExpr A p lam = boundaryPolyThree A p lam := by
  simp [Coeffs.boundaryExpr, boundaryPolyThree, Coeffs.C, certThreeCoeffs, Coeffs.bdryS0]

/-- The certificate properties of `certThreeCoeffs` with `ε = 1/50`, `δ = 1/100` follow from
the interior and boundary polynomial inequalities. -/
theorem certThree_holds_of
    (hI : ∀ A X p g w z ℓ, IsSTF2 A → sq2 A = 1 → IsSTF3 X → g ^ 2 + sq1 p ≤ 1 →
      1 / 50 * (z ^ 2 + sq1 ℓ) ≤ interiorPolyThree A X p g w z ℓ)
    (hB : ∀ A p (lam : ℝ), IsSTF2 A → sq2 A = 1 → sq1 p = 1 →
      (∀ i, ∑ j, A i j * p j = lam * p i) → lam < 0 → 1 / 100 ≤ boundaryPolyThree A p lam) :
    CertificateHolds 3 (1 / 50) (1 / 100) certThreeCoeffs where
  smooth_f := certThree_smooth_f
  smooth_U := certThree_smooth_U
  smooth_K := certThree_smooth_K
  smooth_M := certThree_smooth_M
  smooth_P := certThree_smooth_P
  equiv_f := certThree_equiv_f
  equiv_U := certThree_equiv_U
  equiv_K := certThree_equiv_K
  equiv_M := certThree_equiv_M
  equiv_P := certThree_equiv_P
  even_U := certThree_even_U
  even_K := certThree_even_K
  P_g_zero := certThree_P_g_zero
  interior A X p g w z ℓ hA hA1 hX hpg := by
    rw [certThree_interiorExpr_eq]
    exact hI A X p g w z ℓ hA hA1 hX hpg
  f_ge A p g _ _ _ := certThree_f_ge A p g
  boundary A p lam hA hA1 hp hAp hlam := by
    rw [certThree_boundaryExpr_eq]
    exact hB A p lam hA hA1 hp hAp hlam

end OnePhaseDimension.Gen
