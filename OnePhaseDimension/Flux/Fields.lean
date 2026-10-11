/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Flux.Algebra
public import OnePhaseDimension.Geometry.Homogeneous
public import OnePhaseDimension.Geometry.FrameChange
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Analytic.CPolynomial

/-!
# The flux fields

Let `u` be a function on `ℝⁿ` and `c` certificate data. At a unit vector `y` and an orthonormal
frame `τᵢ = ι eᵢ` of `y^⊥` we read off the frame data

  `T_{ij} = D²u(y)[τᵢ, τⱼ]`, `B_{ijk} = D³u(y)[τᵢ, τⱼ, τ_k]`, `pᵢ = Du(y)[τᵢ]`, `g = u(y)`,

and put `w = |T|`, `A = T/w`, `X = B/w`. The flux fields are the `0`-homogeneous scalar and
tangential vector field on `ℝⁿ \ {0}`

  `h = w^a √f(A, p, g)`,  `Z = ∑_l w^{2a}(G_{lijk}X_{ijk} + w M_l + P_l) τ_l`,

evaluated at `y = x/|x|` in a frame of `y^⊥` chosen at each point (`sphereFrame`). For a
one-homogeneous `u` the frame data are the spherical data `g, p, T, B` of `u` on the unit sphere.
By the orthogonal equivariance of the certificate coefficients the fields do not depend on the
choice of frame (`fluxZ_eq_of_frame`, `fluxH_eq_of_frame`); in particular near a unit vector
`x₀` they are given by the data read in the Rodrigues-transported frame
(`fluxZ_eq_transported`), which is smooth.

The certificate data are generic (`Gen.Coeffs (n - 1)`, with constants `ε, δ`). The
declarations at the end of the file are the case `n = 6` for five-dimensional certificate data.

## Main definitions

* `Gen.frameT`, `Gen.frameB`, `Gen.frameP`: the frame data.
* `Gen.sphereFrame`: the frame of `y^⊥` used in the definitions.
* `Gen.fluxW`, `Gen.fluxH`, `Gen.fluxZ`: the ambient fields `w`, `h`, `Z`.
-/

open Function Filter Topology Set
open scoped RealInnerProductSpace ContDiff Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### Trilinear forms in a changed frame -/

section FrameChange

variable {n : ℕ} {y : E n} {ι ι' : E (n - 1) →ₗᵢ[ℝ] E n}

/-- Reading a trilinear form in the new frame:
`M[σᵢ, σⱼ, σ_k] = ∑ O_{ia} O_{jb} O_{kc} M[τₐ, τ_b, τ_c]`. -/
theorem trilinear_frameVec_frameChange (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0) (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ E n) ℝ)
    (i j k : Fin (n - 1)) :
    M ![frameVec ι' i, frameVec ι' j, frameVec ι' k] =
      ∑ a, ∑ b, ∑ c, frameChange ι ι' i a * frameChange ι ι' j b * frameChange ι ι' k c *
        M ![frameVec ι a, frameVec ι b, frameVec ι c] := by
  have h1 : ∀ w₁ w₂ : E n, M ![frameVec ι' i, w₁, w₂] =
      ∑ a, frameChange ι ι' i a * M ![frameVec ι a, w₁, w₂] := fun w₁ w₂ ↦ by
    rw [frameVec_eq_sum_frameChange hy hι hι' i]
    exact cons_sum_smul_apply M Finset.univ _ _ _
  have h2 : ∀ w₀ w₂ : E n, M ![w₀, frameVec ι' j, w₂] =
      ∑ b, frameChange ι ι' j b * M ![w₀, frameVec ι b, w₂] := fun w₀ w₂ ↦ by
    rw [frameVec_eq_sum_frameChange hy hι hι' j]
    exact cons_sum_smul_apply (M.curryLeft w₀) Finset.univ _ _ ![w₂]
  have h3 : ∀ w₀ w₁ : E n, M ![w₀, w₁, frameVec ι' k] =
      ∑ c, frameChange ι ι' k c * M ![w₀, w₁, frameVec ι c] := fun w₀ w₁ ↦ by
    rw [frameVec_eq_sum_frameChange hy hι hι' k]
    exact cons_sum_smul_apply ((M.curryLeft w₀).curryLeft w₁) Finset.univ _ _ ![]
  rw [h1]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  ring

end FrameChange

/-! ### Radial projection and transport near a nonzero point -/

section Radial

variable {n : ℕ} {u : E n → ℝ} {x₀ x : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n}

theorem radialProj_smul {x : E n} {r : ℝ} (hr : 0 < r) : radialProj (r • x) = radialProj x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialProj]
  simp only [radialProj, norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

/-- Near `x₁ ≠ 0`, the transport from `x₁/|x₁|` is defined. -/
theorem eventually_transport_defined_of_ne {x₁ : E n} (hx₁ : x₁ ≠ 0) :
    ∀ᶠ x in 𝓝 x₁, x ≠ 0 ∧ ⟪radialProj x₁, radialProj x⟫ ≠ -1 := by
  have hc : ContinuousAt (fun x ↦ ⟪radialProj x₁, radialProj x⟫) x₁ := by
    refine continuousAt_const.inner ?_
    unfold radialProj
    exact ((continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.2 hx₁)).smul continuousAt_id
  have h1 : ⟪radialProj x₁, radialProj x₁⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_radialProj hx₁]; norm_num
  exact (eventually_ne_nhds hx₁).and (hc.eventually_ne (by rw [h1]; norm_num))

theorem contDiffAt_radialProj {k : WithTop ℕ∞} {x : E n} (hx : x ≠ 0) :
    ContDiffAt ℝ k radialProj x := by
  unfold radialProj
  exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_id

theorem contDiffAt_transFrame {k : WithTop ℕ∞} (hx : x ≠ 0) (hne : ⟪x₀, radialProj x⟫ ≠ -1)
    (i : Fin (n - 1)) : ContDiffAt ℝ k (fun x ↦ transFrame x₀ ι x i) x := by
  have hopen : IsOpen {b : E n | ⟪x₀, b⟫ ≠ -1} :=
    isOpen_ne_fun (continuous_const.inner continuous_id) continuous_const
  have hR : ContDiffAt ℝ k (rodrigues x₀) (radialProj x) :=
    (contDiffOn_rodrigues x₀).contDiffAt (hopen.mem_nhds hne)
  exact (hR.comp x (contDiffAt_radialProj hx)).clm_apply contDiffAt_const

theorem contDiffAt_transJet (hu : ContDiffAt ℝ ∞ u (radialProj x)) (hx : x ≠ 0)
    (hne : ⟪x₀, radialProj x⟫ ≠ -1) (k : ℕ) (idx : Fin k → Fin (n - 1)) :
    ContDiffAt ℝ ∞ (transJet u x₀ ι k idx) x := by
  have h1 : ContDiffAt ℝ ∞ (fun x ↦ iteratedFDeriv ℝ k u (radialProj x)) x :=
    (hu.iteratedFDeriv_right (m := ∞) (i := k) (by simp)).comp x (contDiffAt_radialProj hx)
  have h2 : ContDiffAt ℝ ∞ (fun x ↦ fun s ↦ transFrame x₀ ι x (idx s)) x :=
    contDiffAt_pi.2 fun s ↦ contDiffAt_transFrame hx hne (idx s)
  have hev := ((ContinuousLinearMap.id ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E n) ℝ)
    ).analyticAt_uncurry_of_multilinear (x := (iteratedFDeriv ℝ k u (radialProj x),
      fun s ↦ transFrame x₀ ι x (idx s)))).contDiffAt (n := ∞)
  exact hev.comp x (h1.prodMk h2)


end Radial

namespace Gen

variable {n : ℕ}

/-! ### Frame data -/

/-- The Hessian read in the frame of `ι`: `T_{ij} = D²u(y)[τᵢ, τⱼ]`. -/
def frameT (u : E n → ℝ) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (y : E n) : Ten2 (n - 1) :=
  fun i j ↦ iteratedFDeriv ℝ 2 u y ![frameVec ι i, frameVec ι j]

/-- The third derivative read in the frame of `ι`: `B_{ijk} = D³u(y)[τᵢ, τⱼ, τ_k]`. -/
def frameB (u : E n → ℝ) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (y : E n) : Ten3 (n - 1) :=
  fun i j k ↦ iteratedFDeriv ℝ 3 u y ![frameVec ι i, frameVec ι j, frameVec ι k]

/-- The gradient read in the frame of `ι`: `pᵢ = Du(y)[τᵢ]`. -/
def frameP (u : E n → ℝ) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (y : E n) : Ten1 (n - 1) :=
  fun i ↦ fderiv ℝ u y (frameVec ι i)

section FrameData

variable {u : E n → ℝ} {y : E n} {ι ι' : E (n - 1) →ₗᵢ[ℝ] E n}

theorem frameT_frameChange (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0) :
    frameT u ι' y = act2 (frameChange ι ι') (frameT u ι y) := by
  funext i j
  exact bilinear_frameVec_frameChange hy hι hι' _ i j

theorem frameB_frameChange (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0) :
    frameB u ι' y = act3 (frameChange ι ι') (frameB u ι y) := by
  funext i j k
  exact trilinear_frameVec_frameChange hy hι hι' _ i j k

theorem frameP_frameChange (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0) :
    frameP u ι' y = act1 (frameChange ι ι') (frameP u ι y) := by
  funext i
  exact apply_frameVec_frameChange hy hι hι' _ i

end FrameData

/-! ### The chosen frame -/

/-- There is a linear isometry `ℝ^{n-1} → ℝⁿ`. -/
theorem nonempty_frame (n : ℕ) : Nonempty (E (n - 1) →ₗᵢ[ℝ] E n) := by
  rcases n with _ | k
  · exact ⟨LinearIsometry.id⟩
  · exact ⟨stdFrame (EuclideanSpace.single 0 1) (by simp)⟩

/-- The orthonormal frame of `y^⊥` used to define the fields at a unit vector `y` (an arbitrary
choice; the fields do not depend on it). -/
def sphereFrame (y : E n) : E (n - 1) →ₗᵢ[ℝ] E n :=
  if hy : ‖y‖ = 1 then stdFrame y hy else (nonempty_frame n).some

theorem inner_sphereFrame {y : E n} (hy : ‖y‖ = 1) (v : E (n - 1)) :
    ⟪sphereFrame y v, y⟫ = 0 := by
  rw [sphereFrame, dite_eq_left hy]
  exact inner_stdFrame hy v

/-! ### The fields -/

/-- The scalar `w = |T|` at `x/|x|` (zero at the origin). -/
def fluxW (u : E n → ℝ) (x : E n) : ℝ :=
  if x = 0 then 0 else normW (frameT u (sphereFrame (radialProj x)) (radialProj x))

theorem fluxW_nonneg (u : E n → ℝ) (x : E n) : 0 ≤ fluxW u x := by
  unfold fluxW
  split_ifs
  · exact le_rfl
  · exact Real.sqrt_nonneg _

/-- The scalar flux field `h = w^a √f(A, p, g)` at `x/|x|` (zero at the origin). -/
def fluxH (c : Coeffs (n - 1)) (u : E n → ℝ) (x : E n) : ℝ :=
  if x = 0 then 0 else
    c.fluxHComp (frameT u (sphereFrame (radialProj x)) (radialProj x))
      (frameP u (sphereFrame (radialProj x)) (radialProj x)) (u (radialProj x))

/-- The coefficient `f(A, p, g)` at `x/|x|` (zero at the origin). -/
def fluxF (c : Coeffs (n - 1)) (u : E n → ℝ) (x : E n) : ℝ :=
  if x = 0 then 0 else
    c.f (normalizedA (frameT u (sphereFrame (radialProj x)) (radialProj x)),
      frameP u (sphereFrame (radialProj x)) (radialProj x), u (radialProj x))

/-- The flux vector field `Z = ∑_l w^{2a}(G_{lijk}X_{ijk} + w M_l + P_l) τ_l` at `x/|x|` (zero at
the origin). -/
def fluxZ (c : Coeffs (n - 1)) (u : E n → ℝ) (x : E n) : E n :=
  if x = 0 then 0 else
    ∑ l, c.fluxZComp (frameT u (sphereFrame (radialProj x)) (radialProj x))
        (frameB u (sphereFrame (radialProj x)) (radialProj x))
        (frameP u (sphereFrame (radialProj x)) (radialProj x)) (u (radialProj x)) l •
      frameVec (sphereFrame (radialProj x)) l

/-! ### Frame independence -/

section Independence

variable {c : Coeffs (n - 1)} {ε δ : ℝ} {u : E n → ℝ} {x : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n}

theorem fluxW_eq_of_frame (hx : x ≠ 0) (hι : ∀ v, ⟪ι v, radialProj x⟫ = 0) :
    fluxW u x = normW (frameT u ι (radialProj x)) := by
  have hy := norm_radialProj hx
  rw [fluxW, ite_eq_right hx, frameT_frameChange hy (inner_sphereFrame hy) hι,
    normW_act2 (isOrth_frameChange hy (inner_sphereFrame hy) hι)]

theorem fluxH_eq_of_frame (hc : CertificateHolds (n - 1) ε δ c) (hx : x ≠ 0)
    (hι : ∀ v, ⟪ι v, radialProj x⟫ = 0) :
    fluxH c u x = c.fluxHComp (frameT u ι (radialProj x)) (frameP u ι (radialProj x))
      (u (radialProj x)) := by
  have hy := norm_radialProj hx
  rw [fluxH, ite_eq_right hx, frameT_frameChange hy (inner_sphereFrame hy) hι,
    frameP_frameChange hy (inner_sphereFrame hy) hι,
    Coeffs.fluxHComp_act hc (isOrth_frameChange hy (inner_sphereFrame hy) hι)]

theorem fluxF_eq_of_frame (hc : CertificateHolds (n - 1) ε δ c) (hx : x ≠ 0)
    (hι : ∀ v, ⟪ι v, radialProj x⟫ = 0) :
    fluxF c u x = c.f (normalizedA (frameT u ι (radialProj x)), frameP u ι (radialProj x),
      u (radialProj x)) := by
  have hy := norm_radialProj hx
  have h0 := inner_sphereFrame hy
  have hO := isOrth_frameChange hy h0 hι
  rw [fluxF, ite_eq_right hx, frameT_frameChange hy h0 hι, frameP_frameChange hy h0 hι,
    normalizedA_act2 hO, hc.equiv_f _ hO]

/-- **Frame independence of `Z`.** In any orthonormal frame of `(x/|x|)^⊥`, `Z(x)` is given by the
same formula. -/
theorem fluxZ_eq_of_frame (hc : CertificateHolds (n - 1) ε δ c) (hx : x ≠ 0)
    (hι : ∀ v, ⟪ι v, radialProj x⟫ = 0) :
    fluxZ c u x = ∑ l, c.fluxZComp (frameT u ι (radialProj x)) (frameB u ι (radialProj x))
        (frameP u ι (radialProj x)) (u (radialProj x)) l • frameVec ι l := by
  have hy := norm_radialProj hx
  have h0 := inner_sphereFrame hy
  rw [fluxZ, ite_eq_right hx]
  refine (sum_smul_frameVec_eq hy h0 hι _ _ fun i ↦ ?_).symm
  rw [frameT_frameChange hy h0 hι, frameB_frameChange hy h0 hι, frameP_frameChange hy h0 hι,
    Coeffs.fluxZComp_act hc (isOrth_frameChange hy h0 hι)]
  rfl

end Independence

/-! ### Homogeneity and tangency -/

theorem isZeroHomogeneous_fluxW (u : E n → ℝ) : IsZeroHomogeneous (fluxW u) := by
  intro r hr x
  simp only [fluxW, smul_eq_zero, hr.ne', false_or, radialProj_smul hr]

theorem isZeroHomogeneous_fluxH (c : Coeffs (n - 1)) (u : E n → ℝ) :
    IsZeroHomogeneous (fluxH c u) := by
  intro r hr x
  simp only [fluxH, smul_eq_zero, hr.ne', false_or, radialProj_smul hr]

theorem isZeroHomogeneous_fluxF (c : Coeffs (n - 1)) (u : E n → ℝ) :
    IsZeroHomogeneous (fluxF c u) := by
  intro r hr x
  simp only [fluxF, smul_eq_zero, hr.ne', false_or, radialProj_smul hr]

theorem isZeroHomogeneous_fluxZ (c : Coeffs (n - 1)) (u : E n → ℝ) :
    IsZeroHomogeneous (fluxZ c u) := by
  intro r hr x
  simp only [fluxZ, smul_eq_zero, hr.ne', false_or, radialProj_smul hr]

/-- `Z` is tangential: `⟪x, Z(x)⟫ = 0`. -/
theorem isTangentialField_fluxZ (c : Coeffs (n - 1)) (u : E n → ℝ) :
    IsTangentialField (fluxZ c u) := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp [fluxZ]
  have hy := norm_radialProj hx
  have hxr : x = ‖x‖ • radialProj x := by
    rw [radialProj, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
  have h0 : ∀ l, ⟪x, frameVec (sphereFrame (radialProj x)) l⟫ = 0 := fun l ↦ by
    rw [hxr, real_inner_smul_left, real_inner_comm, ← hxr]
    rw [show frameVec (sphereFrame (radialProj x)) l = sphereFrame (radialProj x) _ from rfl,
      inner_sphereFrame hy, mul_zero]
  rw [fluxZ, ite_eq_right hx, inner_sum]
  exact Finset.sum_eq_zero fun l _ ↦ by rw [inner_smul_right, h0, mul_zero]

/-! ### The fields in the transported frame -/

section Transported

variable {u : E n → ℝ} {x₀ x : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n}

/-- The transported Hessian as a two-tensor. -/
def transTData (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (x : E n) : Ten2 (n - 1) :=
  fun i j ↦ transT u x₀ ι x i j

/-- The transported third derivative as a three-tensor. -/
def transBData (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (x : E n) : Ten3 (n - 1) :=
  fun i j k ↦ transB u x₀ ι x i j k

/-- The transported gradient as a vector. -/
def transPData (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (x : E n) : Ten1 (n - 1) :=
  fun i ↦ transP u x₀ ι x i

variable (hx₀ : ‖x₀‖ = 1) (hx : x ≠ 0) (hne : ⟪x₀, radialProj x⟫ ≠ -1)
include hx₀ hx hne

theorem frameT_transportIsometry :
    frameT u (transportIsometry x₀ ι hx₀ hx hne) (radialProj x) = transTData u x₀ ι x := by
  funext i j
  simp only [frameT, transTData, transT, transJet]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem frameB_transportIsometry :
    frameB u (transportIsometry x₀ ι hx₀ hx hne) (radialProj x) = transBData u x₀ ι x := by
  funext i j k
  simp only [frameB, transBData, transB, transJet]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem frameP_transportIsometry :
    frameP u (transportIsometry x₀ ι hx₀ hx hne) (radialProj x) = transPData u x₀ ι x := by
  funext i
  simp only [frameP, transPData, transP, transJet, iteratedFDeriv_one_apply]
  rfl

variable {c : Coeffs (n - 1)} {ε δ : ℝ} (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
include hι

/-- `Z` in the transported frame. -/
theorem fluxZ_eq_transported (hc : CertificateHolds (n - 1) ε δ c) :
    fluxZ c u x = ∑ l, c.fluxZComp (transTData u x₀ ι x) (transBData u x₀ ι x)
      (transPData u x₀ ι x) (transG u x) l • transFrame x₀ ι x l := by
  rw [fluxZ_eq_of_frame hc hx (inner_transportIsometry_radialProj hx₀ hι hx hne),
    frameT_transportIsometry hx₀ hx hne, frameB_transportIsometry hx₀ hx hne,
    frameP_transportIsometry hx₀ hx hne]
  rfl

/-- The transported components of `Z`: `⟪τ_l(x), Z(x)⟫ = Z_l`. -/
theorem inner_transFrame_fluxZ (hc : CertificateHolds (n - 1) ε δ c) (l : Fin (n - 1)) :
    ⟪transFrame x₀ ι x l, fluxZ c u x⟫ = c.fluxZComp (transTData u x₀ ι x)
      (transBData u x₀ ι x) (transPData u x₀ ι x) (transG u x) l := by
  rw [fluxZ_eq_transported hx₀ hx hne hι hc, inner_sum]
  simp only [inner_smul_right, inner_transFrame_transFrame hx₀ hx hne, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem fluxH_eq_transported (hc : CertificateHolds (n - 1) ε δ c) :
    fluxH c u x = c.fluxHComp (transTData u x₀ ι x) (transPData u x₀ ι x) (transG u x) := by
  rw [fluxH_eq_of_frame hc hx (inner_transportIsometry_radialProj hx₀ hι hx hne),
    frameT_transportIsometry hx₀ hx hne, frameP_transportIsometry hx₀ hx hne]
  rfl

theorem fluxF_eq_transported (hc : CertificateHolds (n - 1) ε δ c) :
    fluxF c u x = c.f (normalizedA (transTData u x₀ ι x), transPData u x₀ ι x, transG u x) := by
  rw [fluxF_eq_of_frame hc hx (inner_transportIsometry_radialProj hx₀ hι hx hne),
    frameT_transportIsometry hx₀ hx hne, frameP_transportIsometry hx₀ hx hne]
  rfl

theorem fluxW_eq_transported : fluxW u x = normW (transTData u x₀ ι x) := by
  rw [fluxW_eq_of_frame hx (inner_transportIsometry_radialProj hx₀ hι hx hne),
    frameT_transportIsometry hx₀ hx hne]

end Transported

/-! ### Smoothness -/

section Smooth

theorem contDiff_sq2 {m : ℕ} : ContDiff ℝ ∞ (sq2 : Ten2 m → ℝ) := by
  unfold sq2
  fun_prop

theorem normW_pos_iff {m : ℕ} {T : Ten2 m} : 0 < normW T ↔ sq2 T ≠ 0 := by
  have h : 0 ≤ sq2 T := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  rw [normW, Real.sqrt_pos]
  exact ⟨ne_of_gt, fun h' ↦ lt_of_le_of_ne h (Ne.symm h')⟩

theorem contDiffAt_normW {m : ℕ} {T : Ten2 m} (h : sq2 T ≠ 0) : ContDiffAt ℝ ∞ normW T :=
  contDiff_sq2.contDiffAt.sqrt h

section Comp

variable {m : ℕ} {c : Coeffs m} {ε δ : ℝ}

/-- The normalized data `(A, p, g)` as a smooth function of the frame data. -/
theorem contDiffAt_normalizedData {d : Ten2 m × Ten3 m × Ten1 m × ℝ} (h : sq2 d.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ (normalizedA d.1, d.2.2.1, d.2.2.2))
      d := by
  have hw : ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ normW d.1) d :=
    (contDiffAt_normW h).comp d (by fun_prop)
  have hw0 : normW d.1 ≠ 0 := (normW_pos_iff.2 h).ne'
  refine ContDiffAt.prodMk ?_ (by fun_prop)
  refine contDiffAt_pi.2 fun i ↦ contDiffAt_pi.2 fun j ↦ ?_
  exact ContDiffAt.div (by fun_prop) hw hw0

theorem contDiffAt_fluxZComp (hc : CertificateHolds m ε δ c) {d : Ten2 m × Ten3 m × Ten1 m × ℝ}
    (h : sq2 d.1 ≠ 0) (l : Fin m) :
    ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ c.fluxZComp d.1 d.2.1 d.2.2.1 d.2.2.2 l)
      d := by
  have hw : ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ normW d.1) d :=
    (contDiffAt_normW h).comp d (by fun_prop)
  have hw0 : normW d.1 ≠ 0 := (normW_pos_iff.2 h).ne'
  have hA := contDiffAt_normalizedData h
  have hU := hc.smooth_U.contDiffAt.comp d hA
  have hK := hc.smooth_K.contDiffAt.comp d hA
  have hU' : ∀ j k, ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦
      c.U (normalizedA d.1, d.2.2.1, d.2.2.2) j k) d :=
    fun j k ↦ contDiffAt_pi.1 (contDiffAt_pi.1 hU j) k
  have hK' : ∀ l i j k, ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦
      c.K (normalizedA d.1, d.2.2.1, d.2.2.2) l i j k) d :=
    fun l i j k ↦ contDiffAt_pi.1 (contDiffAt_pi.1 (contDiffAt_pi.1 (contDiffAt_pi.1 hK l) i) j) k
  have hM' := contDiffAt_pi.1 (hc.smooth_M.contDiffAt.comp d hA) l
  have hP' := contDiffAt_pi.1 (hc.smooth_P.contDiffAt.comp d hA) l
  have hr : ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ normW d.1 ^ (2 * aExp)) d :=
    hw.rpow_const_of_ne hw0
  have hX : ∀ i j k, ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ d.2.1 i j k / normW d.1)
      d := fun i j k ↦ ContDiffAt.div (by fun_prop) hw hw0
  simp only [Function.comp_def] at hM' hP'
  unfold Coeffs.fluxZComp Coeffs.contractG Coeffs.G Coeffs.C normalizedX
  fun_prop

theorem contDiffAt_fluxHComp (hc : CertificateHolds m ε δ c) {d : Ten2 m × Ten3 m × Ten1 m × ℝ}
    (h : sq2 d.1 ≠ 0) (hf : c.f (normalizedA d.1, d.2.2.1, d.2.2.2) ≠ 0) :
    ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ c.fluxHComp d.1 d.2.2.1 d.2.2.2) d := by
  have hw : ContDiffAt ℝ ∞ (fun d : Ten2 m × Ten3 m × Ten1 m × ℝ ↦ normW d.1) d :=
    (contDiffAt_normW h).comp d (by fun_prop)
  have hw0 : normW d.1 ≠ 0 := (normW_pos_iff.2 h).ne'
  have hF := hc.smooth_f.contDiffAt.comp d (contDiffAt_normalizedData h)
  exact (hw.rpow_const_of_ne hw0).mul (hF.sqrt hf)

end Comp

variable {c : Coeffs (n - 1)} {ε δ : ℝ} {u : E n → ℝ} {x₀ x : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n}

/-- The transported frame data `(T, B, p, g)` are smooth. -/
theorem contDiffAt_transData (hu : ContDiffAt ℝ ∞ u (radialProj x)) (hx : x ≠ 0)
    (hne : ⟪x₀, radialProj x⟫ ≠ -1) :
    ContDiffAt ℝ ∞ (fun x ↦ (transTData u x₀ ι x, transBData u x₀ ι x, transPData u x₀ ι x,
      transG u x)) x := by
  refine ContDiffAt.prodMk ?_ (ContDiffAt.prodMk ?_ (ContDiffAt.prodMk ?_ ?_))
  · exact contDiffAt_pi.2 fun i ↦ contDiffAt_pi.2 fun j ↦ contDiffAt_transJet hu hx hne 2 _
  · exact contDiffAt_pi.2 fun i ↦ contDiffAt_pi.2 fun j ↦ contDiffAt_pi.2 fun k ↦
      contDiffAt_transJet hu hx hne 3 _
  · exact contDiffAt_pi.2 fun i ↦ contDiffAt_transJet hu hx hne 1 _
  · exact hu.comp x (contDiffAt_radialProj hx)

/-- **Smoothness of `w`** at `x ≠ 0` with `w(x) > 0`, if `u` is smooth at `x/|x|`. -/
theorem contDiffAt_fluxW (hx : x ≠ 0) (hu : ContDiffAt ℝ ∞ u (radialProj x))
    (hw : 0 < fluxW u x) : ContDiffAt ℝ ∞ (fluxW u) x := by
  set y := radialProj x
  have hy := norm_radialProj hx
  obtain ⟨hx', hne⟩ := (eventually_transport_defined_of_ne hx).self_of_nhds
  have hev : fluxW u =ᶠ[𝓝 x] fun z ↦ normW (transTData u y (sphereFrame y) z) := by
    filter_upwards [eventually_transport_defined_of_ne hx] with z hz
    exact fluxW_eq_transported hy hz.1 hz.2 (inner_sphereFrame hy)
  rw [hev.self_of_nhds] at hw
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (contDiffAt_normW (normW_pos_iff.1 hw)).comp x
    (contDiffAt_pi.2 fun i ↦ contDiffAt_pi.2 fun j ↦ contDiffAt_transJet hu hx hne 2 _)

/-- **Smoothness of `Z`** at `x ≠ 0` with `w(x) > 0`, if `u` is smooth at `x/|x|`. -/
theorem contDiffAt_fluxZ (hc : CertificateHolds (n - 1) ε δ c) (hx : x ≠ 0)
    (hu : ContDiffAt ℝ ∞ u (radialProj x)) (hw : 0 < fluxW u x) :
    ContDiffAt ℝ ∞ (fluxZ c u) x := by
  set y := radialProj x
  have hy := norm_radialProj hx
  have hι := inner_sphereFrame hy
  obtain ⟨hx', hne⟩ := (eventually_transport_defined_of_ne hx).self_of_nhds
  have hev : fluxZ c u =ᶠ[𝓝 x] fun z ↦ ∑ l, c.fluxZComp (transTData u y (sphereFrame y) z)
      (transBData u y (sphereFrame y) z) (transPData u y (sphereFrame y) z) (transG u z) l •
        transFrame y (sphereFrame y) z l := by
    filter_upwards [eventually_transport_defined_of_ne hx] with z hz
    exact fluxZ_eq_transported hy hz.1 hz.2 hι hc
  rw [fluxW_eq_transported hy hx hne hι] at hw
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine ContDiffAt.sum fun l _ ↦ ?_
  have h1 := (contDiffAt_fluxZComp hc (d := (transTData u y (sphereFrame y) x,
    transBData u y (sphereFrame y) x, transPData u y (sphereFrame y) x, transG u x))
    (normW_pos_iff.1 hw) l).comp x (contDiffAt_transData hu hx hne)
  exact h1.smul (contDiffAt_transFrame hx hne l)

/-- **Smoothness of `h`** at `x ≠ 0` with `w(x) > 0` and `f(x) ≠ 0`, if `u` is smooth at
`x/|x|`. -/
theorem contDiffAt_fluxH (hc : CertificateHolds (n - 1) ε δ c) (hx : x ≠ 0)
    (hu : ContDiffAt ℝ ∞ u (radialProj x)) (hw : 0 < fluxW u x) (hf : fluxF c u x ≠ 0) :
    ContDiffAt ℝ ∞ (fluxH c u) x := by
  set y := radialProj x
  have hy := norm_radialProj hx
  have hι := inner_sphereFrame hy
  obtain ⟨hx', hne⟩ := (eventually_transport_defined_of_ne hx).self_of_nhds
  have hev : fluxH c u =ᶠ[𝓝 x] fun z ↦ c.fluxHComp (transTData u y (sphereFrame y) z)
      (transPData u y (sphereFrame y) z) (transG u z) := by
    filter_upwards [eventually_transport_defined_of_ne hx] with z hz
    exact fluxH_eq_transported hy hz.1 hz.2 hι hc
  rw [fluxW_eq_transported hy hx hne hι] at hw
  rw [fluxF_eq_transported hy hx hne hι hc] at hf
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (contDiffAt_fluxHComp hc (d := (transTData u y (sphereFrame y) x,
    transBData u y (sphereFrame y) x, transPData u y (sphereFrame y) x, transG u x))
    (normW_pos_iff.1 hw) hf).comp x (contDiffAt_transData hu hx hne)

/-- **Smoothness of `Z` on a set.** `Z` is smooth on any set of nonzero points `x` with
`w(x) > 0` at which `u` is smooth at `x/|x|`. -/
theorem contDiffOn_fluxZ (hc : CertificateHolds (n - 1) ε δ c) {S : Set (E n)}
    (hS : ∀ x ∈ S, x ≠ 0 ∧ ContDiffAt ℝ ∞ u (radialProj x) ∧ 0 < fluxW u x) :
    ContDiffOn ℝ ∞ (fluxZ c u) S := fun x hx ↦
  (contDiffAt_fluxZ hc (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2).contDiffWithinAt

/-- **Smoothness of `h` on a set.** -/
theorem contDiffOn_fluxH (hc : CertificateHolds (n - 1) ε δ c) {S : Set (E n)}
    (hS : ∀ x ∈ S, x ≠ 0 ∧ ContDiffAt ℝ ∞ u (radialProj x) ∧ 0 < fluxW u x ∧ fluxF c u x ≠ 0) :
    ContDiffOn ℝ ∞ (fluxH c u) S := fun x hx ↦
  (contDiffAt_fluxH hc (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2.1 (hS x hx).2.2.2).contDiffWithinAt

end Smooth

/-! ### Locality -/

section Locality

variable {c : Coeffs (n - 1)} {ε δ : ℝ} {u v : E n → ℝ} {x : E n}

theorem frameData_congr (h : u =ᶠ[𝓝 (radialProj x)] v) (ι : E (n - 1) →ₗᵢ[ℝ] E n) :
    frameT u ι (radialProj x) = frameT v ι (radialProj x) ∧
      frameB u ι (radialProj x) = frameB v ι (radialProj x) ∧
      frameP u ι (radialProj x) = frameP v ι (radialProj x) ∧
      u (radialProj x) = v (radialProj x) := by
  refine ⟨?_, ?_, ?_, h.eq_of_nhds⟩
  · funext i j; simp only [frameT, (h.iteratedFDeriv ℝ 2).eq_of_nhds]
  · funext i j k; simp only [frameB, (h.iteratedFDeriv ℝ 3).eq_of_nhds]
  · funext i; simp only [frameP, h.fderiv_eq]

/-- The fields at `x` depend only on the germ of `u` at `x/|x|`. This transfers smoothness to
regular boundary points, through a smooth chart `F` with `u = F` on the positive side. -/
theorem fluxZ_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxZ c u x = fluxZ c v x := by
  obtain ⟨h1, h2, h3, h4⟩ := frameData_congr h (sphereFrame (radialProj x))
  simp only [fluxZ, h1, h2, h3, h4]

theorem fluxH_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxH c u x = fluxH c v x := by
  obtain ⟨h1, -, h3, h4⟩ := frameData_congr h (sphereFrame (radialProj x))
  simp only [fluxH, h1, h3, h4]

theorem fluxW_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxW u x = fluxW v x := by
  obtain ⟨h1, -, -, -⟩ := frameData_congr h (sphereFrame (radialProj x))
  simp only [fluxW, h1]

theorem fluxF_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxF c u x = fluxF c v x := by
  obtain ⟨h1, -, h3, h4⟩ := frameData_congr h (sphereFrame (radialProj x))
  simp only [fluxF, h1, h3, h4]

end Locality

end Gen

/-! ### Dimension six -/

section Six

/-- The third derivative read in the frame of `ι`: `B_{ijk} = D³u(y)[τᵢ, τⱼ, τ_k]`. -/
def frameB (u : E 6 → ℝ) (ι : E (6 - 1) →ₗᵢ[ℝ] E 6) (y : E 6) : Ten3 := Gen.frameB u ι y

/-- The orthonormal frame of `y^⊥` used to define the fields at a unit vector `y`. -/
def sphereFrame (y : E 6) : E (6 - 1) →ₗᵢ[ℝ] E 6 := Gen.sphereFrame y

theorem inner_sphereFrame {y : E 6} (hy : ‖y‖ = 1) (v : E (6 - 1)) :
    ⟪sphereFrame y v, y⟫ = 0 :=
  Gen.inner_sphereFrame hy v

/-- The scalar `w = |T|` at `x/|x|` (zero at the origin). -/
def fluxW (u : E 6 → ℝ) (x : E 6) : ℝ := Gen.fluxW u x

theorem fluxW_nonneg (u : E 6 → ℝ) (x : E 6) : 0 ≤ fluxW u x := Gen.fluxW_nonneg u x

/-- The scalar flux field `h = w^a √f(A, p, g)` at `x/|x|` (zero at the origin). -/
def fluxH (c : Coeffs) (u : E 6 → ℝ) (x : E 6) : ℝ := Gen.fluxH (n := 6) c.toGen u x

/-- The coefficient `f(A, p, g)` at `x/|x|` (zero at the origin). -/
def fluxF (c : Coeffs) (u : E 6 → ℝ) (x : E 6) : ℝ := Gen.fluxF (n := 6) c.toGen u x

/-- The flux vector field `Z = ∑_l w^{2a}(G_{lijk}X_{ijk} + w M_l + P_l) τ_l` at `x/|x|` (zero at
the origin). -/
def fluxZ (c : Coeffs) (u : E 6 → ℝ) (x : E 6) : E 6 := Gen.fluxZ (n := 6) c.toGen u x

theorem isZeroHomogeneous_fluxW (u : E 6 → ℝ) : IsZeroHomogeneous (fluxW u) :=
  Gen.isZeroHomogeneous_fluxW u

theorem isZeroHomogeneous_fluxH (c : Coeffs) (u : E 6 → ℝ) : IsZeroHomogeneous (fluxH c u) :=
  Gen.isZeroHomogeneous_fluxH (n := 6) c.toGen u

theorem isZeroHomogeneous_fluxF (c : Coeffs) (u : E 6 → ℝ) : IsZeroHomogeneous (fluxF c u) :=
  Gen.isZeroHomogeneous_fluxF (n := 6) c.toGen u

theorem isZeroHomogeneous_fluxZ (c : Coeffs) (u : E 6 → ℝ) : IsZeroHomogeneous (fluxZ c u) :=
  Gen.isZeroHomogeneous_fluxZ (n := 6) c.toGen u

/-- `Z` is tangential: `⟪x, Z(x)⟫ = 0`. -/
theorem isTangentialField_fluxZ (c : Coeffs) (u : E 6 → ℝ) : IsTangentialField (fluxZ c u) :=
  Gen.isTangentialField_fluxZ (n := 6) c.toGen u

/-- The transported Hessian as a two-tensor. -/
def transTData (u : E 6 → ℝ) (x₀ : E 6) (ι : E (6 - 1) →ₗᵢ[ℝ] E 6) (x : E 6) : Ten2 :=
  Gen.transTData u x₀ ι x

/-- The transported third derivative as a three-tensor. -/
def transBData (u : E 6 → ℝ) (x₀ : E 6) (ι : E (6 - 1) →ₗᵢ[ℝ] E 6) (x : E 6) : Ten3 :=
  Gen.transBData u x₀ ι x

/-- The transported gradient as a vector. -/
def transPData (u : E 6 → ℝ) (x₀ : E 6) (ι : E (6 - 1) →ₗᵢ[ℝ] E 6) (x : E 6) : Ten1 :=
  Gen.transPData u x₀ ι x

variable {c : Coeffs} {u : E 6 → ℝ} {x₀ x : E 6} {ι : E (6 - 1) →ₗᵢ[ℝ] E 6}

theorem fluxF_eq_transported (hx₀ : ‖x₀‖ = 1) (hx : x ≠ 0) (hne : ⟪x₀, radialProj x⟫ ≠ -1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (hc : CertificateHolds c) :
    fluxF c u x = c.f (normalizedA (transTData u x₀ ι x), transPData u x₀ ι x, transG u x) :=
  Gen.fluxF_eq_transported hx₀ hx hne hι hc.toGen

theorem fluxW_eq_transported (hx₀ : ‖x₀‖ = 1) (hx : x ≠ 0) (hne : ⟪x₀, radialProj x⟫ ≠ -1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : fluxW u x = normW (transTData u x₀ ι x) :=
  Gen.fluxW_eq_transported hx₀ hx hne hι

theorem contDiff_sq2 : ContDiff ℝ ∞ (sq2 : Ten2 → ℝ) := Gen.contDiff_sq2

theorem normW_pos_iff {T : Ten2} : 0 < normW T ↔ sq2 T ≠ 0 := Gen.normW_pos_iff

/-- The normalized data `(A, p, g)` as a smooth function of the frame data. -/
theorem contDiffAt_normalizedData {d : Ten2 × Ten3 × Ten1 × ℝ} (h : sq2 d.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun d : Ten2 × Ten3 × Ten1 × ℝ ↦ (normalizedA d.1, d.2.2.1, d.2.2.2)) d :=
  Gen.contDiffAt_normalizedData h

/-- The transported frame data `(T, B, p, g)` are smooth. -/
theorem contDiffAt_transData (hu : ContDiffAt ℝ ∞ u (radialProj x)) (hx : x ≠ 0)
    (hne : ⟪x₀, radialProj x⟫ ≠ -1) :
    ContDiffAt ℝ ∞ (fun x ↦ (transTData u x₀ ι x, transBData u x₀ ι x, transPData u x₀ ι x,
      transG u x)) x :=
  Gen.contDiffAt_transData hu hx hne

/-- **Smoothness of `w`** at `x ≠ 0` with `w(x) > 0`, if `u` is smooth at `x/|x|`. -/
theorem contDiffAt_fluxW (hx : x ≠ 0) (hu : ContDiffAt ℝ ∞ u (radialProj x))
    (hw : 0 < fluxW u x) : ContDiffAt ℝ ∞ (fluxW u) x :=
  Gen.contDiffAt_fluxW hx hu hw

/-- **Smoothness of `Z`** at `x ≠ 0` with `w(x) > 0`, if `u` is smooth at `x/|x|`. -/
theorem contDiffAt_fluxZ (hc : CertificateHolds c) (hx : x ≠ 0)
    (hu : ContDiffAt ℝ ∞ u (radialProj x)) (hw : 0 < fluxW u x) :
    ContDiffAt ℝ ∞ (fluxZ c u) x :=
  Gen.contDiffAt_fluxZ hc.toGen hx hu hw

/-- **Smoothness of `h`** at `x ≠ 0` with `w(x) > 0` and `f(x) ≠ 0`, if `u` is smooth at
`x/|x|`. -/
theorem contDiffAt_fluxH (hc : CertificateHolds c) (hx : x ≠ 0)
    (hu : ContDiffAt ℝ ∞ u (radialProj x)) (hw : 0 < fluxW u x) (hf : fluxF c u x ≠ 0) :
    ContDiffAt ℝ ∞ (fluxH c u) x :=
  Gen.contDiffAt_fluxH hc.toGen hx hu hw hf

variable {v : E 6 → ℝ}

theorem fluxZ_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxZ c u x = fluxZ c v x :=
  Gen.fluxZ_congr h

theorem fluxH_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxH c u x = fluxH c v x :=
  Gen.fluxH_congr h

theorem fluxW_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxW u x = fluxW v x :=
  Gen.fluxW_congr h

theorem fluxF_congr (h : u =ᶠ[𝓝 (radialProj x)] v) : fluxF c u x = fluxF c v x :=
  Gen.fluxF_congr h

end Six

end OnePhaseDimension
