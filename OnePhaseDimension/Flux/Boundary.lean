/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Flux.Parity
public import OnePhaseDimension.Flux.Fields
public import OnePhaseDimension.Geometry.GradientBoundSuspension

/-!
# The signed boundary flux

At a unit point `x₀` of the free boundary, read through a smooth chart `F` (`u = max F 0` near
`x₀`, `F(x₀) = 0`, `|∇F| = 1` on `{F = 0}`), the boundary model is `g = 0`, `p = N`, `|p| = 1`,
`Ap = λp` with `λ = -H/w < 0`, where `N = ∇F(x₀)` is the inward normal and
`H = -D²F(x₀)[N, N]` the mean curvature. The fields `Z = Z[F]`, `h = h[F]` built from the jets of
`F` satisfy

  `N·Z + H h² = w^{2a+1} 𝓢(A, p, λ) ≥ δ w^{2a+1}`,

where `𝓢` is the boundary polynomial of a certificate in `ℝ^{n-1}` with constants `ε > 0`, `δ`
(`IsBoundaryJet.boundary_signed_flux_eq`, `IsBoundaryJet.boundary_signed_flux_ge`). Nothing here
depends on the dimension.

The fields of `F` are the boundary values of the fields of `u`: at every `x` with `x/|x| ∈ D` in
the chart domain, `Z[u](x) = Z[F](x)` and `h[u](x) = h[F](x)` (`ConeData.fluxZ_eq_of_chart`), and
`Z[F]`, `h[F]` are smooth near `x₀` because `w > 0` there. With the boundary signs `H > 0`,
`w > 0`, `λ < 0` proved for original cones and suspensions, this gives the main results
`Gen.ConeData.boundary_signed_flux_pos` (every `n`), and in `ℝ⁶` with `δ = δ*`
`ConeData.boundary_signed_flux_pos` and `IsSuspension.boundary_signed_flux_pos`, in the form

  `⟪Z, ∇F⟫ - D²F[∇F, ∇F] h² ≥ δ w^{2a+1}`, `w > 0`.

## Differences from the source

The 2026-09-24 version evaluates the fields at the side boundary as limits from the positive side.
We evaluate the fields of the chart function `F` at the boundary point; they agree with the fields
of `u` on the positive side by locality.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Finset Filter Topology EllipticBernoulli
open scoped RealInnerProductSpace ContDiff Gradient Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

/-! ### The fields at a boundary jet -/

namespace ConeJets.IsBoundaryJet

variable {n : ℕ} {F : E n → ℝ} {J : ConeJets n} (h : IsBoundaryJet F J)
include h

theorem x₀_ne_zero : J.x₀ ≠ 0 := by
  intro h0
  have := h.isConeJet.norm_x₀
  rw [h0, norm_zero] at this
  norm_num at this

theorem radialProj_x₀ : radialProj J.x₀ = J.x₀ := radialProj_of_norm_eq_one h.isConeJet.norm_x₀

theorem inner_ι_radialProj (v : E (n - 1)) : ⟪J.ι v, radialProj J.x₀⟫ = 0 := by
  rw [h.radialProj_x₀]
  exact h.isConeJet.inner_ι v

theorem frameT_eq : Gen.frameT F J.ι J.x₀ = J.T := by
  funext i j
  exact (h.isConeJet.T_eq i j).symm

theorem frameB_eq : Gen.frameB F J.ι J.x₀ = J.B := by
  funext i j k
  exact (h.isConeJet.B_eq i j k).symm

theorem frameP_eq : Gen.frameP F J.ι J.x₀ = J.p := by
  funext i
  exact (h.isConeJet.p_eq i).symm

theorem fluxW_eq : Gen.fluxW F J.x₀ = J.w := by
  rw [Gen.fluxW_eq_of_frame h.x₀_ne_zero h.inner_ι_radialProj, h.radialProj_x₀, h.frameT_eq]
  rfl

variable {c : Gen.Coeffs (n - 1)} {ε δ : ℝ} (hc : Gen.CertificateHolds (n - 1) ε δ c)
include hc

/-- `Z(x₀) = ∑ Z_l τ_l` with the components computed from the jets of `F`. -/
theorem fluxZ_eq_frameMap : Gen.fluxZ c F J.x₀ = frameMap J.ι (c.fluxZComp J.T J.B J.p J.g) := by
  rw [Gen.fluxZ_eq_of_frame hc h.x₀_ne_zero h.inner_ι_radialProj, h.radialProj_x₀, h.frameT_eq,
    h.frameB_eq, h.frameP_eq, ← h.isConeJet.g_eq, frameMap]

theorem fluxH_eq : Gen.fluxH c F J.x₀ = c.fluxHComp J.T J.p J.g := by
  rw [Gen.fluxH_eq_of_frame hc h.x₀_ne_zero h.inner_ι_radialProj, h.radialProj_x₀, h.frameT_eq,
    h.frameP_eq, ← h.isConeJet.g_eq]

variable (hw : 0 < J.w)
include hw

omit h hc hw in
theorem normalizedA_T : Gen.normalizedA J.T = J.A := rfl

omit h hc hw in
theorem normW_T : Gen.normW J.T = J.w := rfl

omit h hc hw in
theorem normalizedX_T_B : Gen.normalizedX J.T J.B = fun i j k ↦ J.B i j k / J.w := rfl

theorem f_ge : ε ≤ c.f (J.A, J.p, 0) :=
  hc.f_ge _ _ _ h.isSTF2_A (sum_A_sq hw) (by rw [h.sq1_p]; norm_num)

/-- **The normal flux**:
`N·Z = w^{2a+1}(U_{jk}(S₀ + p ⊗ p)_{jk} + C_{lijk} p_l V_{ijk} + p_l M_l)`. -/
theorem inner_fluxZ_gradient :
    ⟪Gen.fluxZ c F J.x₀, ∇ F J.x₀⟫ = J.w ^ (2 * aExp + 1) *
      (∑ j, ∑ k, c.U (J.A, J.p, 0) j k * (J.S₀ j k + J.p j * J.p k) +
        ∑ l, ∑ i, ∑ j, ∑ k, c.C (J.A, J.p, 0) l i j k * J.p l * J.V i j k +
          ∑ l, J.p l * c.M (J.A, J.p, 0) l) := by
  rw [h.fluxZ_eq_frameMap hc, h.gradient_eq, inner_frameMap_frameMap]
  simp only [Gen.Coeffs.fluxZComp, normalizedX_T_B, normalizedA_T, normW_T, h.g_eq_zero,
    hc.P_g_zero, Pi.zero_apply, add_zero, Gen.Coeffs.contractG_div]
  set w := J.w
  have hw0 : w ≠ 0 := hw.ne'
  have e : ∑ i, w ^ (2 * aExp) * (c.contractG (J.A, J.p, 0) J.B i / w +
      w * c.M (J.A, J.p, 0) i) * J.p i =
      w ^ (2 * aExp) / w * ∑ i, J.p i * c.contractG (J.A, J.p, 0) J.B i +
        w ^ (2 * aExp) * w * ∑ i, J.p i * c.M (J.A, J.p, 0) i := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by field_simp
  rw [e, h.boundary_contraction_eq_V hw hc, Real.rpow_add_one hw0]
  field_simp
  ring

/-- `h² = w^{2a} f(A, p, 0)`. -/
theorem fluxH_sq (hε : 0 < ε) : Gen.fluxH c F J.x₀ ^ 2 = J.w ^ (2 * aExp) * c.f (J.A, J.p, 0) := by
  rw [h.fluxH_eq hc, Gen.Coeffs.fluxHComp, normalizedA_T, normW_T, h.g_eq_zero,
    mul_pow, Real.sq_sqrt (hε.le.trans (h.f_ge hc hw)), ← Real.rpow_natCast,
    ← Real.rpow_mul J.w_nonneg]
  ring_nf

/-- **The signed boundary identity** `N·Z + H h² = w^{2a+1} 𝓢`, with `H = -D²F(x₀)[N, N]`. -/
theorem boundary_signed_flux_eq (hε : 0 < ε) :
    ⟪Gen.fluxZ c F J.x₀, ∇ F J.x₀⟫ -
        iteratedFDeriv ℝ 2 F J.x₀ ![∇ F J.x₀, ∇ F J.x₀] * Gen.fluxH c F J.x₀ ^ 2 =
      J.w ^ (2 * aExp + 1) * c.boundaryExpr J.A J.p J.lam := by
  have hS : Gen.Coeffs.bdryS0 J.A J.lam = J.S₀ := rfl
  have hV : Gen.Coeffs.bdryV J.A J.p J.lam = J.V := rfl
  have hT : J.Tpp = J.w * J.lam := by rw [ConeJets.lam, mul_div_cancel₀ _ hw.ne']
  rw [h.inner_fluxZ_gradient hc hw, ← h.Tpp_eq, h.fluxH_sq hc hw hε, hT,
    Real.rpow_add_one hw.ne', Gen.Coeffs.boundaryExpr, hS, hV]
  ring

/-- **The boundary comparison** `N·Z + H h² ≥ δ w^{2a+1}`, given `λ < 0`. -/
theorem boundary_signed_flux_ge (hε : 0 < ε) (hlam : J.lam < 0) :
    δ * J.w ^ (2 * aExp + 1) ≤ ⟪Gen.fluxZ c F J.x₀, ∇ F J.x₀⟫ -
        iteratedFDeriv ℝ 2 F J.x₀ ![∇ F J.x₀, ∇ F J.x₀] * Gen.fluxH c F J.x₀ ^ 2 := by
  rw [h.boundary_signed_flux_eq hc hw hε]
  have hS := hc.boundary J.A J.p J.lam h.isSTF2_A (sum_A_sq hw) h.sq1_p h.A_mulVec_p hlam
  have hpos : 0 < J.w ^ (2 * aExp + 1) := Real.rpow_pos_of_pos hw _
  nlinarith

end ConeJets.IsBoundaryJet

/-! ### Locality: the chart fields are the boundary values -/

namespace ConeData

variable {n : ℕ} {C : ConeData n} {c : Gen.Coeffs (n - 1)} {U : Set (E n)} {F : E n → ℝ}
  {x : E n}

/-- On the positive side of a chart, `Z[u] = Z[F]`. -/
theorem fluxZ_eq_of_chart (hU : IsOpen U) (hu : ∀ y ∈ U, C.u y = max (F y) 0)
    (hxU : radialProj x ∈ U) (hxD : radialProj x ∈ C.D) : Gen.fluxZ c C.u x = Gen.fluxZ c F x :=
  Gen.fluxZ_congr (chart_eventuallyEq hU hu hxU hxD)

/-- On the positive side of a chart, `h[u] = h[F]`. -/
theorem fluxH_eq_of_chart (hU : IsOpen U) (hu : ∀ y ∈ U, C.u y = max (F y) 0)
    (hxU : radialProj x ∈ U) (hxD : radialProj x ∈ C.D) : Gen.fluxH c C.u x = Gen.fluxH c F x :=
  Gen.fluxH_congr (chart_eventuallyEq hU hu hxU hxD)

/-- On the positive side of a chart, `w[u] = w[F]`. -/
theorem fluxW_eq_of_chart (hU : IsOpen U) (hu : ∀ y ∈ U, C.u y = max (F y) 0)
    (hxU : radialProj x ∈ U) (hxD : radialProj x ∈ C.D) : Gen.fluxW C.u x = Gen.fluxW F x :=
  Gen.fluxW_congr (chart_eventuallyEq hU hu hxU hxD)

end ConeData

/-! ### The boundary comparison on the working cones -/

namespace Gen

variable {n : ℕ}

/-- The boundary comparison at a unit boundary point read through a chart, given the boundary
signs `w > 0` and `λ < 0` of the jet record of `F` at `x₀`. -/
theorem boundary_signed_flux_ge_of_chart {c : Coeffs (n - 1)} {ε δ : ℝ}
    (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) {F : E n → ℝ} {x₀ : E n}
    (hJ : ConeJets.IsBoundaryJet F (ConeJets.ofFun F x₀ (sphereFrame x₀)))
    (hw : 0 < (ConeJets.ofFun F x₀ (sphereFrame x₀)).w)
    (hlam : (ConeJets.ofFun F x₀ (sphereFrame x₀)).lam < 0) :
    0 < fluxW F x₀ ∧ δ * fluxW F x₀ ^ (2 * aExp + 1) ≤
      ⟪fluxZ c F x₀, ∇ F x₀⟫ - iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] * fluxH c F x₀ ^ 2 := by
  have hW : fluxW F x₀ = (ConeJets.ofFun F x₀ (sphereFrame x₀)).w := hJ.fluxW_eq
  rw [hW]
  exact ⟨hw, hJ.boundary_signed_flux_ge hc hw hε hlam⟩

namespace ConeData

variable {C : OnePhaseDimension.ConeData n} (hS : C.Sing = {0}) {c : Coeffs (n - 1)} {ε δ : ℝ}
  (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) {U : Set (E n)} {F : E n → ℝ} {x₀ : E n}
include hS hc hε

/-- **The boundary comparison on an original cone.** At every unit point `x₀ ∈ closure D \ D`
and for every chart `F` at `x₀`, with `N = ∇F(x₀)` and `H = -D²F(x₀)[N, N]`, the fields of `F`
satisfy `w > 0` and `N·Z + H h² ≥ δ w^{2a+1}`. -/
theorem boundary_signed_flux_pos (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) :
    0 < fluxW F x₀ ∧ δ * fluxW F x₀ ^ (2 * aExp + 1) ≤
      ⟪fluxZ c F x₀, ∇ F x₀⟫ - iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] * fluxH c F x₀ ^ 2 :=
  boundary_signed_flux_ge_of_chart hc hε
    (OnePhaseDimension.ConeData.isBoundaryJet_chart hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁
      (inner_sphereFrame hx₁))
    (C.boundary_w_pos hS hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ (inner_sphereFrame hx₁))
    (C.boundary_lam_neg hS hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ (inner_sphereFrame hx₁))

/-- **Sign of the boundary flux on an original cone**: `N·Z + H h² ≥ 0`, given `δ ≥ 0`. -/
theorem boundary_signed_flux_nonneg (hδ : 0 ≤ δ) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) :
    0 ≤ ⟪fluxZ c F x₀, ∇ F x₀⟫ - iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] * fluxH c F x₀ ^ 2 := by
  obtain ⟨hw, hge⟩ := boundary_signed_flux_pos hS hc hε hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁
  exact le_trans (mul_nonneg hδ (Real.rpow_nonneg hw.le _)) hge

end ConeData

end Gen

/-! ### Dimension six -/

namespace ConeData

variable {C : ConeData 6} (hS : C.Sing = {0}) {c : Coeffs} (hc : CertificateHolds c)
  {U : Set (E 6)} {F : E 6 → ℝ} {x₀ : E 6}
include hS hc

/-- **The boundary comparison on an original cone.** At every unit point `x₀ ∈ closure D \ D`
and for every chart `F` at `x₀`, with `N = ∇F(x₀)` and `H = -D²F(x₀)[N, N]`, the fields of `F`
satisfy `w > 0` and `N·Z + H h² ≥ δ* w^{2a+1}`. -/
theorem boundary_signed_flux_pos (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) :
    0 < fluxW F x₀ ∧ δStar * fluxW F x₀ ^ (2 * aExp + 1) ≤
      ⟪fluxZ c F x₀, ∇ F x₀⟫ - iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] * fluxH c F x₀ ^ 2 :=
  Gen.ConeData.boundary_signed_flux_pos hS hc.toGen εStar_pos hU hx₀U hF hu hD hgrad hΔ hx₀
    hx₀D hx₁

/-- **Sign of the boundary flux on an original cone**: `N·Z + H h² ≥ 0`. -/
theorem boundary_signed_flux_nonneg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) :
    0 ≤ ⟪fluxZ c F x₀, ∇ F x₀⟫ - iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] * fluxH c F x₀ ^ 2 :=
  Gen.ConeData.boundary_signed_flux_nonneg hS hc.toGen εStar_pos δStar_pos.le hU hx₀U hF hu hD
    hgrad hΔ hx₀ hx₀D hx₁

end ConeData

namespace IsSuspension

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
  {c : Coeffs} (hc : CertificateHolds c) {U : Set (E 6)} {F : E 6 → ℝ} {x₀ : E 6}
include hW hO hc

/-- **The boundary comparison on a suspension.** At every unit point `x₀ ∈ closure D̃ \ D̃` and
for every chart `F̃` at `x₀`, `w̃ > 0` and `Ñ·Z̃ + H̃ h̃² ≥ δ* w̃^{2a+1}`. -/
theorem boundary_signed_flux_pos (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, W.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ W.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure W.D) (hx₀D : x₀ ∉ W.D) (hx₁ : ‖x₀‖ = 1) :
    0 < fluxW F x₀ ∧ δStar * fluxW F x₀ ^ (2 * aExp + 1) ≤
      ⟪fluxZ c F x₀, ∇ F x₀⟫ - iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] * fluxH c F x₀ ^ 2 :=
  Gen.boundary_signed_flux_ge_of_chart (n := 6) hc.toGen εStar_pos
    (ConeData.isBoundaryJet_chart hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ (inner_sphereFrame hx₁))
    (hW.w_pos hO hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ (inner_sphereFrame hx₁))
    (hW.lam_neg hO hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ (inner_sphereFrame hx₁))

/-- **Sign of the boundary flux on a suspension**: `Ñ·Z̃ + H̃ h̃² ≥ 0`. -/
theorem boundary_signed_flux_nonneg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, W.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ W.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure W.D) (hx₀D : x₀ ∉ W.D) (hx₁ : ‖x₀‖ = 1) :
    0 ≤ ⟪fluxZ c F x₀, ∇ F x₀⟫ - iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] * fluxH c F x₀ ^ 2 := by
  obtain ⟨hw, hge⟩ := hW.boundary_signed_flux_pos hO hc hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁
  exact le_trans (mul_nonneg δStar_pos.le (Real.rpow_nonneg hw.le _)) hge

end IsSuspension

end OnePhaseDimension
