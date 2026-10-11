/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Component
public import OnePhaseDimension.Geometry.Suspension
public import OnePhaseDimension.Reduction.Translation
public import OnePhaseDimension.Reduction.Isometry
public import OnePhaseDimension.Reduction.SuspensionMinimality
public import OnePhaseDimension.Reduction.FactorMinimality

/-!
# From a first nonflat minimizer to a working cone

Let `d ∈ {5, 6}`, assume that every nonzero, nonnegative, one-homogeneous global minimizer in
`ℝ^{d-1}` is flat, and let `u` be a continuous, nonnegative, nonzero, one-homogeneous global
minimizer in `ℝᵈ` that is not flat. Then:

* `ConeData.ofFirstNonflat`: `u`, together with a component of `{u > 0}` on which `D²u ≢ 0` and
  the singular set `{0}`, is a cone in the sense of `ConeData`;
* `ConeData.suspend`: the suspension `W = O × ℝ` of a cone `O` in `ℝ⁵` with `O.Sing = {0}`,
  `W.u = O.u ∘ π` with `π` dropping the last coordinate, is a cone in `ℝ⁶` with singular set the
  axis `π⁻¹{0}` (`isSuspension_suspend`);
* `exists_workingCone`: a working cone exists, the original cone if `d = 6` and its suspension
  if `d = 5`.

## Differences from the source

* The 2026-09-24 version describes the suspended component on `S⁵` in the coordinates
  `(t, y) ↦ (sin t y, cos t)` and identifies its singular tips. We work with the Euclidean
  component `π⁻¹ D_o` and product charts `F ∘ π`; the singular set is the axis `π⁻¹{0}`. That
  the axis points are not regular is not needed.
* Global minimality of the suspension, of the factor of a translation-invariant blowup, and of
  isometric images, and the translation invariance of blowups, are used through the
  propositions of `OnePhaseDimension.Reduction.Regular`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### The original cone -/

/-- **The original cone.** A continuous, nonnegative, nonzero, one-homogeneous global minimizer
`u` in `ℝ^{k+1}`, `k ≥ 1`, that is not flat, when minimizers in `ℝᵏ` are flat, with a component
of `{u > 0}` on which `D²u ≢ 0` and the singular set `{0}`. -/
def ConeData.ofFirstNonflat (hR : ReductionInputs) {k : ℕ} (hk : 1 ≤ k) (hlow : FlatInDim k)
    (u : E (k + 1) → ℝ) (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) (hpos : ∃ x, 0 < u x)
    (hnf : ¬ FlatAE u) : ConeData (k + 1) :=
  let hx := exists_pos_iteratedFDeriv_ne_zero hR hk hlow hc hnn hmin hhom hpos hnf
  { u := u
    nonneg := hnn
    continuous := hc
    homog := hhom
    minimizer := hmin
    base := hx.choose
    base_pos := hx.choose_spec.1
    D := connectedComponentIn {x | 0 < u x} hx.choose
    D_eq := rfl
    Sing := {0}
    sing_closed := isClosed_singleton
    zero_mem_sing := rfl
    sing_smul := by
      rintro r - x rfl
      exact smul_zero r
    chart := fun _ hx₀ ↦ chart_of_mem_closure hR hk hlow hc hnn hmin hhom hx₀.1 hx₀.2
    nonflat := ⟨hx.choose, mem_connectedComponentIn (show hx.choose ∈ {x | 0 < u x} from
      hx.choose_spec.1), hx.choose_spec.2⟩ }

/-! ### The suspension -/

section Suspension

/-- `z = π†(π z) + z₆ e₆` in `ℝ⁶`. -/
theorem dropLast_adjoint_add_smul_lastVec (z : E 6) :
    dropLast.adjoint (dropLast z) + z (Fin.last 5) • lastVec 5 = z :=
  adjoint_projInit_add_smul_lastVec (k := 5) z

/-- The components of the suspended positive phase are the suspended components:
`π⁻¹(cc_S(b)) = cc_{π⁻¹ S}(π† b)`. -/
theorem preimage_dropLast_connectedComponentIn {S : Set (E 5)} {b : E 5} (hb : b ∈ S) :
    dropLast ⁻¹' connectedComponentIn S b =
      connectedComponentIn (dropLast ⁻¹' S) (dropLast.adjoint b) := by
  have hπb : dropLast (dropLast.adjoint b) = b := dropLast_adjoint_apply b
  have hπl : dropLast (lastVec 5) = 0 := projInit_lastVec (k := 5)
  refine Subset.antisymm (fun z hz ↦ ?_) ?_
  · -- the suspended component is preconnected
    set g : E 5 × ℝ → E 6 := fun q ↦ dropLast.adjoint q.1 + q.2 • lastVec 5 with hg
    have hgc : Continuous g := by fun_prop
    have hπg : ∀ q, dropLast (g q) = q.1 := fun q ↦ by
      simp only [hg, map_add, map_smul, hπl, smul_zero, add_zero, dropLast_adjoint_apply]
    have hA : IsPreconnected (g '' (connectedComponentIn S b ×ˢ univ)) :=
      (isPreconnected_connectedComponentIn.prod isPreconnected_univ).image _ hgc.continuousOn
    have hAS : g '' (connectedComponentIn S b ×ˢ univ) ⊆ dropLast ⁻¹' S := by
      rintro _ ⟨q, hq, rfl⟩
      change dropLast (g q) ∈ S
      rw [hπg]
      exact connectedComponentIn_subset _ _ hq.1
    have hbA : dropLast.adjoint b ∈ g '' (connectedComponentIn S b ×ˢ univ) :=
      ⟨(b, 0), ⟨mem_connectedComponentIn hb, mem_univ _⟩, by simp [hg]⟩
    have hzA : z ∈ g '' (connectedComponentIn S b ×ˢ univ) :=
      ⟨(dropLast z, z (Fin.last 5)), ⟨hz, mem_univ _⟩, dropLast_adjoint_add_smul_lastVec z⟩
    exact hA.subset_connectedComponentIn hbA hAS hzA
  · -- the projection of the component of the suspension is preconnected
    intro z hz
    have hK : IsPreconnected
        (dropLast '' connectedComponentIn (dropLast ⁻¹' S) (dropLast.adjoint b)) :=
      isPreconnected_connectedComponentIn.image _ dropLast.continuous.continuousOn
    have hKS : dropLast '' connectedComponentIn (dropLast ⁻¹' S) (dropLast.adjoint b) ⊆ S := by
      rintro _ ⟨y, hy, rfl⟩
      exact (connectedComponentIn_subset (dropLast ⁻¹' S) _ hy : y ∈ dropLast ⁻¹' S)
    have hbK : b ∈ dropLast '' connectedComponentIn (dropLast ⁻¹' S) (dropLast.adjoint b) :=
      ⟨dropLast.adjoint b, mem_connectedComponentIn (show dropLast (dropLast.adjoint b) ∈ S by
        rw [hπb]; exact hb), hπb⟩
    exact hK.subset_connectedComponentIn hbK hKS ⟨z, hz, rfl⟩

/-- `Δ(F ∘ π)(z) = ΔF(π z)`. -/
theorem laplacian_comp_dropLast {U : Set (E 5)} (hU : IsOpen U) {F : E 5 → ℝ}
    (hF : ContDiffOn ℝ 2 F U) {z : E 6} (hz : dropLast z ∈ U) :
    Δ (F ∘ dropLast) z = Δ F (dropLast z) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin 6) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin 5) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [iteratedFDeriv_two_comp_dropLast hU hF hz, dropLast_single_castSucc,
    dropLast_single_last]
  rw [ContinuousMultilinearMap.map_coord_zero _ (0 : Fin 2) (by simp), add_zero]

variable (hsusp : SuspensionMinimality) (O : ConeData 5) (hO : O.Sing = {0})

/-- **The suspension** `W = O × ℝ` of a cone `O` in `ℝ⁵` with `O.Sing = {0}`: `W.u = O.u ∘ π`,
`W.D = π⁻¹ O.D`, and `W.Sing = π⁻¹{0}` is the axis. -/
def ConeData.suspend : ConeData 6 where
  u := O.u ∘ dropLast
  nonneg := fun _ ↦ O.nonneg _
  continuous := O.continuous.comp dropLast.continuous
  homog := fun r hr x ↦ by
    simp only [Function.comp_apply, map_smul, O.homog r hr]
  minimizer := hsusp O.nonneg O.minimizer
  base := dropLast.adjoint O.base
  base_pos := by
    simp only [Function.comp_apply, dropLast_adjoint_apply]
    exact O.base_pos
  D := dropLast ⁻¹' O.D
  D_eq := by
    rw [O.D_eq, preimage_dropLast_connectedComponentIn (show O.base ∈ {x | 0 < O.u x} from
      O.base_pos)]
    rfl
  Sing := dropLast ⁻¹' {0}
  sing_closed := isClosed_singleton.preimage dropLast.continuous
  zero_mem_sing := by simp
  sing_smul := by
    intro r _ x hx
    simp only [mem_preimage, mem_singleton_iff, map_smul] at hx ⊢
    rw [hx, smul_zero]
  chart := by
    rintro z ⟨hzD, hzS⟩
    have hz1 : dropLast z ∈ closure O.D :=
      map_mem_closure dropLast.continuous hzD (fun _ hx ↦ hx)
    have hz2 : dropLast z ∉ O.Sing := by
      rw [hO]
      exact hzS
    obtain ⟨U, hU, hzU, F, hF, hu, hD, hgrad, hΔ⟩ := O.chart _ ⟨hz1, hz2⟩
    have hF2 : ContDiffOn ℝ 2 F U := hF.of_le (natCast_le_infty 2)
    refine ⟨dropLast ⁻¹' U, hU.preimage dropLast.continuous, hzU, F ∘ dropLast,
      hF.comp_continuousLinearMap dropLast, fun x hx ↦ hu _ hx, fun x hx hFx ↦ hD _ hx hFx,
      fun x hx hF0 ↦ ?_, fun x hx hFx ↦ ?_⟩
    · rw [(hessian_gradient_comp_dropLast hU hF2 hx).1]
      exact hgrad _ hx hF0
    · rw [laplacian_comp_dropLast hU hF2 hx]
      exact hΔ _ hx hFx
  nonflat := by
    obtain ⟨x, hxD, hx2⟩ := O.nonflat
    have hπx : dropLast (dropLast.adjoint x) = x := dropLast_adjoint_apply x
    refine ⟨dropLast.adjoint x, show dropLast (dropLast.adjoint x) ∈ O.D by rw [hπx]; exact hxD,
      fun h ↦ hx2 ?_⟩
    have hsm : ContDiffOn ℝ 2 O.u O.D := fun y hy ↦
      ((O.contDiffAt_u hO hy).of_le (natCast_le_infty 2)).contDiffWithinAt
    ext m
    have hm : m = ![m 0, m 1] := by
      funext i
      fin_cases i <;> rfl
    have h' := congrArg (fun M ↦ M ![dropLast.adjoint (m 0), dropLast.adjoint (m 1)]) h
    simp only [zero_apply] at h'
    rw [iteratedFDeriv_two_comp_dropLast O.isOpen_D hsm (by rw [hπx]; exact hxD), hπx,
      dropLast_adjoint_apply, dropLast_adjoint_apply, ← hm] at h'
    simpa using h'

theorem ConeData.suspend_sing : (O.suspend hsusp hO).Sing = dropLast ⁻¹' {0} := rfl

/-- The suspension is a suspension in the sense of `IsSuspension`. -/
theorem isSuspension_suspend : IsSuspension (O.suspend hsusp hO) O :=
  ⟨fun _ ↦ rfl, rfl, rfl⟩

end Suspension

/-! ### The working cone -/

/-- **A first nonflat cone gives a working cone.** Let `d ∈ {5, 6}` and assume that every nonzero,
nonnegative, one-homogeneous global minimizer in `ℝ^{d-1}` is flat. If `u` is a continuous,
nonnegative, one-homogeneous global minimizer in `ℝᵈ`, positive somewhere and not flat, then a
working cone exists: the cone of `u` itself if `d = 6`, its suspension if `d = 5`. This version
takes the inputs from the dimension reduction as a hypothesis. -/
theorem exists_workingCone_of_inputs (hR : ReductionInputs) (d : ℕ) (hd : d = 5 ∨ d = 6)
    (hlow : ∀ v : E (d - 1) → ℝ, (∀ᵐ x ∂(volume : Measure (E (d - 1))), 0 ≤ v x) →
      IsLocalEnergyMinimizer univ (fun _ ↦ 1) v → OneHomogeneousAE v → ¬ v =ᵐ[volume] 0 →
        FlatAE v)
    (u : E d → ℝ) (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) (hpos : ∃ x, 0 < u x)
    (hnf : ¬ FlatAE u) :
    Nonempty WorkingCone := by
  rcases hd with rfl | rfl
  · let O : ConeData 5 :=
      ConeData.ofFirstNonflat hR (k := 4) (by norm_num) hlow u hc hnn hmin hhom hpos hnf
    exact ⟨.susp O rfl (O.suspend hR.suspension rfl) (isSuspension_suspend _ O rfl)⟩
  · exact ⟨.orig (ConeData.ofFirstNonflat hR (k := 5) (by norm_num) hlow u hc hnn hmin hhom
      hpos hnf) rfl⟩

/-! ### Inputs from the dimension reduction (pending) -/

/-- Blowups of one-homogeneous minimizers are invariant along the base point. -/
theorem blowupTranslationInvariance : BlowupTranslationInvariance :=
  blowupTranslationInvariance_holds

/-- The factor of a suspended minimizer is a minimizer. -/
theorem factorMinimality : FactorMinimality :=
  factorMinimality_holds

/-- The suspension of a nonnegative minimizer is a minimizer. -/
theorem suspensionMinimality : SuspensionMinimality :=
  suspensionMinimality_holds

/-- Minimality is invariant under linear isometries. -/
theorem isometryMinimality : IsometryMinimality :=
  isometryMinimality_holds

/-- The inputs from the dimension reduction. -/
theorem reductionInputs : ReductionInputs :=
  ⟨blowupTranslationInvariance, factorMinimality, suspensionMinimality, isometryMinimality⟩

/-- **A first nonflat cone gives a working cone.** Let `d ∈ {5, 6}` and assume that every nonzero,
nonnegative, one-homogeneous global minimizer in `ℝ^{d-1}` is flat. If `u` is a continuous,
nonnegative, one-homogeneous global minimizer in `ℝᵈ`, positive somewhere and not flat, then a
working cone exists: the cone of `u` itself if `d = 6`, its suspension if `d = 5`. -/
theorem exists_workingCone (d : ℕ) (hd : d = 5 ∨ d = 6)
    (hlow : ∀ v : E (d - 1) → ℝ, (∀ᵐ x ∂(volume : Measure (E (d - 1))), 0 ≤ v x) →
      IsLocalEnergyMinimizer univ (fun _ ↦ 1) v → OneHomogeneousAE v → ¬ v =ᵐ[volume] 0 →
        FlatAE v)
    (u : E d → ℝ) (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) (hpos : ∃ x, 0 < u x)
    (hnf : ¬ FlatAE u) :
    Nonempty WorkingCone :=
  exists_workingCone_of_inputs reductionInputs d hd hlow u hc hnn hmin hhom hpos hnf

end OnePhaseDimension
