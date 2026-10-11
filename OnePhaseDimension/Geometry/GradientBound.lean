/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Hopf
public import OnePhaseDimension.Geometry.BoundaryData
public import OnePhaseDimension.Statements.Cone
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple

/-!
# The gradient bound `s² < 1` and positivity of `H` and `w` on the free boundary

Let `C` be a cone whose singular set is the vertex, `C.Sing = {0}`. Put `s² = |∇u|²` on `D`.

* `ConeData.sSq_lt_one`, `ConeData.sSq_le_one`: `|∇u|² < 1` on `D`.
* `ConeData.hessian_gradient_neg`: at a free-boundary point `x₀ ∈ closure D \ D`, `x₀ ≠ 0`, every
  chart `F` has `D²F(x₀)[N, N] < 0` for `N = ∇F(x₀)`, i.e. `H = -D²F(x₀)[N, N] > 0`.
* `ConeData.boundary_Tpp_neg`, `ConeData.boundary_w_pos`, `ConeData.boundary_lam_neg`,
  `ConeData.boundary_T_eigen`: the same at a unit boundary point in the language of jet records:
  `T(p, p) = -H < 0`, `w = |T| ≥ H > 0`, `λ = T(p, p)/w < 0` and `Tp = -H p`.

## Proof

The function `s²` is zero-homogeneous on `D`, subharmonic there (`Δ|∇u|² = 2|D²u|²`), and equals
`|∇F|²` up to the boundary in every chart, with `|∇F| = 1` on `{F = 0}`. So `s²`, extended by `1`
off `D`, is continuous on the compact link `closure D ∩ S^{n-1}` and attains its maximum there.
A maximum point in `D` is, by homogeneity, a maximum point of `s²` over the connected open set `D`;
the strong maximum principle makes `s²` constant on `D`, so `|D²u|² = Δs²/2 = 0` on `D`,
contradicting nonflatness. Hence the maximum is attained on the boundary, where `s² = 1`, and the
same argument rules out `s² = 1` inside `D`.

At a boundary point the closed interior ball of the chart lies in `{F > 0} ∪ {x₀}`, where
`|∇F|² = s² < 1 = |∇F(x₀)|²`; the Hopf lemma gives `D|∇F|²(x₀)[-N] > 0`, i.e. `D²F(x₀)[N, N] < 0`.

## Differences from the source

The 2026-09-24 version takes the maximum of `s²` over the compact closure of the link and applies
the strong maximum principle and Hopf's lemma on the sphere. We work on the cone in `ℝⁿ` with the
zero-homogeneous function `s²`; the maximum over `closure D ∩ S^{n-1}` is transported to all of `D`
by homogeneity. The interior ball at a boundary point is produced directly from a second-order
Taylor bound for the chart.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Metric Laplacian EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

/-- A bilinear form vanishing on all pairs of vectors of an orthonormal basis is zero: if
`|D²u(x)|² = 0` then `D²u(x) = 0`. -/
theorem iteratedFDeriv_two_eq_zero_of_jetNormSq_eq_zero {n : ℕ} {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ (E n)) {u : E n → ℝ} {x : E n} (h : jetNormSq e 2 u x = 0) :
    iteratedFDeriv ℝ 2 u x = 0 := by
  rw [jetNormSq, multilinearNormSq_two] at h
  have hab : ∀ a b, iteratedFDeriv ℝ 2 u x ![e a, e b] = 0 := fun a b ↦ by
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ ↦
      Finset.sum_nonneg fun b _ ↦ sq_nonneg (iteratedFDeriv ℝ 2 u x ![e a, e b])).1 h a
      (Finset.mem_univ a)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ ↦
      sq_nonneg (iteratedFDeriv ℝ 2 u x ![e a, e b])).1 h1 b (Finset.mem_univ b)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  set L := fderiv ℝ (fderiv ℝ u) x
  have hL : ∀ a b, L (e a) (e b) = 0 := fun a b ↦ by
    simpa [iteratedFDeriv_two_apply] using hab a b
  have hLa : ∀ a v, L (e a) v = 0 := fun a v ↦ by
    rw [← sum_inner_mul_apply e v (L (e a))]
    exact Finset.sum_eq_zero fun b _ ↦ by rw [hL, mul_zero]
  ext v
  rw [iteratedFDeriv_two_apply]
  change L (v 0) (v 1) = 0
  rw [← L.flip_apply, ← sum_inner_mul_apply e (v 0) (L.flip (v 1))]
  exact Finset.sum_eq_zero fun a _ ↦ by rw [L.flip_apply, hLa, mul_zero]

namespace ConeJets.IsBoundaryJet

variable {n : ℕ} {F : E n → ℝ} {J : ConeJets n} (h : IsBoundaryJet F J)
include h

/-- `T(p, p) = D²F(x₀)[N, N]` with `N = ∇F(x₀)`. -/
theorem Tpp_eq : J.Tpp = iteratedFDeriv ℝ 2 F J.x₀ ![∇ F J.x₀, ∇ F J.x₀] := by
  rw [h.gradient_eq, h.isConeJet.D2_frameMap]
  rfl

/-- `|T(p, p)| ≤ w = |T|`, since `|p| = 1`. -/
theorem abs_Tpp_le_w : |J.Tpp| ≤ J.w := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (n - 1) × Fin (n - 1)))
    (fun q ↦ J.p q.1 * J.p q.2) (fun q ↦ J.T q.1 q.2)
  simp only [Fintype.sum_prod_type] at hcs
  have hpp : ∑ i, ∑ j, (J.p i * J.p j) ^ 2 = 1 := by
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, h.sum_p_sq, one_mul]
  rw [hpp, one_mul] at hcs
  exact Real.abs_le_sqrt hcs

/-- `H = -T(p, p) ≤ w`. -/
theorem neg_Tpp_le_w : -J.Tpp ≤ J.w := (neg_le_abs _).trans h.abs_Tpp_le_w

theorem w_pos_of_Tpp_neg (hT : J.Tpp < 0) : 0 < J.w := by
  linarith [h.neg_Tpp_le_w]

end ConeJets.IsBoundaryJet

namespace ConeData

variable {n : ℕ} (C : ConeData n) {x : E n}

/-! ### Elementary facts about the cone -/

private theorem isOpen_D_aux : IsOpen C.D := by
  rw [C.D_eq]
  exact (isOpen_lt continuous_const C.continuous).connectedComponentIn

private theorem isPreconnected_D_aux : IsPreconnected C.D := by
  rw [C.D_eq]
  exact isPreconnected_connectedComponentIn

theorem u_pos_of_mem_D (hx : x ∈ C.D) : 0 < C.u x := by
  rw [C.D_eq] at hx
  have h := connectedComponentIn_subset _ _ hx
  exact h

theorem isOneHomogeneous_u : IsOneHomogeneous C.u := fun r hr y ↦ by
  rw [C.homog r hr y, smul_eq_mul]

theorem u_zero : C.u 0 = 0 := by
  have h := C.homog 2 two_pos 0
  rw [smul_zero] at h
  linarith

theorem ne_zero_of_mem_D (hx : x ∈ C.D) : x ≠ 0 := by
  rintro rfl
  exact (C.u_pos_of_mem_D hx).ne' C.u_zero

/-- `D` is a cone. -/
theorem smul_mem_D (hx : x ∈ C.D) {r : ℝ} (hr : 0 < r) : r • x ∈ C.D := by
  have hconn : IsPreconnected ((fun t : ℝ ↦ t • x) '' Ioi 0) :=
    isPreconnected_Ioi.image _ (continuous_id.smul continuous_const).continuousOn
  have hsub : (fun t : ℝ ↦ t • x) '' Ioi 0 ⊆ {y | 0 < C.u y} := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [mem_ofPred_eq, C.homog t ht]
    exact mul_pos ht (C.u_pos_of_mem_D hx)
  have hmem := hconn.subset_connectedComponentIn ⟨1, one_pos, one_smul _ _⟩ hsub
  have hDx : C.D = connectedComponentIn {y | 0 < C.u y} x := by
    have hx' := hx
    rw [C.D_eq] at hx' ⊢
    exact connectedComponentIn_eq hx'
  rw [hDx]
  exact hmem ⟨r, hr, rfl⟩

theorem inv_norm_smul_mem_D (hx : x ∈ C.D) : ‖x‖⁻¹ • x ∈ C.D :=
  C.smul_mem_D hx (inv_pos.2 (norm_pos_iff.2 (C.ne_zero_of_mem_D hx)))

/-! ### Charts -/

section Chart

variable {C} {U : Set (E n)} {F : E n → ℝ}

theorem chart_pos_of_mem_D (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hxU : x ∈ U) (hxD : x ∈ C.D) :
    0 < F x := by
  have h := C.u_pos_of_mem_D hxD
  rw [hu x hxU] at h
  by_contra hle
  exact (lt_irrefl _) (h.trans_le (max_le (not_lt.1 hle) le_rfl))

/-- On a chart domain, `u = F` near every point of `D`. -/
theorem chart_eventuallyEq (hU : IsOpen U) (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hxU : x ∈ U)
    (hxD : x ∈ C.D) : C.u =ᶠ[𝓝 x] F := by
  filter_upwards [hU.mem_nhds hxU, (isOpen_D_aux C).mem_nhds hxD] with y hyU hyD
  rw [hu y hyU, max_eq_left (chart_pos_of_mem_D hu hyU hyD).le]

/-- A chart vanishes at the points of `closure D \ D` in its domain. -/
theorem chart_eq_zero (hU : IsOpen U) (hF : ContinuousOn F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D) (hxU : x ∈ U)
    (hxc : x ∈ closure C.D) (hxD : x ∉ C.D) : F x = 0 := by
  refine le_antisymm (not_lt.1 fun h ↦ hxD (hD x hxU h)) (not_lt.1 fun hneg ↦ ?_)
  have hev : ∀ᶠ y in 𝓝 x, F y < 0 ∧ y ∈ U :=
    ((hF.continuousAt (hU.mem_nhds hxU)).eventually (gt_mem_nhds hneg)).and (hU.mem_nhds hxU)
  obtain ⟨y, hyD, hyneg, hyU⟩ := ((mem_closure_iff_frequently.1 hxc).and_eventually hev).exists
  exact (lt_asymm hyneg) (chart_pos_of_mem_D hu hyU hyD)

end Chart

/-! ### Smoothness on `D` -/

section Smooth

variable (hS : C.Sing = {0})
include hS

theorem mem_closure_diff_sing {y : E n} (hy : y ∈ closure C.D) (h0 : y ≠ 0) :
    y ∈ closure C.D \ C.Sing :=
  ⟨hy, by rw [hS]; exact h0⟩

theorem contDiffAt_u (hx : x ∈ C.D) : ContDiffAt ℝ ∞ C.u x := by
  obtain ⟨U, hU, hxU, F, hF, hu, -, -, -⟩ :=
    C.chart x (C.mem_closure_diff_sing hS (subset_closure hx) (C.ne_zero_of_mem_D hx))
  exact (hF.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
    (chart_eventuallyEq hU hu hxU hx)

theorem laplacian_u (hx : x ∈ C.D) : Δ C.u x = 0 := by
  obtain ⟨U, hU, hxU, F, -, hu, -, -, hΔ⟩ :=
    C.chart x (C.mem_closure_diff_sing hS (subset_closure hx) (C.ne_zero_of_mem_D hx))
  rw [(InnerProductSpace.laplacian_congr_nhds (chart_eventuallyEq hU hu hxU hx)).self_of_nhds]
  exact hΔ x hxU (chart_pos_of_mem_D hu hxU hx)

theorem eventually_contDiffAt_u (hx : x ∈ C.D) (k : ℕ) : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ k C.u y := by
  filter_upwards [(isOpen_D_aux C).mem_nhds hx] with y hy
  exact (C.contDiffAt_u hS hy).of_le (natCast_le_infty k)

theorem eventually_laplacian_u (hx : x ∈ C.D) : ∀ᶠ y in 𝓝 x, Δ C.u y = 0 := by
  filter_upwards [(isOpen_D_aux C).mem_nhds hx] with y hy using C.laplacian_u hS hy

/-- `∇u` is zero-homogeneous on `D`. -/
theorem gradient_smul (hx : x ∈ C.D) {r : ℝ} (hr : 0 < r) : ∇ C.u (r • x) = ∇ C.u x := by
  have hd : fderiv ℝ C.u (r • x) = fderiv ℝ C.u x := by
    ext v
    have h := C.isOneHomogeneous_u.pow_smul_iteratedFDeriv_smul hr (k := 1)
      ((C.contDiffAt_u hS hx).of_le (natCast_le_infty 1)) ![v]
    simp only [pow_one, smul_eq_mul, iteratedFDeriv_one_apply, Matrix.cons_val_zero] at h
    exact mul_left_cancel₀ hr.ne' h
  simp only [gradient, hd]

end Smooth

/-! ### The extended function `s²` -/

open Classical in
/-- `s² = |∇u|²` on `D`, extended by `1` off `D`. -/
def sSqExt (y : E n) : ℝ := if y ∈ C.D then ‖∇ C.u y‖ ^ 2 else 1

/-- In a chart, `s² = |∇F|²` on `closure D`. -/
theorem sSqExt_eq_of_chart {U : Set (E n)} {F : E n → ℝ} (hU : IsOpen U)
    (hF : ContinuousOn F U) (hu : ∀ y ∈ U, C.u y = max (F y) 0)
    (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D) (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) {y : E n}
    (hyU : y ∈ U) (hyc : y ∈ closure C.D) : C.sSqExt y = ‖∇ F y‖ ^ 2 := by
  unfold sSqExt
  split_ifs with hyD
  · rw [(chart_eventuallyEq hU hu hyU hyD).gradient_eq]
  · rw [hgrad y hyU (chart_eq_zero hU hF hu hD hyU hyc hyD), one_pow]

theorem continuousWithinAt_sSqExt (hS : C.Sing = {0}) {y : E n} (hy : y ∈ closure C.D)
    (h0 : y ≠ 0) : ContinuousWithinAt C.sSqExt (closure C.D) y := by
  obtain ⟨U, hU, hyU, F, hF, hu, hD, hgrad, -⟩ := C.chart y (C.mem_closure_diff_sing hS hy h0)
  have hcont : ContinuousAt (fun z ↦ ‖∇ F z‖ ^ 2) y :=
    ((contDiffAt_gradient (k := 1) ((hF.contDiffAt (hU.mem_nhds hyU)).of_le
      (natCast_le_infty 2))).continuousAt.norm).pow 2
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_
    (C.sSqExt_eq_of_chart hU hF.continuousOn hu hD hgrad hyU hy)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hyU)] with z hzc hzU
  exact C.sSqExt_eq_of_chart hU hF.continuousOn hu hD hgrad hzU hzc

/-! ### The gradient bound -/

section Bound

variable (hS : C.Sing = {0})
include hS

/-- `s² = |∇u|²` has no maximum point in `D`: by the strong maximum principle it would be constant
on `D`, so `2|D²u|² = Δs² = 0` on `D`, contradicting nonflatness. -/
theorem not_isMaxOn_sSq {a : E n} (ha : a ∈ C.D) :
    ¬ IsMaxOn (fun y ↦ ‖∇ C.u y‖ ^ 2) C.D a := by
  intro hmax
  set e := stdOrthonormalBasis ℝ (E n)
  have hconst := TauCeti.eqOn_const_of_laplacian_nonneg_of_isMaxOn (isOpen_D_aux C) ha
    (isPreconnected_D_aux C)
    (fun y hy ↦ (contDiffAt_gradient (k := 2) ((C.contDiffAt_u hS hy).of_le
      (natCast_le_infty 3))).norm_sq ℝ)
    (fun y hy ↦ laplacian_normSq_gradient_nonneg (C.eventually_contDiffAt_u hS hy 3)
      (C.eventually_laplacian_u hS hy)) hmax
  obtain ⟨x₁, hx₁, hne⟩ := C.nonflat
  have hev : (fun y ↦ ‖∇ C.u y‖ ^ 2) =ᶠ[𝓝 x₁] fun _ ↦ ‖∇ C.u a‖ ^ 2 := by
    filter_upwards [(isOpen_D_aux C).mem_nhds hx₁] with y hy using hconst hy
  have h1 := (InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds
  rw [InnerProductSpace.laplacian_const, Pi.zero_apply,
    laplacian_normSq_gradient_eq e (C.eventually_contDiffAt_u hS hx₁ 3)
      (C.eventually_laplacian_u hS hx₁)] at h1
  exact hne (iteratedFDeriv_two_eq_zero_of_jetNormSq_eq_zero e (by simpa using h1))

/-- **Gradient bound**, `geo:gradient-bound`: `|∇u|² < 1` on `D`. -/
theorem sSq_lt_one (hx : x ∈ C.D) : ‖∇ C.u x‖ ^ 2 < 1 := by
  set L := closure C.D ∩ sphere (0 : E n) 1
  have hLc : IsCompact L := (isCompact_sphere 0 1).inter_left isClosed_closure
  have hproj : ∀ z ∈ C.D, ‖z‖⁻¹ • z ∈ L ∧ ‖∇ C.u (‖z‖⁻¹ • z)‖ ^ 2 = ‖∇ C.u z‖ ^ 2 := by
    intro z hz
    have hz0 := C.ne_zero_of_mem_D hz
    refine ⟨⟨subset_closure (C.inv_norm_smul_mem_D hz), ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hz0)]
    · rw [C.gradient_smul hS hz (inv_pos.2 (norm_pos_iff.2 hz0))]
  have hcont : ContinuousOn C.sSqExt L := fun z hz ↦
    (C.continuousWithinAt_sSqExt hS hz.1
      (ne_zero_of_mem_sphere (by norm_num) ⟨z, hz.2⟩)).mono inter_subset_left
  obtain ⟨y, hyL, hymax⟩ := hLc.exists_isMaxOn ⟨_, (hproj x hx).1⟩ hcont
  have hval : ∀ z ∈ C.D, C.sSqExt (‖z‖⁻¹ • z) = ‖∇ C.u z‖ ^ 2 := fun z hz ↦ by
    rw [sSqExt, ite_eq_left (C.inv_norm_smul_mem_D hz), (hproj z hz).2]
  have hle : ∀ z ∈ C.D, ‖∇ C.u z‖ ^ 2 ≤ C.sSqExt y := fun z hz ↦
    hval z hz ▸ hymax (hproj z hz).1
  have hy1 : C.sSqExt y ≤ 1 := by
    by_cases hyD : y ∈ C.D
    · refine absurd (fun z hz ↦ ?_) (C.not_isMaxOn_sSq hS hyD)
      have h := hle z hz
      rw [sSqExt, ite_eq_left hyD] at h
      exact h
    · rw [sSqExt, ite_eq_right hyD]
  rcases (hle x hx |>.trans hy1).lt_or_eq with h | h
  · exact h
  · refine absurd (fun z hz ↦ ?_) (C.not_isMaxOn_sSq hS hx)
    change ‖∇ C.u z‖ ^ 2 ≤ ‖∇ C.u x‖ ^ 2
    rw [h]
    exact (hle z hz).trans hy1

theorem sSq_le_one (hx : x ∈ C.D) : ‖∇ C.u x‖ ^ 2 ≤ 1 :=
  (C.sSq_lt_one hS hx).le

theorem norm_gradient_lt_one (hx : x ∈ C.D) : ‖∇ C.u x‖ < 1 := by
  have h := C.sSq_lt_one hS hx
  nlinarith [norm_nonneg (∇ C.u x)]

end Bound

/-! ### Hopf at the free boundary -/

section Boundary

variable {C} {U : Set (E n)} {F : E n → ℝ} {x₀ : E n}

/-- **`H > 0` from the gradient bound.** If `|∇u|² < 1` on `D`, then at every point `x₀` of
`closure D \ D` lying in the domain of a chart `F`, `D²F(x₀)[N, N] < 0` for `N = ∇F(x₀)`. -/
theorem hessian_gradient_neg_of_sSq_lt (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 < 1) (hU : IsOpen U)
    (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hu : ∀ y ∈ U, C.u y = max (F y) 0)
    (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D) (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1)
    (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0) (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) :
    iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] < 0 := by
  refine hessian_gradient_neg_of_chart hU hx₀U hF
    (chart_eq_zero hU hF.continuousOn hu hD hx₀U hx₀ hx₀D) hgrad hΔ fun y hyU hy ↦ ?_
  have hyD := hD y hyU hy
  have h := hs y hyD
  rw [(chart_eventuallyEq hU hu hyU hyD).gradient_eq] at h
  nlinarith [norm_nonneg (∇ F y)]

/-- At a unit point of `closure D \ D`, the jet record of a chart is a boundary jet record. -/
theorem isBoundaryJet_chart (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) {ι : E (n - 1) →ₗᵢ[ℝ] E n}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : ConeJets.IsBoundaryJet F (ConeJets.ofFun F x₀ ι) :=
  ConeJets.isBoundaryJet_of_chart hx₁ hι hU hx₀U hF
    (chart_eq_zero hU hF.continuousOn hu hD hx₀U hx₀ hx₀D) C.isOneHomogeneous_u hu hΔ hgrad

/-- **`T(p, p) = -H < 0`** at a unit free-boundary point, given the gradient bound. -/
theorem Tpp_neg_of_sSq_lt (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 < 1) (hU : IsOpen U)
    (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hu : ∀ y ∈ U, C.u y = max (F y) 0)
    (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D) (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1)
    (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0) (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D)
    (hx₁ : ‖x₀‖ = 1) {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hι : ∀ v, ⟪ι v, x₀⟫ = 0) :
    (ConeJets.ofFun F x₀ ι).Tpp < 0 := by
  rw [(isBoundaryJet_chart hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι).Tpp_eq]
  exact hessian_gradient_neg_of_sSq_lt hs hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D

variable (hS : C.Sing = {0})
include hS

/-- **`H > 0`**, `geo:gradient-bound`: at every point `x₀ ∈ closure D \ D` and every chart `F`
at `x₀`, `D²F(x₀)[N, N] < 0` for `N = ∇F(x₀)`. -/
theorem hessian_gradient_neg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) :
    iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] < 0 :=
  hessian_gradient_neg_of_sSq_lt (fun _ hy ↦ C.sSq_lt_one hS hy) hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D

/-- **`H > 0`**: `H = -D²F(x₀)[N, N] > 0` at every point `x₀ ∈ closure D \ D`, for every chart
`F` at `x₀`. -/
theorem boundary_H_pos (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) :
    0 < -iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] :=
  neg_pos.2 (C.hessian_gradient_neg hS hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D)

/-- **`H > 0`** in jet form: `T(p, p) < 0` at a unit free-boundary point. -/
theorem boundary_Tpp_neg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) {ι : E (n - 1) →ₗᵢ[ℝ] E n}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : (ConeJets.ofFun F x₀ ι).Tpp < 0 :=
  Tpp_neg_of_sSq_lt (fun _ hy ↦ C.sSq_lt_one hS hy) hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι

/-- **`w ≥ H > 0`** at a unit free-boundary point. -/
theorem boundary_w_pos (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) {ι : E (n - 1) →ₗᵢ[ℝ] E n}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : 0 < (ConeJets.ofFun F x₀ ι).w :=
  (isBoundaryJet_chart hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι).w_pos_of_Tpp_neg
    (C.boundary_Tpp_neg hS hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι)

/-- **`λ = T(p, p)/w < 0`** at a unit free-boundary point. -/
theorem boundary_lam_neg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) {ι : E (n - 1) →ₗᵢ[ℝ] E n}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : (ConeJets.ofFun F x₀ ι).lam < 0 :=
  div_neg_of_neg_of_pos (C.boundary_Tpp_neg hS hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι)
    (C.boundary_w_pos hS hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι)

/-- **`T N = -H N`** at a unit free-boundary point, with `H = -T(p, p) > 0`. -/
theorem boundary_T_eigen (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, C.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ C.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure C.D) (hx₀D : x₀ ∉ C.D) (hx₁ : ‖x₀‖ = 1) {ι : E (n - 1) →ₗᵢ[ℝ] E n}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) :
    0 < -(ConeJets.ofFun F x₀ ι).Tpp ∧ ∀ i, ∑ j, (ConeJets.ofFun F x₀ ι).T i j *
      (ConeJets.ofFun F x₀ ι).p j = -(-(ConeJets.ofFun F x₀ ι).Tpp) * (ConeJets.ofFun F x₀ ι).p i :=
  ⟨neg_pos.2 (C.boundary_Tpp_neg hS hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι), fun i ↦ by
    rw [neg_neg]
    exact (isBoundaryJet_chart hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι).T_mulVec_p i⟩

end Boundary

/-! ### The Hessian zero set -/

/-- The zero set `𝒵 = {x ∈ D ∩ S^{n-1} : D²u(x) = 0}` of the Hessian on the link. -/
def hessZero : Set (E n) := {x | x ∈ C.D ∧ ‖x‖ = 1 ∧ iteratedFDeriv ℝ 2 C.u x = 0}

theorem hessZero_subset_D : C.hessZero ⊆ C.D := fun _ hx ↦ hx.1

section Compact

variable (hS : C.Sing = {0}) {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
include hS

/-- **Local lower bound for `|D²u|²`.** Near a point `y ≠ 0` of `closure D` that is either a
free-boundary point or a point of `D` with `D²u(y) ≠ 0`, `|D²u|²` is bounded below on `D` by a
positive constant. At a free-boundary point this is `D²F(y) ≠ 0` for a chart, which is `H > 0`. -/
theorem eventually_le_jetNormSq {y : E n} (hy : y ∈ closure C.D) (h0 : y ≠ 0)
    (hyD : y ∈ C.D → iteratedFDeriv ℝ 2 C.u y ≠ 0) :
    ∃ c > 0, ∀ᶠ x in 𝓝 y, x ∈ C.D → c ≤ jetNormSq e 2 C.u x := by
  obtain ⟨U, hU, hyU, F, hF, hu, hD, hgrad, hΔ⟩ := C.chart y (C.mem_closure_diff_sing hS hy h0)
  have hne : iteratedFDeriv ℝ 2 F y ≠ 0 := by
    by_cases hyD' : y ∈ C.D
    · rw [← ((chart_eventuallyEq hU hu hyU hyD').iteratedFDeriv ℝ 2).self_of_nhds]
      exact hyD hyD'
    · intro h2
      have h := C.hessian_gradient_neg hS hU hyU hF hu hD hgrad hΔ hy hyD'
      rw [h2] at h
      exact lt_irrefl _ h
  have hpos : 0 < jetNormSq e 2 F y := (jetNormSq_nonneg e 2 F y).lt_of_ne
    fun h ↦ hne (iteratedFDeriv_two_eq_zero_of_jetNormSq_eq_zero e h.symm)
  have hcont : ContinuousAt (jetNormSq e 2 F) y :=
    (differentiableAt_jetNormSq e (k := 2) ((hF.contDiffAt (hU.mem_nhds hyU)).of_le
      (natCast_le_infty 3))).continuousAt
  refine ⟨jetNormSq e 2 F y / 2, by positivity, ?_⟩
  filter_upwards [hcont.eventually (lt_mem_nhds (half_lt_self hpos)), hU.mem_nhds hyU] with
    x hx hxU hxD
  have h2 := ((chart_eventuallyEq hU hu hxU hxD).iteratedFDeriv ℝ 2).self_of_nhds
  have h3 : jetNormSq e 2 C.u x = jetNormSq e 2 F x := by
    simp only [jetNormSq, h2]
  rw [h3]
  exact hx.le

/-- **Uniform lower bound on compact sets.** If `K ⊆ closure D` is compact, avoids `0`, and
`D²u ≠ 0` on `K ∩ D`, then `|D²u|² ≥ δ > 0` on `V ∩ D` for an open `V ⊇ K`. -/
theorem exists_le_jetNormSq_of_isCompact {K : Set (E n)} (hK : IsCompact K)
    (hKc : K ⊆ closure C.D) (hK0 : (0 : E n) ∉ K)
    (hKD : ∀ y ∈ K, y ∈ C.D → iteratedFDeriv ℝ 2 C.u y ≠ 0) :
    ∃ δ > 0, ∃ V : Set (E n), IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V ∩ C.D, δ ≤ jetNormSq e 2 C.u x := by
  refine hK.induction_on (p := fun s ↦ ∃ δ > 0, ∃ V : Set (E n), IsOpen V ∧ s ⊆ V ∧
      ∀ x ∈ V ∩ C.D, δ ≤ jetNormSq e 2 C.u x)
    ⟨1, one_pos, ∅, isOpen_empty, subset_rfl, fun x hx ↦ hx.1.elim⟩ ?_ ?_ ?_
  · rintro s t hst ⟨δ, hδ, V, hV, htV, hb⟩
    exact ⟨δ, hδ, V, hV, hst.trans htV, hb⟩
  · rintro s t ⟨δ, hδ, V, hV, hsV, hb⟩ ⟨δ', hδ', V', hV', htV', hb'⟩
    refine ⟨min δ δ', lt_min hδ hδ', V ∪ V', hV.union hV', union_subset_union hsV htV',
      fun x hx ↦ ?_⟩
    rcases hx.1 with h | h
    · exact (min_le_left _ _).trans (hb x ⟨h, hx.2⟩)
    · exact (min_le_right _ _).trans (hb' x ⟨h, hx.2⟩)
  · intro y hy
    obtain ⟨c, hc, hev⟩ := C.eventually_le_jetNormSq hS e (hKc hy)
      (fun h ↦ hK0 (h ▸ hy)) (hKD y hy)
    obtain ⟨W, hWsub, hWo, hyW⟩ := _root_.mem_nhds_iff.1 hev
    exact ⟨W, mem_nhdsWithin_of_mem_nhds (hWo.mem_nhds hyW), c, hc, W, hWo, subset_rfl,
      fun x hx ↦ hWsub hx.1 hx.2⟩

/-- **Compact zero set**: the Hessian zero set on the link is a compact subset of `D` (it stays
away from the free boundary, where `D²F ≠ 0`). -/
theorem hessZero_isCompact : IsCompact C.hessZero := by
  set e₀ := stdOrthonormalBasis ℝ (E n)
  refine (isCompact_sphere (0 : E n) 1).of_isClosed_subset ?_
    fun x hx ↦ mem_sphere_zero_iff_norm.2 hx.2.1
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  have hyc : y ∈ closure C.D := closure_mono (fun x hx ↦ hx.1) hy
  have hy1 : ‖y‖ = 1 := by
    have : y ∈ closure (sphere (0 : E n) 1) :=
      closure_mono (fun x hx ↦ mem_sphere_zero_iff_norm.2 hx.2.1) hy
    rwa [isClosed_sphere.closure_eq, mem_sphere_zero_iff_norm] at this
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  by_contra hyZ
  have hyD : y ∈ C.D → iteratedFDeriv ℝ 2 C.u y ≠ 0 := fun h h2 ↦ hyZ ⟨h, hy1, h2⟩
  obtain ⟨c, hc, hev⟩ := C.eventually_le_jetNormSq hS e₀ hyc hy0 hyD
  obtain ⟨x, hxZ, hx⟩ := ((mem_closure_iff_frequently.1 hy).and_eventually hev).exists
  have h0 : jetNormSq e₀ 2 C.u x = 0 := by
    simp [jetNormSq, multilinearNormSq, hxZ.2.2]
  linarith [hx hxZ.1]

/-- The Hessian zero set is a compact subset of `D`. -/
theorem hessZero_isCompact_subset : IsCompact C.hessZero ∧ C.hessZero ⊆ C.D :=
  ⟨C.hessZero_isCompact hS, C.hessZero_subset_D⟩

/-- **Lower bound near the free boundary**: there are `δ₀ > 0` and an open `V ⊇ ∂D ∩ S^{n-1}` with
`|D²u|² ≥ δ₀` on `V ∩ D`. -/
theorem exists_w_lower_bound_near_boundary :
    ∃ δ > 0, ∃ V : Set (E n), IsOpen V ∧ frontier C.D ∩ sphere 0 1 ⊆ V ∧
      ∀ x ∈ V ∩ C.D, δ ≤ jetNormSq e 2 C.u x := by
  have hfr : frontier C.D = closure C.D \ C.D := (isOpen_D_aux C).frontier_eq
  refine C.exists_le_jetNormSq_of_isCompact hS e
    ((isCompact_sphere 0 1).inter_left isClosed_frontier) (fun y hy ↦ frontier_subset_closure hy.1)
    (fun h ↦ by simpa using h.2) fun y hy hyD ↦ absurd hyD ?_
  rw [hfr] at hy
  exact hy.1.2

/-- **Lower bound away from the zero set**: for every open `V ⊇ 𝒵`, `|D²u|²` is bounded below by
a positive constant on `(D ∩ S^{n-1}) \ V`. -/
theorem exists_w_lower_bound_off {V : Set (E n)} (hV : IsOpen V) (hZV : C.hessZero ⊆ V) :
    ∃ δ > 0, ∀ x ∈ C.D, ‖x‖ = 1 → x ∉ V → δ ≤ jetNormSq e 2 C.u x := by
  set K := (closure C.D ∩ sphere (0 : E n) 1) ∩ Vᶜ
  have hK : IsCompact K :=
    ((isCompact_sphere 0 1).inter_left isClosed_closure).inter_right hV.isClosed_compl
  obtain ⟨δ, hδ, W, -, hKW, hb⟩ := C.exists_le_jetNormSq_of_isCompact hS e hK
    (fun y hy ↦ hy.1.1) (fun h ↦ by simpa using h.1.2)
    fun y hy hyD h2 ↦ hy.2 (hZV ⟨hyD, mem_sphere_zero_iff_norm.1 hy.1.2, h2⟩)
  refine ⟨δ, hδ, fun x hx hx1 hxV ↦ hb x ⟨hKW ⟨⟨subset_closure hx, ?_⟩, hxV⟩, hx⟩⟩
  exact mem_sphere_zero_iff_norm.2 hx1

end Compact

end ConeData

end OnePhaseDimension
