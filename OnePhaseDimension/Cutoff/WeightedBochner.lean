/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.SphereGreen
public import OnePhaseDimension.Geometry.GradientBound
public import OnePhaseDimension.Geometry.JetBochner

/-!
# The weighted Bochner estimate on an original cone

Let `C` be a cone in `ℝⁿ` whose singular set is the vertex, `C.Sing = {0}`. On the link
`D ∩ S^{n-1}` we use the `0`-homogeneous quantities

* `w² = |T|² = |D²u(x̂)|²` (`ConeData.wSq`),
* `|B|² = |D³u(x̂)|² - 3 |D²u(x̂)|²` (`ConeData.bSq`), the squared norm of the tangential part
  `B_{ijk} = D³u(x̂)[τᵢ, τⱼ, τ_k]` of `D³u` (`ConeData.bSq_eq`),

and spherical integrals against `σ = volume.toSphere`, as integrals over the unit sphere of
`D.indicator g`. Fix `1/2 < a < 1` (the source uses `a = 29/50`).

* `ConeData.weightedBochner_uniform`: for a cut-off `η ≥ 0` on the cone over `D`, every `δ > 0`
  and every bound `w² ≤ M` on the support of `η`,
  `(4a - 2) ∫ η (w² + δ)^{a-1} |B|² dσ ≤ a⁻¹ (M + δ)^a ∫ |Δη| dσ`; for `a = 29/50` and `δ ≤ 1`
  this is `(8/25) I_δ ≤ a⁻¹ (M + 1)^a ‖Δη‖_{L¹}` (`ConeData.weightedBochner_absorption`).
* `ConeData.integrable_weighted_B`: `w^{2a-2} |B|²` is integrable on the link (it is `0` where
  `w = 0`, by the convention `0^{a-1} = 0`).
* `ConeData.dominatorO`, `ConeData.dominatorO_le`, `ConeData.integrable_dominatorO`: the
  dominator `D_o = w^{2a}(1 + |B|/w)²` (and `0` where `w = 0`) satisfies
  `D_o ≤ 2 w^{2a} + 2 w^{2a-2} |B|²` and is integrable on the link.

## Proof

`W = w²` is smooth on the cone over `D`, and at unit vectors of `D` the Bochner identity gives
`ΔW ≥ 2|B|²` and `|∇W|² ≤ 4 W |B|²`. With `V = W + δ`, the spherical integrations by parts
`∫ (η V^{a-1} ΔW + ⟪∇(η V^{a-1}), ∇W⟫) = 0` and `∫ (V^a Δη + ⟪∇η, ∇V^a⟫) = 0` give, pointwise
after the chain rule, `(4a - 2) η V^{a-1}|B|² ≤ (first integrand) - a⁻¹ (second) + a⁻¹ V^a Δη`.
Fatou's lemma along `δ = 1/(k+1)` gives `∫ η w^{2a-2}|B|² < ∞`. Off the open set where `η = 1`,
which contains the Hessian zero set, `w² ≥ b > 0`, and `|B|²` is bounded on the link.

Boundedness of `|D²u|` and `|D³u|` on the link (`ConeData.exists_jetNormSq_le`) comes from the
charts: near a point of `closure D ∩ S^{n-1}`, `u = F` on `D` for a chart `F` smooth on an open
set, so the jet norms of `u` on `D` are those of `F`, which are continuous; compactness of
`closure D ∩ S^{n-1}` finishes.

## Differences from the source

* The 2026-09-24 version integrates by parts on the link `Ω_o`. We use the spherical divergence
  theorem for `0`-homogeneous fields (radial cut-off, Euclidean divergence theorem and polar
  separation), and write the two integrations by parts in first-order form.
* The 2026-09-24 version treats an empty Hessian zero set separately. The cut-off argument
  covers that case as well.
* The 2026-09-24 version takes the limit `δ ↓ 0` by monotone convergence. We use Fatou's lemma
  along `δ = 1/(k + 1)`, which needs only the pointwise limit.
* The 2026-09-24 version bounds the integral off `η = 1` by `b_η^{2a-2} ‖B_o‖²_{L²}`. We bound
  the integrand pointwise by `b^{a-1} sup |B|²` and integrate; boundedness of `B` on the link is
  proved from the charts.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace Laplacian ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### Jet norms -/

/-- `r^{2k} |Dᵏu(r x)|² = r² |Dᵏu(x)|²` for a one-homogeneous `u`. -/
theorem IsOneHomogeneous.jetNormSq_smul {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    {u : E n → ℝ} (hu : IsOneHomogeneous u) {r : ℝ} (hr : 0 < r) {k : ℕ} {x : E n}
    (hk : ContDiffAt ℝ k u x) :
    r ^ (2 * k) * jetNormSq e k u (r • x) = r ^ 2 * jetNormSq e k u x := by
  simp only [jetNormSq, multilinearNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  have h := hu.pow_smul_iteratedFDeriv_smul hr hk (fun j ↦ e (I j))
  simp only [smul_eq_mul] at h
  calc r ^ (2 * k) * (iteratedFDeriv ℝ k u (r • x) fun j ↦ e (I j)) ^ 2
      = (r ^ k * iteratedFDeriv ℝ k u (r • x) fun j ↦ e (I j)) ^ 2 := by ring
    _ = r ^ 2 * (iteratedFDeriv ℝ k u x fun j ↦ e (I j)) ^ 2 := by rw [h]; ring

/-- `|Dᵏu|²` is `Cᵐ` where `u` is `C^{k+m}`. -/
theorem contDiffAt_jetNormSq {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    {u : E n → ℝ} {k m : ℕ} {x : E n} (hu : ContDiffAt ℝ (k + m : ℕ) u x) :
    ContDiffAt ℝ m (jetNormSq e k u) x := by
  have : jetNormSq e k u =
      fun y ↦ ∑ I : Fin k → κ, iteratedFDeriv ℝ k u y (fun j ↦ e (I j)) ^ 2 := rfl
  rw [this]
  exact ContDiffAt.sum fun I _ ↦ (contDiffAt_iteratedFDeriv_apply hu _).pow 2

namespace ConeData

variable (C : ConeData n)

local notation "e₀" => stdOrthonormalBasis ℝ (E n)

/-! ### The spherical quantities `w²` and `|B|²` -/

/-- `w² = |D²u(x̂)|²`, the squared norm of the spherical Hessian `T` at `x̂ = x/|x|`. -/
def wSq (x : E n) : ℝ := jetNormSq e₀ 2 C.u (radialProj x)

/-- `|B|² = |D³u(x̂)|² - 3|D²u(x̂)|²`, the squared norm of `B_{ijk} = D³u(x̂)[τᵢ, τⱼ, τ_k]`. -/
def bSq (x : E n) : ℝ :=
  jetNormSq e₀ 3 C.u (radialProj x) - 3 * jetNormSq e₀ 2 C.u (radialProj x)

theorem wSq_nonneg (x : E n) : 0 ≤ C.wSq x := jetNormSq_nonneg _ _ _ _

theorem isZeroHomogeneous_wSq : IsZeroHomogeneous C.wSq :=
  isZeroHomogeneous_comp_radialProj (jetNormSq e₀ 2 C.u)

theorem isZeroHomogeneous_bSq : IsZeroHomogeneous C.bSq :=
  isZeroHomogeneous_comp_radialProj fun y ↦ jetNormSq e₀ 3 C.u y - 3 * jetNormSq e₀ 2 C.u y

theorem wSq_of_norm_eq_one {x : E n} (hx : ‖x‖ = 1) : C.wSq x = jetNormSq e₀ 2 C.u x := by
  rw [wSq, radialProj_of_norm_eq_one hx]

/-- In a jet record at a unit vector, `w² = ∑ T_{ij}²`. -/
theorem wSq_eq {J : ConeJets n} (h : ConeJets.IsConeJet C.u J) :
    C.wSq J.x₀ = ∑ i, ∑ j, J.T i j ^ 2 := by
  rw [C.wSq_of_norm_eq_one h.norm_x₀, h.jetNormSq_two_eq]

/-- In a jet record at a unit vector, `|B|² = ∑ B_{ijk}²`. -/
theorem bSq_eq {J : ConeJets n} (h : ConeJets.IsConeJet C.u J) :
    C.bSq J.x₀ = ∑ i, ∑ j, ∑ k, J.B i j k ^ 2 := by
  rw [bSq, radialProj_of_norm_eq_one h.norm_x₀, h.jetNormSq_three_eq, h.jetNormSq_two_eq]
  ring

section Smooth

variable (hS : C.Sing = {0})
include hS

theorem contDiffAt_wSq {x : E n} (hx : x ≠ 0) (hxD : radialProj x ∈ C.D) (m : ℕ) :
    ContDiffAt ℝ m C.wSq x :=
  (contDiffAt_jetNormSq e₀ (k := 2) ((C.contDiffAt_u hS hxD).of_le (natCast_le_infty _))).comp x
    (contDiffAt_radialProj_of_ne_zero hx)

theorem contDiffAt_bSq {x : E n} (hx : x ≠ 0) (hxD : radialProj x ∈ C.D) (m : ℕ) :
    ContDiffAt ℝ m C.bSq x := by
  have h3 : ContDiffAt ℝ m (jetNormSq e₀ 3 C.u) (radialProj x) :=
    contDiffAt_jetNormSq e₀ ((C.contDiffAt_u hS hxD).of_le (natCast_le_infty _))
  have h2 : ContDiffAt ℝ m (jetNormSq e₀ 2 C.u) (radialProj x) :=
    contDiffAt_jetNormSq e₀ ((C.contDiffAt_u hS hxD).of_le (natCast_le_infty _))
  exact (h3.sub (h2.const_smul (3 : ℝ))).comp x (contDiffAt_radialProj_of_ne_zero hx)

theorem continuousOn_wSq : ContinuousOn C.wSq C.D := fun _ hx ↦
  (C.contDiffAt_wSq hS (C.ne_zero_of_mem_D hx) (C.radialProj_mem_D hx) 0).continuousAt
    |>.continuousWithinAt

theorem continuousOn_bSq : ContinuousOn C.bSq C.D := fun _ hx ↦
  (C.contDiffAt_bSq hS (C.ne_zero_of_mem_D hx) (C.radialProj_mem_D hx) 0).continuousAt
    |>.continuousWithinAt

/-- On `D`, `w²(x) = |x|² |D²u(x)|²`. -/
theorem wSq_eventuallyEq {x : E n} (hx : x ∈ C.D) :
    C.wSq =ᶠ[𝓝 x] fun y ↦ ‖y‖ ^ 2 * jetNormSq e₀ 2 C.u y := by
  filter_upwards [C.isOpen_D.mem_nhds hx] with y hy
  have hy0 := C.ne_zero_of_mem_D hy
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
  have h := C.isOneHomogeneous_u.jetNormSq_smul e₀ (inv_pos.2 (norm_pos_iff.2 hy0)) (k := 2)
    ((C.contDiffAt_u hS hy).of_le (natCast_le_infty _))
  change jetNormSq e₀ 2 C.u (‖y‖⁻¹ • y) = _
  calc jetNormSq e₀ 2 C.u (‖y‖⁻¹ • y)
      = ‖y‖ ^ 4 * (‖y‖⁻¹ ^ (2 * 2) * jetNormSq e₀ 2 C.u (‖y‖⁻¹ • y)) := by
        rw [← mul_assoc, show (2 * 2 : ℕ) = 4 from rfl, ← mul_pow, mul_inv_cancel₀ hn, one_pow,
          one_mul]
    _ = ‖y‖ ^ 4 * (‖y‖⁻¹ ^ 2 * jetNormSq e₀ 2 C.u y) := by rw [h]
    _ = ‖y‖ ^ 2 * jetNormSq e₀ 2 C.u y := by
        have h4 : ‖y‖ ^ 4 * ‖y‖⁻¹ ^ 2 = ‖y‖ ^ 2 := by
          rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (pow_ne_zero 2 hn)]; ring
        rw [← mul_assoc, h4]

/-- The jet record of `u` at a unit vector of `D`. -/
theorem isConeJet_of_mem_D {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    ConeJets.IsConeJet C.u (ConeJets.ofHarmonicHomogeneous C.u x h1) :=
  ConeJets.isConeJet_ofHarmonicHomogeneous h1 C.isOneHomogeneous_u
    (C.eventually_contDiffAt_u hS hx 4) (C.eventually_laplacian_u hS hx)

theorem bSq_nonneg {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) : 0 ≤ C.bSq x := by
  have h := C.bSq_eq (C.isConeJet_of_mem_D hS hx h1)
  change C.bSq x = _ at h
  rw [h]
  positivity

/-- **Bochner**: `Δw² ≥ 2|B|²` at unit vectors of `D`. -/
theorem two_bSq_le_laplacian_wSq {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    2 * C.bSq x ≤ Δ C.wSq x := by
  have hJ := C.isConeJet_of_mem_D hS hx h1
  have hB := hJ.two_sum_sq_B_le_laplacian e₀ C.isOneHomogeneous_u
    (C.eventually_contDiffAt_u hS hx 4) (C.eventually_laplacian_u hS hx)
  have hb := C.bSq_eq hJ
  change C.bSq x = _ at hb
  change 2 * _ ≤ Δ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e₀ 2 C.u y) x at hB
  rw [(InnerProductSpace.laplacian_congr_nhds (C.wSq_eventuallyEq hS hx)).self_of_nhds, hb]
  exact hB

/-- `|∇w²|² ≤ 4 w² |B|²` at unit vectors of `D`. -/
theorem norm_gradient_wSq_sq_le {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    ‖∇ C.wSq x‖ ^ 2 ≤ 4 * C.wSq x * C.bSq x := by
  have hJ := C.isConeJet_of_mem_D hS hx h1
  have hG := hJ.norm_gradient_rsq_jetNormSq_two_sq_le e₀ C.isOneHomogeneous_u
    ((C.contDiffAt_u hS hx).of_le (natCast_le_infty 3))
  have hb := C.bSq_eq hJ
  change C.bSq x = _ at hb
  change ‖∇ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e₀ 2 C.u y) x‖ ^ 2 ≤
    4 * (‖x‖ ^ 2 * jetNormSq e₀ 2 C.u x) * _ at hG
  rw [(C.wSq_eventuallyEq hS hx).gradient_eq, hb, C.wSq_of_norm_eq_one h1]
  rw [h1, one_pow, one_mul] at hG
  exact hG

/-! ### Bounds on the link -/

/-- **`|Dᵏu|` is bounded on the link.** Near each point of `closure D ∩ S^{n-1}` the jet norms
of `u` on `D` are those of a chart, which are continuous. -/
theorem exists_jetNormSq_le (k : ℕ) :
    ∃ M, ∀ x ∈ C.D, ‖x‖ = 1 → jetNormSq e₀ k C.u x ≤ M := by
  set K := closure C.D ∩ sphere (0 : E n) 1
  have hK : IsCompact K := (isCompact_sphere 0 1).inter_left isClosed_closure
  have hloc : ∀ y ∈ K, ∃ t ∈ 𝓝[K] y, ∃ M, ∃ V : Set (E n), IsOpen V ∧ t ⊆ V ∧
      ∀ x ∈ V ∩ C.D, jetNormSq e₀ k C.u x ≤ M := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl; simp [K] at hy
    obtain ⟨U, hU, hyU, F, hF, hu, -, -, -⟩ := C.chart y (C.mem_closure_diff_sing hS hy.1 hy0)
    have hcont : ContinuousAt (jetNormSq e₀ k F) y :=
      (contDiffAt_jetNormSq e₀ (m := 0) ((hF.contDiffAt (hU.mem_nhds hyU)).of_le
        (natCast_le_infty _))).continuousAt
    have hev : ∀ᶠ x in 𝓝 y, jetNormSq e₀ k F x < jetNormSq e₀ k F y + 1 ∧ x ∈ U :=
      (hcont.eventually (gt_mem_nhds (lt_add_one _))).and (hU.mem_nhds hyU)
    obtain ⟨W, hWsub, hWo, hyW⟩ := _root_.mem_nhds_iff.1 hev
    refine ⟨W, mem_nhdsWithin_of_mem_nhds (hWo.mem_nhds hyW), jetNormSq e₀ k F y + 1, W, hWo,
      subset_rfl, fun x hx ↦ ?_⟩
    obtain ⟨hlt, hxU⟩ := hWsub hx.1
    have h2 := ((chart_eventuallyEq hU hu hxU hx.2).iteratedFDeriv ℝ k).self_of_nhds
    have h3 : jetNormSq e₀ k C.u x = jetNormSq e₀ k F x := by simp only [jetNormSq, h2]
    rw [h3]
    exact hlt.le
  obtain ⟨M, V, -, hKV, hb⟩ := hK.induction_on (p := fun s ↦ ∃ M, ∃ V : Set (E n), IsOpen V ∧
      s ⊆ V ∧ ∀ x ∈ V ∩ C.D, jetNormSq e₀ k C.u x ≤ M)
    ⟨0, ∅, isOpen_empty, subset_rfl, fun x hx ↦ hx.1.elim⟩
    (fun s t hst ⟨M, V, hV, htV, hb⟩ ↦ ⟨M, V, hV, hst.trans htV, hb⟩)
    (fun s t ⟨M, V, hV, hsV, hb⟩ ⟨M', V', hV', htV', hb'⟩ ↦
      ⟨max M M', V ∪ V', hV.union hV', union_subset_union hsV htV', fun x hx ↦ by
        rcases hx.1 with h | h
        · exact (hb x ⟨h, hx.2⟩).trans (le_max_left _ _)
        · exact (hb' x ⟨h, hx.2⟩).trans (le_max_right _ _)⟩) hloc
  exact ⟨M, fun x hx h1 ↦ hb x ⟨hKV ⟨subset_closure hx, mem_sphere_zero_iff_norm.2 h1⟩, hx⟩⟩

/-- `w²` and `|B|²` are bounded on the link. -/
theorem exists_wSq_bSq_le :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ C.D, ‖x‖ = 1 → C.wSq x ≤ M ∧ C.bSq x ≤ M := by
  obtain ⟨M₂, h₂⟩ := C.exists_jetNormSq_le hS 2
  obtain ⟨M₃, h₃⟩ := C.exists_jetNormSq_le hS 3
  refine ⟨max (max M₂ M₃) 0, le_max_right _ _, fun x hx h1 ↦ ⟨?_, ?_⟩⟩
  · rw [C.wSq_of_norm_eq_one h1]
    exact (h₂ x hx h1).trans ((le_max_left _ _).trans (le_max_left _ _))
  · have hn := jetNormSq_nonneg e₀ 2 C.u x
    rw [bSq, radialProj_of_norm_eq_one h1]
    have := h₃ x hx h1
    have : M₃ ≤ max (max M₂ M₃) 0 := (le_max_right _ _).trans (le_max_left _ _)
    linarith

/-! ### The cut-off near the Hessian zero set -/

/-- A cut-off `0 ≤ η ≤ 1` on the cone over `D`, with spherical support in a compact `K ⊆ D ∩ S`,
equal to `1` on an open set `V` containing the Hessian zero set. -/
theorem exists_cutoff_hessZero :
    ∃ η : E n → ℝ, ∃ K V : Set (E n), IsConeCutoff η K C.D ∧ K ⊆ sphere 0 1 ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ IsOpen V ∧ C.hessZero ⊆ V ∧ ∀ x ∈ V, η x = 1 := by
  have hZ := C.hessZero_isCompact hS
  obtain ⟨ε, hε, hεD⟩ := hZ.exists_cthickening_subset_open C.isOpen_D C.hessZero_subset_D
  obtain ⟨χ, hχ, hχc, hχD, hχ01, hχ1⟩ := exists_smooth_cutoff hZ.cthickening C.isOpen_D hεD
  refine ⟨fun x ↦ χ (radialProj x), tsupport χ ∩ sphere 0 1,
    {x | x ≠ 0 ∧ radialProj x ∈ thickening ε C.hessZero}, ?_, inter_subset_right,
    fun x ↦ hχ01 _, isOpen_cone isOpen_thickening, ?_, ?_⟩
  · exact
      { isOpen := C.isOpen_D
        isCompact := hχc.inter_right isClosed_sphere
        subset := fun x hx ↦ hχD hx.1
        homog := isZeroHomogeneous_comp_radialProj χ
        contDiffAt := fun x hx _ ↦ ((hχ.of_le (natCast_le_infty 2)).contDiffAt).comp x
          (contDiffAt_radialProj_of_ne_zero hx)
        eq_zero := fun x hx hxK ↦ by
          simp only [radialProj_of_norm_eq_one (mem_sphere_zero_iff_norm.1 hx)]
          exact image_eq_zero_of_notMem_tsupport fun h ↦ hxK ⟨h, hx⟩ }
  · intro z hz
    have h1 : ‖z‖ = 1 := hz.2.1
    refine ⟨fun h ↦ by simp [h] at h1, ?_⟩
    rw [radialProj_of_norm_eq_one h1]
    exact self_subset_thickening hε _ hz
  · intro x hx
    exact hχ1 _ (thickening_subset_cthickening _ _ hx.2)

end Smooth

/-! ### The uniform estimate -/

section Uniform

variable (hS : C.Sing = {0}) {η : E n → ℝ} {K : Set (E n)}
include hS

theorem contDiffAt_wSq_add_rpow {x : E n} (hx : x ≠ 0) (hxD : radialProj x ∈ C.D) {δ : ℝ}
    (hδ : 0 < δ) (p : ℝ) : ContDiffAt ℝ 2 (fun y ↦ (C.wSq y + δ) ^ p) x :=
  ((C.contDiffAt_wSq hS hx hxD 2).add contDiffAt_const).rpow_const_of_ne
    (by linarith [C.wSq_nonneg x])

omit hS in
theorem isZeroHomogeneous_wSq_add_rpow (δ p : ℝ) :
    IsZeroHomogeneous fun y ↦ (C.wSq y + δ) ^ p := fun r hr x ↦ by
  simp only [C.isZeroHomogeneous_wSq r hr x]

omit hS in
private theorem indicator_eq_of_cutoff (hη : IsConeCutoff η K C.D) {F : E n → ℝ} {u : E n}
    (hu : ‖u‖ = 1) : C.D.indicator (fun x ↦ η x * F x) u = η u * F u := by
  by_cases huD : u ∈ C.D
  · rw [indicator_of_mem huD]
  · have huK : u ∉ K := fun h ↦ huD (hη.subset h)
    rw [indicator_of_notMem huD, hη.eq_zero u (mem_sphere_zero_iff_norm.2 hu) huK, zero_mul]

omit hS in
/-- A function on the cone over `D` that vanishes near the unit vectors off `K` and is continuous
at the unit vectors of `D` is integrable on the sphere after restriction to `D`. -/
private theorem integrable_indicator_of_cutoff (hη : IsConeCutoff η K C.D) {F : E n → ℝ}
    (hF : ∀ u, ‖u‖ = 1 → u ∈ C.D → ContinuousAt (fun x ↦ η x * F x) u) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator (fun x ↦ η x * F x) u)
      (volume : Measure (E n)).toSphere := by
  refine integrable_sphere_of_continuousAt (F := C.D.indicator (fun x ↦ η x * F x))
    fun u hu ↦ ?_
  have hu1 := mem_sphere_zero_iff_norm.1 hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  by_cases huD : u ∈ C.D
  · refine (continuousAt_congr ?_).2 (hF u hu1 huD)
    filter_upwards [C.isOpen_D.mem_nhds huD] with y hy
    rw [indicator_of_mem hy]
  · have huK : radialProj u ∉ K := by
      rw [radialProj_of_norm_eq_one hu1]; exact fun h ↦ huD (hη.subset h)
    refine (continuousAt_congr ?_).2 (continuousAt_const (y := (0 : ℝ)))
    filter_upwards [hη.eventuallyEq_zero hu0 huK] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

/-- The integrand `η (w² + δ)^{a-1} |B|²` is integrable on the sphere. -/
theorem integrable_cutoff_weighted (hη : IsConeCutoff η K C.D) {a δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (fun x ↦ η x * ((C.wSq x + δ) ^ (a - 1) * C.bSq x)) u)
      (volume : Measure (E n)).toSphere := by
  refine C.integrable_indicator_of_cutoff hη fun u hu1 huD ↦ ?_
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have huD' : radialProj u ∈ C.D := by rwa [radialProj_of_norm_eq_one hu1]
  exact (hη.contDiffAt u hu0 huD').continuousAt.mul
    ((C.contDiffAt_wSq_add_rpow hS hu0 huD' hδ _).continuousAt.mul
      (C.contDiffAt_bSq hS hu0 huD' 0).continuousAt)

/-- **The pointwise inequality.** At a unit vector `u`, with `V = w² + δ`,
`(4a - 2) η V^{a-1} |B|² ≤ A - a⁻¹ B + a⁻¹ V^a Δη`, where `A = η V^{a-1} Δw² + ⟪∇(η V^{a-1}), ∇w²⟫`
and `B = V^a Δη + ⟪∇η, ∇V^a⟫` are the integrands of the two integrations by parts. -/
theorem weightedBochner_pointwise (hη : IsConeCutoff η K C.D) (hη0 : ∀ x, 0 ≤ η x) {a δ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ) {u : E n} (hu1 : ‖u‖ = 1) :
    (4 * a - 2) * (η u * ((C.wSq u + δ) ^ (a - 1) * C.bSq u)) ≤
      ((η u * (C.wSq u + δ) ^ (a - 1)) * Δ C.wSq u +
          ⟪∇ (fun x ↦ η x * (C.wSq x + δ) ^ (a - 1)) u, ∇ C.wSq u⟫) -
        a⁻¹ * ((C.wSq u + δ) ^ a * Δ η u + ⟪∇ η u, ∇ (fun x ↦ (C.wSq x + δ) ^ a) u⟫) +
        a⁻¹ * ((C.wSq u + δ) ^ a * Δ η u) := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  set f₁ : E n → ℝ := fun x ↦ η x * (C.wSq x + δ) ^ (a - 1) with hf₁_def
  have hf₁ : IsConeCutoff f₁ K C.D := hη.mul (C.isZeroHomogeneous_wSq_add_rpow δ (a - 1))
    fun x hx hxD ↦ C.contDiffAt_wSq_add_rpow hS hx hxD hδ _
  by_cases huK : u ∈ K
  swap
  · -- off the support everything vanishes
    have huK' : radialProj u ∉ K := by rwa [radialProj_of_norm_eq_one hu1]
    have hηu : η u = 0 := hη.eq_zero u (mem_sphere_zero_iff_norm.2 hu1) huK
    have hf₁u : f₁ u = 0 := hf₁.eq_zero u (mem_sphere_zero_iff_norm.2 hu1) huK
    rw [hf₁.gradient_eq_zero hu0 huK', hη.gradient_eq_zero hu0 huK',
      hη.laplacian_eq_zero hu0 huK', hηu]
    simp
  have huD : u ∈ C.D := hη.subset huK
  have huD' : radialProj u ∈ C.D := by rwa [radialProj_of_norm_eq_one hu1]
  -- derivatives
  set W := C.wSq
  set V := W u + δ with hV_def
  have hV : 0 < V := by have := C.wSq_nonneg u; rw [hV_def]; linarith
  have hWd : HasFDerivAt W (fderiv ℝ W u) u :=
    ((C.contDiffAt_wSq hS hu0 huD' 1).differentiableAt one_ne_zero).hasFDerivAt
  have hηd : HasFDerivAt η (fderiv ℝ η u) u :=
    ((hη.contDiffAt u hu0 huD').differentiableAt (by norm_num)).hasFDerivAt
  have hg₁ := (hWd.add_const δ).rpow_const (p := a - 1) (Or.inl hV.ne')
  have hg₂ := (hWd.add_const δ).rpow_const (p := a) (Or.inl hV.ne')
  have hf₁d : HasFDerivAt f₁ (η u • (((a - 1) * (W u + δ) ^ (a - 1 - 1)) • fderiv ℝ W u) +
      (W u + δ) ^ (a - 1) • fderiv ℝ η u) u := hηd.mul hg₁
  have hA : ⟪∇ f₁ u, ∇ W u⟫ =
      η u * ((a - 1) * V ^ (a - 1 - 1)) * ‖∇ W u‖ ^ 2 +
        V ^ (a - 1) * ⟪∇ η u, ∇ W u⟫ := by
    rw [inner_gradient_left, hf₁d.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [← inner_gradient_left (f := W), real_inner_self_eq_norm_sq, ← inner_gradient_left]
    ring
  have hB : ⟪∇ η u, ∇ (fun x ↦ (W x + δ) ^ a) u⟫ = a * V ^ (a - 1) * ⟪∇ η u, ∇ W u⟫ := by
    rw [real_inner_comm, inner_gradient_left, hg₂.fderiv, smul_apply,
      smul_eq_mul, ← inner_gradient_left, real_inner_comm]
  rw [hA, hB]
  -- the Bochner inequalities
  have hb0 := C.bSq_nonneg hS huD hu1
  have hL := C.two_bSq_le_laplacian_wSq hS huD hu1
  have hN := C.norm_gradient_wSq_sq_le hS huD hu1
  have hWV : W u ≤ V := by rw [hV_def]; linarith
  set P := V ^ (a - 1) with hP_def
  have hP : 0 < P := Real.rpow_pos_of_pos hV _
  have hP2 : V ^ (a - 1 - 1) = P / V := Real.rpow_sub_one hV.ne' _
  have hPa : V ^ a = P * V := by
    rw [hP_def, Real.rpow_sub_one hV.ne']; field_simp
  rw [hP2, hPa]
  set e := η u
  have he : 0 ≤ e := hη0 u
  set N := ‖∇ W u‖ ^ 2
  have hN' : P / V * N ≤ 4 * P * C.bSq u := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hV]
    have : N ≤ 4 * V * C.bSq u := hN.trans (by nlinarith)
    nlinarith
  have key : (e * P * Δ W u + (e * ((a - 1) * (P / V)) * N + P * ⟪∇ η u, ∇ W u⟫) -
      a⁻¹ * (P * V * Δ η u + a * P * ⟪∇ η u, ∇ W u⟫) + a⁻¹ * (P * V * Δ η u)) =
      e * P * Δ W u - e * (1 - a) * (P / V * N) := by
    field_simp
    ring
  rw [key]
  have h1 : e * P * (2 * C.bSq u) ≤ e * P * Δ W u :=
    mul_le_mul_of_nonneg_left hL (mul_nonneg he hP.le)
  have h2 : e * (1 - a) * (P / V * N) ≤ e * (1 - a) * (4 * P * C.bSq u) :=
    mul_le_mul_of_nonneg_left hN' (mul_nonneg he (by linarith))
  nlinarith

/-- **Uniform weighted Bochner estimate.** For a cut-off `η ≥ 0` on the cone over `D` with
spherical support `K`, `0 < a ≤ 1`, `δ > 0` and `w² ≤ M` on `K`,

  `(4a - 2) ∫ η (w² + δ)^{a-1} |B|² dσ ≤ a⁻¹ (M + δ)^a ∫ |Δη| dσ`. -/
theorem weightedBochner_uniform [NeZero n] (hη : IsConeCutoff η K C.D) (hη0 : ∀ x, 0 ≤ η x)
    {a δ M : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hδ : 0 < δ) (hM : ∀ x ∈ K, C.wSq x ≤ M) :
    (4 * a - 2) * ∫ u : sphere (0 : E n) 1,
        C.D.indicator (fun x ↦ η x * ((C.wSq x + δ) ^ (a - 1) * C.bSq x)) u
        ∂(volume : Measure (E n)).toSphere ≤
      a⁻¹ * (M + δ) ^ a * ∫ u : sphere (0 : E n) 1, |Δ η u| ∂(volume : Measure (E n)).toSphere := by
  set σ := (volume : Measure (E n)).toSphere
  set f₁ : E n → ℝ := fun x ↦ η x * (C.wSq x + δ) ^ (a - 1) with hf₁_def
  set g₂ : E n → ℝ := fun x ↦ (C.wSq x + δ) ^ a with hg₂_def
  have hWd : ∀ x, x ≠ 0 → radialProj x ∈ C.D → ContDiffAt ℝ 2 C.wSq x :=
    fun x hx hxD ↦ C.contDiffAt_wSq hS hx hxD 2
  have hg₂d : ∀ x, x ≠ 0 → radialProj x ∈ C.D → ContDiffAt ℝ 2 g₂ x :=
    fun x hx hxD ↦ C.contDiffAt_wSq_add_rpow hS hx hxD hδ a
  have hf₁ : IsConeCutoff f₁ K C.D := hη.mul (C.isZeroHomogeneous_wSq_add_rpow δ (a - 1))
    fun x hx hxD ↦ C.contDiffAt_wSq_add_rpow hS hx hxD hδ _
  have hIA := integral_sphere_mul_laplacian_add_inner hf₁ C.isZeroHomogeneous_wSq hWd
  have hIB := integral_sphere_mul_laplacian_add_inner' hη
    (C.isZeroHomogeneous_wSq_add_rpow δ a) hg₂d
  have iA : Integrable (fun u : sphere (0 : E n) 1 ↦ f₁ u * Δ C.wSq u + ⟪∇ f₁ u, ∇ C.wSq u⟫) σ :=
    (integrable_sphere_mul_laplacian hf₁ hWd).add (integrable_sphere_inner_gradient hf₁ hWd)
  have iB : Integrable (fun u : sphere (0 : E n) 1 ↦ g₂ u * Δ η u + ⟪∇ η u, ∇ g₂ u⟫) σ :=
    (integrable_sphere_mul_laplacian' hη hg₂d).add (integrable_sphere_inner_gradient hη hg₂d)
  have iC : Integrable (fun u : sphere (0 : E n) 1 ↦ g₂ u * Δ η u) σ :=
    integrable_sphere_mul_laplacian' hη hg₂d
  have iL := C.integrable_cutoff_weighted hS hη (a := a) hδ
  have iΔ : Integrable (fun u : sphere (0 : E n) 1 ↦ |Δ η u|) σ := by
    have h := integrable_sphere_mul_laplacian' hη (g := fun _ ↦ (1 : ℝ))
      fun _ _ _ ↦ contDiffAt_const
    simpa only [one_mul] using h.abs
  -- integrate the pointwise inequality
  have hpt : ∀ u : sphere (0 : E n) 1,
      (4 * a - 2) * C.D.indicator (fun x ↦ η x * ((C.wSq x + δ) ^ (a - 1) * C.bSq x)) u ≤
        (f₁ u * Δ C.wSq u + ⟪∇ f₁ u, ∇ C.wSq u⟫) -
          a⁻¹ * (g₂ u * Δ η u + ⟪∇ η u, ∇ g₂ u⟫) + a⁻¹ * (g₂ u * Δ η u) := fun u ↦ by
    rw [C.indicator_eq_of_cutoff hη (norm_eq_of_mem_sphere u)]
    exact C.weightedBochner_pointwise hS hη hη0 ha ha1 hδ (norm_eq_of_mem_sphere u)
  have iB' : Integrable (fun u : sphere (0 : E n) 1 ↦
      a⁻¹ * (g₂ u * Δ η u + ⟪∇ η u, ∇ g₂ u⟫)) σ := iB.const_mul a⁻¹
  have iC' : Integrable (fun u : sphere (0 : E n) 1 ↦ a⁻¹ * (g₂ u * Δ η u)) σ := iC.const_mul a⁻¹
  have iAB : Integrable (fun u : sphere (0 : E n) 1 ↦ (f₁ u * Δ C.wSq u + ⟪∇ f₁ u, ∇ C.wSq u⟫) -
      a⁻¹ * (g₂ u * Δ η u + ⟪∇ η u, ∇ g₂ u⟫)) σ := iA.sub iB'
  have iR : Integrable (fun u : sphere (0 : E n) 1 ↦ (f₁ u * Δ C.wSq u + ⟪∇ f₁ u, ∇ C.wSq u⟫) -
      a⁻¹ * (g₂ u * Δ η u + ⟪∇ η u, ∇ g₂ u⟫) + a⁻¹ * (g₂ u * Δ η u)) σ := iAB.add iC'
  have iL' : Integrable (fun u : sphere (0 : E n) 1 ↦ (4 * a - 2) *
      C.D.indicator (fun x ↦ η x * ((C.wSq x + δ) ^ (a - 1) * C.bSq x)) u) σ :=
    iL.const_mul (4 * a - 2)
  have hmono := integral_mono iL' iR hpt
  rw [integral_const_mul, integral_add iAB iC', integral_sub iA iB', integral_const_mul,
    integral_const_mul, hIA, hIB] at hmono
  -- bound the remaining term
  have hC : ∫ u : sphere (0 : E n) 1, g₂ u * Δ η u ∂σ ≤
      (M + δ) ^ a * ∫ u : sphere (0 : E n) 1, |Δ η u| ∂σ := by
    rw [← integral_const_mul]
    refine integral_mono iC (iΔ.const_mul _) fun u ↦ ?_
    have hu1 := norm_eq_of_mem_sphere u
    have hu0 : (u : E n) ≠ 0 := by intro h; rw [h] at hu1; simp at hu1
    by_cases huK : (u : E n) ∈ K
    · have hV : 0 ≤ C.wSq u + δ := by linarith [C.wSq_nonneg u]
      have hg : g₂ u ≤ (M + δ) ^ a :=
        Real.rpow_le_rpow hV (by linarith [hM _ huK]) ha.le
      have hg0 : 0 ≤ g₂ u := Real.rpow_nonneg hV _
      calc g₂ u * Δ η u ≤ g₂ u * |Δ η u| := mul_le_mul_of_nonneg_left (le_abs_self _) hg0
        _ ≤ (M + δ) ^ a * |Δ η u| := mul_le_mul_of_nonneg_right hg (abs_nonneg _)
    · have huK' : radialProj (u : E n) ∉ K := by rwa [radialProj_of_norm_eq_one hu1]
      rw [hη.laplacian_eq_zero hu0 huK']
      simp
  have ha' : 0 ≤ a⁻¹ := inv_nonneg.2 ha.le
  calc (4 * a - 2) * ∫ u : sphere (0 : E n) 1,
        C.D.indicator (fun x ↦ η x * ((C.wSq x + δ) ^ (a - 1) * C.bSq x)) u ∂σ
      ≤ 0 - a⁻¹ * 0 + a⁻¹ * ∫ u : sphere (0 : E n) 1, g₂ u * Δ η u ∂σ := hmono
    _ ≤ a⁻¹ * ((M + δ) ^ a * ∫ u : sphere (0 : E n) 1, |Δ η u| ∂σ) := by
      have := mul_le_mul_of_nonneg_left hC ha'
      linarith
    _ = _ := by ring

/-- **The absorption estimate** for `a = 29/50` and `0 < δ ≤ 1`:
`(8/25) I_δ ≤ a⁻¹ (M + 1)^a ‖Δη‖_{L¹}`. -/
theorem weightedBochner_absorption [NeZero n] (hη : IsConeCutoff η K C.D)
    (hη0 : ∀ x, 0 ≤ η x) {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ K, C.wSq x ≤ M) :
    8 / 25 * ∫ u : sphere (0 : E n) 1,
        C.D.indicator (fun x ↦ η x * ((C.wSq x + δ) ^ ((29 / 50 : ℝ) - 1) * C.bSq x)) u
        ∂(volume : Measure (E n)).toSphere ≤
      (29 / 50 : ℝ)⁻¹ * (M + 1) ^ (29 / 50 : ℝ) *
        ∫ u : sphere (0 : E n) 1, |Δ η u| ∂(volume : Measure (E n)).toSphere := by
  have h := C.weightedBochner_uniform hS hη hη0 (a := 29 / 50) (by norm_num) (by norm_num) hδ hM
  have hpow : (M + δ) ^ (29 / 50 : ℝ) ≤ (M + 1) ^ (29 / 50 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hΔ : 0 ≤ ∫ u : sphere (0 : E n) 1, |Δ η u| ∂(volume : Measure (E n)).toSphere :=
    integral_nonneg fun _ ↦ abs_nonneg _
  have h4 : (4 * (29 / 50 : ℝ) - 2) = 8 / 25 := by norm_num
  rw [h4] at h
  refine h.trans ?_
  gcongr

end Uniform

/-! ### Integrability on the link -/

section Integrability

variable (hS : C.Sing = {0})
include hS

omit hS in
theorem rpow_wSq_eq_zero {a : ℝ} (ha1 : a < 1) {x : E n} (hx : ¬0 < C.wSq x) :
    C.wSq x ^ (a - 1) = 0 := by
  have : C.wSq x = 0 := le_antisymm (not_lt.1 hx) (C.wSq_nonneg x)
  rw [this, Real.zero_rpow (by linarith)]

/-- The positive set `{x ∈ D : w(x) > 0}` is open. -/
theorem isOpen_wSq_pos : IsOpen {x | x ∈ C.D ∧ 0 < C.wSq x} :=
  (C.continuousOn_wSq hS).isOpen_inter_preimage C.isOpen_D isOpen_Ioi

omit hS in
/-- `w^{2a-2}|B|²` restricted to `D` is the restriction to the positive set. -/
theorem indicator_weighted_eq {a : ℝ} (ha1 : a < 1) :
    C.D.indicator (fun x ↦ C.wSq x ^ (a - 1) * C.bSq x) =
      {x | x ∈ C.D ∧ 0 < C.wSq x}.indicator (fun x ↦ C.wSq x ^ (a - 1) * C.bSq x) := by
  funext x
  by_cases hx : x ∈ C.D
  · by_cases hw : 0 < C.wSq x
    · rw [indicator_of_mem hx,
        indicator_of_mem (show x ∈ {x | x ∈ C.D ∧ 0 < C.wSq x} from ⟨hx, hw⟩)]
    · rw [indicator_of_mem hx, indicator_of_notMem (fun h ↦ hw h.2), C.rpow_wSq_eq_zero ha1 hw,
        zero_mul]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h ↦ hx h.1)]

theorem measurable_weighted {a : ℝ} (ha1 : a < 1) :
    Measurable fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (fun x ↦ C.wSq x ^ (a - 1) * C.bSq x) u := by
  rw [C.indicator_weighted_eq ha1]
  refine measurable_sphere_indicator (C.isOpen_wSq_pos hS) fun x hx ↦ ?_
  have hw := (C.continuousOn_wSq hS).continuousAt (C.isOpen_D.mem_nhds hx.1)
  have hb := (C.continuousOn_bSq hS).continuousAt (C.isOpen_D.mem_nhds hx.1)
  exact ((hw.rpow_const (Or.inl hx.2.ne')).mul hb).continuousWithinAt

/-- **Weighted integrability** (`1/2 < a < 1`): `∫_{D ∩ S, w > 0} w^{2a-2} |B|² dσ < ∞`. The
integrand is `0` where `w = 0`, by the convention `0^{a-1} = 0`. -/
theorem integrable_weighted_B [NeZero n] {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) :
    Integrable (fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (fun x ↦ C.wSq x ^ (a - 1) * C.bSq x) u)
      (volume : Measure (E n)).toSphere := by
  set σ := (volume : Measure (E n)).toSphere
  set T : E n → ℝ := C.D.indicator (fun x ↦ C.wSq x ^ (a - 1) * C.bSq x) with hT
  have hT0 : ∀ u : sphere (0 : E n) 1, 0 ≤ T u := fun u ↦ by
    by_cases hu : (u : E n) ∈ C.D
    · rw [hT, indicator_of_mem hu]
      exact mul_nonneg (Real.rpow_nonneg (C.wSq_nonneg _) _)
        (C.bSq_nonneg hS hu (norm_eq_of_mem_sphere u))
    · rw [hT, indicator_of_notMem hu]
  have hTm : Measurable fun u : sphere (0 : E n) 1 ↦ T u := C.measurable_weighted hS ha1
  -- the cut-off and the constants
  obtain ⟨η, K, V, hη, hKs, hη01, hV, hZV, hηV⟩ := C.exists_cutoff_hessZero hS
  obtain ⟨b, hb, hbV⟩ := C.exists_w_lower_bound_off hS e₀ hV hZV
  obtain ⟨M, hM0, hM⟩ := C.exists_wSq_bSq_le hS
  have hMK : ∀ x ∈ K, C.wSq x ≤ M := fun x hx ↦
    (hM x (hη.subset hx) (mem_sphere_zero_iff_norm.1 (hKs hx))).1
  set A := a⁻¹ * (M + 1) ^ a * (∫ u : sphere (0 : E n) 1, |Δ η u| ∂σ) / (4 * a - 2) with hA
  have h4a : 0 < 4 * a - 2 := by linarith
  have ha0 : 0 < a := by linarith
  -- the uniform bound along `δ = 1/(k+1)`
  set δ : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hδ_def
  have hδ : ∀ k, 0 < δ k := fun k ↦ by positivity
  have hδ1 : ∀ k, δ k ≤ 1 := fun k ↦ by
    rw [hδ_def, div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set I : ℕ → E n → ℝ :=
    fun k ↦ C.D.indicator (fun x ↦ η x * ((C.wSq x + δ k) ^ (a - 1) * C.bSq x)) with hI
  have hI0 : ∀ k (u : sphere (0 : E n) 1), 0 ≤ I k u := fun k u ↦ by
    by_cases hu : (u : E n) ∈ C.D
    · rw [hI]; dsimp only; rw [indicator_of_mem hu]
      have hV0 : 0 ≤ C.wSq u + δ k := by linarith [C.wSq_nonneg u, hδ k]
      exact mul_nonneg (hη01 _).1 (mul_nonneg (Real.rpow_nonneg hV0 _)
        (C.bSq_nonneg hS hu (norm_eq_of_mem_sphere u)))
    · rw [hI]; dsimp only; rw [indicator_of_notMem hu]
  have iI : ∀ k, Integrable (fun u : sphere (0 : E n) 1 ↦ I k u) σ := fun k ↦
    C.integrable_cutoff_weighted hS hη (hδ k)
  have hΔ : 0 ≤ ∫ u : sphere (0 : E n) 1, |Δ η u| ∂σ := integral_nonneg fun _ ↦ abs_nonneg _
  have hIle : ∀ k, ∫ u : sphere (0 : E n) 1, I k u ∂σ ≤ A := fun k ↦ by
    have h := C.weightedBochner_uniform hS hη (fun x ↦ (hη01 x).1) ha0 ha1.le (hδ k) hMK
    have hpow : (M + δ k) ^ a ≤ (M + 1) ^ a :=
      Real.rpow_le_rpow (by linarith [hδ k]) (by linarith [hδ1 k]) ha0.le
    rw [hA, le_div_iff₀ h4a, mul_comm]
    refine h.trans ?_
    have : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
    gcongr
  -- Fatou's lemma
  have hlim : ∀ u : sphere (0 : E n) 1, ENNReal.ofReal (η u * T u) ≤
      liminf (fun k ↦ ENNReal.ofReal (I k u)) atTop := fun u ↦ by
    by_cases hu : (u : E n) ∈ C.D ∧ 0 < C.wSq u
    · have ht : Tendsto (fun k ↦ I k u) atTop (𝓝 (η u * T u)) := by
        simp only [hI, hT, indicator_of_mem hu.1]
        have hc : ContinuousAt (fun t : ℝ ↦ η u * ((C.wSq u + t) ^ (a - 1) * C.bSq u)) 0 := by
          refine continuousAt_const.mul (ContinuousAt.mul ?_ continuousAt_const)
          exact (continuousAt_const.add continuousAt_id).rpow_const
            (Or.inl (by simpa using hu.2.ne'))
        have := hc.tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa [Function.comp_def, hδ_def] using this
      exact (((ENNReal.continuous_ofReal.tendsto _).comp ht).liminf_eq).symm.le
    · have : η u * T u = 0 := by
        by_cases hD : (u : E n) ∈ C.D
        · have hw : ¬0 < C.wSq u := fun h ↦ hu ⟨hD, h⟩
          rw [hT, indicator_of_mem hD, C.rpow_wSq_eq_zero ha1 hw]
          ring
        · rw [hT, indicator_of_notMem hD, mul_zero]
      rw [this, ENNReal.ofReal_zero]
      exact zero_le
  have hfatou : ∫⁻ u, ENNReal.ofReal (η u * T u) ∂σ ≤ ENNReal.ofReal A := by
    calc ∫⁻ u, ENNReal.ofReal (η u * T u) ∂σ
        ≤ ∫⁻ u, liminf (fun k ↦ ENNReal.ofReal (I k u)) atTop ∂σ := lintegral_mono hlim
      _ ≤ liminf (fun k ↦ ∫⁻ u, ENNReal.ofReal (I k u) ∂σ) atTop :=
        lintegral_liminf_le' fun k ↦ (iI k).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal A := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun k ↦ ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (iI k) (ae_of_all _ (hI0 k))]
        exact ENNReal.ofReal_le_ofReal (hIle k)
  -- off the set where `η = 1`
  set c := b ^ (a - 1) * M
  have hpt : ∀ u : sphere (0 : E n) 1,
      ENNReal.ofReal (T u) ≤ ENNReal.ofReal (η u * T u) + ENNReal.ofReal c := fun u ↦ by
    have hu1 := norm_eq_of_mem_sphere u
    by_cases hD : (u : E n) ∈ C.D
    swap
    · rw [hT, indicator_of_notMem hD, ENNReal.ofReal_zero]
      exact zero_le
    by_cases huV : (u : E n) ∈ V
    · rw [hηV _ huV, one_mul]
      exact le_self_add
    · have hbw : b ≤ C.wSq u := by rw [C.wSq_of_norm_eq_one hu1]; exact hbV _ hD hu1 huV
      have h1 : C.wSq u ^ (a - 1) ≤ b ^ (a - 1) :=
        Real.rpow_le_rpow_of_nonpos hb hbw (by linarith)
      have h2 : T u ≤ c := by
        rw [hT, indicator_of_mem hD]
        exact mul_le_mul h1 (hM _ hD hu1).2 (C.bSq_nonneg hS hD hu1) (Real.rpow_nonneg hb.le _)
      exact (ENNReal.ofReal_le_ofReal h2).trans le_add_self
  have hfin : ∫⁻ u, ENNReal.ofReal (T u) ∂σ < ⊤ := by
    calc ∫⁻ u, ENNReal.ofReal (T u) ∂σ
        ≤ ∫⁻ u, (ENNReal.ofReal (η u * T u) + ENNReal.ofReal c) ∂σ := lintegral_mono hpt
      _ = ∫⁻ u, ENNReal.ofReal (η u * T u) ∂σ + ENNReal.ofReal c * σ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hfatou.trans_lt ENNReal.ofReal_lt_top,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  exact ⟨hTm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hT0)).2 hfin⟩

/-- `w^{2a}` is integrable on the link (`a > 0`). -/
theorem integrable_wSq_rpow {a : ℝ} (ha : 0 < a) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator (fun x ↦ C.wSq x ^ a) u)
      (volume : Measure (E n)).toSphere := by
  obtain ⟨M, hM0, hM⟩ := C.exists_wSq_bSq_le hS
  have hmeas : Measurable fun u : sphere (0 : E n) 1 ↦ C.D.indicator (fun x ↦ C.wSq x ^ a) u :=
    measurable_sphere_indicator C.isOpen_D fun x hx ↦
      (((C.continuousOn_wSq hS).continuousAt (C.isOpen_D.mem_nhds hx)).rpow_const
        (Or.inr ha.le)).continuousWithinAt
  refine Integrable.mono' (integrable_const (M ^ a)) hmeas.aestronglyMeasurable
    (ae_of_all _ fun u ↦ ?_)
  have hu1 := norm_eq_of_mem_sphere u
  by_cases hD : (u : E n) ∈ C.D
  · rw [indicator_of_mem hD, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (C.wSq_nonneg _) _)]
    exact Real.rpow_le_rpow (C.wSq_nonneg _) (hM _ hD hu1).1 ha.le
  · rw [indicator_of_notMem hD, norm_zero]
    exact Real.rpow_nonneg hM0 a

end Integrability

/-! ### The dominator -/

/-- The dominator `D_o = w^{2a} (1 + |B|/w)²` on `{w > 0}`, and `0` on `{w = 0}`. -/
def dominatorO (a : ℝ) (x : E n) : ℝ :=
  if 0 < C.wSq x then C.wSq x ^ a * (1 + √(C.bSq x) / √(C.wSq x)) ^ 2 else 0

theorem dominatorO_nonneg (a : ℝ) (x : E n) : 0 ≤ C.dominatorO a x := by
  unfold dominatorO
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (C.wSq_nonneg x) _) (sq_nonneg _)
  · exact le_rfl

/-- `D_o ≤ 2 w^{2a} + 2 w^{2a-2} |B|²`. -/
theorem dominatorO_le {a : ℝ} {x : E n} (hb : 0 ≤ C.bSq x) :
    C.dominatorO a x ≤ 2 * C.wSq x ^ a + 2 * (C.wSq x ^ (a - 1) * C.bSq x) := by
  have hw0 := C.wSq_nonneg x
  have h1 := Real.rpow_nonneg hw0 a
  have h2 := Real.rpow_nonneg hw0 (a - 1)
  unfold dominatorO
  split_ifs with hw
  · set s := √(C.bSq x) / √(C.wSq x)
    have hs : s ^ 2 = C.bSq x / C.wSq x := by
      rw [div_pow, Real.sq_sqrt hb, Real.sq_sqrt hw0]
    have hsq : (1 + s) ^ 2 ≤ 2 + 2 * s ^ 2 := by nlinarith [sq_nonneg (1 - s)]
    have hpow : C.wSq x ^ (a - 1) = C.wSq x ^ a / C.wSq x := Real.rpow_sub_one hw.ne' a
    calc C.wSq x ^ a * (1 + s) ^ 2 ≤ C.wSq x ^ a * (2 + 2 * s ^ 2) :=
          mul_le_mul_of_nonneg_left hsq h1
      _ = 2 * C.wSq x ^ a + 2 * (C.wSq x ^ (a - 1) * C.bSq x) := by
          rw [hs, hpow]
          field_simp
  · exact add_nonneg (mul_nonneg two_pos.le h1) (mul_nonneg two_pos.le (mul_nonneg h2 hb))

/-- **Integrability of the dominator** (`1/2 < a < 1`): `D_o ∈ L¹(D ∩ S^{n-1})`. -/
theorem integrable_dominatorO [NeZero n] (hS : C.Sing = {0}) {a : ℝ} (ha : 1 / 2 < a)
    (ha1 : a < 1) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator (C.dominatorO a) u)
      (volume : Measure (E n)).toSphere := by
  set σ := (volume : Measure (E n)).toSphere
  obtain ⟨M, hM0, hM⟩ := C.exists_wSq_bSq_le hS
  have iT := C.integrable_weighted_B hS ha ha1
  have hmeas : Measurable fun u : sphere (0 : E n) 1 ↦ C.D.indicator (C.dominatorO a) u := by
    have heq : C.D.indicator (C.dominatorO a) = {x | x ∈ C.D ∧ 0 < C.wSq x}.indicator
        (fun x ↦ C.wSq x ^ a * (1 + √(C.bSq x) / √(C.wSq x)) ^ 2) := by
      funext x
      by_cases hx : x ∈ C.D
      · by_cases hw : 0 < C.wSq x
        · rw [indicator_of_mem hx,
            indicator_of_mem (show x ∈ {x | x ∈ C.D ∧ 0 < C.wSq x} from ⟨hx, hw⟩)]
          simp [dominatorO, hw]
        · rw [indicator_of_mem hx, indicator_of_notMem (fun h ↦ hw h.2)]
          simp [dominatorO, hw]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h ↦ hx h.1)]
    rw [heq]
    refine measurable_sphere_indicator (C.isOpen_wSq_pos hS) fun x hx ↦ ?_
    have hw := (C.continuousOn_wSq hS).continuousAt (C.isOpen_D.mem_nhds hx.1)
    have hb := (C.continuousOn_bSq hS).continuousAt (C.isOpen_D.mem_nhds hx.1)
    exact ((hw.rpow_const (Or.inl hx.2.ne')).mul ((continuousAt_const.add
      (hb.sqrt.div hw.sqrt (Real.sqrt_pos.2 hx.2).ne')).pow 2)).continuousWithinAt
  have ig : Integrable (fun u : sphere (0 : E n) 1 ↦ 2 * M ^ a +
      2 * C.D.indicator (fun x ↦ C.wSq x ^ (a - 1) * C.bSq x) u) σ :=
    (integrable_const _).add (iT.const_mul 2)
  refine Integrable.mono' ig hmeas.aestronglyMeasurable (ae_of_all _ fun u ↦ ?_)
  have hu1 := norm_eq_of_mem_sphere u
  rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun x _ ↦ C.dominatorO_nonneg a x) _)]
  by_cases hD : (u : E n) ∈ C.D
  · rw [indicator_of_mem hD, indicator_of_mem hD]
    have h := C.dominatorO_le (a := a) (C.bSq_nonneg hS hD hu1)
    have hwa : C.wSq u ^ a ≤ M ^ a :=
      Real.rpow_le_rpow (C.wSq_nonneg _) (hM _ hD hu1).1 (by linarith)
    linarith
  · rw [indicator_of_notMem hD, indicator_of_notMem hD]
    have := Real.rpow_nonneg hM0 a
    linarith

end ConeData

end OnePhaseDimension
