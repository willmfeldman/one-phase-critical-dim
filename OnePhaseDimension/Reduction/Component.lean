/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Regular

/-!
# Components of the positive phase of a first nonflat cone

Let `u` be a continuous, nonnegative, one-homogeneous global minimizer in `ℝ^{k+1}`, `k ≥ 1`, and
assume that minimizers in `ℝᵏ` are flat. We prove:

* `chart_of_mem_closure`: every component `D` of `{u > 0}` has a smooth one-sided chart at each
  point `x₀ ≠ 0` of its closure, with the positive side of the chart inside `D`;
* `connectedComponentIn_eq_of_mem_closure`: a point `x₀ ≠ 0` with `u x₀ = 0` lies in the closure
  of at most one component;
* `connectedComponentIn_eq_halfSpace`: a component on which `D²u ≡ 0` is an open half-space
  `{⟪x, b⟫ > 0}` on which `u = ⟪x, b⟫`;
* `exists_pos_iteratedFDeriv_ne_zero`: if `u` is nonzero and not flat, then `D²u(x) ≠ 0` at some
  point `x` of the positive phase.

## Differences from the source

* The 2026-09-24 version shows that the link has finitely many components with pairwise disjoint
  closures, and separates the selected component through these closures. We only use local
  separation: the positive side of the cited chart at `x₀` is connected, so it lies in a single
  component, and a point `x₀ ≠ 0` of the free boundary lies in the closure of at most one
  component. Finiteness of the set of components is not needed.
* The 2026-09-24 version selects a nonflat component by `T_o ≢ 0` and rules out the alternative
  using `|b_i| = 1` from the Bernoulli condition, opposite unit normals of disjoint half-spaces,
  and disjointness of closures. We use the ambient Hessian. If `D²u ≡ 0` on the positive phase,
  the component of a positive point is a half-space `{⟪x, b⟫ > 0}`; any other component is a
  half-space `{⟪x, b'⟫ > 0}` whose closure meets the hyperplane `b^⊥` away from `0`, which
  contradicts local separation. Hence `u = max ⟪x, b⟫ 0`, and `|b| = 1` follows by comparing `u`
  with its own (constant) blowups at a nonzero point of `b^⊥`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-- The inputs from the dimension reduction used by the reduction to a working cone. -/
structure ReductionInputs : Prop where
  translation : BlowupTranslationInvariance
  factor : FactorMinimality
  suspension : SuspensionMinimality
  isometry : IsometryMinimality

/-! ### Topology of the components -/

section Topology

variable {n : ℕ} {u : E n → ℝ}

/-- A point of the positive phase in the closure of a component lies in that component. -/
theorem mem_connectedComponentIn_of_mem_closure (hc : Continuous u) {p x : E n}
    (hx : x ∈ closure (connectedComponentIn {y | 0 < u y} p)) (hxpos : 0 < u x) :
    x ∈ connectedComponentIn {y | 0 < u y} p := by
  have hS : IsOpen {y | 0 < u y} := isOpen_lt continuous_const hc
  obtain ⟨y, hyx, hyp⟩ := mem_closure_iff.1 hx _ hS.connectedComponentIn
    (mem_connectedComponentIn (show x ∈ {y | 0 < u y} from hxpos))
  rw [connectedComponentIn_eq hyp, ← connectedComponentIn_eq hyx]
  exact mem_connectedComponentIn (show x ∈ {y | 0 < u y} from hxpos)

/-- A zero of `u` in the closure of a component of `{u > 0}` is a free boundary point. -/
theorem mem_freeBoundary_of_mem_closure {p x : E n}
    (hx : x ∈ closure (connectedComponentIn {y | 0 < u y} p)) (hx0 : u x = 0) :
    x ∈ freeBoundary u univ := by
  have hsub : connectedComponentIn {y | 0 < u y} p ⊆ posSet u univ := fun y hy ↦
    ⟨mem_univ y, connectedComponentIn_subset {y | 0 < u y} p hy⟩
  refine ⟨⟨closure_mono hsub hx, fun hint ↦ ?_⟩, mem_univ x⟩
  have h := (interior_subset hint).2
  rw [hx0] at h
  exact lt_irrefl _ h

/-- If `u = max F 0` on `ball x₀ ρ` and `x₀` lies in the closure of a component `D`, then the
positive side `{F > 0}` of the ball meets `D`. -/
theorem exists_mem_connectedComponentIn_chart_pos {F : E n → ℝ} {x₀ p : E n} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ∀ x ∈ ball x₀ ρ, u x = max (F x) 0)
    (hx₀ : x₀ ∈ closure (connectedComponentIn {y | 0 < u y} p)) :
    ∃ y ∈ connectedComponentIn {y | 0 < u y} p, y ∈ ball x₀ ρ ∧ 0 < F y := by
  obtain ⟨y, hyB, hyD⟩ := mem_closure_iff.1 hx₀ _ isOpen_ball (mem_ball_self hρ)
  refine ⟨y, hyD, hyB, ?_⟩
  have hpos : y ∈ {y | 0 < u y} := connectedComponentIn_subset _ _ hyD
  rw [mem_ofPred_eq, hu y hyB] at hpos
  by_contra h
  rw [max_eq_right (not_lt.1 h)] at hpos
  exact lt_irrefl _ hpos

/-- **Single-side property.** If `u = max F 0` on `ball x₀ ρ`, the positive side
`{x ∈ ball x₀ ρ | 0 < F x}` is preconnected, and `x₀` lies in the closure of a component `D` of
`{u > 0}`, then the positive side lies in `D`. -/
theorem chart_pos_subset_connectedComponentIn {F : E n → ℝ} {x₀ p : E n} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ∀ x ∈ ball x₀ ρ, u x = max (F x) 0)
    (hP : IsPreconnected {x ∈ ball x₀ ρ | 0 < F x})
    (hx₀ : x₀ ∈ closure (connectedComponentIn {y | 0 < u y} p)) :
    {x ∈ ball x₀ ρ | 0 < F x} ⊆ connectedComponentIn {y | 0 < u y} p := by
  obtain ⟨y, hyD, hyB, hFy⟩ := exists_mem_connectedComponentIn_chart_pos hρ hu hx₀
  have hPS : {x ∈ ball x₀ ρ | 0 < F x} ⊆ {y | 0 < u y} := by
    rintro x ⟨hxB, hFx⟩
    change 0 < u x
    rw [hu x hxB]
    exact hFx.trans_le (le_max_left _ _)
  rw [connectedComponentIn_eq hyD]
  exact hP.subset_connectedComponentIn ⟨hyB, hFy⟩ hPS

end Topology

/-! ### Charts on the closure of a component -/

section Chart

variable {k : ℕ} {u : E (k + 1) → ℝ}

/-- **Local separation.** A point `x₀ ≠ 0` with `u x₀ = 0` lies in the closure of at most one
component of `{u > 0}`. -/
theorem connectedComponentIn_eq_of_mem_closure (hR : ReductionInputs) (hk : 1 ≤ k)
    (hlow : FlatInDim k) (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) {x₀ p q : E (k + 1)} (h0 : x₀ ≠ 0)
    (hx0 : u x₀ = 0) (hp : x₀ ∈ closure (connectedComponentIn {y | 0 < u y} p))
    (hq : x₀ ∈ closure (connectedComponentIn {y | 0 < u y} q)) :
    connectedComponentIn {y | 0 < u y} p = connectedComponentIn {y | 0 < u y} q := by
  obtain ⟨ρ, hρ, F, -, hu, -, -, -, hP⟩ := exists_chart_of_freeBoundary hR.translation
    hR.isometry hR.factor hk hlow hc hnn hmin hhom (mem_freeBoundary_of_mem_closure hp hx0) h0
  obtain ⟨y, hyq, hyB, hFy⟩ := exists_mem_connectedComponentIn_chart_pos hρ hu hq
  have hyp := chart_pos_subset_connectedComponentIn hρ hu hP hp ⟨hyB, hFy⟩
  rw [connectedComponentIn_eq hyp, connectedComponentIn_eq hyq]

/-- **The chart field.** At every point `x₀ ≠ 0` of the closure of a component `D` of `{u > 0}`
there is a smooth one-sided chart: `u = max F 0` near `x₀`, the positive side lies in `D`,
`|∇F| = 1` on `{F = 0}`, and `F` is harmonic on `{F > 0}`. -/
theorem chart_of_mem_closure (hR : ReductionInputs) (hk : 1 ≤ k) (hlow : FlatInDim k)
    (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) {x₀ p : E (k + 1)}
    (hx₀ : x₀ ∈ closure (connectedComponentIn {y | 0 < u y} p)) (h0 : x₀ ≠ 0) :
    ∃ U : Set (E (k + 1)), IsOpen U ∧ x₀ ∈ U ∧
      ∃ F : E (k + 1) → ℝ, ContDiffOn ℝ ∞ F U ∧ (∀ x ∈ U, u x = max (F x) 0) ∧
        (∀ x ∈ U, 0 < F x → x ∈ connectedComponentIn {y | 0 < u y} p) ∧
        (∀ x ∈ U, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ U, 0 < F x → Δ F x = 0) := by
  rcases (hnn x₀).lt_or_eq with hpos | hzero
  · -- interior point: the chart is `u` itself on the component
    have hD := mem_connectedComponentIn_of_mem_closure hc hx₀ hpos
    have hS : IsOpen {y | 0 < u y} := isOpen_lt continuous_const hc
    have hDS : connectedComponentIn {y | 0 < u y} p ⊆ {y | 0 < u y} :=
      connectedComponentIn_subset _ _
    obtain ⟨hsm, hΔ⟩ := contDiffOn_pos_and_laplacian (by omega) hc hnn hmin
    refine ⟨_, hS.connectedComponentIn, hD, u, hsm.mono hDS, fun x hx ↦ ?_, fun x hx _ ↦ hx,
      fun x hx hx0 ↦ ?_, fun x _ hx ↦ hΔ x hx⟩
    · exact (max_eq_left (hnn x)).symm
    · exact absurd hx0 (ne_of_gt (hDS hx))
  · -- free boundary point: the cited chart, whose positive side lies in the component
    obtain ⟨ρ, hρ, F, hF, hu, -, hgrad, hΔ, hP⟩ := exists_chart_of_freeBoundary hR.translation
      hR.isometry hR.factor hk hlow hc hnn hmin hhom
      (mem_freeBoundary_of_mem_closure hx₀ hzero.symm) h0
    exact ⟨ball x₀ ρ, isOpen_ball, mem_ball_self hρ, F, hF, hu,
      fun x hx hFx ↦ chart_pos_subset_connectedComponentIn hρ hu hP hx₀ ⟨hx, hFx⟩, hgrad, hΔ⟩

end Chart

/-! ### Components with vanishing Hessian -/

section HalfSpace

variable {n : ℕ} {u : E n → ℝ}

/-- A point `x` with `⟪x, c⟫ ≥ 0` lies in the closure of the open half-space `{⟪y, c⟫ > 0}`,
`c ≠ 0`. -/
theorem mem_closure_halfSpace {c x : E n} (hc : c ≠ 0) (hx : 0 ≤ ⟪x, c⟫) :
    x ∈ closure {y : E n | 0 < ⟪y, c⟫} := by
  have ht : Tendsto (fun t : ℝ ↦ x + t • c) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous fun t : ℝ ↦ x + t • c := by fun_prop
    have : Tendsto (fun t : ℝ ↦ x + t • c) (𝓝 0) (𝓝 (x + (0 : ℝ) • c)) := hcont.tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  show 0 < ⟪x + t • c, c⟫
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have : 0 < ‖c‖ ^ 2 := by positivity
  positivity

/-- **A component with vanishing Hessian is a half-space.** If `u` is continuous,
one-homogeneous and smooth on `{u > 0}`, and `D²u ≡ 0` on the component `D` of `{u > 0}`
containing `p`, then `D = {⟪x, b⟫ > 0}` and `u = ⟪x, b⟫` on `D` for some `b`. -/
theorem connectedComponentIn_eq_halfSpace (hc : Continuous u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x)
    (hsm : ContDiffOn ℝ ∞ u {x | 0 < u x}) {p : E n} (hp : 0 < u p)
    (hD2 : ∀ x ∈ connectedComponentIn {y | 0 < u y} p, iteratedFDeriv ℝ 2 u x = 0) :
    ∃ b : E n, connectedComponentIn {y | 0 < u y} p = {x | 0 < ⟪x, b⟫} ∧
      ∀ x ∈ connectedComponentIn {y | 0 < u y} p, u x = ⟪x, b⟫ := by
  set D := connectedComponentIn {y | 0 < u y} p with hDdef
  have hS : IsOpen {y | 0 < u y} := isOpen_lt continuous_const hc
  have hDo : IsOpen D := hS.connectedComponentIn
  have hDc : IsPreconnected D := isPreconnected_connectedComponentIn
  have hpD : p ∈ D := mem_connectedComponentIn (show p ∈ {y | 0 < u y} from hp)
  have hDS : D ⊆ {y | 0 < u y} := connectedComponentIn_subset _ _
  have hsmD : ContDiffOn ℝ ∞ u D := hsm.mono hDS
  have hdiff : DifferentiableOn ℝ u D := hsmD.differentiableOn (by simp)
  -- the derivative is constant on `D`
  have hdiff' : DifferentiableOn ℝ (fderiv ℝ u) D :=
    (hsmD.fderiv_of_isOpen hDo (m := 1) (by norm_cast)).differentiableOn one_ne_zero
  have hzero : D.EqOn (fderiv ℝ (fderiv ℝ u)) 0 := by
    intro x hx
    change fderiv ℝ (fderiv ℝ u) x = 0
    ext v w
    have h := iteratedFDeriv_two_apply (𝕜 := ℝ) u x ![v, w]
    rw [hD2 x hx] at h
    simpa using h.symm
  obtain ⟨L, hL⟩ := hDo.exists_is_const_of_fderiv_eq_zero hDc hdiff' hzero
  obtain ⟨c, hcL⟩ := hDo.exists_eq_add_of_fderiv_eq hDc hdiff L.differentiable.differentiableOn
    (fun x hx ↦ by rw [hL x hx, L.fderiv])
  -- homogeneity kills the constant
  have hev : ∀ᶠ t in 𝓝[>] (1 : ℝ), t • p ∈ D ∧ 1 < t := by
    have ht : Tendsto (fun t : ℝ ↦ t • p) (𝓝 1) (𝓝 p) := by
      have hcont : Continuous fun t : ℝ ↦ t • p := by fun_prop
      simpa using hcont.tendsto 1
    exact ((ht.eventually (hDo.mem_nhds hpD)).filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin
  obtain ⟨t, htD, ht1⟩ := hev.exists
  have hc0 : c = 0 := by
    have h1 := hcL htD
    have h2 := hcL hpD
    beta_reduce at h1 h2
    rw [hhom t (by linarith) p, h2, map_smul, smul_eq_mul] at h1
    have : (t - 1) * c = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  set b := (InnerProductSpace.toDual ℝ (E n)).symm L with hbdef
  have hLb : ∀ x, L x = ⟪x, b⟫ := fun x ↦ by
    rw [real_inner_comm, hbdef, InnerProductSpace.toDual_symm_apply]
  have huD : ∀ x ∈ D, u x = ⟪x, b⟫ := fun x hx ↦ by
    rw [hcL hx, hc0]
    simp only [add_zero]
    exact hLb x
  refine ⟨b, Subset.antisymm (fun x hx ↦ ?_) ?_, huD⟩
  · change 0 < ⟪x, b⟫
    rw [← huD x hx]
    exact hDS hx
  -- the half-space is preconnected and `D` is relatively clopen in it
  have hlin : IsLinearMap ℝ fun x : E n ↦ ⟪x, b⟫ :=
    ⟨fun x y ↦ inner_add_left x y b, fun c x ↦ real_inner_smul_left x b c⟩
  have hpH : 0 < ⟪p, b⟫ := by rw [← huD p hpD]; exact hp
  refine (convex_halfSpace_gt hlin 0).isPreconnected.subset_of_closure_inter_subset hDo
    ⟨p, hpH, hpD⟩ ?_
  rintro x ⟨hxcl, hxH⟩
  have huc : EqOn u (fun x ↦ ⟪x, b⟫) (closure D) :=
    Set.EqOn.closure huD hc (continuous_id.inner continuous_const)
  have hxpos : 0 < u x := by rw [huc hxcl]; exact hxH
  exact mem_connectedComponentIn_of_mem_closure hc hxcl hxpos

end HalfSpace

/-! ### Selection of a nonflat component -/

section Nonflat

/-- A nonzero vector orthogonal to `b` in `ℝ^{k+1}`, `k ≥ 1`. -/
theorem exists_ne_zero_inner_eq_zero {k : ℕ} (hk : 1 ≤ k) (b : E (k + 1)) :
    ∃ p : E (k + 1), p ≠ 0 ∧ ⟪p, b⟫ = 0 := by
  by_cases hb : b = 0
  · refine ⟨lastVec k, fun h ↦ ?_, by simp [hb]⟩
    have := norm_lastVec (k := k)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have : Fact (Module.finrank ℝ (E (k + 1)) = k + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hr : Module.finrank ℝ (ℝ ∙ b)ᗮ = k := Submodule.finrank_orthogonal_span_singleton hb
  have hne : (ℝ ∙ b)ᗮ ≠ ⊥ := Submodule.one_le_finrank_iff.1 (by rw [hr]; exact hk)
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨p, hp0, ?_⟩
  rw [real_inner_comm]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hp

/-- Every blowup of `max ⟪·, b⟫ 0` at a point of `b^⊥` is `max ⟪·, b⟫ 0` itself; hence a
half-space blowup limit `max ⟪·, e⟫ 0` there equals `max ⟪·, b⟫ 0`. -/
theorem halfSpace_eq_of_isBlowupLimit {n : ℕ} {u : E n → ℝ} {b e x₀ : E n}
    (hu : ∀ x, u x = max ⟪x, b⟫ 0) (hx₀ : ⟪x₀, b⟫ = 0)
    (h : IsBlowupLimit u x₀ (fun y ↦ max ⟪y, e⟫ 0)) (y : E n) :
    max ⟪y, e⟫ 0 = max ⟪y, b⟫ 0 := by
  obtain ⟨r, hr, -, hconv⟩ := h
  have hconst : ∀ j, blowup u x₀ (r j) y = max ⟪y, b⟫ 0 := by
    intro j
    have hm : max (r j * ⟪y, b⟫) 0 = r j * max ⟪y, b⟫ 0 := by
      rw [mul_max_of_nonneg _ _ (hr j).le, mul_zero]
    rw [blowup, hu, inner_add_left, hx₀, zero_add, real_inner_smul_left, hm,
      mul_div_cancel_left₀ _ (hr j).ne']
  have ht := (hconv.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ y)
  simp only [hconst] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

variable {k : ℕ} {u : E (k + 1) → ℝ}

/-- **Selection of a nonflat component.** If `u` is nonzero and not flat, then the Hessian of `u`
does not vanish at some point of the positive phase. -/
theorem exists_pos_iteratedFDeriv_ne_zero (hR : ReductionInputs) (hk : 1 ≤ k)
    (hlow : FlatInDim k) (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) (hpos : ∃ x, 0 < u x)
    (hnf : ¬ FlatAE u) :
    ∃ x, 0 < u x ∧ iteratedFDeriv ℝ 2 u x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hnf
  obtain ⟨hsm, -⟩ := contDiffOn_pos_and_laplacian (by omega) hc hnn hmin
  have hD2 : ∀ q, ∀ x ∈ connectedComponentIn {y | 0 < u y} q, iteratedFDeriv ℝ 2 u x = 0 :=
    fun q x hx ↦ hcon x (connectedComponentIn_subset {y | 0 < u y} q hx)
  have hmem : ∀ q, 0 < u q → q ∈ connectedComponentIn {y | 0 < u y} q :=
    fun q hq ↦ mem_connectedComponentIn (show q ∈ {y | 0 < u y} from hq)
  have hne : ∀ {q : E (k + 1)} {c : E (k + 1)}, 0 < u q →
      connectedComponentIn {y | 0 < u y} q = {x | 0 < ⟪x, c⟫} → c ≠ 0 := by
    rintro q c hq hD rfl
    have h := hmem q hq
    rw [hD] at h
    simp at h
  obtain ⟨p, hp⟩ := hpos
  obtain ⟨b, hDb, hub⟩ := connectedComponentIn_eq_halfSpace hc hhom hsm hp (hD2 p)
  have hb : b ≠ 0 := hne hp hDb
  have hucl : ∀ x, 0 ≤ ⟪x, b⟫ →
      x ∈ closure (connectedComponentIn {y | 0 < u y} p) ∧ u x = ⟪x, b⟫ := by
    intro x hx
    have hcl : x ∈ closure (connectedComponentIn {y | 0 < u y} p) := by
      rw [hDb]
      exact mem_closure_halfSpace hb hx
    exact ⟨hcl, Set.EqOn.closure hub hc (continuous_id.inner continuous_const) hcl⟩
  obtain ⟨p₀, hp₀, hp₀b⟩ := exists_ne_zero_inner_eq_zero hk b
  -- every positive point lies in the component of `p`
  have hall : ∀ y, 0 < u y → y ∈ connectedComponentIn {y | 0 < u y} p := by
    intro y hy
    by_contra hyD
    obtain ⟨b₂, hD₂, -⟩ := connectedComponentIn_eq_halfSpace hc hhom hsm hy (hD2 y)
    have hb₂ : b₂ ≠ 0 := hne hy hD₂
    obtain ⟨x₀, hx₀0, hx₀b, hx₀b₂⟩ : ∃ x₀ : E (k + 1), x₀ ≠ 0 ∧ ⟪x₀, b⟫ = 0 ∧ 0 ≤ ⟪x₀, b₂⟫ := by
      rcases le_total 0 ⟪p₀, b₂⟫ with h | h
      · exact ⟨p₀, hp₀, hp₀b, h⟩
      · refine ⟨-p₀, neg_ne_zero.2 hp₀, by rw [inner_neg_left, hp₀b, neg_zero], ?_⟩
        rw [inner_neg_left]
        linarith
    obtain ⟨hcl₁, hux⟩ := hucl x₀ hx₀b.ge
    have hcl₂ : x₀ ∈ closure (connectedComponentIn {y | 0 < u y} y) := by
      rw [hD₂]
      exact mem_closure_halfSpace hb₂ hx₀b₂
    have heq := connectedComponentIn_eq_of_mem_closure hR hk hlow hc hnn hmin hhom hx₀0
      (by rw [hux, hx₀b]) hcl₁ hcl₂
    exact hyD (heq ▸ hmem y hy)
  -- hence `u = max ⟪x, b⟫ 0`
  have hu_eq : ∀ x, u x = max ⟪x, b⟫ 0 := by
    intro x
    rcases (hnn x).lt_or_eq with hx | hx
    · rw [← hub x (hall x hx)]
      exact (max_eq_left (hnn x)).symm
    · rw [← hx]
      have hle : ⟪x, b⟫ ≤ 0 := by
        by_contra h
        push Not at h
        have hxD : x ∈ connectedComponentIn {y | 0 < u y} p := by
          rw [hDb]
          exact h
        have := hub x hxD
        linarith
      exact (max_eq_right hle).symm
  -- the normal is a unit vector: compare with a blowup at `p₀ ∈ b^⊥`
  obtain ⟨hcl₀, hu₀⟩ := hucl p₀ hp₀b.ge
  have hfb : p₀ ∈ freeBoundary u univ :=
    mem_freeBoundary_of_mem_closure hcl₀ (by rw [hu₀, hp₀b])
  obtain ⟨e, he, hbl⟩ := exists_flat_blowup hR.translation hR.isometry hR.factor hk hlow hc hnn
    hmin hhom hfb hp₀
  refine ⟨e, he, Filter.Eventually.of_forall fun x ↦ ?_⟩
  rw [hu_eq x, halfSpace_eq_of_isBlowupLimit hu_eq hp₀b hbl x]

end Nonflat

end OnePhaseDimension
