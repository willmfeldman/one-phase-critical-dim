/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.FluxFunctional
public import OnePhaseDimension.Geometry.BoundaryJets

/-!
# The collar extension

Given a cone `C : ConeData n` and a compact set `K` away from the singular set, we glue the
defining charts of `C` at the points of `K ∩ closure D` into one smooth function `F̂` on the whole
space. On an open set `W ⊇ K ∩ closure D`:

* `u = max F̂ 0` and `D = {F̂ > 0}`;
* `F̂ < 0` off `closure D`, and `|∇F̂| = 1` on `{F̂ = 0}`;
* at every point of `closure D ∩ W`, all derivatives of `F̂` agree with those of any chart
  `u = max F 0` (in particular with `u` from inside `D`).

The gluing is sequential: `G_{k+1} = ψ_k F_k + (1 - ψ_k) G_k`, with `ψ_k` a cut-off supported in
the `k`-th chart and equal to `1` on a ball. At each point of `W` the value of `F̂` is a convex
combination of the chart values there, and the chart values agree with `u` on `D` and are
negative off `closure D`.

## Main results

* `ConeData.exists_collar`: the collar extension.
* `iteratedFDeriv_eq_of_eqOn`: functions agreeing on an open set have the same jets at the
  points of its closure.

## Differences from the source

The 2026-09-24 version extends `F` across the boundary by a smooth extension of the one-sided
jets (and cites smooth boundary regularity). We glue the charts supplied by `ConeData`, which
are already two-sided.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### Jets of functions agreeing on an open set -/

theorem eq_zero_of_mem_closure' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [Zero Y] {φ : X → Y} {S : Set X} {x₀ : X} (hφ : ContinuousAt φ x₀)
    (hx : x₀ ∈ closure S) (h : ∀ y ∈ S, φ y = 0) : φ x₀ = 0 := by
  have := hφ.continuousWithinAt.mem_closure_image hx
  have hsub : φ '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  simpa using closure_mono hsub this

/-- Functions that are `C^k` near `x` and agree on an open set `S` with `x ∈ closure S` have the
same `k`-th derivative at `x`. -/
theorem iteratedFDeriv_eq_of_eqOn {f g : E n → ℝ} {S : Set (E n)} {x : E n} {k : ℕ}
    (hS : IsOpen S) (hx : x ∈ closure S) (hfg : EqOn f g S) (hf : ContDiffAt ℝ k f x)
    (hg : ContDiffAt ℝ k g x) : iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k g x := by
  refine sub_eq_zero.1 (eq_zero_of_mem_closure' (φ := fun y ↦
    iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k g y) ?_ hx fun y hy ↦ ?_)
  · exact (hf.iteratedFDeriv_right (m := 0) (by simp)).continuousAt.sub
      (hg.iteratedFDeriv_right (m := 0) (by simp)).continuousAt
  · have hev : f =ᶠ[𝓝 y] g := Filter.eventually_of_mem (hS.mem_nhds hy) hfg
    exact sub_eq_zero.2 (hev.iteratedFDeriv ℝ k).self_of_nhds

/-! ### Scalar products with cut-offs -/

/-- A smooth function supported in `U` times a function of class `C^k` on `U` is `C^k`. -/
theorem contDiff_mul_of_tsupport_subset {χ G : E n → ℝ} {U : Set (E n)} {k : WithTop ℕ∞}
    (hU : IsOpen U) (hχ : ContDiff ℝ k χ) (hG : ContDiffOn ℝ k G U) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ k fun y ↦ χ y * G y := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul (hG.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h ↦ hx (hχU h)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
    simp [hy]

/-! ### Collar pieces and sequential gluing -/

namespace ConeData

variable (C : ConeData n)

/-- A value `v` is admissible for the collar at `x`: `v = u(x)` on `D`, `v ≤ 0` off `D`, and
`v < 0` off `closure D`. -/
def CollarGood (x : E n) (v : ℝ) : Prop :=
  (x ∈ C.D → v = C.u x) ∧ (x ∉ C.D → v ≤ 0) ∧ (x ∉ closure C.D → v < 0)

variable {C}

theorem CollarGood.convex {x : E n} {a b t : ℝ} (ha : C.CollarGood x a) (hb : C.CollarGood x b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : C.CollarGood x (t * a + (1 - t) * b) := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [ha.1 hx, hb.1 hx]; ring
  · have := ha.2.1 hx; have := hb.2.1 hx; nlinarith
  · have h1 : t * a ≤ t * max a b := mul_le_mul_of_nonneg_left (le_max_left _ _) ht0
    have h2 : (1 - t) * b ≤ (1 - t) * max a b :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    have h3 : max a b < 0 := max_lt (ha.2.2 hx) (hb.2.2 hx)
    linarith

theorem D_subset_pos : C.D ⊆ {x | 0 < C.u x} := by
  rw [C.D_eq]; exact connectedComponentIn_subset _ _

/-- One piece of the collar: a chart `(U, F)` of `C` and a cut-off `ψ` supported in `U`, equal
to `1` on the open set `V`. -/
structure CollarPiece (C : ConeData n) where
  /-- The cut-off. -/
  ψ : E n → ℝ
  /-- The chart domain. -/
  U : Set (E n)
  /-- The chart function. -/
  F : E n → ℝ
  /-- The open set on which the cut-off equals `1`. -/
  V : Set (E n)
  contDiff_ψ : ContDiff ℝ ∞ ψ
  nonneg_ψ : ∀ x, 0 ≤ ψ x
  le_one_ψ : ∀ x, ψ x ≤ 1
  tsupport_ψ : tsupport ψ ⊆ U
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  ψ_eq_one : ∀ x ∈ V, ψ x = 1
  contDiffOn_F : ContDiffOn ℝ ∞ F U
  eq_max : ∀ x ∈ U, C.u x = max (F x) 0
  pos_mem : ∀ x ∈ U, 0 < F x → x ∈ C.D
  norm_gradient : ∀ x ∈ U, F x = 0 → ‖∇ F x‖ = 1
  disjoint_sing : Disjoint U C.Sing

namespace CollarPiece

variable (p : CollarPiece C)

theorem V_subset_U : p.V ⊆ p.U := fun x hx ↦
  p.tsupport_ψ (subset_tsupport _ (by
    rw [Function.mem_support, p.ψ_eq_one x hx]; exact one_ne_zero))

/-- The chart values are admissible. -/
theorem collarGood {x : E n} (hx : x ∈ p.U) : C.CollarGood x (p.F x) := by
  refine ⟨fun hxD ↦ ?_, fun hxD ↦ ?_, fun hxD ↦ ?_⟩
  · have hpos : 0 < C.u x := D_subset_pos hxD
    rw [p.eq_max x hx] at hpos ⊢
    rcases le_or_gt (p.F x) 0 with h | h
    · rw [max_eq_right h] at hpos; exact absurd hpos (lt_irrefl _)
    · rw [max_eq_left h.le]
  · exact not_lt.1 fun h ↦ hxD (p.pos_mem x hx h)
  · have hle : p.F x ≤ 0 := not_lt.1 fun h ↦ hxD (subset_closure (p.pos_mem x hx h))
    refine lt_of_le_of_ne hle fun h0 ↦ hxD ?_
    have hgrad := p.norm_gradient x hx h0
    have hdiff : DifferentiableAt ℝ p.F x :=
      (p.contDiffOn_F.contDiffAt (p.isOpen_U.mem_nhds hx)).differentiableAt (by simp)
    have hne : fderiv ℝ p.F x ≠ 0 := fun h ↦ by
      rw [gradient, h, map_zero, norm_zero] at hgrad
      exact zero_ne_one hgrad
    have hcl := mem_closure_pos_of_fderiv_ne_zero (p.isOpen_U.mem_nhds hx) hdiff.hasFDerivAt
      h0 hne
    exact closure_mono (fun y hy ↦ p.pos_mem y hy.1 hy.2) hcl

end CollarPiece

/-- Sequential gluing: `glue [] = 0`, `glue (p :: ps) = ψ_p F_p + (1 - ψ_p) glue ps`. -/
def glue : List (CollarPiece C) → E n → ℝ
  | [] => fun _ ↦ 0
  | p :: ps => fun x ↦ p.ψ x * p.F x + (1 - p.ψ x) * glue ps x

/-- The region where the glued function is controlled: the union of the sets `V`. -/
def glueSet : List (CollarPiece C) → Set (E n)
  | [] => ∅
  | p :: ps => p.V ∪ glueSet ps

theorem contDiff_glue : ∀ ps : List (CollarPiece C), ContDiff ℝ ∞ (glue ps)
  | [] => contDiff_const
  | p :: ps => by
    have h1 := contDiff_mul_of_tsupport_subset p.isOpen_U p.contDiff_ψ p.contDiffOn_F p.tsupport_ψ
    exact h1.add ((contDiff_const.sub p.contDiff_ψ).mul (contDiff_glue ps))

theorem isOpen_glueSet : ∀ ps : List (CollarPiece C), IsOpen (glueSet ps)
  | [] => isOpen_empty
  | p :: ps => p.isOpen_V.union (isOpen_glueSet ps)

theorem collarGood_glue : ∀ (ps : List (CollarPiece C)), ∀ x ∈ glueSet ps,
    C.CollarGood x (glue ps x)
  | [], _, hx => absurd hx (notMem_empty _)
  | p :: ps, x, hx => by
    simp only [glue]
    rcases hx with hxV | hxW
    · rw [p.ψ_eq_one x hxV, one_mul, sub_self, zero_mul, add_zero]
      exact p.collarGood (p.V_subset_U hxV)
    · have hg := collarGood_glue ps x hxW
      by_cases hψ : p.ψ x = 0
      · rw [hψ, zero_mul, zero_add, sub_zero, one_mul]; exact hg
      · have hxU : x ∈ p.U :=
          p.tsupport_ψ (subset_tsupport _ (Function.mem_support.2 hψ))
        exact (p.collarGood hxU).convex hg (p.nonneg_ψ x) (p.le_one_ψ x)

theorem glueSet_subset_sing_compl : ∀ (ps : List (CollarPiece C)), glueSet ps ⊆ C.Singᶜ
  | [] => empty_subset _
  | p :: ps => union_subset
      (fun _ hx ↦ Set.disjoint_left.1 p.disjoint_sing (p.V_subset_U hx))
      (glueSet_subset_sing_compl ps)

theorem exists_mem_V : ∀ (ps : List (CollarPiece C)), ∀ x ∈ glueSet ps, ∃ p ∈ ps, x ∈ p.V
  | [], _, hx => absurd hx (notMem_empty _)
  | p :: ps, x, hx => by
    rcases hx with hxV | hxW
    · exact ⟨p, List.mem_cons_self, hxV⟩
    · obtain ⟨q, hq, hxq⟩ := exists_mem_V ps x hxW
      exact ⟨q, List.mem_cons_of_mem _ hq, hxq⟩

/-- Every point of `closure D` away from the singular set lies in the `V` of some piece. -/
theorem exists_collarPiece {x₀ : E n} (hx₀ : x₀ ∈ closure C.D) (hs : x₀ ∉ C.Sing) :
    ∃ p : CollarPiece C, x₀ ∈ p.V := by
  obtain ⟨U, hU, hx₀U, F, hF, hu, hD, hgrad, -⟩ := C.chart x₀ ⟨hx₀, hs⟩
  set U' := U ∩ C.Singᶜ
  have hU' : IsOpen U' := hU.inter C.sing_closed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU' x₀ ⟨hx₀U, hs⟩
  obtain ⟨ψ, hψ, -, hψU, hψ01, hψ1⟩ := exists_smooth_cutoff (isCompact_closedBall x₀ (r / 2))
    isOpen_ball (closedBall_subset_ball (half_lt_self hr))
  refine ⟨⟨ψ, U', F, ball x₀ (r / 2), hψ, fun x ↦ (hψ01 x).1, fun x ↦ (hψ01 x).2,
    hψU.trans hball, hU', isOpen_ball, fun x hx ↦ hψ1 x (ball_subset_closedBall hx),
    hF.mono inter_subset_left, fun x hx ↦ hu x hx.1, fun x hx ↦ hD x hx.1,
    fun x hx ↦ hgrad x hx.1, Set.disjoint_left.2 fun x hx ↦ hx.2⟩, mem_ball_self (half_pos hr)⟩

/-- A finite list of pieces whose sets `V` cover a compact subset of `closure D \ Sing`. -/
theorem exists_collarPieces {L : Set (E n)} (hL : IsCompact L) (hLD : L ⊆ closure C.D)
    (hLS : Disjoint L C.Sing) : ∃ ps : List (CollarPiece C), L ⊆ glueSet ps := by
  have hloc : ∀ x ∈ L, ∃ p : CollarPiece C, x ∈ p.V := fun x hx ↦
    exists_collarPiece (hLD hx) (Set.disjoint_left.1 hLS hx)
  choose P hP using hloc
  obtain ⟨T, hcover⟩ := hL.elim_nhds_subcover' (fun x hx ↦ (P x hx).V)
    fun x hx ↦ (P x hx).isOpen_V.mem_nhds (hP x hx)
  refine ⟨T.toList.map fun x : L ↦ P x x.2, fun y hy ↦ ?_⟩
  obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 (hcover hy)
  have key : ∀ (l : List L), x ∈ l → y ∈ glueSet (l.map fun x : L ↦ P x x.2) := by
    intro l
    induction l with
    | nil => intro h; exact absurd h List.not_mem_nil
    | cons a l ih =>
      intro h
      simp only [List.map_cons, glueSet]
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl hyx
      · exact Or.inr (ih h)
  exact key _ (Finset.mem_toList.2 hxT)

/-- On a chart domain, `F = u` on `D`. -/
theorem eq_of_mem_D {U : Set (E n)} {F : E n → ℝ} (hu : ∀ y ∈ U, C.u y = max (F y) 0) {y : E n}
    (hyU : y ∈ U) (hyD : y ∈ C.D) : F y = C.u y := by
  have hpos : 0 < C.u y := D_subset_pos hyD
  rw [hu y hyU] at hpos ⊢
  rcases le_or_gt (F y) 0 with h | h
  · rw [max_eq_right h] at hpos; exact absurd hpos (lt_irrefl _)
  · rw [max_eq_left h.le]

/-- **The collar extension.** For a compact set `K` away from the singular set there are an open
set `W ⊇ K ∩ closure D` away from the singular set and a smooth function `F̂` on the whole space
such that `(W, F̂)` is a defining chart of `D` (`u = max F̂ 0`, `D = {F̂ > 0}` on `W`), `F̂ < 0` on
`W \ closure D`, `|∇F̂| = 1` on `{F̂ = 0} ∩ W`, and at every point of `closure D ∩ W` the jets of
`F̂` agree with those of any chart `u = max F 0`. -/
theorem exists_collar (C : ConeData n) {K : Set (E n)} (hK : IsCompact K)
    (hKS : Disjoint K C.Sing) :
    ∃ (W : Set (E n)) (F : E n → ℝ), IsOpen W ∧ K ∩ closure C.D ⊆ W ∧ Disjoint W C.Sing ∧
      ContDiff ℝ ∞ F ∧ IsBoundaryChart ∞ C.D C.u W F ∧
      (∀ x ∈ W, x ∉ closure C.D → F x < 0) ∧ (∀ x ∈ W, F x = 0 → ‖∇ F x‖ = 1) ∧
      ∀ x ∈ W ∩ closure C.D, ∀ (U : Set (E n)) (G : E n → ℝ), IsOpen U → x ∈ U →
        ContDiffOn ℝ ∞ G U → (∀ y ∈ U, C.u y = max (G y) 0) →
        ∀ k : ℕ, iteratedFDeriv ℝ k F x = iteratedFDeriv ℝ k G x := by
  obtain ⟨ps, hps⟩ := exists_collarPieces (hK.inter_right isClosed_closure) inter_subset_right
    (hKS.mono_left inter_subset_left)
  set W := glueSet ps
  set F := glue ps
  have hW : IsOpen W := isOpen_glueSet ps
  have hF : ContDiff ℝ ∞ F := contDiff_glue ps
  have hgood : ∀ x ∈ W, C.CollarGood x (F x) := collarGood_glue ps
  have hWS : W ⊆ C.Singᶜ := glueSet_subset_sing_compl ps
  -- jets
  have hjet : ∀ x ∈ W ∩ closure C.D, ∀ (U : Set (E n)) (G : E n → ℝ), IsOpen U → x ∈ U →
      ContDiffOn ℝ ∞ G U → (∀ y ∈ U, C.u y = max (G y) 0) →
      ∀ k : ℕ, iteratedFDeriv ℝ k F x = iteratedFDeriv ℝ k G x := by
    intro x hx U G hU hxU hG hu k
    have hO : IsOpen (U ∩ W) := hU.inter hW
    have hS : IsOpen (U ∩ W ∩ C.D) := hO.inter C.isOpen_D
    have hxS : x ∈ closure (U ∩ W ∩ C.D) := hO.inter_closure ⟨⟨hxU, hx.1⟩, hx.2⟩
    refine iteratedFDeriv_eq_of_eqOn hS hxS (fun y hy ↦ ?_)
      (hF.contDiffAt.of_le (natCast_le_infty k))
      ((hG.contDiffAt (hU.mem_nhds hxU)).of_le (natCast_le_infty k))
    rw [(hgood y hy.1.2).1 hy.2, eq_of_mem_D hu hy.1.1 hy.2]
  have hnorm : ∀ x ∈ W, F x = 0 → ‖∇ F x‖ = 1 := by
    intro x hx h0
    have hxD : x ∉ C.D := fun h ↦ by
      have h1 := (hgood x hx).1 h
      have h2 : 0 < C.u x := D_subset_pos h
      rw [← h1, h0] at h2
      exact lt_irrefl _ h2
    have hxcl : x ∈ closure C.D := by
      by_contra h
      have := (hgood x hx).2.2 h
      rw [h0] at this
      exact lt_irrefl _ this
    obtain ⟨U, hU, hxU, G, hG, hu, hD, hgrad, -⟩ := C.chart x ⟨hxcl, hWS hx⟩
    have hG0 : G x = 0 := by
      refine le_antisymm (not_lt.1 fun h ↦ hxD (hD x hxU h)) ?_
      by_contra hneg
      push Not at hneg
      have hopen : IsOpen (U ∩ G ⁻¹' Iio 0) :=
        hG.continuousOn.isOpen_inter_preimage hU isOpen_Iio
      obtain ⟨y, ⟨hyU, hy⟩, hyD⟩ := mem_closure_iff.1 hxcl _ hopen ⟨hxU, hneg⟩
      have h1 := eq_of_mem_D hu hyU hyD
      have h2 : 0 < C.u y := D_subset_pos hyD
      simp only [mem_preimage, mem_Iio] at hy
      rw [← h1] at h2
      exact lt_asymm hy h2
    have h1 := hjet x ⟨hx, hxcl⟩ U G hU hxU hG hu 1
    have hfd : fderiv ℝ F x = fderiv ℝ G x := by
      ext v
      have := congrArg (fun T ↦ T (fun _ ↦ v)) h1
      simpa [iteratedFDeriv_one_apply] using this
    have hgr : ∇ F x = ∇ G x := by simp only [gradient, hfd]
    rw [hgr]
    exact hgrad x hxU hG0
  refine ⟨W, F, hW, hps, Set.disjoint_left.2 fun x hx ↦ hWS hx, hF, ⟨hW, hF.contDiffOn,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx h0 h ↦ ?_⟩, fun x hx ↦ (hgood x hx).2.2,
    hnorm, hjet⟩
  · by_cases hxD : x ∈ C.D
    · rw [(hgood x hx).1 hxD, max_eq_left (C.nonneg x)]
    · obtain ⟨p, -, hxp⟩ := exists_mem_V ps x hx
      have hxU := p.V_subset_U hxp
      rw [p.eq_max x hxU, max_eq_right ((p.collarGood hxU).2.1 hxD),
        max_eq_right ((hgood x hx).2.1 hxD)]
  · refine ⟨fun hxD ↦ ?_, fun hpos ↦ ?_⟩
    · rw [(hgood x hx).1 hxD]; exact D_subset_pos hxD
    · by_contra hxD; exact absurd ((hgood x hx).2.1 hxD) (not_le.2 hpos)
  · have := hnorm x hx h0
    rw [h, norm_zero] at this
    exact zero_ne_one this

end ConeData

end OnePhaseDimension
