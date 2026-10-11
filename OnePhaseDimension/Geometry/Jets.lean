/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import OnePhaseDimension.Geometry.JetNorm

/-!
# Tangential jets of a one-homogeneous harmonic function

Let `u` be one-homogeneous and harmonic near a unit vector `x₀ ∈ ℝⁿ`, and let
`ι : ℝ^{n-1} → x₀^⊥` be a linear isometry with frame `τᵢ = ι eᵢ`. With `m = n - 1` and
`δ` the identity of `ℝ^{m}` (whose trace is `m`, not `n`), we define the spherical data at `x₀`:

* `g = u(x₀)`, `pᵢ = Du(x₀)[τᵢ]`;
* `T_{ij} = D²u(x₀)[τᵢ, τⱼ]`, `B_{ijk} = D³u(x₀)[τᵢ, τⱼ, τ_k]` (`B` is the pullback of `D³u` in
  every slot; `D³u` itself is not tangential);
* `(∇B)_{lijk} = D⁴u(x₀)[τ_l, τᵢ, τⱼ, τ_k] + δ_{li}T_{jk} + δ_{lj}T_{ik} + δ_{lk}T_{ij}`.

The last formula is the transported covariant derivative of `B`; here it is a definition.
All identities below are pointwise algebra at `x₀`, using only:

* symmetry of `D²u, D³u, D⁴u` (`OnePhaseDimension.iteratedFDeriv_comp_perm_of_contDiffAt`);
* the Euler relations `D^{k+1}u(x₀)[x₀, v] = (1 - k) Dᵏu(x₀)[v]`, `k ≤ 3`;
* the vanishing of the traces of `D²u, D³u, D⁴u` in two slots (harmonicity).

These three facts are bundled as `JetFacts u x₀`; `jetFacts_of_harmonic` proves them for a
`C⁴`, one-homogeneous function harmonic near `x₀`. Splitting each ambient trace into its
tangential part and its `x₀x₀` part gives `tr T = 0`, `tr B = 0` and
`∑ᵢ D⁴u[τᵢ, τᵢ, a, b] = -D⁴u[x₀, x₀, a, b] = -2 D²u[a, b]`.

## Main results

* `ConeJets`, `ConeJets.ofFun`, `ConeJets.IsConeJet` (the defining equations).
* `IsConeJet.T_symm`, `T_trace`, `B_symm₁₂`, `B_symm₂₃`, `B_trace`.
* `IsConeJet.DB_trace_eq`: `∑_l (∇B)_{lljk} = m T_{jk}` (the identity `ΔT = mT`).
* `IsConeJet.DB_commutator`: `(∇B)_{lijk} - (∇B)_{iljk} = δ_{lj}T_{ik} + δ_{lk}T_{ij} -
  δ_{ij}T_{lk} - δ_{ik}T_{lj}`.
* `IsConeJet.contract_antisymm_DB`: for `C` antisymmetric in its first two slots,
  `C_{lijk}(∇B)_{lijk} = C_{lijk}(δ_{lj}T_{ik} + δ_{lk}T_{ij})`.
* `IsConeJet.jetNormSq_two_eq`, `IsConeJet.jetNormSq_three_eq`: `|D²u(x₀)|² = |T|²` and
  `|D³u(x₀)|² = |B|² + 3|T|²`.

## Differences from the source

The 2026-09-24 version proves these identities intrinsically on the sphere, through the Codazzi
property of `T` and the curvature of the round sphere. We use the ambient jets of `u` at `x₀`:
the commutator identity then follows from the symmetry of `D⁴u`, and the contraction against an
antisymmetric tensor needs no curvature.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Laplacian EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

variable {n : ℕ}

/-! ### Frames -/

/-- The frame vectors `τᵢ = ι eᵢ`. -/
def frameVec (ι : E (n - 1) →ₗᵢ[ℝ] E n) (i : Fin (n - 1)) : E n :=
  ι (EuclideanSpace.basisFun (Fin (n - 1)) ℝ i)

/-- The orthonormal family `x₀, τ₁, …, τ_m`, indexed by `Option (Fin (n - 1))`. -/
def adaptedVec (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) : Option (Fin (n - 1)) → E n :=
  fun o ↦ o.elim x₀ (frameVec ι)

@[simp] theorem adaptedVec_none (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) :
    adaptedVec x₀ ι none = x₀ := rfl

@[simp] theorem adaptedVec_some (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (i : Fin (n - 1)) :
    adaptedVec x₀ ι (some i) = frameVec ι i := rfl

theorem orthonormal_frameVec (ι : E (n - 1) →ₗᵢ[ℝ] E n) : Orthonormal ℝ (frameVec ι) :=
  (EuclideanSpace.basisFun (Fin (n - 1)) ℝ).orthonormal.comp_linearIsometry ι

theorem inner_frameVec_frameVec (ι : E (n - 1) →ₗᵢ[ℝ] E n) (i j : Fin (n - 1)) :
    ⟪frameVec ι i, frameVec ι j⟫ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.1 (orthonormal_frameVec ι) i j

/-- The vector `∑ᵢ aᵢ τᵢ ∈ x₀^⊥` with frame coordinates `a`. -/
def frameMap (ι : E (n - 1) →ₗᵢ[ℝ] E n) (a : Fin (n - 1) → ℝ) : E n :=
  ∑ i, a i • frameVec ι i

theorem inner_frameMap_frameVec (ι : E (n - 1) →ₗᵢ[ℝ] E n) (a : Fin (n - 1) → ℝ)
    (j : Fin (n - 1)) : ⟪frameMap ι a, frameVec ι j⟫ = a j := by
  simp [frameMap, sum_inner, inner_smul_left, inner_frameVec_frameVec]

theorem inner_frameMap_frameMap (ι : E (n - 1) →ₗᵢ[ℝ] E n) (a c : Fin (n - 1) → ℝ) :
    ⟪frameMap ι a, frameMap ι c⟫ = ∑ i, a i * c i := by
  conv_lhs => rw [frameMap.eq_def ι c]
  simp only [inner_sum, inner_smul_right, inner_frameMap_frameVec]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

theorem orthonormal_adaptedVec {x₀ : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : Orthonormal ℝ (adaptedVec x₀ ι) := by
  rw [orthonormal_iff_ite]
  rintro (_ | i) (_ | j)
  · simp [hx]
  · rw [ite_eq_right (by simp), adaptedVec_none, adaptedVec_some, real_inner_comm]
    exact hι _
  · rw [ite_eq_right (by simp)]
    exact hι _
  · simp [inner_frameVec_frameVec]

theorem pos_of_norm_eq_one {x₀ : E n} (hx : ‖x₀‖ = 1) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [EuclideanSpace.norm_eq] at hx
  · exact h

/-- A linear isometry `ℝ^{n-1} → x₀^⊥` for a unit vector `x₀`, built from
`OrthonormalBasis.fromOrthogonalSpanSingleton`. Nothing depends on this particular choice. -/
def stdFrame (x₀ : E n) (hx : ‖x₀‖ = 1) : E (n - 1) →ₗᵢ[ℝ] E n :=
  haveI : Fact (Module.finrank ℝ (E n) = (n - 1) + 1) :=
    ⟨by have := pos_of_norm_eq_one hx; simp; omega⟩
  (ℝ ∙ x₀)ᗮ.subtypeₗᵢ.comp (OrthonormalBasis.fromOrthogonalSpanSingleton (n - 1)
    (fun h0 ↦ by simp [h0] at hx)).repr.symm.toLinearIsometry

theorem inner_stdFrame {x₀ : E n} (hx : ‖x₀‖ = 1) (v : E (n - 1)) :
    ⟪stdFrame x₀ hx v, x₀⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_left.1 (Submodule.coe_mem _)

/-- The orthonormal basis `x₀, τ₁, …, τ_m` of `ℝⁿ`. -/
def adaptedBasis {x₀ : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : OrthonormalBasis (Option (Fin (n - 1))) ℝ (E n) :=
  OrthonormalBasis.mk (orthonormal_adaptedVec hx hι)
    ((orthonormal_adaptedVec hx hι).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by have := pos_of_norm_eq_one hx; simp; omega)).ge

@[simp] theorem adaptedBasis_apply {x₀ : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (o : Option (Fin (n - 1))) :
    adaptedBasis hx hι o = adaptedVec x₀ ι o := by
  simp [adaptedBasis]

/-! ### Jet facts -/

/-- The pointwise facts about the ambient jets of `u` at `x₀` used by the jet algebra:
symmetry of the derivatives of order at most four, the Euler relations of a one-homogeneous
function, and the vanishing of the traces of `D²u, D³u, D⁴u` in two slots. -/
structure JetFacts (u : E n → ℝ) (x₀ : E n) : Prop where
  symm : ∀ k ≤ 4, ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E n),
    iteratedFDeriv ℝ k u x₀ (v ∘ σ) = iteratedFDeriv ℝ k u x₀ v
  euler : ∀ k ≤ 3, ∀ v : Fin k → E n,
    iteratedFDeriv ℝ (k + 1) u x₀ (Fin.cons x₀ v) = (1 - k : ℝ) * iteratedFDeriv ℝ k u x₀ v
  trace : ∀ k ≤ 2, ∀ (κ : Type) [Fintype κ] (e : OrthonormalBasis κ ℝ (E n)) (v : Fin k → E n),
    ∑ i, iteratedFDeriv ℝ (k + 2) u x₀ (Fin.cons (e i) (Fin.cons (e i) v)) = 0

/-- A `C⁴`, one-homogeneous function that is harmonic near `x₀` satisfies the jet facts. -/
theorem jetFacts_of_harmonic {u : E n → ℝ} {x₀ : E n} (hhom : IsOneHomogeneous u)
    (hu : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 4 u y) (hΔ : ∀ᶠ y in 𝓝 x₀, Δ u y = 0) :
    JetFacts u x₀ where
  symm k hk σ v :=
    iteratedFDeriv_comp_perm_of_contDiffAt (hu.self_of_nhds.of_le (by exact_mod_cast hk)) σ v
  euler k hk v := by
    rw [hhom.iteratedFDeriv_succ_apply_cons_self
      (hu.self_of_nhds.of_le (by exact_mod_cast (by omega : k + 1 ≤ 4))) v, smul_eq_mul]
  trace k hk κ _ e v :=
    sum_iteratedFDeriv_cons_cons_eq_zero e
      (hu.mono fun y hy ↦ hy.of_le (by exact_mod_cast (by omega : k + 2 ≤ 4))) hΔ v

/-! ### Elementary consequences -/

section JetFacts

variable {u : E n → ℝ} {x₀ : E n} (hJ : JetFacts u x₀)
include hJ

local notation "D1" => iteratedFDeriv ℝ 1 u x₀
local notation "D2" => iteratedFDeriv ℝ 2 u x₀
local notation "D3" => iteratedFDeriv ℝ 3 u x₀
local notation "D4" => iteratedFDeriv ℝ 4 u x₀

theorem JetFacts.D2_comm (a b : E n) : D2 ![a, b] = D2 ![b, a] := by
  have h := hJ.symm 2 (by norm_num) (Equiv.swap 0 1) ![a, b]
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem JetFacts.D3_comm₁₂ (a b c : E n) : D3 ![a, b, c] = D3 ![b, a, c] := by
  have h := hJ.symm 3 (by norm_num) (Equiv.swap 0 1) ![a, b, c]
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem JetFacts.D3_comm₂₃ (a b c : E n) : D3 ![a, b, c] = D3 ![a, c, b] := by
  have h := hJ.symm 3 (by norm_num) (Equiv.swap 1 2) ![a, b, c]
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem JetFacts.D4_comm₁₂ (a b c d : E n) : D4 ![a, b, c, d] = D4 ![b, a, c, d] := by
  have h := hJ.symm 4 (by norm_num) (Equiv.swap 0 1) ![a, b, c, d]
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem JetFacts.D4_swap_pairs (a b c d : E n) : D4 ![a, b, c, d] = D4 ![c, d, a, b] := by
  have h := hJ.symm 4 (by norm_num) (Equiv.swap 0 2 * Equiv.swap 1 3) ![a, b, c, d]
  rw [← h]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem JetFacts.D1_self : D1 ![x₀] = u x₀ := by
  have h := hJ.euler 0 (by norm_num) ![]
  simpa using h

theorem JetFacts.D2_self_left (a : E n) : D2 ![x₀, a] = 0 := by
  have h := hJ.euler 1 (by norm_num) ![a]
  simpa using h

theorem JetFacts.D2_self_right (a : E n) : D2 ![a, x₀] = 0 := by
  rw [hJ.D2_comm, hJ.D2_self_left]

theorem JetFacts.D3_self₁ (a b : E n) : D3 ![x₀, a, b] = -D2 ![a, b] := by
  have h := hJ.euler 2 (by norm_num) ![a, b]
  have h' : D3 ![x₀, a, b] = (1 - ((2 : ℕ) : ℝ)) * D2 ![a, b] := h
  rw [h']
  ring

theorem JetFacts.D3_self₂ (a b : E n) : D3 ![a, x₀, b] = -D2 ![a, b] := by
  rw [hJ.D3_comm₁₂, hJ.D3_self₁]

theorem JetFacts.D3_self₃ (a b : E n) : D3 ![a, b, x₀] = -D2 ![a, b] := by
  rw [hJ.D3_comm₂₃, hJ.D3_self₂]

theorem JetFacts.D4_self₁ (a b c : E n) : D4 ![x₀, a, b, c] = -2 * D3 ![a, b, c] := by
  have h := hJ.euler 3 (by norm_num) ![a, b, c]
  have h' : D4 ![x₀, a, b, c] = (1 - ((3 : ℕ) : ℝ)) * D3 ![a, b, c] := h
  rw [h']
  ring

/-- `D⁴u[x₀, x₀, a, b] = 2 D²u[a, b]`. -/
theorem JetFacts.D4_self_self (a b : E n) : D4 ![x₀, x₀, a, b] = 2 * D2 ![a, b] := by
  rw [hJ.D4_self₁, hJ.D3_self₁]
  ring

/-- The trace of `D²u` in an orthonormal basis vanishes. -/
theorem JetFacts.sum_D2 {κ : Type} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n)) :
    ∑ i, D2 ![e i, e i] = 0 :=
  hJ.trace 0 (by norm_num) κ e ![]

theorem JetFacts.sum_D3 {κ : Type} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n)) (c : E n) :
    ∑ i, D3 ![e i, e i, c] = 0 :=
  hJ.trace 1 (by norm_num) κ e ![c]

theorem JetFacts.sum_D4 {κ : Type} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n)) (a b : E n) :
    ∑ i, D4 ![e i, e i, a, b] = 0 :=
  hJ.trace 2 (by norm_num) κ e ![a, b]

end JetFacts

/-- A double sum of a function antisymmetric in its two arguments vanishes. -/
theorem sum_sum_eq_zero_of_antisymm {α : Type*} [Fintype α] (F : α → α → ℝ)
    (hF : ∀ a b, F a b = -F b a) : ∑ a, ∑ b, F a b = 0 := by
  have h1 : ∑ a, ∑ b, F a b = ∑ a, ∑ b, -F a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ hF b a
  simp only [Finset.sum_neg_distrib] at h1
  linarith

/-! ### The jet record -/

/-- The spherical data of a one-homogeneous function at a unit vector `x₀`, in the frame `ι`:
the value `g`, the tangential gradient `p`, the spherical Hessian `T`, its derivative `B` and the
second derivative `DB` of `T`, as arrays indexed by `Fin (n - 1)`. -/
structure ConeJets (n : ℕ) where
  /-- The base point, a unit vector. -/
  x₀ : E n
  /-- A linear isometry onto `x₀^⊥`. -/
  ι : E (n - 1) →ₗᵢ[ℝ] E n
  /-- `g = u(x₀)`. -/
  g : ℝ
  /-- `pᵢ = Du(x₀)[τᵢ]`. -/
  p : Fin (n - 1) → ℝ
  /-- `T_{ij} = D²u(x₀)[τᵢ, τⱼ]`. -/
  T : Fin (n - 1) → Fin (n - 1) → ℝ
  /-- `B_{ijk} = D³u(x₀)[τᵢ, τⱼ, τ_k]`. -/
  B : Fin (n - 1) → Fin (n - 1) → Fin (n - 1) → ℝ
  /-- `(∇B)_{lijk} = D⁴u(x₀)[τ_l, τᵢ, τⱼ, τ_k] + δ_{li}T_{jk} + δ_{lj}T_{ik} + δ_{lk}T_{ij}`. -/
  DB : Fin (n - 1) → Fin (n - 1) → Fin (n - 1) → Fin (n - 1) → ℝ

namespace ConeJets

/-- The jet record of `u` at `x₀` in the frame `ι`. -/
def ofFun (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) : ConeJets n where
  x₀ := x₀
  ι := ι
  g := u x₀
  p i := fderiv ℝ u x₀ (frameVec ι i)
  T i j := iteratedFDeriv ℝ 2 u x₀ ![frameVec ι i, frameVec ι j]
  B i j k := iteratedFDeriv ℝ 3 u x₀ ![frameVec ι i, frameVec ι j, frameVec ι k]
  DB l i j k :=
    iteratedFDeriv ℝ 4 u x₀ ![frameVec ι l, frameVec ι i, frameVec ι j, frameVec ι k] +
      (if l = i then iteratedFDeriv ℝ 2 u x₀ ![frameVec ι j, frameVec ι k] else 0) +
      (if l = j then iteratedFDeriv ℝ 2 u x₀ ![frameVec ι i, frameVec ι k] else 0) +
      (if l = k then iteratedFDeriv ℝ 2 u x₀ ![frameVec ι i, frameVec ι j] else 0)

/-- `J` is the jet record of `u`: `x₀` is a unit vector, `ι` maps isometrically into `x₀^⊥`,
`u` satisfies the jet facts at `x₀`, and the fields are given by their defining equations. -/
structure IsConeJet (u : E n → ℝ) (J : ConeJets n) : Prop where
  norm_x₀ : ‖J.x₀‖ = 1
  inner_ι : ∀ v, ⟪J.ι v, J.x₀⟫ = 0
  facts : JetFacts u J.x₀
  g_eq : J.g = u J.x₀
  p_eq : ∀ i, J.p i = fderiv ℝ u J.x₀ (frameVec J.ι i)
  T_eq : ∀ i j, J.T i j = iteratedFDeriv ℝ 2 u J.x₀ ![frameVec J.ι i, frameVec J.ι j]
  B_eq : ∀ i j k, J.B i j k =
    iteratedFDeriv ℝ 3 u J.x₀ ![frameVec J.ι i, frameVec J.ι j, frameVec J.ι k]
  DB_eq : ∀ l i j k, J.DB l i j k =
    iteratedFDeriv ℝ 4 u J.x₀ ![frameVec J.ι l, frameVec J.ι i, frameVec J.ι j, frameVec J.ι k] +
      (if l = i then J.T j k else 0) + (if l = j then J.T i k else 0) +
      (if l = k then J.T i j else 0)

theorem isConeJet_ofFun {u : E n → ℝ} {x₀ : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n}
    (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (hJ : JetFacts u x₀) :
    IsConeJet u (ofFun u x₀ ι) where
  norm_x₀ := hx
  inner_ι := hι
  facts := hJ
  g_eq := rfl
  p_eq _ := rfl
  T_eq _ _ := rfl
  B_eq _ _ _ := rfl
  DB_eq _ _ _ _ := rfl

/-- The jet record of a one-homogeneous harmonic function at a unit vector `x₀`, in the frame
`stdFrame x₀`. -/
def ofHarmonicHomogeneous (u : E n → ℝ) (x₀ : E n) (hx : ‖x₀‖ = 1) : ConeJets n :=
  ofFun u x₀ (stdFrame x₀ hx)

theorem isConeJet_ofHarmonicHomogeneous {u : E n → ℝ} {x₀ : E n} (hx : ‖x₀‖ = 1)
    (hhom : IsOneHomogeneous u) (hu : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 4 u y)
    (hΔ : ∀ᶠ y in 𝓝 x₀, Δ u y = 0) : IsConeJet u (ofHarmonicHomogeneous u x₀ hx) :=
  isConeJet_ofFun hx (inner_stdFrame hx) (jetFacts_of_harmonic hhom hu hΔ)

namespace IsConeJet

variable {u : E n → ℝ} {J : ConeJets n} (h : IsConeJet u J)
include h

/-- The adapted orthonormal basis `x₀, τ₁, …, τ_m`. -/
def basis : OrthonormalBasis (Option (Fin (n - 1))) ℝ (E n) :=
  adaptedBasis h.norm_x₀ h.inner_ι

@[simp] theorem basis_none : h.basis none = J.x₀ := by simp [basis]

@[simp] theorem basis_some (i : Fin (n - 1)) : h.basis (some i) = frameVec J.ι i := by
  simp [basis]

theorem p_eq' (i : Fin (n - 1)) :
    J.p i = iteratedFDeriv ℝ 1 u J.x₀ ![frameVec J.ι i] := by
  rw [h.p_eq, iteratedFDeriv_one_apply]
  rfl

/-! #### Symmetry and traces of `T` and `B` -/

theorem T_symm (i j : Fin (n - 1)) : J.T i j = J.T j i := by
  rw [h.T_eq, h.T_eq, h.facts.D2_comm]

theorem T_trace : ∑ i, J.T i i = 0 := by
  have h0 := h.facts.sum_D2 h.basis
  rw [Fintype.sum_option] at h0
  simp only [basis_none, basis_some, h.facts.D2_self_left, zero_add] at h0
  simpa [h.T_eq] using h0

theorem B_symm₁₂ (i j k : Fin (n - 1)) : J.B i j k = J.B j i k := by
  rw [h.B_eq, h.B_eq, h.facts.D3_comm₁₂]

theorem B_symm₂₃ (i j k : Fin (n - 1)) : J.B i j k = J.B i k j := by
  rw [h.B_eq, h.B_eq, h.facts.D3_comm₂₃]

theorem B_symm₁₃ (i j k : Fin (n - 1)) : J.B i j k = J.B k j i := by
  rw [h.B_symm₁₂, h.B_symm₂₃, h.B_symm₁₂]

/-- The trace of `B` in its first two slots vanishes. -/
theorem B_trace (k : Fin (n - 1)) : ∑ i, J.B i i k = 0 := by
  have h0 := h.facts.sum_D3 h.basis (frameVec J.ι k)
  rw [Fintype.sum_option] at h0
  simp only [basis_none, basis_some, h.facts.D3_self₁, h.facts.D2_self_left, neg_zero,
    zero_add] at h0
  simpa [h.B_eq] using h0

/-- The trace of `B` in its last two slots vanishes. -/
theorem B_trace₂₃ (k : Fin (n - 1)) : ∑ i, J.B k i i = 0 := by
  rw [Finset.sum_congr rfl fun i _ ↦ h.B_symm₁₃ k i i]
  exact h.B_trace k

/-- The tangential trace of `D⁴u` is `-2T`. -/
theorem sum_D4_frame (j k : Fin (n - 1)) :
    ∑ l, iteratedFDeriv ℝ 4 u J.x₀ ![frameVec J.ι l, frameVec J.ι l, frameVec J.ι j,
      frameVec J.ι k] = -2 * J.T j k := by
  have h0 := h.facts.sum_D4 h.basis (frameVec J.ι j) (frameVec J.ι k)
  rw [Fintype.sum_option] at h0
  simp only [basis_none, basis_some, h.facts.D4_self_self] at h0
  rw [h.T_eq]
  linarith

/-! #### The derivative of `B` -/

/-- **`ΔT = mT`**: `∑_l (∇B)_{lljk} = m T_{jk}` with `m = n - 1`. -/
theorem DB_trace_eq (j k : Fin (n - 1)) :
    ∑ l, J.DB l l j k = ((n - 1 : ℕ) : ℝ) * J.T j k := by
  simp_rw [h.DB_eq]
  simp only [ite_true, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h.sum_D4_frame, h.T_symm k j]
  ring

/-- **Commutator identity**: `(∇B)_{lijk} - (∇B)_{iljk} =
δ_{lj}T_{ik} + δ_{lk}T_{ij} - δ_{ij}T_{lk} - δ_{ik}T_{lj}`. -/
theorem DB_commutator (l i j k : Fin (n - 1)) :
    J.DB l i j k - J.DB i l j k =
      (if l = j then J.T i k else 0) + (if l = k then J.T i j else 0) -
        (if i = j then J.T l k else 0) - (if i = k then J.T l j else 0) := by
  rw [h.DB_eq, h.DB_eq, h.facts.D4_comm₁₂ (frameVec J.ι l)]
  simp only [eq_comm (a := i) (b := l)]
  ring

/-- **Contraction against an antisymmetric tensor.** If `C_{lijk} = -C_{iljk}`, then
`∑ C_{lijk}(∇B)_{lijk} = ∑ C_{lijk}(δ_{lj}T_{ik} + δ_{lk}T_{ij})`. No curvature is used: the
`D⁴u` term and the `δ_{li}T_{jk}` term are symmetric in `(l, i)`. -/
theorem contract_antisymm_DB (C : Fin (n - 1) → Fin (n - 1) → Fin (n - 1) → Fin (n - 1) → ℝ)
    (hC : ∀ l i j k, C l i j k = -C i l j k) :
    ∑ l, ∑ i, ∑ j, ∑ k, C l i j k * J.DB l i j k =
      ∑ l, ∑ i, ∑ j, ∑ k, C l i j k *
        ((if l = j then J.T i k else 0) + (if l = k then J.T i j else 0)) := by
  set S : Fin (n - 1) → Fin (n - 1) → Fin (n - 1) → Fin (n - 1) → ℝ := fun l i j k ↦
    iteratedFDeriv ℝ 4 u J.x₀ ![frameVec J.ι l, frameVec J.ι i, frameVec J.ι j,
      frameVec J.ι k] + (if l = i then J.T j k else 0) with hS
  have hSsymm : ∀ l i j k, S l i j k = S i l j k := by
    intro l i j k
    simp only [hS, h.facts.D4_comm₁₂ (frameVec J.ι l), eq_comm (a := l) (b := i)]
  have hsplit : ∀ l i j k, J.DB l i j k = S l i j k +
      ((if l = j then J.T i k else 0) + (if l = k then J.T i j else 0)) := by
    intro l i j k
    rw [h.DB_eq]
    ring
  have hzero : ∑ l, ∑ i, ∑ j, ∑ k, C l i j k * S l i j k = 0 :=
    sum_sum_eq_zero_of_antisymm (fun l i ↦ ∑ j, ∑ k, C l i j k * S l i j k) fun l i ↦ by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hC, hSsymm]
      ring
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib, hzero, zero_add]

/-! #### Squared norms of `D²u` and `D³u` at `x₀` -/

/-- `|D²u(x₀)|² = |T|²`, in any orthonormal basis. -/
theorem jetNormSq_two_eq {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n)) :
    jetNormSq e 2 u J.x₀ = ∑ i, ∑ j, J.T i j ^ 2 := by
  rw [jetNormSq_eq e h.basis, jetNormSq, multilinearNormSq_two]
  simp only [Fintype.sum_option, basis_none, basis_some, h.facts.D2_self_left,
    h.facts.D2_self_right, ← h.T_eq]
  simp

/-! #### Frame coordinates -/

theorem inner_frameMap_x₀ (a : Fin (n - 1) → ℝ) : ⟪frameMap J.ι a, J.x₀⟫ = 0 := by
  simp [frameMap, sum_inner, inner_smul_left, frameVec, h.inner_ι]

/-- `∇u(x₀) = g x₀ + ∑ pᵢ τᵢ`. -/
theorem gradient_eq : ∇ u J.x₀ = J.g • J.x₀ + frameMap J.ι J.p := by
  conv_lhs => rw [← h.basis.sum_repr' (∇ u J.x₀)]
  rw [Fintype.sum_option, basis_none]
  simp only [basis_some]
  congr 1
  · rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply, h.g_eq,
      ← h.facts.D1_self, iteratedFDeriv_one_apply]
    rfl
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply, h.p_eq]

/-- **`s² = g² + |p|²`**: `|∇u(x₀)|² = g² + ∑ pᵢ²`. -/
theorem normSq_gradient_eq : ‖∇ u J.x₀‖ ^ 2 = J.g ^ 2 + ∑ i, J.p i ^ 2 := by
  rw [← jetNormSq_one h.basis, jetNormSq, multilinearNormSq_one, Fintype.sum_option,
    basis_none, h.facts.D1_self, ← h.g_eq]
  simp only [basis_some, ← h.p_eq']

omit h in
theorem D2_frameMap_left (a : Fin (n - 1) → ℝ) (w : E n) :
    iteratedFDeriv ℝ 2 u J.x₀ ![frameMap J.ι a, w] =
      ∑ i, a i * iteratedFDeriv ℝ 2 u J.x₀ ![frameVec J.ι i, w] :=
  cons_sum_smul_apply _ _ _ _ _

theorem D2_frameMap (a c : Fin (n - 1) → ℝ) :
    iteratedFDeriv ℝ 2 u J.x₀ ![frameMap J.ι a, frameMap J.ι c] =
      ∑ i, ∑ j, a i * c j * J.T i j := by
  rw [D2_frameMap_left]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h.facts.D2_comm, D2_frameMap_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [h.facts.D2_comm, ← h.T_eq]
  ring

theorem D2_frameMap_frameVec (a : Fin (n - 1) → ℝ) (l : Fin (n - 1)) :
    iteratedFDeriv ℝ 2 u J.x₀ ![frameMap J.ι a, frameVec J.ι l] = ∑ i, a i * J.T i l := by
  rw [D2_frameMap_left]
  simp only [← h.T_eq]

theorem D2_frameVec_frameMap (l : Fin (n - 1)) (c : Fin (n - 1) → ℝ) :
    iteratedFDeriv ℝ 2 u J.x₀ ![frameVec J.ι l, frameMap J.ι c] = ∑ k, c k * J.T l k := by
  rw [h.facts.D2_comm, h.D2_frameMap_frameVec]
  simp only [h.T_symm _ l]

omit h in
theorem D3_frameMap_left (a : Fin (n - 1) → ℝ) (w₁ w₂ : E n) :
    iteratedFDeriv ℝ 3 u J.x₀ ![frameMap J.ι a, w₁, w₂] =
      ∑ i, a i * iteratedFDeriv ℝ 3 u J.x₀ ![frameVec J.ι i, w₁, w₂] :=
  cons_sum_smul_apply _ _ _ _ _

theorem D3_frameMap (a b c : Fin (n - 1) → ℝ) :
    iteratedFDeriv ℝ 3 u J.x₀ ![frameMap J.ι a, frameMap J.ι b, frameMap J.ι c] =
      ∑ i, ∑ j, ∑ k, a i * b j * c k * J.B i j k := by
  rw [D3_frameMap_left]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h.facts.D3_comm₁₂, D3_frameMap_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [h.facts.D3_comm₁₂, h.facts.D3_comm₂₃, h.facts.D3_comm₁₂, D3_frameMap_left,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [h.facts.D3_comm₁₂, h.facts.D3_comm₂₃, ← h.B_eq]
  ring

/-- **`|D³u(x₀)|² = |B|² + 3|T|²`**, in any orthonormal basis: the entries with no radial slot
give `|B|²`, those with one radial slot (three positions) give `T`, and those with two or three
radial slots vanish. -/
theorem jetNormSq_three_eq {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n)) :
    jetNormSq e 3 u J.x₀ = ∑ i, ∑ j, ∑ k, J.B i j k ^ 2 + 3 * ∑ i, ∑ j, J.T i j ^ 2 := by
  rw [jetNormSq_eq e h.basis, jetNormSq, multilinearNormSq_three]
  simp only [Fintype.sum_option, basis_none, basis_some, h.facts.D3_self₁, h.facts.D3_self₂,
    h.facts.D3_self₃, h.facts.D2_self_left, h.facts.D2_self_right, ← h.T_eq, ← h.B_eq, neg_sq,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add,
    Finset.sum_add_distrib]
  ring

end IsConeJet

end ConeJets

end OnePhaseDimension
