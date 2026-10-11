/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Flux.Bounds
public import OnePhaseDimension.Stability.ConeScaling
public import OnePhaseDimension.Cutoff.WeightedBochner

/-!
# Suspension data in the ambient encoding

Let `W = O × ℝ` be the suspension of a cone `O` in `ℝ⁵` with `O.Sing = {0}`, so that
`ũ = u_o ∘ π` with `π = dropLast : ℝ⁶ → ℝ⁵`. At a unit point `z` of the component of `W`, put
`ρ = |π z| ∈ (0, 1]` and `y = π z / ρ ∈ S⁴`. We prove:

* `iteratedFDeriv_suspension`: `Dᵏũ(z) = Dᵏu_o(π z) ∘ π` (in every slot), so the jets of `ũ`
  are those of `u_o` with zeros in the last direction;
* `jetNormSq_suspension`: `|Dᵏũ(z)| = |Dᵏu_o(π z)|` (Hilbert–Schmidt norms), and with the
  homogeneity scaling `|Dᵏu_o(ρ y)|² = ρ^{2 - 2k} |Dᵏu_o(y)|²` (`jetNormSq_smul`);
* `fluxW_suspension`: `w̃ = ρ⁻¹ w_o`;
* `fluxBNorm_sq_suspension_le`: `|B̃|² ≤ ρ⁻⁴ (|B_o|² + 3 w_o²)`;
* `normSq_gradient_suspension`: `s̃² = s_o²`;
* `fluxX_suspension_le`: `|X̃| = |B̃|/w̃ ≤ √3 ρ⁻¹ (1 + b_o)` with `b_o = |B_o|/w_o`;
* `suspension_K_bound`: `1 + w̃ + |X̃| ≤ K_s ρ⁻¹ (1 + b_o)` with `K_s = 1 + M_o + √3`;
* `hessian_gradient_suspension`: for a product chart `F̃ = F ∘ π`, `|∇F̃(z)| = |∇F(π z)|` and
  `D²F̃(z)[∇F̃, ∇F̃] = D²F(π z)[∇F, ∇F]`.

Here `w_o = sphHessNorm u_o` and `|B_o| = sphBNorm u_o` are the `0`-homogeneous spherical
quantities of a cone in any dimension, defined from the ambient Hilbert–Schmidt norms at `x̂`:
`w² = |D²u(x̂)|²` and `|B|² = |D³u(x̂)|² - 3 |D²u(x̂)|²`. At unit points they agree with the frame
quantities `|T|` and `|B|` (`sphHessNorm_eq`, `sphBNorm_eq`), and in `ℝ⁶` with `fluxW` and
`fluxBNorm`.

## Differences from the source

The 2026-09-24 version computes the suspended data in warped-product coordinates
`(t, y) ↦ (ρ y, cos t)` with the warped connection, component by component, and obtains
`|B̃|² = ρ⁻⁴(|B_o|² + 3 cos²t w_o²)` and `H̃ = ρ⁻¹ H_o`. We use the product structure
`ũ = u_o ∘ π` and Euclidean jets: `Dᵏũ(z) = Dᵏu_o(π z) ∘ π` and the one-homogeneity scaling of
`Dᵏu_o`. We prove only the inequality `|B̃|² ≤ ρ⁻⁴(|B_o|² + 3 w_o²)`, which is all the cutoff
argument uses. For the side boundary we prove the ambient chart identity
`D²F̃(z)[Ñ, Ñ] = D²F(π z)[N, N]`; the positivity `H̃ > 0` is proved directly on the suspension
elsewhere.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Metric EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

/-! ### The projection `π = dropLast` -/

@[simp] theorem dropLast_apply (x : E 6) (i : Fin 5) : dropLast x i = x (Fin.castSucc i) := rfl

theorem dropLast_single_castSucc (i : Fin 5) :
    dropLast (EuclideanSpace.single (Fin.castSucc i) (1 : ℝ)) = EuclideanSpace.single i 1 := by
  ext j
  simp [PiLp.single_apply]

theorem dropLast_single_last :
    dropLast (EuclideanSpace.single (Fin.last 5) (1 : ℝ)) = 0 := by
  ext j
  simp only [dropLast_apply, PiLp.single_apply, PiLp.zero_apply]
  exact ite_eq_right (Fin.castSucc_ne_last j)

/-- `π ∘ π† = id`: the adjoint of `dropLast` is the embedding `x ↦ (x, 0)`. -/
theorem dropLast_adjoint_apply (v : E 5) : dropLast (dropLast.adjoint v) = v := by
  ext i
  have h := dropLast.adjoint_inner_left (EuclideanSpace.single (Fin.castSucc i) (1 : ℝ)) v
  rw [dropLast_single_castSucc, EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_right] at h
  simpa using h

theorem norm_dropLast_adjoint (v : E 5) : ‖dropLast.adjoint v‖ = ‖v‖ := by
  have h : ‖dropLast.adjoint v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ContinuousLinearMap.adjoint_inner_left, dropLast_adjoint_apply]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `|z|² = |π z|² + z₆²`. -/
theorem norm_sq_eq_dropLast (z : E 6) : ‖z‖ ^ 2 = ‖dropLast z‖ ^ 2 + z (Fin.last 5) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp

/-! ### Hilbert–Schmidt norms under `π` -/

section HilbertSchmidt

variable {n : ℕ}

/-- Splitting the Hilbert–Schmidt norm along the first slot. -/
theorem multilinearNormSq_eq_sum_curryLeft {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ (E n)) {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E n) ℝ) :
    multilinearNormSq e M = ∑ a, multilinearNormSq e (M.curryLeft (e a)) := by
  rw [multilinearNormSq_succ]
  rfl

/-- `|M ∘ π|² = |M|²` for a multilinear form `M` on `ℝ⁵`. -/
theorem multilinearNormSq_compContinuousLinearMap_dropLast :
    ∀ {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E 5) ℝ),
      multilinearNormSq (EuclideanSpace.basisFun (Fin 6) ℝ)
          (M.compContinuousLinearMap fun _ ↦ dropLast) =
        multilinearNormSq (EuclideanSpace.basisFun (Fin 5) ℝ) M
  | 0, M => by
      simp only [multilinearNormSq, Fintype.sum_unique,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 2
      funext i
      exact i.elim0
  | k + 1, M => by
      rw [multilinearNormSq_eq_sum_curryLeft, multilinearNormSq_eq_sum_curryLeft,
        Fin.sum_univ_castSucc]
      have hc : ∀ x : E 6, (M.compContinuousLinearMap fun _ ↦ dropLast).curryLeft x =
          (M.curryLeft (dropLast x)).compContinuousLinearMap fun _ ↦ dropLast := by
        intro x
        ext v
        simp only [ContinuousMultilinearMap.curryLeft_apply,
          ContinuousMultilinearMap.compContinuousLinearMap_apply]
        congr 1
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      simp only [hc, multilinearNormSq_compContinuousLinearMap_dropLast,
        EuclideanSpace.basisFun_apply, dropLast_single_last, map_zero]
      simp only [dropLast_single_castSucc, multilinearNormSq]
      simp

end HilbertSchmidt

/-! ### Homogeneity scaling of Hilbert–Schmidt norms -/

section Scaling

variable {n : ℕ} {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (E n)) {u : E n → ℝ}

/-- `|x|^{2k} |Dᵏu(x)|² = |x|² |Dᵏu(x̂)|²` for a one-homogeneous `u`. -/
theorem jetNormSq_radialProj (hu : IsOneHomogeneous u) {k : ℕ} {x : E n} (hx : x ≠ 0)
    (hk : ContDiffAt ℝ k u (radialProj x)) :
    ‖x‖ ^ (2 * k) * jetNormSq e k u x = ‖x‖ ^ 2 * jetNormSq e k u (radialProj x) := by
  have h := hu.jetNormSq_smul e (norm_pos_iff.2 hx) hk
  rwa [norm_smul_radialProj hx] at h

end Scaling

/-! ### The spherical quantities `w` and `|B|` -/

section Spherical

variable {n : ℕ}

/-- The spherical Hessian norm `w(x) = |D²u(x̂)|` (the Hilbert–Schmidt norm, `0`-homogeneous;
`x̂ = 0` at the origin). At a unit point where `u` is one-homogeneous this is `|T|`. -/
def sphHessNorm (u : E n → ℝ) (x : E n) : ℝ :=
  √(jetNormSq (EuclideanSpace.basisFun (Fin n) ℝ) 2 u (radialProj x))

/-- The norm `|B|(x)` of the spherical third derivative, `|B|² = |D³u(x̂)|² - 3|D²u(x̂)|²`
(`0`-homogeneous). At a unit point where `u` is one-homogeneous, smooth and harmonic, this is the
norm of the frame tensor `B`. -/
def sphBNorm (u : E n → ℝ) (x : E n) : ℝ :=
  √(jetNormSq (EuclideanSpace.basisFun (Fin n) ℝ) 3 u (radialProj x) -
    3 * jetNormSq (EuclideanSpace.basisFun (Fin n) ℝ) 2 u (radialProj x))

theorem sphHessNorm_nonneg (u : E n → ℝ) (x : E n) : 0 ≤ sphHessNorm u x := Real.sqrt_nonneg _

theorem sphBNorm_nonneg (u : E n → ℝ) (x : E n) : 0 ≤ sphBNorm u x := Real.sqrt_nonneg _

theorem isZeroHomogeneous_sphHessNorm (u : E n → ℝ) : IsZeroHomogeneous (sphHessNorm u) :=
  fun _ hr x ↦ by simp only [sphHessNorm, radialProj_smul_of_pos hr]

theorem isZeroHomogeneous_sphBNorm (u : E n → ℝ) : IsZeroHomogeneous (sphBNorm u) :=
  fun _ hr x ↦ by simp only [sphBNorm, radialProj_smul_of_pos hr]

theorem sphHessNorm_radialProj (u : E n → ℝ) (x : E n) :
    sphHessNorm u (radialProj x) = sphHessNorm u x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialProj]
  · exact isZeroHomogeneous_sphHessNorm u _ (inv_pos.2 (norm_pos_iff.2 hx)) x

theorem sphBNorm_radialProj (u : E n → ℝ) (x : E n) :
    sphBNorm u (radialProj x) = sphBNorm u x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialProj]
  · exact isZeroHomogeneous_sphBNorm u _ (inv_pos.2 (norm_pos_iff.2 hx)) x

namespace ConeJets.IsConeJet

variable {u : E n → ℝ} {J : ConeJets n} (h : IsConeJet u J)
include h

/-- `w = |T|` at the base point. -/
theorem sphHessNorm_eq : sphHessNorm u J.x₀ = √(∑ i, ∑ j, J.T i j ^ 2) := by
  rw [sphHessNorm, radialProj_of_norm_eq_one h.norm_x₀, h.jetNormSq_two_eq]

theorem sphHessNorm_sq : sphHessNorm u J.x₀ ^ 2 = ∑ i, ∑ j, J.T i j ^ 2 := by
  rw [h.sphHessNorm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

/-- `|B|` is the norm of the frame tensor `B` at the base point. -/
theorem sphBNorm_eq : sphBNorm u J.x₀ = √(∑ i, ∑ j, ∑ k, J.B i j k ^ 2) := by
  rw [sphBNorm, radialProj_of_norm_eq_one h.norm_x₀, h.jetNormSq_two_eq, h.jetNormSq_three_eq]
  congr 1
  ring

theorem sphBNorm_sq : sphBNorm u J.x₀ ^ 2 = ∑ i, ∑ j, ∑ k, J.B i j k ^ 2 := by
  rw [h.sphBNorm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]

/-- `|D³u(x₀)|² = |B|² + 3w²`. -/
theorem jetNormSq_three_eq_sph :
    jetNormSq (EuclideanSpace.basisFun (Fin n) ℝ) 3 u J.x₀ =
      sphBNorm u J.x₀ ^ 2 + 3 * sphHessNorm u J.x₀ ^ 2 := by
  rw [h.sphBNorm_sq, h.sphHessNorm_sq, h.jetNormSq_three_eq]

theorem jetNormSq_two_eq_sph :
    jetNormSq (EuclideanSpace.basisFun (Fin n) ℝ) 2 u J.x₀ = sphHessNorm u J.x₀ ^ 2 := by
  rw [h.sphHessNorm_sq, h.jetNormSq_two_eq]

end ConeJets.IsConeJet

end Spherical

namespace ConeJets.IsConeJet

variable {u : E 6 → ℝ} {J : ConeJets 6} (h : IsConeJet u J)
include h

/-- In `ℝ⁶`, `fluxW = w`. -/
theorem fluxW_eq_sphHessNorm : fluxW u J.x₀ = sphHessNorm u J.x₀ := by
  rw [fluxW, h.fluxW_self, Gen.normW, Gen.sq2, h.sphHessNorm_eq]

/-- In `ℝ⁶`, `fluxBNorm = |B|`. -/
theorem fluxBNorm_eq_sphBNorm : fluxBNorm u J.x₀ = sphBNorm u J.x₀ := by
  have hx0 : J.x₀ ≠ 0 := by
    intro h0
    have := h.norm_x₀
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hr := radialProj_of_norm_eq_one h.norm_x₀
  rw [fluxBNorm_eq_of_frame hx0 (by rw [hr]; exact h.inner_ι), hr, h.sphBNorm_eq]
  congr 1
  simp only [sq3, frameB, Gen.frameB, h.B_eq]

end ConeJets.IsConeJet

/-! ### Cone jets on cones and suspensions -/

namespace ConeData

variable {n : ℕ} (C : ConeData n) (hS : C.Sing = {0})
include hS

/-- `|x|^{2k} |Dᵏu(x)|² = |x|² |Dᵏu(x̂)|²` on `D`. -/
theorem jetNormSq_radialProj {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (E n)) (k : ℕ)
    {x : E n} (hx : x ∈ C.D) :
    ‖x‖ ^ (2 * k) * jetNormSq e k C.u x = ‖x‖ ^ 2 * jetNormSq e k C.u (radialProj x) :=
  OnePhaseDimension.jetNormSq_radialProj e C.isOneHomogeneous_u (C.ne_zero_of_mem_D hx)
    ((C.contDiffAt_u hS (C.radialProj_mem_D hx)).of_le (natCast_le_infty k))

/-- `|D³u(x̂)|² = |B|² + 3 w²` on `D`. -/
theorem jetNormSq_three_radialProj {x : E n} (hx : x ∈ C.D) :
    jetNormSq (EuclideanSpace.basisFun (Fin n) ℝ) 3 C.u (radialProj x) =
      sphBNorm C.u x ^ 2 + 3 * sphHessNorm C.u x ^ 2 := by
  have hx0 := C.ne_zero_of_mem_D hx
  have h := C.isConeJet_of_mem_D hS (C.radialProj_mem_D hx) (norm_radialProj hx0)
  rw [← sphBNorm_radialProj, ← sphHessNorm_radialProj]
  exact h.jetNormSq_three_eq_sph

omit hS in
/-- `w = √(w²)` in the notation of the weighted Bochner estimate. -/
theorem sphHessNorm_eq_sqrt_wSq (x : E n) : sphHessNorm C.u x = √(C.wSq x) := by
  rw [sphHessNorm, wSq, jetNormSq_eq _ (stdOrthonormalBasis ℝ (E n))]

omit hS in
/-- `|B| = √(|B|²)` in the notation of the weighted Bochner estimate. -/
theorem sphBNorm_eq_sqrt_bSq (x : E n) : sphBNorm C.u x = √(C.bSq x) := by
  rw [sphBNorm, bSq, jetNormSq_eq _ (stdOrthonormalBasis ℝ (E n)),
    jetNormSq_eq (EuclideanSpace.basisFun (Fin n) ℝ) (stdOrthonormalBasis ℝ (E n))]

omit hS in
/-- The dominator `D_o = w^{2a}(1 + |B|/w)²` of the weighted Bochner estimate, in terms of
`w = sphHessNorm` and `|B| = sphBNorm`, where `w > 0`. -/
theorem dominatorO_eq {x : E n} (hw : 0 < sphHessNorm C.u x) :
    C.dominatorO aExp x =
      sphHessNorm C.u x ^ (2 * aExp) * (1 + sphBNorm C.u x / sphHessNorm C.u x) ^ 2 := by
  have hw' : 0 < C.wSq x := by
    rw [sphHessNorm_eq_sqrt_wSq] at hw
    exact Real.sqrt_pos.1 hw
  rw [dominatorO, ite_eq_left hw', sphHessNorm_eq_sqrt_wSq, sphBNorm_eq_sqrt_bSq,
    Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (C.wSq_nonneg x)]

end ConeData

namespace IsSuspension

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
include hW hO

omit hO in
theorem notMem_sing {z : E 6} (hz : z ∈ W.D) : z ∉ W.Sing := by
  rw [hW.sing_eq]
  exact O.ne_zero_of_mem_D (hW.mem_D_iff.1 hz)

omit hO in
theorem u_eq_comp : W.u = O.u ∘ dropLast := funext hW.u_eq

/-- **Ambient jets of the suspension**: `Dᵏũ(z) = Dᵏu_o(π z) ∘ π`. -/
theorem iteratedFDeriv_suspension {z : E 6} (hz : z ∈ W.D) (k : ℕ) :
    iteratedFDeriv ℝ k W.u z =
      (iteratedFDeriv ℝ k O.u (dropLast z)).compContinuousLinearMap fun _ ↦ dropLast := by
  have hs : IsOpen O.D := O.isOpen_D
  have hs' : IsOpen (dropLast ⁻¹' O.D) := hs.preimage dropLast.continuous
  have hf : ContDiffOn ℝ ∞ O.u O.D := fun x hx ↦ (O.contDiffAt_u hO hx).contDiffWithinAt
  have hpz : dropLast z ∈ O.D := hW.mem_D_iff.1 hz
  have h := dropLast.iteratedFDerivWithin_comp_right hf hs.uniqueDiffOn hs'.uniqueDiffOn hpz
    (natCast_le_infty k)
  rw [iteratedFDerivWithin_of_isOpen k hs' (show z ∈ dropLast ⁻¹' O.D from hpz),
    iteratedFDerivWithin_of_isOpen k hs hpz] at h
  rw [hW.u_eq_comp]
  exact h

/-- `|Dᵏũ(z)| = |Dᵏu_o(π z)|`. -/
theorem jetNormSq_suspension {z : E 6} (hz : z ∈ W.D) (k : ℕ) :
    jetNormSq (EuclideanSpace.basisFun (Fin 6) ℝ) k W.u z =
      jetNormSq (EuclideanSpace.basisFun (Fin 5) ℝ) k O.u (dropLast z) := by
  rw [jetNormSq, jetNormSq, hW.iteratedFDeriv_suspension hO hz,
    multilinearNormSq_compContinuousLinearMap_dropLast]

omit hO in
/-- The jet record of the suspension at a unit point of its component. -/
theorem isConeJet {z : E 6} (hz : z ∈ W.D) (hz1 : ‖z‖ = 1) :
    ConeJets.IsConeJet W.u (ConeJets.ofHarmonicHomogeneous W.u z hz1) := by
  refine ConeJets.isConeJet_ofHarmonicHomogeneous hz1 W.isOneHomogeneous_u ?_
    (ConeData.contDiffAt_u_and_eventually_laplacian hz (hW.notMem_sing hz)).2
  filter_upwards [W.isOpen_D.mem_nhds hz] with y hy
  exact (ConeData.contDiffAt_u_and_eventually_laplacian hy (hW.notMem_sing hy)).1.of_le
    (natCast_le_infty 4)

omit hO in
theorem dropLast_ne_zero {z : E 6} (hz : z ∈ W.D) : dropLast z ≠ 0 :=
  O.ne_zero_of_mem_D (hW.mem_D_iff.1 hz)

omit hO in
theorem norm_dropLast_pos {z : E 6} (hz : z ∈ W.D) : 0 < ‖dropLast z‖ :=
  norm_pos_iff.2 (hW.dropLast_ne_zero hz)

/-- **`w̃ = ρ⁻¹ w_o`**, with `ρ = |π z|`. -/
theorem fluxW_suspension {z : E 6} (hz : z ∈ W.D) (hz1 : ‖z‖ = 1) :
    fluxW W.u z = ‖dropLast z‖⁻¹ * sphHessNorm O.u (dropLast z) := by
  have hJ := hW.isConeJet hz hz1
  have hpz : dropLast z ∈ O.D := hW.mem_D_iff.1 hz
  have hρ := hW.norm_dropLast_pos hz
  have hsc := O.jetNormSq_radialProj hO (EuclideanSpace.basisFun (Fin 5) ℝ) 2 hpz
  have e1 : fluxW W.u z = sphHessNorm W.u z := hJ.fluxW_eq_sphHessNorm
  rw [e1, sphHessNorm, radialProj_of_norm_eq_one hz1, hW.jetNormSq_suspension hO hz, sphHessNorm]
  set a := jetNormSq (EuclideanSpace.basisFun (Fin 5) ℝ) 2 O.u (dropLast z)
  set b := jetNormSq (EuclideanSpace.basisFun (Fin 5) ℝ) 2 O.u (radialProj (dropLast z))
  set ρ := ‖dropLast z‖
  have ha : a = (ρ⁻¹) ^ 2 * b := by
    have hρ2 : ρ ^ 2 ≠ 0 := by positivity
    have h' : ρ ^ 2 * (ρ ^ 2 * a) = ρ ^ 2 * b := by rw [← hsc]; ring
    rw [← mul_left_cancel₀ hρ2 h']
    field_simp
  rw [ha, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- **`|B̃|² ≤ ρ⁻⁴ (|B_o|² + 3 w_o²)`**, with `ρ = |π z|`. -/
theorem fluxBNorm_sq_suspension_le {z : E 6} (hz : z ∈ W.D) (hz1 : ‖z‖ = 1) :
    fluxBNorm W.u z ^ 2 ≤
      (‖dropLast z‖⁻¹) ^ 4 * (sphBNorm O.u (dropLast z) ^ 2 +
        3 * sphHessNorm O.u (dropLast z) ^ 2) := by
  have hJ := hW.isConeJet hz hz1
  have hpz : dropLast z ∈ O.D := hW.mem_D_iff.1 hz
  have hρ := hW.norm_dropLast_pos hz
  have hsc := O.jetNormSq_radialProj hO (EuclideanSpace.basisFun (Fin 5) ℝ) 3 hpz
  have h3 : jetNormSq (EuclideanSpace.basisFun (Fin 6) ℝ) 3 W.u z =
      sphBNorm W.u z ^ 2 + 3 * sphHessNorm W.u z ^ 2 := hJ.jetNormSq_three_eq_sph
  have hB : fluxBNorm W.u z ^ 2 ≤
      jetNormSq (EuclideanSpace.basisFun (Fin 6) ℝ) 3 W.u z := by
    have e1 : fluxBNorm W.u z = sphBNorm W.u z := hJ.fluxBNorm_eq_sphBNorm
    rw [e1]
    rw [h3]
    nlinarith [sq_nonneg (sphHessNorm W.u z)]
  rw [hW.jetNormSq_suspension hO hz] at hB
  rw [← O.jetNormSq_three_radialProj hO hpz]
  set ρ := ‖dropLast z‖
  set a := jetNormSq (EuclideanSpace.basisFun (Fin 5) ℝ) 3 O.u (dropLast z)
  set b := jetNormSq (EuclideanSpace.basisFun (Fin 5) ℝ) 3 O.u (radialProj (dropLast z))
  have ha : a = (ρ⁻¹) ^ 4 * b := by
    have hρ2 : ρ ^ 2 ≠ 0 := by positivity
    have h' : ρ ^ 2 * (ρ ^ 4 * a) = ρ ^ 2 * b := by rw [← hsc]; ring
    rw [← mul_left_cancel₀ hρ2 h']
    field_simp
  rw [← ha]
  exact hB

/-- **`s̃² = s_o²`**: `|∇ũ(z)|² = |∇u_o(π z / |π z|)|²`. -/
theorem normSq_gradient_suspension {z : E 6} (hz : z ∈ W.D) :
    ‖∇ W.u z‖ ^ 2 = ‖∇ O.u (radialProj (dropLast z))‖ ^ 2 := by
  have hpz : dropLast z ∈ O.D := hW.mem_D_iff.1 hz
  have hρ := hW.norm_dropLast_pos hz
  have hsc := O.jetNormSq_radialProj hO (EuclideanSpace.basisFun (Fin 5) ℝ) 1 hpz
  rw [← jetNormSq_one (EuclideanSpace.basisFun (Fin 6) ℝ), hW.jetNormSq_suspension hO hz,
    ← jetNormSq_one (EuclideanSpace.basisFun (Fin 5) ℝ)]
  have hρ2 : ‖dropLast z‖ ^ 2 ≠ 0 := by positivity
  simp only [mul_one] at hsc
  exact mul_left_cancel₀ hρ2 hsc

/-- **`|X̃| = |B̃|/w̃ ≤ √3 ρ⁻¹ (1 + b_o)`**, with `b_o = |B_o|/w_o`, where `w_o > 0`. -/
theorem fluxX_suspension_le {z : E 6} (hz : z ∈ W.D) (hz1 : ‖z‖ = 1)
    (hw : 0 < sphHessNorm O.u (dropLast z)) :
    fluxBNorm W.u z / fluxW W.u z ≤
      √3 * ‖dropLast z‖⁻¹ *
        (1 + sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z)) := by
  have hρ := hW.norm_dropLast_pos hz
  have hB := hW.fluxBNorm_sq_suspension_le hO hz hz1
  rw [hW.fluxW_suspension hO hz hz1]
  set ρ := ‖dropLast z‖
  set w := sphHessNorm O.u (dropLast z)
  set b := sphBNorm O.u (dropLast z)
  set B := fluxBNorm W.u z
  have hb0 : 0 ≤ b := sphBNorm_nonneg _ _
  have hB0 : 0 ≤ B := fluxBNorm_nonneg _ _
  have h3 : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hle : B ≤ √3 * (ρ⁻¹) ^ 2 * (w + b) := by
    have hsq : B ^ 2 ≤ (√3 * (ρ⁻¹) ^ 2 * (w + b)) ^ 2 := by
      refine hB.trans ?_
      rw [mul_pow, mul_pow, h33, ← pow_mul]
      have hρ4 : 0 ≤ (ρ⁻¹) ^ (2 * 2) := by positivity
      nlinarith [mul_nonneg hρ4 (mul_nonneg hw.le hb0), mul_nonneg hρ4 (sq_nonneg b)]
    exact (pow_le_pow_iff_left₀ hB0 (by positivity) two_ne_zero).1 hsq
  rw [div_le_iff₀ (by positivity)]
  calc B ≤ √3 * (ρ⁻¹) ^ 2 * (w + b) := hle
    _ = √3 * ρ⁻¹ * (1 + b / w) * (ρ⁻¹ * w) := by field_simp

/-- **`1 + w̃ + |X̃| ≤ K_s ρ⁻¹ (1 + b_o)`** with `K_s = 1 + M_o + √3`, where `w_o ≤ M_o` and
`w_o > 0`. -/
theorem suspension_K_bound {z : E 6} (hz : z ∈ W.D) (hz1 : ‖z‖ = 1)
    (hw : 0 < sphHessNorm O.u (dropLast z)) {M : ℝ} (hM : sphHessNorm O.u (dropLast z) ≤ M) :
    1 + fluxW W.u z + fluxBNorm W.u z / fluxW W.u z ≤
      (1 + M + √3) * ‖dropLast z‖⁻¹ *
        (1 + sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z)) := by
  have hρ := hW.norm_dropLast_pos hz
  have hρ1 : ‖dropLast z‖ ≤ 1 := hz1 ▸ norm_dropLast_le z
  have hX := hW.fluxX_suspension_le hO hz hz1 hw
  rw [hW.fluxW_suspension hO hz hz1] at hX ⊢
  set ρ := ‖dropLast z‖
  set w := sphHessNorm O.u (dropLast z)
  set q := 1 + sphBNorm O.u (dropLast z) / w
  have hq : 1 ≤ q := by
    have : 0 ≤ sphBNorm O.u (dropLast z) / w := div_nonneg (sphBNorm_nonneg _ _) hw.le
    linarith
  have hρi : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ |>.2 hρ1
  have hM0 : 0 ≤ M := hw.le.trans hM
  have h1 : 1 ≤ ρ⁻¹ * q := by nlinarith
  have hwq : w ≤ M * q := by nlinarith
  have h2 : ρ⁻¹ * w ≤ M * (ρ⁻¹ * q) := by
    have := mul_le_mul_of_nonneg_left hwq (inv_pos.2 hρ).le
    linarith [show ρ⁻¹ * (M * q) = M * (ρ⁻¹ * q) by ring]
  nlinarith

end IsSuspension

/-! ### Product charts on the side boundary -/

section ProductChart

variable {F : E 5 → ℝ} {z : E 6}

/-- `∇(F ∘ π)(z) = π†∇F(π z) = (∇F(π z), 0)`. -/
theorem gradient_comp_dropLast (hF : DifferentiableAt ℝ F (dropLast z)) :
    ∇ (F ∘ dropLast) z = dropLast.adjoint (∇ F (dropLast z)) := by
  refine ext_inner_right ℝ fun v ↦ ?_
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left,
    fderiv_comp z hF dropLast.differentiableAt, dropLast.fderiv]
  rfl

/-- `D²(F ∘ π)(z)[a, b] = D²F(π z)[π a, π b]`. -/
theorem iteratedFDeriv_two_comp_dropLast {U : Set (E 5)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) (hz : dropLast z ∈ U) (a b : E 6) :
    iteratedFDeriv ℝ 2 (F ∘ dropLast) z ![a, b] =
      iteratedFDeriv ℝ 2 F (dropLast z) ![dropLast a, dropLast b] := by
  have hU' : IsOpen (dropLast ⁻¹' U) := hU.preimage dropLast.continuous
  have h := dropLast.iteratedFDerivWithin_comp_right hF hU.uniqueDiffOn hU'.uniqueDiffOn hz
    (i := 2) le_rfl
  rw [iteratedFDerivWithin_of_isOpen 2 hU' (show z ∈ dropLast ⁻¹' U from hz),
    iteratedFDerivWithin_of_isOpen 2 hU hz] at h
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **The side boundary of a product chart.** For `F̃ = F ∘ π`: `|∇F̃(z)| = |∇F(π z)|` and
`D²F̃(z)[∇F̃, ∇F̃] = D²F(π z)[∇F, ∇F]`, so `H̃(z) = H(π z)` for the ambient
`H = -D²F[∇F, ∇F]`. -/
theorem hessian_gradient_comp_dropLast {U : Set (E 5)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) (hz : dropLast z ∈ U) :
    ‖∇ (F ∘ dropLast) z‖ = ‖∇ F (dropLast z)‖ ∧
      iteratedFDeriv ℝ 2 (F ∘ dropLast) z ![∇ (F ∘ dropLast) z, ∇ (F ∘ dropLast) z] =
        iteratedFDeriv ℝ 2 F (dropLast z) ![∇ F (dropLast z), ∇ F (dropLast z)] := by
  have hd : DifferentiableAt ℝ F (dropLast z) :=
    ((hF.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  rw [gradient_comp_dropLast hd, norm_dropLast_adjoint,
    iteratedFDeriv_two_comp_dropLast hU hF hz, dropLast_adjoint_apply]
  exact ⟨rfl, rfl⟩

end ProductChart

end OnePhaseDimension
