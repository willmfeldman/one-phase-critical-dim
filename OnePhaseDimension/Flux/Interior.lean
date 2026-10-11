/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Flux.Generator

/-!
# The divergence identity and the interior comparison

Let `u` be one-homogeneous, smooth and harmonic near a unit vector `x₀ ∈ ℝⁿ` with `w(x₀) > 0`,
let `m = n - 1`, and let `c` satisfy the certificate in `ℝ^m` with constants `ε > 0`, `δ`. With
`A = T/w`, `X = B/w`, `q_l = X_{lij}A_{ij}` and every `D_l` evaluated at `z = 1`:

* **Fourth elimination** (`fourth_elimination`): with `C_{lijk} = K_{lijk} - K_{iljk}`,
  `(δ_{li}U_{jk} + C_{lijk})(∇B)_{lijk} = m U_{jk}T_{jk} + C_{lijk}(δ_{lj}T_{ik} + δ_{lk}T_{ij})`.
* **Divergence identity** (`divergence_fluxZ_eq`):
  `w^{-2a} div Z = mU:A + C(δA + δA) + [D_lG + (2a-1)q_lG]X + w[D_lM + (2a+1)q_lM]
    + D_lP + 2a q_lP`.
* **Derivative of `h`** (`fderiv_fluxH_frame`, `normSq_gradient_fluxH`):
  `∇_l h = w^a 𝓕_l / (2√f)` with `𝓕_l = D_lf + 2a q_l f`, and `|∇h|² = w^{2a}|𝓕|²/(4f)`.
* **Square completion** (`interior_square_completion`) and the **interior comparison**
  (`Gen.div_fluxZ_ge`): `div Z ≥ β²h² + |∇h|² + ε w^{2a}` with the Hardy constant
  `β² = ((m - 1)/2)²` of `S^m`.

The five-dimensional statement `div_fluxZ_ge` (`n = 6`, `β² = 4`, `ε = ε*`) is the case `m = 5`.

## Differences from the source

The 2026-09-24 version eliminates the fourth derivatives with the curvature commutator of the
sphere and a factor `1/2`. We use the ambient formula
`(∇B)_{lijk} = D⁴u_{lijk} + δ_{li}T_{jk} + δ_{lj}T_{ik} + δ_{lk}T_{ij}`: the `D⁴u` and
`δ_{li}T_{jk}` terms are symmetric in `(l, i)` and so vanish against the antisymmetric `C`.
The admissibility `g² + |p|² ≤ 1` is taken as the hypothesis `|∇u(x₀)|² ≤ 1`.
The 2026-09-24 version works on `S⁵`, where `ΔT = 5T` and the Hardy constant is `4`; on `S^m` the
same computation gives `ΔT = mT` and `β² = ((m - 1)/2)²`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set
open scoped RealInnerProductSpace ContDiff Gradient Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

namespace ConeJets.IsConeJet

variable {n : ℕ} {u : E n → ℝ} {J : ConeJets n} (h : IsConeJet u J)
include h

/-- **Fourth elimination.** For any `U` and `K`, with `C_{lijk} = K_{lijk} - K_{iljk}`,
`(δ_{li}U_{jk} + C_{lijk})(∇B)_{lijk} = 5 U_{jk}T_{jk} + C_{lijk}(δ_{lj}T_{ik} + δ_{lk}T_{ij})`.
The trace part uses `ΔT = 5T`; the skew part uses only the symmetry of `D⁴u`. -/
theorem fourth_elimination (U : Gen.Ten2 (n - 1)) (K : Gen.Ten4 (n - 1)) :
    ∑ l, ∑ i, ∑ j, ∑ k, (Gen.kron l i * U j k + (K l i j k - K i l j k)) * J.DB l i j k =
      ((n - 1 : ℕ) : ℝ) * ∑ j, ∑ k, U j k * J.T j k +
        ∑ l, ∑ i, ∑ j, ∑ k, (K l i j k - K i l j k) *
          (Gen.kron l j * J.T i k + Gen.kron l k * J.T i j) := by
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · have h1 : ∀ l : Fin (n - 1), ∑ i, ∑ j, ∑ k, Gen.kron l i * U j k * J.DB l i j k =
        ∑ j, ∑ k, U j k * J.DB l l j k := fun l ↦ by
      rw [Finset.sum_eq_single l (fun i _ hi ↦ by simp [Gen.kron, Ne.symm hi]) (by simp)]
      simp [Gen.kron]
    simp only [h1]
    rw [← Gen.sum3_comm (fun j k l ↦ U j k * J.DB l l j k)]
    simp only [← Finset.mul_sum]
    simp only [h.DB_trace_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  · have h3 := h.contract_antisymm_DB (fun l i j k ↦ K l i j k - K i l j k)
      (fun l i j k ↦ by ring)
    rw [h3]
    simp only [Gen.kron, ite_mul, one_mul, zero_mul]

end ConeJets.IsConeJet

/-! ### Smoothness of the coefficient entries -/

namespace Gen.CertificateHolds

variable {m : ℕ} {c : Gen.Coeffs m} {ε δ : ℝ} (hc : Gen.CertificateHolds m ε δ c)
include hc

theorem contDiff_G_apply (l i j k : Fin m) : ContDiff ℝ ∞ (fun y ↦ c.G y l i j k) := by
  have hU := hc.smooth_U
  have hK := hc.smooth_K
  have hU' : ContDiff ℝ ∞ (fun y ↦ c.U y j k) := contDiff_pi.1 (contDiff_pi.1 hU j) k
  have hK1 : ContDiff ℝ ∞ (fun y ↦ c.K y l i j k) :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hK l) i) j) k
  have hK2 : ContDiff ℝ ∞ (fun y ↦ c.K y i l j k) :=
    contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hK i) l) j) k
  unfold Gen.Coeffs.G Gen.Coeffs.C
  fun_prop

theorem contDiff_M_apply (l : Fin m) : ContDiff ℝ ∞ (fun y ↦ c.M y l) :=
  contDiff_pi.1 hc.smooth_M l

theorem contDiff_P_apply (l : Fin m) : ContDiff ℝ ∞ (fun y ↦ c.P y l) :=
  contDiff_pi.1 hc.smooth_P l

end Gen.CertificateHolds

/-! ### The divergence identity -/

namespace ConeJets.IsConeJet

variable {n : ℕ} {u : E n → ℝ} {J : ConeJets n} {c : Gen.Coeffs (n - 1)} {ε δ : ℝ}
  (hc : Gen.CertificateHolds (n - 1) ε δ c)
  (h : IsConeJet u J) (hu : ContDiffAt ℝ ∞ u J.x₀) (hw : Gen.sq2 J.T ≠ 0)
include hc h hu hw

/-- The derivative of the frame component `Z_l` along `τ_l` at `x₀`. -/
theorem fderiv_fluxZComp (l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ c.fluxZComp (Gen.transTData u J.x₀ J.ι x) (Gen.transBData u J.x₀ J.ι x)
        (Gen.transPData u J.x₀ J.ι x) (transG u x) l) J.x₀ (frameVec J.ι l) =
      Gen.normW J.T ^ (2 * aExp) *
        (∑ i, ∑ j, ∑ k, c.G (Gen.normalizedA J.T, J.p, J.g) l i j k * (J.DB l i j k / Gen.normW
            J.T) +
          ∑ i, ∑ j, ∑ k, (Gen.Dl (fun y ↦ c.G y l i j k) (Gen.normalizedA J.T) (Gen.normalizedX J.T
              J.B) J.p
              J.g (Gen.normW J.T) 1 l +
              (2 * aExp - 1) * Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l *
              c.G (Gen.normalizedA J.T, J.p, J.g) l i j k) * Gen.normalizedX J.T J.B i j k +
          Gen.normW J.T * (Gen.Dl (fun y ↦ c.M y l) (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B)
              J.p J.g
              (Gen.normW J.T) 1 l + (2 * aExp + 1) * Gen.qVec (Gen.normalizedX J.T J.B)
                  (Gen.normalizedA J.T) l *
              c.M (Gen.normalizedA J.T, J.p, J.g) l) +
          (Gen.Dl (fun y ↦ c.P y l) (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g
              (Gen.normW J.T) 1 l +
            2 * aExp * Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l *
              c.P (Gen.normalizedA J.T, J.p, J.g) l)) := by
  -- abbreviations for the transported data
  set nd : E n → Gen.Ten2 (n - 1) × Gen.Ten1 (n - 1) × ℝ := fun x ↦
    (Gen.normalizedA (Gen.transTData u J.x₀ J.ι x), Gen.transPData u J.x₀ J.ι x, transG u x) with
        hnd
  set W : E n → ℝ := fun x ↦ Gen.normW (Gen.transTData u J.x₀ J.ι x) with hW
  set tX : E n → Gen.Ten3 (n - 1) := fun x ↦ Gen.normalizedX (Gen.transTData u J.x₀ J.ι x)
      (Gen.transBData u J.x₀ J.ι x)
    with htX
  have hnd0 : nd J.x₀ = (Gen.normalizedA J.T, J.p, J.g) := h.normalizedData_self
  have hW0 : W J.x₀ = Gen.normW J.T := h.transW_self
  have hX0 : tX J.x₀ = Gen.normalizedX J.T J.B := by
    simp only [htX, h.transTData_self, h.transBData_self]
  have hw0 : Gen.normW J.T ≠ 0 := normW_ne_zero hw
  have hdnd : DifferentiableAt ℝ nd J.x₀ := h.differentiableAt_normalizedData hu hw
  have hdW : DifferentiableAt ℝ W J.x₀ := h.differentiableAt_transW hu hw
  have hdX : ∀ i j k, DifferentiableAt ℝ (fun x ↦ tX x i j k) J.x₀ :=
    h.differentiableAt_transX hu hw
  have hdG : ∀ i j k, DifferentiableAt ℝ (fun x ↦ c.G (nd x) l i j k) J.x₀ := fun i j k ↦
    ((hc.contDiff_G_apply l i j k).differentiable (by simp) _).comp J.x₀ hdnd
  have hdM : DifferentiableAt ℝ (fun x ↦ c.M (nd x) l) J.x₀ :=
    ((hc.contDiff_M_apply l).differentiable (by simp) _).comp J.x₀ hdnd
  have hdP : DifferentiableAt ℝ (fun x ↦ c.P (nd x) l) J.x₀ :=
    ((hc.contDiff_P_apply l).differentiable (by simp) _).comp J.x₀ hdnd
  have hDG : ∀ i j k, fderiv ℝ (fun x ↦ c.G (nd x) l i j k) J.x₀ (frameVec J.ι l) =
      Gen.Dl (fun y ↦ c.G y l i j k) (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g
          (Gen.normW J.T) 1 l :=
    fun i j k ↦ h.fderiv_certPoly_eq_Dl hu hw _
      (((hc.contDiff_G_apply l i j k).differentiable (by simp)) _) l
  have hDM : fderiv ℝ (fun x ↦ c.M (nd x) l) J.x₀ (frameVec J.ι l) =
      Gen.Dl (fun y ↦ c.M y l) (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW
          J.T) 1 l :=
    h.fderiv_certPoly_eq_Dl hu hw _ (((hc.contDiff_M_apply l).differentiable (by simp)) _) l
  have hDP : fderiv ℝ (fun x ↦ c.P (nd x) l) J.x₀ (frameVec J.ι l) =
      Gen.Dl (fun y ↦ c.P y l) (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW
          J.T) 1 l :=
    h.fderiv_certPoly_eq_Dl hu hw _ (((hc.contDiff_P_apply l).differentiable (by simp)) _) l
  have hDW := h.fderiv_transW hu hw l
  have hDX : ∀ i j k, fderiv ℝ (fun x ↦ tX x i j k) J.x₀ (frameVec J.ι l) =
      J.DB l i j k / Gen.normW J.T -
        Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l * Gen.normalizedX J.T J.B i j
            k :=
    fun i j k ↦ h.fderiv_transX hu hw i j k l
  -- the component as a product
  have hdC : DifferentiableAt ℝ
      (fun x ↦ ∑ i, ∑ j, ∑ k, c.G (nd x) l i j k * tX x i j k) J.x₀ :=
    DifferentiableAt.fun_sum fun i _ ↦ DifferentiableAt.fun_sum fun j _ ↦
      DifferentiableAt.fun_sum fun k _ ↦ (hdG i j k).mul (hdX i j k)
  have hdWM : DifferentiableAt ℝ (fun x ↦ W x * c.M (nd x) l) J.x₀ := hdW.mul hdM
  change fderiv ℝ (fun x ↦ W x ^ (2 * aExp) *
    (∑ i, ∑ j, ∑ k, c.G (nd x) l i j k * tX x i j k + W x * c.M (nd x) l + c.P (nd x) l))
      J.x₀ (frameVec J.ι l) = _
  rw [fderiv_mul_apply' (hdW.rpow_const (Or.inl (by rw [hW0]; exact hw0)))
      ((hdC.fun_add hdWM).fun_add hdP),
    fderiv_rpow_apply' hdW (by rw [hW0]; exact hw0), hDW,
    fderiv_add_apply' (hdC.fun_add hdWM) hdP, fderiv_add_apply' hdC hdWM,
    fderiv_mul_apply' hdW hdM, hDM, hDP, hDW]
  rw [fderiv_sum_apply' (φ := fun i x ↦ ∑ j, ∑ k, c.G (nd x) l i j k * tX x i j k)
      fun i ↦ DifferentiableAt.fun_sum fun j _ ↦
      DifferentiableAt.fun_sum fun k _ ↦ (hdG i j k).fun_mul (hdX i j k)]
  simp only [fun i ↦ fderiv_sum_apply' (x := J.x₀) (v := frameVec J.ι l)
      (φ := fun j x ↦ ∑ k, c.G (nd x) l i j k * tX x i j k)
      fun j ↦ DifferentiableAt.fun_sum fun k _ ↦ (hdG i j k).fun_mul (hdX i j k)]
  simp only [fun i j ↦ fderiv_sum_apply' (x := J.x₀) (v := frameVec J.ι l)
      (φ := fun k x ↦ c.G (nd x) l i j k * tX x i j k) fun k ↦ (hdG i j k).fun_mul (hdX i j k)]
  simp only [fun i j k ↦ fderiv_mul_apply' (v := frameVec J.ι l) (hdG i j k) (hdX i j k), hDG,
    hDX, hnd0, hW0, hX0]
  -- algebra
  set w := Gen.normW J.T
  set q := Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l
  set X := Gen.normalizedX J.T J.B
  have hpow : w ^ (2 * aExp - 1) * w = w ^ (2 * aExp) := by
    rw [Real.rpow_sub_one hw0, div_mul_cancel₀ _ hw0]
  have hsum : ∑ i, ∑ j, ∑ k, (c.G (Gen.normalizedA J.T, J.p, J.g) l i j k *
        (J.DB l i j k / w - q * X i j k) +
      X i j k * Gen.Dl (fun y ↦ c.G y l i j k) (Gen.normalizedA J.T) X J.p J.g w 1 l) =
      ∑ i, ∑ j, ∑ k, c.G (Gen.normalizedA J.T, J.p, J.g) l i j k * (J.DB l i j k / w) +
        ∑ i, ∑ j, ∑ k, (Gen.Dl (fun y ↦ c.G y l i j k) (Gen.normalizedA J.T) X J.p J.g w 1 l +
          (2 * aExp - 1) * q * c.G (Gen.normalizedA J.T, J.p, J.g) l i j k) * X i j k -
        2 * aExp * q * ∑ i, ∑ j, ∑ k, c.G (Gen.normalizedA J.T, J.p, J.g) l i j k * X i j k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  linear_combination w ^ (2 * aExp) * hsum + 2 * aExp * q *
    (∑ i, ∑ j, ∑ k, c.G (Gen.normalizedA J.T, J.p, J.g) l i j k * X i j k +
      w * c.M (Gen.normalizedA J.T, J.p, J.g) l + c.P (Gen.normalizedA J.T, J.p, J.g) l) * hpow

omit hc hu hw in
/-- The contraction `G_{lijk}(∇B)_{lijk}/w` of the fourth-derivative tensor:
`5 U:A + C_{lijk}(δ_{lj}A_{ik} + δ_{lk}A_{ij})`. -/
theorem sum_G_mul_DB_div :
    ∑ l, ∑ i, ∑ j, ∑ k, c.G (Gen.normalizedA J.T, J.p, J.g) l i j k * (J.DB l i j k / Gen.normW
        J.T) =
      ((n - 1 : ℕ) : ℝ) * ∑ j, ∑ k, c.U (Gen.normalizedA J.T, J.p, J.g) j k *
        Gen.normalizedA J.T j k +
        ∑ l, ∑ i, ∑ j, ∑ k, c.C (Gen.normalizedA J.T, J.p, J.g) l i j k *
          (Gen.kron l j * Gen.normalizedA J.T i k + Gen.kron l k * Gen.normalizedA J.T i j) := by
  set x := (Gen.normalizedA J.T, J.p, J.g)
  have h4 := h.fourth_elimination (c.U x) (c.K x)
  calc ∑ l, ∑ i, ∑ j, ∑ k, c.G x l i j k * (J.DB l i j k / Gen.normW J.T)
      = (∑ l, ∑ i, ∑ j, ∑ k, (Gen.kron l i * c.U x j k + (c.K x l i j k - c.K x i l j k)) *
          J.DB l i j k) / Gen.normW J.T := by
        simp only [Finset.sum_div, Gen.Coeffs.G, Gen.Coeffs.C, mul_div_assoc]
    _ = _ := by
        rw [h4, add_div]
        unfold Gen.normalizedA Gen.Coeffs.C
        congr 1
        · rw [mul_div_assoc, Finset.sum_div]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
        · simp only [Finset.sum_div]
          refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦
            Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
          ring

/-- **The divergence identity.** At `x₀`, with every `D_l` at `z = 1`,
`w^{-2a} div Z = 5U:A + C(δA + δA) + [D_lG + (2a-1)q_lG]X + w[D_lM + (2a+1)q_lM]
  + D_lP + 2a q_lP`. -/
theorem divergence_fluxZ_eq :
    divergence (Gen.fluxZ c u) J.x₀ = Gen.normW J.T ^ (2 * aExp) *
      (((n - 1 : ℕ) : ℝ) * ∑ j, ∑ k, c.U (Gen.normalizedA J.T, J.p, J.g) j k *
          Gen.normalizedA J.T j k +
        ∑ l, ∑ i, ∑ j, ∑ k, c.C (Gen.normalizedA J.T, J.p, J.g) l i j k *
          (Gen.kron l j * Gen.normalizedA J.T i k + Gen.kron l k * Gen.normalizedA J.T i j) +
        c.termG (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1 +
        c.termM (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1 +
        c.termP (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1) := by
  have hx0 := h.norm_x₀
  have hwpos : 0 < Gen.fluxW u J.x₀ := by
    rw [Gen.fluxW_eq_transported hx0 h.x₀_ne_zero h.inner_radialProj_x₀ h.inner_ι, h.transW_self]
    exact Gen.normW_pos_iff.2 hw
  have hd : DifferentiableAt ℝ (Gen.fluxZ c u) J.x₀ :=
    (Gen.contDiffAt_fluxZ hc h.x₀_ne_zero (by rwa [radialProj_of_norm_eq_one hx0]) hwpos
      ).differentiableAt (by simp)
  rw [(Gen.isZeroHomogeneous_fluxZ c u).divergence_eq_transported_trace
    (Gen.isTangentialField_fluxZ c u) hx0 h.inner_ι hd]
  have hev : ∀ l : Fin (n - 1), (fun x ↦ ⟪transFrame J.x₀ J.ι x l, Gen.fluxZ c u x⟫) =ᶠ[𝓝 J.x₀]
      fun x ↦ c.fluxZComp (Gen.transTData u J.x₀ J.ι x) (Gen.transBData u J.x₀ J.ι x)
        (Gen.transPData u J.x₀ J.ι x) (transG u x) l := fun l ↦ by
    filter_upwards [eventually_transport_defined hx0] with x hx
    exact Gen.inner_transFrame_fluxZ hx0 hx.1 hx.2 h.inner_ι hc l
  rw [Finset.sum_congr rfl fun l _ ↦ by rw [(hev l).fderiv_eq, h.fderiv_fluxZComp hc hu hw l],
    ← Finset.mul_sum]
  congr 1
  unfold Gen.Coeffs.termG Gen.Coeffs.termM Gen.Coeffs.termP
  rw [one_mul, Finset.mul_sum (a := Gen.normW J.T)]
  simp only [Finset.sum_add_distrib]
  rw [h.sum_G_mul_DB_div]

end ConeJets.IsConeJet

/-! ### Admissibility of the normalized data -/

theorem Gen.sq2_normalizedA {m : ℕ} {T : Gen.Ten2 m} (hw : Gen.sq2 T ≠ 0) :
    Gen.sq2 (Gen.normalizedA T) = 1 := by
  have h0 : 0 ≤ Gen.sq2 T := by unfold Gen.sq2; positivity
  have hw2 : Gen.normW T ^ 2 = Gen.sq2 T := Real.sq_sqrt h0
  have hw0 : Gen.normW T ^ 2 ≠ 0 := pow_ne_zero 2 (Gen.normW_pos_iff.2 hw).ne'
  calc Gen.sq2 (Gen.normalizedA T) = (∑ i, ∑ j, T i j ^ 2) / Gen.normW T ^ 2 := by
        simp only [Gen.sq2, Gen.normalizedA, div_pow, Finset.sum_div]
    _ = 1 := by
        rw [show (∑ i, ∑ j, T i j ^ 2) = Gen.sq2 T from rfl, ← hw2]
        exact div_self hw0

namespace ConeJets.IsConeJet

variable {n : ℕ} {u : E n → ℝ} {J : ConeJets n} (h : IsConeJet u J)
include h

theorem isSTF2_normalizedA : Gen.IsSTF2 (Gen.normalizedA J.T) := by
  refine ⟨fun i j ↦ by simp only [Gen.normalizedA, h.T_symm i j], ?_⟩
  simp only [Gen.normalizedA, ← Finset.sum_div, h.T_trace, zero_div]

theorem isSTF3_normalizedX : Gen.IsSTF3 (Gen.normalizedX J.T J.B) := by
  refine ⟨fun i j k ↦ by simp only [Gen.normalizedX, h.B_symm₁₂ i j k],
    fun i j k ↦ by simp only [Gen.normalizedX, h.B_symm₂₃ i j k], fun k ↦ ?_⟩
  simp only [Gen.normalizedX, ← Finset.sum_div, h.B_trace k, zero_div]

/-- The admissibility `g² + |p|² ≤ 1` is `|∇u(x₀)|² ≤ 1`. -/
theorem admissible_of_normSq_gradient_le (hs : ‖∇ u J.x₀‖ ^ 2 ≤ 1) :
    J.g ^ 2 + Gen.sq1 J.p ≤ 1 := by
  rw [h.normSq_gradient_eq] at hs
  exact hs

end ConeJets.IsConeJet

/-! ### The derivative of `h` -/

/-- `𝓕_l = D_l f + 2a q_l f` at `z = 1`. -/
def Gen.Coeffs.calF {m : ℕ} (c : Gen.Coeffs m) (A : Gen.Ten2 m) (X : Gen.Ten3 m) (p : Gen.Ten1 m)
    (g w : ℝ) (l : Fin m) : ℝ :=
  Gen.Dl c.f A X p g w 1 l + 2 * aExp * Gen.qVec X A l * c.f (A, p, g)

/-- The minimizer `ℓ* = 𝓕 / (2f)` of the quadratic `f|ℓ|² - 𝓕·ℓ`. -/
def Gen.Coeffs.ellStar {m : ℕ} (c : Gen.Coeffs m) (A : Gen.Ten2 m) (X : Gen.Ten3 m) (p : Gen.Ten1 m)
    (g w : ℝ) : Gen.Ten1 m :=
  fun l ↦ c.calF A X p g w l / (2 * c.f (A, p, g))

/-- For a `0`-homogeneous scalar differentiable at a unit vector `x₀`,
`|∇φ(x₀)|² = ∑_l (Dφ(x₀)[τ_l])²`. -/
theorem normSq_gradient_eq_sum_frame {n : ℕ} {φ : E n → ℝ} (hφ : IsZeroHomogeneous φ) {x₀ : E n}
    {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
    (hd : DifferentiableAt ℝ φ x₀) :
    ‖∇ φ x₀‖ ^ 2 = ∑ l, fderiv ℝ φ x₀ (frameVec ι l) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (adaptedBasis hx hι).sum_inner_mul_inner, Fintype.sum_option]
  have hc : ∀ v, ⟪v, ∇ φ x₀⟫ = fderiv ℝ φ x₀ v := fun v ↦ by
    rw [real_inner_comm, inner_gradient_left]
  simp only [adaptedBasis_apply, adaptedVec_none, adaptedVec_some, inner_gradient_left, hc,
    hφ.fderiv_apply_self hd, mul_zero, zero_add, sq]

namespace ConeJets.IsConeJet

variable {n : ℕ} {u : E n → ℝ} {J : ConeJets n} {c : Gen.Coeffs (n - 1)} {ε δ : ℝ}
  (hc : Gen.CertificateHolds (n - 1) ε δ c)
  (h : IsConeJet u J) (hu : ContDiffAt ℝ ∞ u J.x₀) (hw : Gen.sq2 J.T ≠ 0)
  (hf : 0 < c.f (Gen.normalizedA J.T, J.p, J.g))
include hc h hu hw hf

theorem fderiv_fluxHComp (l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ c.fluxHComp (Gen.transTData u J.x₀ J.ι x) (Gen.transPData u J.x₀ J.ι x)
        (transG u x)) J.x₀ (frameVec J.ι l) =
      Gen.normW J.T ^ aExp * c.calF (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g
          (Gen.normW J.T) l /
        (2 * √(c.f (Gen.normalizedA J.T, J.p, J.g))) := by
  set nd : E n → Gen.Ten2 (n - 1) × Gen.Ten1 (n - 1) × ℝ := fun x ↦
    (Gen.normalizedA (Gen.transTData u J.x₀ J.ι x), Gen.transPData u J.x₀ J.ι x, transG u x) with
        hnd
  set W : E n → ℝ := fun x ↦ Gen.normW (Gen.transTData u J.x₀ J.ι x) with hW
  have hnd0 : nd J.x₀ = (Gen.normalizedA J.T, J.p, J.g) := h.normalizedData_self
  have hW0 : W J.x₀ = Gen.normW J.T := h.transW_self
  have hw0 : Gen.normW J.T ≠ 0 := normW_ne_zero hw
  have hdnd : DifferentiableAt ℝ nd J.x₀ := h.differentiableAt_normalizedData hu hw
  have hdW : DifferentiableAt ℝ W J.x₀ := h.differentiableAt_transW hu hw
  have hdf : DifferentiableAt ℝ (fun x ↦ c.f (nd x)) J.x₀ :=
    (hc.smooth_f.differentiable (by simp) _).comp J.x₀ hdnd
  have hDf : fderiv ℝ (fun x ↦ c.f (nd x)) J.x₀ (frameVec J.ι l) =
      Gen.Dl c.f (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1 l :=
    h.fderiv_certPoly_eq_Dl hu hw _ ((hc.smooth_f.differentiable (by simp)) _) l
  have hf0 : c.f (nd J.x₀) ≠ 0 := by rw [hnd0]; exact hf.ne'
  change fderiv ℝ (fun x ↦ W x ^ aExp * √(c.f (nd x))) J.x₀ (frameVec J.ι l) = _
  rw [fderiv_mul_apply' (hdW.rpow_const (Or.inl (by rw [hW0]; exact hw0))) (hdf.sqrt hf0),
    fderiv_sqrt_apply' hdf hf0, fderiv_rpow_apply' hdW (by rw [hW0]; exact hw0), hDf,
    h.fderiv_transW hu hw l, hnd0, hW0]
  unfold Gen.Coeffs.calF
  set w := Gen.normW J.T
  set f0 := c.f (Gen.normalizedA J.T, J.p, J.g)
  have hsq : √f0 * √f0 = f0 := Real.mul_self_sqrt hf.le
  have hs0 : √f0 ≠ 0 := (Real.sqrt_pos.2 hf).ne'
  have hpow : w ^ (aExp - 1) * w = w ^ aExp := by
    rw [Real.rpow_sub_one hw0, div_mul_cancel₀ _ hw0]
  field_simp
  linear_combination (2 * aExp * Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l * f0) *
      hpow +
    (2 * aExp * w ^ (aExp - 1) * w * Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l) *
        hsq

omit hu hw hf in
theorem fluxH_self :
    Gen.fluxH c u J.x₀ = Gen.normW J.T ^ aExp * √(c.f (Gen.normalizedA J.T, J.p, J.g)) := by
  rw [Gen.fluxH_eq_transported h.norm_x₀ h.x₀_ne_zero h.inner_radialProj_x₀ h.inner_ι hc,
    h.transTData_self, h.transPData_self, h.transG_self]
  rfl

omit hc hu hw hf in
theorem fluxW_self : Gen.fluxW u J.x₀ = Gen.normW J.T := by
  rw [Gen.fluxW_eq_transported h.norm_x₀ h.x₀_ne_zero h.inner_radialProj_x₀ h.inner_ι,
    h.transTData_self]

omit hu hw hf in
theorem fluxF_self : Gen.fluxF c u J.x₀ = c.f (Gen.normalizedA J.T, J.p, J.g) := by
  rw [Gen.fluxF_eq_transported h.norm_x₀ h.x₀_ne_zero h.inner_radialProj_x₀ h.inner_ι hc,
    h.transTData_self, h.transPData_self, h.transG_self]

theorem differentiableAt_fluxH : DifferentiableAt ℝ (Gen.fluxH c u) J.x₀ := by
  have hx0 := h.norm_x₀
  refine (Gen.contDiffAt_fluxH hc h.x₀_ne_zero (by rwa [radialProj_of_norm_eq_one hx0])
    (by rw [h.fluxW_self]; exact Gen.normW_pos_iff.2 hw)
    (by rw [h.fluxF_self hc]; exact hf.ne')).differentiableAt (by simp)

/-- **`∇_l h = w^a 𝓕_l / (2√f)`.** -/
theorem fderiv_fluxH_frame (l : Fin (n - 1)) :
    fderiv ℝ (Gen.fluxH c u) J.x₀ (frameVec J.ι l) =
      Gen.normW J.T ^ aExp * c.calF (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g
          (Gen.normW J.T) l /
        (2 * √(c.f (Gen.normalizedA J.T, J.p, J.g))) := by
  have hev : Gen.fluxH c u =ᶠ[𝓝 J.x₀] fun x ↦ c.fluxHComp (Gen.transTData u J.x₀ J.ι x)
      (Gen.transPData u J.x₀ J.ι x) (transG u x) := by
    filter_upwards [eventually_transport_defined h.norm_x₀] with x hx
    exact Gen.fluxH_eq_transported h.norm_x₀ hx.1 hx.2 h.inner_ι hc
  rw [hev.fderiv_eq, h.fderiv_fluxHComp hc hu hw hf l]

/-- **`|∇h|² = w^{2a} |𝓕|² / (4f)`.** -/
theorem normSq_gradient_fluxH :
    ‖∇ (Gen.fluxH c u) J.x₀‖ ^ 2 = Gen.normW J.T ^ (2 * aExp) *
      Gen.sq1 (c.calF (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T)) /
        (4 * c.f (Gen.normalizedA J.T, J.p, J.g)) := by
  rw [normSq_gradient_eq_sum_frame (Gen.isZeroHomogeneous_fluxH c u) h.norm_x₀ h.inner_ι
    (h.differentiableAt_fluxH hc hu hw hf)]
  simp only [h.fderiv_fluxH_frame hc hu hw hf]
  have hw0 : 0 ≤ Gen.normW J.T := Real.sqrt_nonneg _
  have hpow : (Gen.normW J.T ^ aExp) ^ 2 = Gen.normW J.T ^ (2 * aExp) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0]
    ring_nf
  have hsq : √(c.f (Gen.normalizedA J.T, J.p, J.g)) ^ 2 = c.f (Gen.normalizedA J.T, J.p, J.g) :=
    Real.sq_sqrt hf.le
  unfold Gen.sq1
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [div_pow, mul_pow, mul_pow, hpow, hsq]
  ring

omit hu hw in
/-- **`h² = w^{2a} f`.** -/
theorem fluxH_self_sq :
    Gen.fluxH c u J.x₀ ^ 2 = Gen.normW J.T ^ (2 * aExp) * c.f (Gen.normalizedA J.T, J.p, J.g) := by
  rw [h.fluxH_self hc, mul_pow, Real.sq_sqrt hf.le, ← Real.rpow_natCast,
    ← Real.rpow_mul (show 0 ≤ Gen.normW J.T from Real.sqrt_nonneg _)]
  ring_nf

/-- **Square completion**: for every `ℓ`,
`𝓘|_{z=1} = w^{-2a}(div Z - β²h² - |∇h|²) + f|ℓ - ℓ*|²`, with `β² = ((n - 2)/2)²`. -/
theorem interior_square_completion (ℓ : Gen.Ten1 (n - 1)) :
    c.interiorExpr (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1 ℓ =
      (divergence (Gen.fluxZ c u) J.x₀ - Gen.hardyConst (n - 1) * Gen.fluxH c u J.x₀ ^ 2 - ‖∇
          (Gen.fluxH c u) J.x₀‖ ^ 2) /
          Gen.normW J.T ^ (2 * aExp) +
        c.f (Gen.normalizedA J.T, J.p, J.g) *
          Gen.sq1 (ℓ - c.ellStar (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW
              J.T)) := by
  have hW : Gen.normW J.T ^ (2 * aExp) ≠ 0 :=
    (Real.rpow_pos_of_pos (Gen.normW_pos_iff.2 hw) _).ne'
  rw [h.divergence_fluxZ_eq hc hu hw, h.fluxH_self_sq hc hf,
    h.normSq_gradient_fluxH hc hu hw hf]
  set f0 := c.f (Gen.normalizedA J.T, J.p, J.g)
  set F := c.calF (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T)
  have hF : ∑ l, (Gen.Dl c.f (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW
      J.T) 1 l +
      2 * aExp * Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l * f0) * ℓ l =
      ∑ l, F l * ℓ l := rfl
  have hquad : f0 * Gen.sq1 (ℓ - c.ellStar (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g
      (Gen.normW J.T)) = f0 * Gen.sq1 ℓ - ∑ l, F l * ℓ l + Gen.sq1 F / (4 * f0) := by
    unfold Gen.sq1 Gen.Coeffs.ellStar
    simp only [Pi.sub_apply, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    change f0 * (ℓ l - F l / (2 * f0)) ^ 2 = _
    field_simp
    ring
  unfold Gen.Coeffs.interiorExpr Gen.Coeffs.termZ Gen.Coeffs.termF
  rw [hF, hquad]
  field_simp
  ring

/-- **The interior comparison, sharp form**:
`div Z - β²h² - |∇h|² ≥ ε w^{2a}(1 + |ℓ*|²)` at `x₀`, for admissible data. -/
theorem interior_comparison_sharp (hs : J.g ^ 2 + Gen.sq1 J.p ≤ 1) :
    ε * Gen.normW J.T ^ (2 * aExp) *
        (1 + Gen.sq1 (c.ellStar (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW
            J.T))) ≤
      divergence (Gen.fluxZ c u) J.x₀ - Gen.hardyConst (n - 1) * Gen.fluxH c u J.x₀ ^ 2 - ‖∇
          (Gen.fluxH c u) J.x₀‖ ^ 2 := by
  set ℓs := c.ellStar (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T)
  have hI := hc.interior (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1
      ℓs
    h.isSTF2_normalizedA (Gen.sq2_normalizedA hw) h.isSTF3_normalizedX hs
  rw [h.interior_square_completion hc hu hw hf ℓs, sub_self] at hI
  have hW : 0 < Gen.normW J.T ^ (2 * aExp) := Real.rpow_pos_of_pos (Gen.normW_pos_iff.2 hw) _
  have h0 : Gen.sq1 (0 : Gen.Ten1 (n - 1)) = 0 := by simp [Gen.sq1]
  rw [h0, mul_zero, add_zero, le_div_iff₀ hW] at hI
  nlinarith [hI]

end ConeJets.IsConeJet

namespace Gen

variable {n : ℕ}

/-- **The interior comparison, with the minimizer.** Let `u` be one-homogeneous, smooth and
harmonic near a unit vector `x₀ ∈ ℝⁿ`, with `w(x₀) > 0` and `|∇u(x₀)|² ≤ 1`, and let `c` satisfy
the certificate in `ℝ^{n-1}` with constants `ε > 0`, `δ`. Then there is `ℓ` with
`div Z - β²h² - |∇h|² ≥ ε w^{2a}(1 + |ℓ|²)` at `x₀`, where `β² = ((n - 2)/2)²`. -/
theorem div_fluxZ_sub_ge {c : Coeffs (n - 1)} {ε δ : ℝ} (hc : CertificateHolds (n - 1) ε δ c)
    (hε : 0 < ε) {u : E n → ℝ}
    (hhom : IsOneHomogeneous u) {x₀ : E n} (hx₀ : ‖x₀‖ = 1) (hu : ContDiffAt ℝ ∞ u x₀)
    (hΔ : ∀ᶠ y in 𝓝 x₀, Δ u y = 0) (hw : 0 < fluxW u x₀) (hs : ‖∇ u x₀‖ ^ 2 ≤ 1) :
    ∃ ℓ : Ten1 (n - 1), ε * fluxW u x₀ ^ (2 * aExp) * (1 + sq1 ℓ) ≤
      divergence (fluxZ c u) x₀ - hardyConst (n - 1) * fluxH c u x₀ ^ 2 - ‖∇ (fluxH c u) x₀‖ ^ 2 :=
          by
  have hu4 : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 4 u y :=
    (hu.of_le (by simp)).eventually (by simp)
  have hJ := ConeJets.isConeJet_ofHarmonicHomogeneous hx₀ hhom hu4 hΔ
  set J := ConeJets.ofHarmonicHomogeneous u x₀ hx₀
  have hu' : ContDiffAt ℝ ∞ u J.x₀ := hu
  have hs' := hJ.admissible_of_normSq_gradient_le hs
  have hw' : sq2 J.T ≠ 0 := by
    have hw1 : 0 < fluxW u J.x₀ := hw
    rw [hJ.fluxW_self] at hw1
    exact normW_pos_iff.1 hw1
  have hf : 0 < c.f (normalizedA J.T, J.p, J.g) :=
    lt_of_lt_of_le hε (hc.f_ge _ _ _ hJ.isSTF2_normalizedA (sq2_normalizedA hw') hs')
  refine ⟨c.ellStar (normalizedA J.T) (normalizedX J.T J.B) J.p J.g (normW J.T), ?_⟩
  have := hJ.interior_comparison_sharp hc hu' hw' hf hs'
  change ε * fluxW u J.x₀ ^ (2 * aExp) * _ ≤ divergence (fluxZ c u) J.x₀ -
    hardyConst (n - 1) * fluxH c u J.x₀ ^ 2 - ‖∇ (fluxH c u) J.x₀‖ ^ 2
  rwa [hJ.fluxW_self]

/-- **The interior comparison**. Let `u` be one-homogeneous, smooth and harmonic near a unit
vector `x₀ ∈ ℝⁿ`, with `w(x₀) > 0` and `|∇u(x₀)|² ≤ 1`, and let `c` satisfy the certificate in
`ℝ^{n-1}` with constants `ε > 0`, `δ`. Then `div Z ≥ β²h² + |∇h|² + ε w^{2a}` at `x₀`, where
`β² = ((n - 2)/2)²` is the Hardy constant of `S^{n-1}`. -/
theorem div_fluxZ_ge {c : Coeffs (n - 1)} {ε δ : ℝ} (hc : CertificateHolds (n - 1) ε δ c)
    (hε : 0 < ε) {u : E n → ℝ}
    (hhom : IsOneHomogeneous u) {x₀ : E n} (hx₀ : ‖x₀‖ = 1) (hu : ContDiffAt ℝ ∞ u x₀)
    (hΔ : ∀ᶠ y in 𝓝 x₀, Δ u y = 0) (hw : 0 < fluxW u x₀) (hs : ‖∇ u x₀‖ ^ 2 ≤ 1) :
    hardyConst (n - 1) * fluxH c u x₀ ^ 2 + ‖∇ (fluxH c u) x₀‖ ^ 2 + ε * fluxW u x₀ ^ (2 * aExp) ≤
      divergence (fluxZ c u) x₀ := by
  obtain ⟨ℓ, hℓ⟩ := div_fluxZ_sub_ge hc hε hhom hx₀ hu hΔ hw hs
  have hW : 0 ≤ ε * fluxW u x₀ ^ (2 * aExp) :=
    mul_nonneg hε.le (Real.rpow_nonneg (fluxW_nonneg u x₀) _)
  have hℓ0 : 0 ≤ sq1 ℓ := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  nlinarith

end Gen

/-! ### Dimension six -/

/-- **The interior comparison in `ℝ⁶`**. Let `u` be one-homogeneous, smooth
and harmonic near a unit vector `x₀ ∈ ℝ⁶`, with `w(x₀) > 0` and `|∇u(x₀)|² ≤ 1`, and let `c`
satisfy the certificate. Then `div Z ≥ 4h² + |∇h|² + ε* w^{2a}` at `x₀`. -/
theorem div_fluxZ_ge {c : Coeffs} (hc : CertificateHolds c) {u : E 6 → ℝ}
    (hhom : IsOneHomogeneous u) {x₀ : E 6} (hx₀ : ‖x₀‖ = 1) (hu : ContDiffAt ℝ ∞ u x₀)
    (hΔ : ∀ᶠ y in 𝓝 x₀, Δ u y = 0) (hw : 0 < fluxW u x₀) (hs : ‖∇ u x₀‖ ^ 2 ≤ 1) :
    4 * fluxH c u x₀ ^ 2 + ‖∇ (fluxH c u) x₀‖ ^ 2 + εStar * fluxW u x₀ ^ (2 * aExp) ≤
      divergence (fluxZ c u) x₀ := by
  have h := Gen.div_fluxZ_ge (n := 6) hc.toGen εStar_pos hhom hx₀ hu hΔ hw hs
  have h5 : Gen.hardyConst (6 - 1) = 4 := Gen.hardyConst_five
  rw [h5] at h
  exact h

/-- `|A| = 1` for `A = T/|T|`, `T ≠ 0`. -/
theorem sq2_normalizedA {T : Ten2} (hw : sq2 T ≠ 0) : sq2 (normalizedA T) = 1 :=
  Gen.sq2_normalizedA hw

end OnePhaseDimension
