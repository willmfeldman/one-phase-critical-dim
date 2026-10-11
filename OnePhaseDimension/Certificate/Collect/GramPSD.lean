/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Projection
public import OnePhaseDimension.Certificate.Spike.Expand
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Nonnegativity of Gram sums

For a symmetric positive semidefinite bilinear form `β` and vectors `v_s` with integer
coefficient columns `(c_{sc})_c`, the Gram sum over unordered pairs

  `∑_s (∑_c c_{sc}²) β(v_s, v_s) + ∑_{s < t} 2 (∑_c c_{sc} c_{tc}) β(v_s, v_t)`

equals `∑_c β(J_c, J_c)` with `J_c = ∑_s c_{sc} v_s`, hence is nonnegative. The columns are
peeled off one at a time (`Expand.dot` of the columns is the first products plus `dot` of the
tails), so ragged columns need no special treatment.

The bilinear forms of the four projections are built from an inner product `ip` and a
self-adjoint operator `P` as `β(x, y) = ip y (P x)`.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Expand Finset

theorem dot_comm : ∀ a b : List ℤ, dot a b = dot b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by simp only [dot, dot_comm a b, mul_comm]

theorem dot_eq_head_tail : ∀ a b : List ℤ, dot a b = a.headD 0 * b.headD 0 + dot a.tail b.tail
  | [], [] => rfl
  | [], _ :: _ => by simp [dot]
  | _ :: _, [] => by simp [dot]
  | _ :: _, _ :: _ => rfl

theorem dot_eq_zero_of_length {a b : List ℤ} (ha : a.length = 0) : dot a b = 0 := by
  rw [List.length_eq_zero_iff] at ha; subst ha; cases b <;> rfl

theorem le_sum_of_mem' {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.sum
  | b :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem' h; simp; omega

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- The Gram sum over ordered pairs. -/
noncomputable def fullSum (L : List (V × List ℤ)) : ℝ :=
  (L.map fun s => (L.map fun t => (dot s.2 t.2 : ℝ) * β s.1 t.1).sum).sum

/-- The Gram sum over unordered pairs, off-diagonal pairs counted twice. -/
noncomputable def upperSum : List (V × List ℤ) → ℝ
  | [] => 0
  | r :: L => (dot r.2 r.2 : ℝ) * β r.1 r.1 +
      (L.map fun t => ((2 * dot r.2 t.2 : ℤ) : ℝ) * β r.1 t.1).sum + upperSum L

theorem list_sum_apply_left (L : List (V × List ℤ)) (f : V × List ℤ → ℝ) (y : V) :
    β (L.map fun s => f s • s.1).sum y = (L.map fun s => f s * β s.1 y).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem list_sum_apply_right (L : List (V × List ℤ)) (f : V × List ℤ → ℝ) (x : V) :
    β x (L.map fun s => f s • s.1).sum = (L.map fun s => f s * β x s.1).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

theorem fullSum_eq_head_add_tail (L : List (V × List ℤ)) :
    fullSum β L = β (L.map fun s => ((s.2.headD 0 : ℤ) : ℝ) • s.1).sum
        (L.map fun s => ((s.2.headD 0 : ℤ) : ℝ) • s.1).sum +
      fullSum β (L.map fun r => (r.1, r.2.tail)) := by
  rw [list_sum_apply_left]
  simp only [fullSum, list_sum_apply_right, List.map_map, Function.comp_def,
    ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  rw [← List.sum_map_mul_left, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [dot_eq_head_tail]
  push_cast
  ring

/-- A positive semidefinite Gram sum over ordered pairs is nonnegative. -/
theorem fullSum_nonneg (hpsd : ∀ x, 0 ≤ β x x) :
    ∀ (n : ℕ) (L : List (V × List ℤ)), (∀ r ∈ L, r.2.length ≤ n) → 0 ≤ fullSum β L
  | 0, L, h => by
    have : fullSum β L = 0 := by
      simp only [fullSum]
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      refine List.sum_eq_zero fun y hy => ?_
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hy
      rw [dot_eq_zero_of_length (Nat.le_zero.1 (h s hs))]
      simp
    rw [this]
  | n + 1, L, h => by
    rw [fullSum_eq_head_add_tail]
    refine add_nonneg (hpsd _) (fullSum_nonneg hpsd n _ fun r hr => ?_)
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    simp only [List.length_tail]
    have := h s hs
    omega

/-- For a symmetric form, the sum over unordered pairs is the sum over ordered pairs. -/
theorem upperSum_eq_fullSum (hsym : ∀ x y, β x y = β y x) :
    ∀ L : List (V × List ℤ), upperSum β L = fullSum β L
  | [] => rfl
  | r :: L => by
    rw [upperSum, upperSum_eq_fullSum hsym L]
    simp only [fullSum, List.map_cons, List.sum_cons]
    have h : (L.map fun s => (dot s.2 r.2 : ℝ) * β s.1 r.1) =
        L.map fun t => (dot r.2 t.2 : ℝ) * β r.1 t.1 :=
      List.map_congr_left fun s _ => by rw [dot_comm, hsym]
    rw [List.sum_map_add, h]
    have h3 : (L.map fun t => ((2 * dot r.2 t.2 : ℤ) : ℝ) * β r.1 t.1).sum =
        2 * (L.map fun t => (dot r.2 t.2 : ℝ) * β r.1 t.1).sum := by
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun t _ => by push_cast; ring
    rw [h3]
    ring

theorem upperSum_nonneg (hsym : ∀ x y, β x y = β y x) (hpsd : ∀ x, 0 ≤ β x x)
    (L : List (V × List ℤ)) : 0 ≤ upperSum β L := by
  rw [upperSum_eq_fullSum β hsym]
  exact fullSum_nonneg β hpsd ((L.map fun r => r.2.length).sum) L fun r hr =>
    le_sum_of_mem' (List.mem_map.2 ⟨r, hr, rfl⟩)

end Abstract

/-! ### Forms from a self-adjoint operator -/

section Forms

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The bilinear form `β(x, y) = ip y (P x)` of an operator `P` self-adjoint for a pairing `ip`
that is linear in its first argument. -/
noncomputable def mkForm (ip : W → W → ℝ) (P : W → W)
    (hadd : ∀ a b c, ip (a + b) c = ip a c + ip b c)
    (hsmul : ∀ (r : ℝ) a c, ip (r • a) c = r * ip a c)
    (hcomm : ∀ T S, ip T (P S) = ip S (P T)) : W →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ip y (P x))
    (fun x x' y => by rw [hcomm, hadd, ← hcomm, ← hcomm y x'])
    (fun r x y => by rw [hcomm, hsmul, ← hcomm, smul_eq_mul])
    (fun x y y' => hadd y y' (P x))
    (fun r x y => by rw [hsmul, smul_eq_mul])

theorem mkForm_apply (ip : W → W → ℝ) (P : W → W) (hadd hsmul hcomm) (x y : W) :
    mkForm ip P hadd hsmul hcomm x y = ip y (P x) := rfl

theorem mkForm_symm (ip : W → W → ℝ) (P : W → W) (hadd hsmul hcomm) (x y : W) :
    mkForm ip P hadd hsmul hcomm x y = mkForm ip P hadd hsmul hcomm y x := hcomm y x

end Forms

theorem inner2_add (a b c : Fin 5 → Fin 5 → ℝ) :
    Proj.inner2 (a + b) c = Proj.inner2 a c + Proj.inner2 b c := by
  simp only [Proj.inner2, Pi.add_apply, add_mul, sum_add_distrib]

theorem inner2_smul (r : ℝ) (a c : Fin 5 → Fin 5 → ℝ) :
    Proj.inner2 (r • a) c = r * Proj.inner2 a c := by
  simp only [Proj.inner2, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

theorem inner3_add (a b c : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    Proj.inner3 (a + b) c = Proj.inner3 a c + Proj.inner3 b c := by
  simp only [Proj.inner3, Pi.add_apply, add_mul, sum_add_distrib]

theorem inner3_smul (r : ℝ) (a c : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    Proj.inner3 (r • a) c = r * Proj.inner3 a c := by
  simp only [Proj.inner3, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

/-- The plain pairing `∑_α x(α) y(α)` on functions of `α : Fin r → Fin 5`. -/
noncomputable def ipNone (r : ℕ) (x y : (Fin r → Fin 5) → ℝ) : ℝ := ∑ α, x α * y α

/-- The form of the projection `none` of rank `r`. -/
noncomputable def formNone (r : ℕ) : ((Fin r → Fin 5) → ℝ) →ₗ[ℝ] ((Fin r → Fin 5) → ℝ) →ₗ[ℝ] ℝ :=
  mkForm (ipNone r) id
    (fun a b c => by simp only [ipNone, Pi.add_apply, add_mul, sum_add_distrib])
    (fun r a c => by simp only [ipNone, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum])
    (fun T S => by simp only [ipNone, id, mul_comm])

/-- The form of the projection `sym` of rank `2`. -/
noncomputable def formSym2 : (Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] ℝ :=
  mkForm Proj.inner2 Proj.projSym2 inner2_add inner2_smul Proj.inner_projSym2_comm

/-- The form of the projection `anti` of rank `2`. -/
noncomputable def formAnti2 : (Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] ℝ :=
  mkForm Proj.inner2 Proj.projAnti2 inner2_add inner2_smul Proj.inner_projAnti2_comm

/-- The form of the projection `sym` of rank `3`. -/
noncomputable def formSym3 :
    (Fin 5 → Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] ℝ :=
  mkForm Proj.inner3 Proj.projSym3 inner3_add inner3_smul Proj.inner_projSym3_comm

/-- The form of the projection `hook` of rank `3`. -/
noncomputable def formHook :
    (Fin 5 → Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → Fin 5 → Fin 5 → ℝ) →ₗ[ℝ] ℝ :=
  mkForm Proj.inner3 Proj.projHook inner3_add inner3_smul Proj.inner_projHook_comm

theorem formNone_nonneg (r : ℕ) (x : (Fin r → Fin 5) → ℝ) : 0 ≤ formNone r x x :=
  sum_nonneg fun _ _ => mul_self_nonneg _

theorem formSym2_nonneg (x : Fin 5 → Fin 5 → ℝ) : 0 ≤ formSym2 x x :=
  Proj.inner_projSym2_nonneg x

theorem formAnti2_nonneg (x : Fin 5 → Fin 5 → ℝ) : 0 ≤ formAnti2 x x :=
  Proj.inner_projAnti2_nonneg x

theorem formSym3_nonneg (x : Fin 5 → Fin 5 → Fin 5 → ℝ) : 0 ≤ formSym3 x x :=
  Proj.inner_projSym3_nonneg x

theorem formHook_nonneg (x : Fin 5 → Fin 5 → Fin 5 → ℝ) : 0 ≤ formHook x x :=
  Proj.inner_projHook_nonneg x

end OnePhaseDimension.Certificate.Collect
