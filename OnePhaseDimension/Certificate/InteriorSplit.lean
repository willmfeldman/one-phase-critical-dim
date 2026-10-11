/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Polynomials

/-!
# The interior expression splits by coefficient family

The interior expression `𝓘` of coefficient maps `(f, U, K, M, P)` is the sum of five parts, each
depending on one family only (the coupling `G = δ U + C` in the derivative term is split by
linearity of `D_l`, given differentiability). Each part is affine-linear in its family, so its
value on a sum of rows is the sum of the values on the rows.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

variable (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (ℓ : Ten1)

/-- The part of `𝓘` depending on `f`. -/
noncomputable def iPartF (f : Ten2 × Ten1 × ℝ → ℝ) : ℝ :=
  -4 * z ^ 2 * f (A, p, g) + f (A, p, g) * sq1 ℓ -
    ∑ l, (Dl f A X p g w z l + 2 * aExp * qVec X A l * f (A, p, g)) * ℓ l

/-- The part of `𝓘` depending on `U`. -/
noncomputable def iPartU (U : Ten2 × Ten1 × ℝ → Ten2) : ℝ :=
  z ^ 2 * (5 * ∑ j, ∑ k, U (A, p, g) j k * A j k) +
    ∑ l, ∑ i, ∑ j, ∑ k, (Dl (fun y => kron l i * U y j k) A X p g w z l +
      (2 * aExp - 1) * qVec X A l * (kron l i * U (A, p, g) j k)) * X i j k

/-- The part of `𝓘` depending on `K`. -/
noncomputable def iPartK (K : Ten2 × Ten1 × ℝ → Ten4) : ℝ :=
  z ^ 2 * ∑ l, ∑ i, ∑ j, ∑ k, (K (A, p, g) l i j k - K (A, p, g) i l j k) *
      (kron l j * A i k + kron l k * A i j) +
    ∑ l, ∑ i, ∑ j, ∑ k, (Dl (fun y => K y l i j k - K y i l j k) A X p g w z l +
      (2 * aExp - 1) * qVec X A l * (K (A, p, g) l i j k - K (A, p, g) i l j k)) * X i j k

/-- The part of `𝓘` depending on a vector family, with factor `s` and constant `κ`. -/
noncomputable def iPartV (κ s : ℝ) (V : Ten2 × Ten1 × ℝ → Ten1) : ℝ :=
  s * ∑ l, (Dl (fun y => V y l) A X p g w z l + κ * qVec X A l * V (A, p, g) l)

variable {A X p g w z ℓ}

theorem interiorExpr_split (c : Coeffs)
    (hU : ∀ j k, DifferentiableAt ℝ (fun y => c.U y j k) (A, p, g))
    (hK : ∀ l i j k, DifferentiableAt ℝ (fun y => c.K y l i j k) (A, p, g)) :
    c.interiorExpr A X p g w z ℓ = iPartF A X p g w z ℓ c.f + iPartU A X p g w z c.U +
      iPartK A X p g w z c.K + iPartV A X p g w z (2 * aExp + 1) w c.M +
      iPartV A X p g w z (2 * aExp) z c.P := by
  have hG : ∀ l i j k, (Dl (fun y => c.G y l i j k) A X p g w z l +
      (2 * aExp - 1) * qVec X A l * c.G (A, p, g) l i j k) * X i j k =
      (Dl (fun y => kron l i * c.U y j k) A X p g w z l +
        (2 * aExp - 1) * qVec X A l * (kron l i * c.U (A, p, g) j k)) * X i j k +
      (Dl (fun y => c.K y l i j k - c.K y i l j k) A X p g w z l +
        (2 * aExp - 1) * qVec X A l * (c.K (A, p, g) l i j k - c.K (A, p, g) i l j k)) *
          X i j k := by
    intro l i j k
    have h1 : (fun y => c.G y l i j k) =
        fun y => kron l i * c.U y j k + (c.K y l i j k - c.K y i l j k) := rfl
    have d1 : DifferentiableAt ℝ (fun y => kron l i * c.U y j k) (A, p, g) :=
      (hU j k).const_mul _
    have d2 : DifferentiableAt ℝ (fun y => c.K y l i j k - c.K y i l j k) (A, p, g) :=
      (hK l i j k).sub (hK i l j k)
    rw [h1, Dl_add A X p g w z l d1 d2]
    simp only [Coeffs.G, Coeffs.C]
    ring
  simp only [Coeffs.interiorExpr, Coeffs.termZ, Coeffs.termG, Coeffs.termM, Coeffs.termP,
    Coeffs.termF, hG, sum_add_distrib, iPartF, iPartU, iPartK, iPartV, Coeffs.C]
  ring

/-! ### Affine linearity of the parts -/

theorem Dl_zero' : Dl (fun _ : Ten2 × Ten1 × ℝ => (0 : ℝ)) A X p g w z = fun _ => 0 := by
  funext l; simp [Dl]

theorem Dl_smul_add (a : ℝ) {F G : Ten2 × Ten1 × ℝ → ℝ} (hF : DifferentiableAt ℝ F (A, p, g))
    (hG : DifferentiableAt ℝ G (A, p, g)) (l : Fin 5) :
    Dl (fun y => a * F y + G y) A X p g w z l = a * Dl F A X p g w z l + Dl G A X p g w z l := by
  rw [Dl_add A X p g w z l (hF.const_mul a) hG, Dl_const_mul A X p g w z l a hF]

theorem iPartF_add (a : ℝ) {F G : Ten2 × Ten1 × ℝ → ℝ} (hF : DifferentiableAt ℝ F (A, p, g))
    (hG : DifferentiableAt ℝ G (A, p, g)) :
    iPartF A X p g w z ℓ (fun y => a * F y + G y) =
      a * iPartF A X p g w z ℓ F + iPartF A X p g w z ℓ G := by
  have h : ∀ l, (Dl (fun y => a * F y + G y) A X p g w z l +
      2 * aExp * qVec X A l * (a * F (A, p, g) + G (A, p, g))) * ℓ l =
      a * ((Dl F A X p g w z l + 2 * aExp * qVec X A l * F (A, p, g)) * ℓ l) +
      (Dl G A X p g w z l + 2 * aExp * qVec X A l * G (A, p, g)) * ℓ l := fun l => by
    rw [Dl_smul_add a hF hG]; ring
  simp only [iPartF, h, sum_add_distrib, ← mul_sum]
  ring

theorem iPartF_zero : iPartF A X p g w z ℓ (fun _ => 0) = 0 := by
  simp [iPartF, Dl_zero']

theorem iPartU_add (a : ℝ) {U V : Ten2 × Ten1 × ℝ → Ten2}
    (hU : ∀ j k, DifferentiableAt ℝ (fun y => U y j k) (A, p, g))
    (hV : ∀ j k, DifferentiableAt ℝ (fun y => V y j k) (A, p, g)) :
    iPartU A X p g w z (fun y j k => a * U y j k + V y j k) =
      a * iPartU A X p g w z U + iPartU A X p g w z V := by
  have h : ∀ l i j k, (Dl (fun y => kron l i * (a * U y j k + V y j k)) A X p g w z l +
      (2 * aExp - 1) * qVec X A l * (kron l i * (a * U (A, p, g) j k + V (A, p, g) j k))) *
        X i j k =
      a * ((Dl (fun y => kron l i * U y j k) A X p g w z l +
        (2 * aExp - 1) * qVec X A l * (kron l i * U (A, p, g) j k)) * X i j k) +
      (Dl (fun y => kron l i * V y j k) A X p g w z l +
        (2 * aExp - 1) * qVec X A l * (kron l i * V (A, p, g) j k)) * X i j k := by
    intro l i j k
    have e : (fun y => kron l i * (a * U y j k + V y j k)) =
        fun y => a * (kron l i * U y j k) + kron l i * V y j k := by funext y; ring
    rw [e, Dl_smul_add a ((hU j k).const_mul _) ((hV j k).const_mul _)]
    ring
  have h2 : ∀ j k, (a * U (A, p, g) j k + V (A, p, g) j k) * A j k =
      a * (U (A, p, g) j k * A j k) + V (A, p, g) j k * A j k := fun j k => by ring
  simp only [iPartU, h, h2, sum_add_distrib, ← mul_sum]
  ring

theorem iPartU_zero : iPartU A X p g w z (fun _ _ _ => 0) = 0 := by
  simp [iPartU, Dl_zero']

theorem iPartK_add (a : ℝ) {U V : Ten2 × Ten1 × ℝ → Ten4}
    (hU : ∀ l i j k, DifferentiableAt ℝ (fun y => U y l i j k) (A, p, g))
    (hV : ∀ l i j k, DifferentiableAt ℝ (fun y => V y l i j k) (A, p, g)) :
    iPartK A X p g w z (fun y l i j k => a * U y l i j k + V y l i j k) =
      a * iPartK A X p g w z U + iPartK A X p g w z V := by
  have h : ∀ l i j k, (Dl (fun y => a * U y l i j k + V y l i j k -
      (a * U y i l j k + V y i l j k)) A X p g w z l + (2 * aExp - 1) * qVec X A l *
        (a * U (A, p, g) l i j k + V (A, p, g) l i j k -
          (a * U (A, p, g) i l j k + V (A, p, g) i l j k))) * X i j k =
      a * ((Dl (fun y => U y l i j k - U y i l j k) A X p g w z l +
        (2 * aExp - 1) * qVec X A l * (U (A, p, g) l i j k - U (A, p, g) i l j k)) * X i j k) +
      (Dl (fun y => V y l i j k - V y i l j k) A X p g w z l +
        (2 * aExp - 1) * qVec X A l * (V (A, p, g) l i j k - V (A, p, g) i l j k)) *
          X i j k := by
    intro l i j k
    have e : (fun y => a * U y l i j k + V y l i j k - (a * U y i l j k + V y i l j k)) =
        fun y => a * (U y l i j k - U y i l j k) + (V y l i j k - V y i l j k) := by
      funext y; ring
    have d1 : DifferentiableAt ℝ (fun y => U y l i j k - U y i l j k) (A, p, g) :=
      (hU l i j k).sub (hU i l j k)
    have d2 : DifferentiableAt ℝ (fun y => V y l i j k - V y i l j k) (A, p, g) :=
      (hV l i j k).sub (hV i l j k)
    rw [e, Dl_smul_add a d1 d2]
    ring
  have h2 : ∀ l i j k, (a * U (A, p, g) l i j k + V (A, p, g) l i j k -
      (a * U (A, p, g) i l j k + V (A, p, g) i l j k)) * (kron l j * A i k + kron l k * A i j) =
      a * ((U (A, p, g) l i j k - U (A, p, g) i l j k) * (kron l j * A i k + kron l k * A i j)) +
      (V (A, p, g) l i j k - V (A, p, g) i l j k) * (kron l j * A i k + kron l k * A i j) :=
    fun l i j k => by ring
  simp only [iPartK, h, h2, sum_add_distrib, ← mul_sum]
  ring

theorem iPartK_zero : iPartK A X p g w z (fun _ _ _ _ _ => 0) = 0 := by
  simp [iPartK, Dl_zero']

theorem iPartV_add (κ s a : ℝ) {U V : Ten2 × Ten1 × ℝ → Ten1}
    (hU : ∀ l, DifferentiableAt ℝ (fun y => U y l) (A, p, g))
    (hV : ∀ l, DifferentiableAt ℝ (fun y => V y l) (A, p, g)) :
    iPartV A X p g w z κ s (fun y l => a * U y l + V y l) =
      a * iPartV A X p g w z κ s U + iPartV A X p g w z κ s V := by
  have h : ∀ l, Dl (fun y => a * U y l + V y l) A X p g w z l +
      κ * qVec X A l * (a * U (A, p, g) l + V (A, p, g) l) =
      a * (Dl (fun y => U y l) A X p g w z l + κ * qVec X A l * U (A, p, g) l) +
      (Dl (fun y => V y l) A X p g w z l + κ * qVec X A l * V (A, p, g) l) := fun l => by
    rw [Dl_smul_add a (hU l) (hV l)]; ring
  simp only [iPartV, h, sum_add_distrib, ← mul_sum]
  ring

theorem iPartV_zero (κ s : ℝ) : iPartV A X p g w z κ s (fun _ _ => 0) = 0 := by
  simp [iPartV, Dl_zero']

/-! ### Sums of rows -/

variable (A X p g w z ℓ)

theorem iPartF_polyMap (Q : ℝ) (ι : ℕ → Fin 5) :
    ∀ L : List (ℤ × Key), RowsXFree L →
      iPartF A X p g w z ℓ (polyMap L Q ι) =
        (L.map fun t => (t.1 / Q : ℝ) * iPartF A X p g w z ℓ (t.2.evalFun CertData.base ι)).sum
  | [], _ => by
    rw [show polyMap [] Q ι = fun _ => 0 from rfl, iPartF_zero]; rfl
  | t :: L, h => by
    have e : polyMap (t :: L) Q ι = fun y => (t.1 / Q : ℝ) * t.2.evalFun CertData.base ι y +
        polyMap L Q ι y := by funext y; simp [polyMap]
    have hL : RowsXFree L := fun s hs => h s (by simp [hs])
    rw [e, iPartF_add _ ((Key.contDiff_evalFun (n := 1) (h t (by simp)) _ ι).differentiable
      one_ne_zero _) ((contDiff_polyMap (n := 1) hL Q ι).differentiable one_ne_zero _),
      iPartF_polyMap Q ι L hL, List.map_cons, List.sum_cons]

theorem iPartU_famTen2 (Q : ℝ) :
    ∀ L : List (ℤ × Key), RowsXFree L →
      iPartU A X p g w z (famTen2 L Q) = (L.map fun t => (t.1 / Q : ℝ) *
        iPartU A X p g w z (fun y j k => t.2.evalFun CertData.base (idx2 j k) y)).sum
  | [], _ => by
    rw [show famTen2 [] Q = fun _ _ _ => 0 from rfl, iPartU_zero]; rfl
  | t :: L, h => by
    have e : famTen2 (t :: L) Q = fun y j k => (t.1 / Q : ℝ) *
        t.2.evalFun CertData.base (idx2 j k) y + famTen2 L Q y j k := by
      funext y j k; simp [famTen2, polyMap]
    have hL : RowsXFree L := fun s hs => h s (by simp [hs])
    rw [e, iPartU_add (V := famTen2 L Q) _ (fun j k =>
      (Key.contDiff_evalFun (n := 1) (h t (by simp)) _ _).differentiable one_ne_zero _)
      (fun j k => (contDiff_polyMap (n := 1) hL Q _).differentiable one_ne_zero _),
      iPartU_famTen2 Q L hL, List.map_cons, List.sum_cons]

theorem iPartK_famTen4 (Q : ℝ) :
    ∀ L : List (ℤ × Key), RowsXFree L →
      iPartK A X p g w z (famTen4 L Q) = (L.map fun t => (t.1 / Q : ℝ) *
        iPartK A X p g w z (fun y l i j k => t.2.evalFun CertData.base (idx4 l i j k) y)).sum
  | [], _ => by
    rw [show famTen4 [] Q = fun _ _ _ _ _ => 0 from rfl, iPartK_zero]; rfl
  | t :: L, h => by
    have e : famTen4 (t :: L) Q = fun y l i j k => (t.1 / Q : ℝ) *
        t.2.evalFun CertData.base (idx4 l i j k) y + famTen4 L Q y l i j k := by
      funext y l i j k; simp [famTen4, polyMap]
    have hL : RowsXFree L := fun s hs => h s (by simp [hs])
    rw [e, iPartK_add (V := famTen4 L Q) _ (fun l i j k =>
      (Key.contDiff_evalFun (n := 1) (h t (by simp)) _ _).differentiable one_ne_zero _)
      (fun l i j k => (contDiff_polyMap (n := 1) hL Q _).differentiable one_ne_zero _),
      iPartK_famTen4 Q L hL, List.map_cons, List.sum_cons]

theorem iPartV_famVec (κ s Q : ℝ) :
    ∀ L : List (ℤ × Key), RowsXFree L →
      iPartV A X p g w z κ s (famVec L Q) = (L.map fun t => (t.1 / Q : ℝ) *
        iPartV A X p g w z κ s (fun y l => t.2.evalFun CertData.base (fun _ => l) y)).sum
  | [], _ => by
    rw [show famVec [] Q = fun _ _ => 0 from rfl, iPartV_zero]; rfl
  | t :: L, h => by
    have e : famVec (t :: L) Q = fun y l => (t.1 / Q : ℝ) *
        t.2.evalFun CertData.base (fun _ => l) y + famVec L Q y l := by
      funext y l; simp [famVec, polyMap]
    have hL : RowsXFree L := fun s hs => h s (by simp [hs])
    rw [e, iPartV_add (V := famVec L Q) _ _ _ (fun l =>
      (Key.contDiff_evalFun (n := 1) (h t (by simp)) _ _).differentiable one_ne_zero _)
      (fun l => (contDiff_polyMap (n := 1) hL Q _).differentiable one_ne_zero _),
      iPartV_famVec κ s Q L hL, List.map_cons, List.sum_cons]

end OnePhaseDimension.Certificate
