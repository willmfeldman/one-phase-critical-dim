/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Interior
public import OnePhaseDimension.Certificate.Boundary

/-!
# The universal certificate

The coefficient maps of the first table satisfy all the properties of the certificate:
smoothness, orthogonal equivariance (with `f` invariant), evenness of `U` and `K` in `p`,
`P = 0` at `g = 0`, the interior inequality and `f ≥ ε*`, and the boundary inequality.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Data

/-- **The boundary inequality** for the coefficient maps of the first table. -/
theorem tableCoeffs_boundary (A : Ten2) (p : Ten1) (lam : ℝ) (hA : IsSTF2 A) (hA1 : sq2 A = 1)
    (hp : sq1 p = 1) (hev : ∀ i, ∑ j, A i j * p j = lam * p i) (hlam : lam < 0) :
    δStar ≤ tableCoeffs.boundaryExpr A p lam :=
  boundary_inequality A p lam hA hA1 hp hev hlam

/-- The coefficient maps of the first table satisfy the certificate properties. -/
theorem tableCoeffs_holds : CertificateHolds tableCoeffs := by
  have hf := rowsOfRank_famEntries_f
  have hu := rowsOfRank_famEntries_U
  have hk := rowsOfRank_famEntries_K
  have hm := rowsOfRank_famEntries_M
  have hp := rowsOfRank_famEntries_P
  obtain ⟨sf, sU, sK, sM, sP⟩ := rowsCoeffs_smooth (Q := certQ) hf.plain hu.plain hk.plain
    hm.plain hp.plain
  exact
    { smooth_f := sf
      smooth_U := sU
      smooth_K := sK
      smooth_M := sM
      smooth_P := sP
      equiv_f := fun O hO A p g => (rowsCoeffs_equiv hf hu hk hm hp O hO A p g).1
      equiv_U := fun O hO A p g => (rowsCoeffs_equiv hf hu hk hm hp O hO A p g).2.1
      equiv_K := fun O hO A p g => (rowsCoeffs_equiv hf hu hk hm hp O hO A p g).2.2.1
      equiv_M := fun O hO A p g => (rowsCoeffs_equiv hf hu hk hm hp O hO A p g).2.2.2.1
      equiv_P := fun O hO A p g => (rowsCoeffs_equiv hf hu hk hm hp O hO A p g).2.2.2.2
      even_U := rowsCoeffs_even_U hu.plain even_pCount_famEntries_U
      even_K := rowsCoeffs_even_K hk.plain even_pCount_famEntries_K
      P_g_zero := rowsCoeffs_P_g_zero gPow_ne_zero_famEntries_P
      interior := fun _ _ _ _ _ _ _ hA hA1 hX hgp => interior_inequality hA hA1 hX hgp
      f_ge := fun _ _ _ hA hA1 hgp => certF_ge_eps hA hA1 hgp
      boundary := fun A p lam hA hA1 hp hev hlam =>
        tableCoeffs_boundary A p lam hA hA1 hp hev hlam }

/-- **The universal certificate** (Proposition "Universal inequalities"). -/
theorem certificateStatement_holds : CertificateStatement := ⟨tableCoeffs, tableCoeffs_holds⟩

end OnePhaseDimension.Certificate
