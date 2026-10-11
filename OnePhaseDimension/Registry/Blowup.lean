/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import OnePhaseDimension.Reduction.BlowupCompactness
public import OnePhaseDimension.Reduction.BlowupHomogeneity

/-!
# Blowups of minimizers

For a continuous nonnegative global minimizer of the one-phase energy and a free boundary point
`x₀`, the rescalings `u_{x₀,r}(y) = u(x₀ + r y)/r` have locally uniform subsequential limits along
every sequence `r_j → 0`; each limit is a nonzero, nonnegative, continuous global minimizer
vanishing at the origin, and every blowup limit is one-homogeneous.

The first statement is proved here: compactness comes from the Lipschitz bound, minimality of the
limit from the one-sided limit theorems for downward and upward minimizers together with the
lattice inequality `J(max u v) + J(min u v) ≤ J(u) + J(v)`, and nondegeneracy from the
Alt–Caffarelli density estimate. The 2026-09-24 version of the preprint cites strong `H¹`
convergence of the rescalings (Velichkov 2023, Proposition 6.2); we use the one-sided route.

The second statement is also proved here. A minimizer is stationary under domain variations, hence
a variational solution in the sense of Kriventsov–Weiss on every ball, and blowup limits of
variational solutions are one-homogeneous by the Weiss monotonicity formula. The 2026-09-24
version cites the monotonicity formula for minimizers (Velichkov 2023, Proposition 9.12).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer (2023), Proposition 4.1, Proposition 6.2, Proposition 9.12.
* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), 545–591;
  arXiv:2306.10131.
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999).
-/

open Filter Topology

@[expose] public section

namespace OnePhaseDimension.Registry

open EllipticBernoulli

/-- Compactness and nondegeneracy of blowups: along a subsequence of any `r_j → 0⁺`, the
rescalings converge locally uniformly to a continuous, nonnegative, nonzero global minimizer `U₀`
with `U₀ 0 = 0` (Velichkov 2023, Proposition 4.1 and Proposition 6.2). -/
theorem exists_blowup_limit {d : ℕ} (hd : 2 ≤ d) {u : E d → ℝ} (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u Set.univ) {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hr₀ : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U₀ : E d → ℝ,
      TendstoLocallyUniformly (fun j ↦ blowup u x₀ (r (φ j))) U₀ atTop ∧
      Continuous U₀ ∧ (∀ y, 0 ≤ U₀ y) ∧ IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) U₀ ∧
      (∃ y, 0 < U₀ y) ∧ U₀ 0 = 0 :=
  exists_blowup_limit_proof hd hc hnn hmin hx₀ hr hr₀

/-- Every blowup limit at a free boundary point is one-homogeneous (Weiss 1999; Velichkov 2023,
Proposition 9.12). -/
theorem blowup_limit_oneHomogeneous {d : ℕ} (hd : 2 ≤ d) {u : E d → ℝ} (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u Set.univ) {U₀ : E d → ℝ}
    (hU₀ : IsBlowupLimit u x₀ U₀) :
    ∀ r : ℝ, 0 < r → ∀ y, U₀ (r • y) = r * U₀ y :=
  blowup_limit_oneHomogeneous_proof hd hc hnn hmin hx₀ hU₀

end OnePhaseDimension.Registry
