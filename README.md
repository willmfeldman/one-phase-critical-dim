# one-phase-critical-dim

A Lean 4 / Mathlib proof that, in dimensions at most six, every one-homogeneous global minimizer
of the one-phase Bernoulli energy is flat.

## Statement from the author

This is an autoformalization project with the vast majority of the work carried out by Claude Opus 5.5. 

The goal was to verify the [claimed result](https://github.com/openai/math/blob/main/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026.pdf) by OpenAI on the critical dimension for minimizers of the one-phase Bernoulli free boundary problem. The Lean formalization [published by OpenAI](https://github.com/openai/math/blob/main/lean/ComparatorChallenges/BernoulliNonflatInSeven.lean) only formalized the existence of a singular minimizing cone in $d=7$ (the result of De Silva and Jerison) and did not Lean verify the new claimed result.  The paper was successfully Lean formalized and AI agents reported no necessary significant deviation from the paper proof route. I hope that Lean verification of this AI-proved result can help human mathematicians in their decision whether to spend the time to read and understand the work and the new ideas there.

I have made an initial reading (October 2026) of the preprint by OpenAI. My current understanding is the following. The paper follows, at a high level, the same structure of previous techniques by Simons (for minimal surfaces) and by Caffarelli–Jerison–Kenig and Jerison–Savin. The idea is to look for a test perturbation that violates positivity of the second variation.  The test perturbation needs to be a subsolution of a certain PDE problem, determined by the hypothetical nonflat minimizer, set on the intersection of the sphere with the positivity cone. 

The new idea is a systematic approach to constructing such test perturbations as a function of the value, gradient, and Hessian matrix of the unknown candidate minimizer.  This function on the space of second-order jets needs to satisfy a certain differential inequality in order for the resulting test function to be a subsolution as desired. By looking in an appropriately large class of polynomials on the jet space this can be turned into a finite dimensional semi-definite programming problem. The paper of OpenAI searched for and found an approximate solution to this problem, rounded to rational coefficients which can be verified in exact arithmetic.  In this repo we have also implemented a similar strategy for the previously known $d=3$ (Caffarelli–Jerison–Kenig) and $d=4$ (Jerison–Savin) cases with new, much smaller, certificates.

Interestingly, even though this is a positive result, the new idea fits into a certain theme recently where current generation AI models are excellent at sophisticated and highly strategic approaches to locating difficult counterexamples.

I have also included two AI written notes. The [first](expository/note.pdf) is expository, with the key ideas of the paper presented in an order which is intended to be friendly to the reader. This went through a few rounds of AI revisions based on my ability to read and understand the logical structure. I will try to improve it more in the future. The other is on [literature](expository/literature-jet-calibrations.md) trying to explore the novelty of this kind of approach. The conclusion, essentially, is that each aspect of this idea has appeared before in some form but the combination seems to be new and it is a challenging and involved application of these ideas.

Comments, issues, or suggestions are welcome.

## Background

The one-phase Bernoulli problem minimizes

$$J(v; B) = \int_B |\nabla v|^2 + \mathbf 1_{\{v > 0\}}$$

over nonnegative functions with fixed boundary values. Regularity of the free boundary
$\partial\{u > 0\}$ comes down to one question: in which dimensions $d$ is every
one-homogeneous global minimizer (a *cone*) flat, that is, equal to $(x \cdot e)^+$? The
preprint
[*The critical dimension for one-phase Bernoulli minimizers*](https://github.com/openai/math)
(OpenAI, 2026-09-24) shows the answer is $d \le 6$. The answer has two halves:

1. **Flatness for $d \le 6$.** Every nonzero, nonnegative, one-homogeneous global minimizer in
   $\mathbb R^d$, $1 \le d \le 6$, is flat.
2. **A nonflat cone for $d = 7$.** There is a nonflat one-homogeneous global minimizer in
   $\mathbb R^7$, the axisymmetric cone of De Silva and Jerison.

Together they make seven the critical dimension.

## What the OpenAI repository formalizes

The [openai/math](https://github.com/openai/math) repository contains a Lean formalization,
[`lean/OAI/Analysis/BernoulliCone`](https://github.com/openai/math/tree/main/lean/OAI/Analysis/BernoulliCone),
of **half 2 only**:

```lean
theorem OAI.Bernoulli.nonflat_in_seven : ∃ u : Space 7 → ℝ,
    GlobalMinimizer u ∧ Nonzero u ∧ OneHomogeneous u ∧ ¬ Flat u
```

The proof writes the De Silva–Jerison cone down explicitly. It proves the cone is minimal by
upper and lower calibrations, which compare it with an arbitrary nonnegative Sobolev competitor
on any ball. The development is about 90 files and has no `sorry`. A
[Comparator](https://github.com/leanprover/comparator) challenge
(`lean/ComparatorChallenges/BernoulliNonflatInSeven`) fixes the statement and allows only the
standard axioms.

The scope note in that repository
([`lean/docs/367.md`](https://github.com/openai/math/blob/main/lean/docs/367.md)) says:

> The flatness classification in dimensions at most six and the resulting regularity and
> singular-set bounds are outside this selected statement.

So **half 1 is not formalized there.** Half 1 is the harder direction and the one that matters
for regularity.

*(Checked against openai/math commit `fd4aeeb`, 2026-10-07.)*

## What this repository adds

This repository formalizes **half 1**:

```lean
/-- For `1 ≤ d ≤ 6`, every nonnegative, nonzero, one-homogeneous global minimizer of the
one-phase Bernoulli energy in `ℝᵈ` is flat. -/
theorem OnePhaseDimension.headline : HeadlineStatement

theorem OnePhaseDimension.flat_of_oneHomogeneous_of_le_six {d : ℕ} (hd₁ : 1 ≤ d) (hd₆ : d ≤ 6)
    (u : E d → ℝ) (hnn : ∀ᵐ x ∂volume, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    (hhom : OneHomogeneousAE u) (hne : ¬ u =ᵐ[volume] 0) :
    ∃ e : E d, ‖e‖ = 1 ∧ ∀ᵐ x ∂volume, u x = max (inner ℝ x e) 0
```

(`OnePhaseDimension/Main.lean`; the statement is frozen in
`OnePhaseDimension/Statements/Headline.lean`.)

The proof follows the preprint's method. A universal certificate rules out two kinds of singular
minimizing cone in $\mathbb R^6$: a cone whose only singularity is the origin, and the product
$O \times \mathbb R$ of such a cone $O$ in $\mathbb R^5$ with a line. The code calls these
*working cones* (`WorkingCone` in `OnePhaseDimension/Statements/Cone.lean`), after the preprint's
"working domain" on the sphere. The proof differs from the preprint in two places.

- **Low dimensions are proved, not cited.** The preprint cites the classification for
  $d \le 4$ (Caffarelli–Jerison–Kenig; Jerison–Savin). Here $d = 1, 2$ are proved directly, and
  $d = 3, 4$ are proved by the same exclusion argument, using new universal certificates on
  $\mathbb R^2$ (checked by hand) and $\mathbb R^3$ (a sum-of-squares certificate checked by the
  Lean kernel).
- **Induction instead of a least dimension.** The preprint argues from a least dimension
  $d_* \in \{5, 6\}$ that carries a nonflat cone. Here flatness in dimension $d - 1$, together
  with the exclusion of these cones, gives flatness in dimension $d$ for $d \in \{5, 6\}$.

Each deviation from the preprint is explained in the module docstring of the affected file, in a
section "Differences from the source".

## Nothing is cited

The proof has no `sorry` and no extra axioms. `#print axioms OnePhaseDimension.headline` lists
only `propext`, `Classical.choice` and `Quot.sound`.

The preprint cites the classical regularity theory of one-phase minimizers. All of it is proved,
either here or in
[elliptic-bernoulli-foundations](https://github.com/willmfeldman/elliptic-bernoulli-foundations)
(EBF), [bernoulli-rectifiability](https://github.com/willmfeldman/bernoulli-rectifiability) (BR)
or [bernoulli-perron-variational](https://github.com/willmfeldman/bernoulli-perron-variational)
(BPV):

| Input | Classical reference | Where it is proved |
|---|---|---|
| Lipschitz representative, smooth and harmonic in $\{u > 0\}$ | Alt–Caffarelli 1981; Velichkov 2023, Thm 3.1 | EBF |
| Smooth chart at points with a flat blowup: $u = \max(F, 0)$ with $\lvert\nabla F\rvert = 1$ on $\{F = 0\}$ | Velichkov 2023, Thm 8.1; De Silva–Ferrari–Salsa 2019; Kinderlehrer–Nirenberg 1977 | EBF |
| Compactness of blowups, nondegeneracy | Velichkov 2023, Props 4.1, 6.2 | here, using EBF and BPV (stability of one-sided minimality under blowup) |
| One-homogeneity of blowups (Weiss monotonicity) | Weiss 1999 | BR (for variational solutions); here, that minimizers are variational solutions |
| Hopf lemma, maximum principles | — | ported from Tau Ceti |
| Classification for $d \le 4$ | Caffarelli–Jerison–Kenig 2004; Jerison–Savin 2015 | here, by the exclusion method |

## Relation to the OpenAI formalization

- **Independent.** No code from openai/math is imported, vendored, ported, or used as a proof
  source. The preprint is read only as mathematics (see `THIRD_PARTY_NOTICES.md`).
- **Different definitions.** The two projects state "global minimizer" separately. Here it is
  `IsLocalEnergyMinimizer` from elliptic-bernoulli-foundations; there it is
  `OAI.Bernoulli.GlobalMinimizer`. Both compare $J$ on balls against nonnegative $H^1$
  competitors with the same trace. No machine-checked bridge between the two definitions exists
  yet, so the two theorems are not yet one formal statement of "seven is the critical
  dimension".
- **Still open in both.** The consequences for free-boundary regularity (the bound on the
  dimension of the singular set) are formalized in neither repository.

## Building

```sh
lake exe cache get
lake build
```

- Toolchain: `leanprover/lean4:v4.35.0-rc3`; Mathlib `v4.35.0-rc3`; requires
  [elliptic-bernoulli-foundations](https://github.com/willmfeldman/elliptic-bernoulli-foundations)
  v0.4.0, [bernoulli-rectifiability](https://github.com/willmfeldman/bernoulli-rectifiability)
  v0.4.2 and
  [bernoulli-perron-variational](https://github.com/willmfeldman/bernoulli-perron-variational)
  v0.2.1 (pinned in `lakefile.toml` and `lake-manifest.json`).
- `lake build OnePhaseDimensionChecks` builds the kernel regression checks of the certificate
  engine, a separate library (several GB of memory per module).
- `sorry` audit: `python3 scripts/check_integrity.py` (no `sorry`, `admit`, `axiom` or
  `native_decide` outside comments and strings).
- CI (`.github/workflows/ci.yml`) runs the same build with `--wfail`, the integrity scan, the
  manifest and exact-axiom checks of `formalization.yaml`, and the challenge workspaces.

## Layout

| Path | Contents |
|---|---|
| `OnePhaseDimension.lean` | Root module; imports every library module |
| `OnePhaseDimension/Statements/` | Frozen statements: headline, cones, certificate, stability, exclusion, sanity |
| `OnePhaseDimension/Certificate/` | The universal certificate and its bounds |
| `OnePhaseDimension/Flux/`, `Stability/` | Flux fields, second variation, spherical stability |
| `OnePhaseDimension/Cutoff/` | Cutoffs and the exclusion of the singular cones |
| `OnePhaseDimension/Geometry/` | Jets, rotations, polar coordinates, Hopf lemma, gradient bound |
| `OnePhaseDimension/Reduction/` | Minimizer bridges, blowups, dimension reduction |
| `OnePhaseDimension/LowDim/` | Dimensions one to four |
| `OnePhaseDimension/Registry/` | Interfaces to the regularity results proved in EBF |
| `OnePhaseDimension/Sanity/` | The textbook minimizer class, its equivalence with the library's, sanity checks |
| `OnePhaseDimension/Vendor/TauCeti/` | Files ported from Tau Ceti, with attribution (`THIRD_PARTY_NOTICES.md`) |
| `challenges/` | Comparator challenge workspaces (`challenges/README.md`) |
| `formalization.yaml` | Theorem manifest: targets, expected axioms, challenges |
| `expository/` | AI-written notes: an expository account of the proof (`note.pdf`) and a literature survey of the method (`literature-jet-calibrations.md`) |
| `scripts/cert_search/` | The search and exact checker that produced the certificates for $d = 3, 4$ (provenance only; Lean checks the certificates itself) |

## Formalization metadata

`formalization.yaml` records the headline targets with their Lean names, the expected axioms
(exactly `propext`, `Classical.choice`, `Quot.sound`), and the comparator challenge. The
challenge `challenges/headline` states its theorems over Mathlib alone: its `Challenge.lean`
restates, verbatim, `OnePhaseDimension/Sanity/Textbook/Defs.lean`, which defines the textbook
minimizer class `TextbookMin` of Alt and Caffarelli. It contains

- the main theorem, with `TextbookMin` in place of the library's minimizer class;
- six checks of the definitions, not headline results: the textbook class contains the half-space
  solutions, rejects wrong encodings, and shows that the hypotheses of the main theorem are
  needed.

The release Comparator workflow checks the challenge against its solution.

## Credits

The theorem and the universal-certificate method are from OpenAI, *The critical dimension for
one-phase Bernoulli minimizers*, preprint, September 24, 2026, in the
[openai/math](https://github.com/openai/math/tree/main/preprints/The-critical-dimension-for-one-phase-Bernoulli-minimizers-September-24-2026) repository. Other principal sources:

- H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
- G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999).

Several proofs were written based on the following sources, which might not be the original location of the ideas:

- B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer (2023), DOI 10.1007/978-3-031-13238-4.
- D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131.
- F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.

The files under `OnePhaseDimension/Vendor/TauCeti/` are ported from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) (Apache-2.0); each keeps the upstream
header and has a `## Provenance` section, and `THIRD_PARTY_NOTICES.md` lists them.

The Lean proofs were written by AI coding agents (Claude Opus 5.5, by Anthropic) under the
author's direction. The author reviewed the statement of the main theorem and the textbook
definitions used by the comparator challenge (`OnePhaseDimension/Sanity/Textbook/Defs.lean`); no
other Lean code was reviewed by hand. The author also reviewed the expository notes in `expository/`
to some degree. Correctness rests on Lean's kernel check, together with the comparator challenge in
`challenges/headline`.

## License

Apache 2.0; see `LICENSE`.

## Citation

See `CITATION.cff`.
