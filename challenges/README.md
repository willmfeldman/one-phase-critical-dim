# Comparator challenges

This directory contains the release comparator workspace for `OnePhaseDimension`,
`challenges/headline`. It has no Lake project of its own: `Vocabulary`, `Challenge` and `Solution`
are libraries of the root `lakefile.toml` with `srcDir = "challenges/headline"`, not default
targets, so the challenge is built and checked from the repository root
(`lake build Vocabulary Challenge Solution`) with the root's toolchain, dependencies and options.
The workspace contains:

- `Vocabulary.lean`: a verbatim copy (after the copyright header) of the library file
  `OnePhaseDimension/Sanity/Textbook/Defs.lean`. It imports Mathlib only and defines the textbook
  class `TextbookMin u` of one-phase minimizers: on every ball `B`, `u ∈ H¹(B)` and
  `J(u; B) = ∫_B |∇u|² + 1_{u > 0} ≤ J(v; B)` for every `v ∈ H¹(B)` with `v - u ∈ H¹₀(B)`
  (H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144);
- `Challenge.lean`: the trusted statement surface. It starts with a block generated from
  `Vocabulary.lean` by `scripts/challenge-prep.py sync` (the vocabulary's Mathlib imports and its
  text, verbatim), has no other imports, and states the claims below the block with `sorry`;
- `Solution.lean`: imports the library only (not `Vocabulary`, which declares the same names) and
  proves the same statements under the same names;
- `config.json`: comparator module names, theorem names and permitted axioms
  (`propext`, `Quot.sound`, `Classical.choice`);
- `formalization.yaml`: the entry metadata of the challenge;
- `check.sh` and `tools/fingerprint.lean`: a local substitute for a Comparator run (see below).

The trusted surface of the challenge is Mathlib plus the restated vocabulary: the library's own
minimizer class `IsLocalEnergyMinimizer` does not appear in any challenge statement. After editing
`Vocabulary.lean` (always together with the library file), run
`python3 scripts/challenge-prep.py sync`; `python3 scripts/challenge-prep.py check` (run in CI)
fails if the generated block is out of date.

| Theorems | What it certifies |
|---|---|
| `OnePhaseDimension.Headline.challenge_flat_of_textbookMin` | The main theorem in textbook vocabulary: for `1 ≤ d ≤ 6`, a nonnegative, one-homogeneous, not a.e. vanishing `TextbookMin` function on `ℝᵈ` equals `max ⟪x, e⟫ 0` a.e. for a unit vector `e`. |
| six `OnePhaseDimension.Sanity.challenge_*` theorems | Checks of the definitions, not headline results: `TextbookMin` contains the half-space solutions in every dimension; it rejects a wrong slope, the two-sided cone, and `1 + ‖x‖²`; `0` and a translated half-space solution are minimizers that are not flat, so the hypotheses "nonzero" and "one-homogeneous" of the main theorem are needed. |

## Running

**Release gate (Linux).** `.github/workflows/release-comparator.yml` installs pinned revisions of
[Comparator](https://github.com/leanprover/comparator), lean4export and landrun
(`scripts/release-comparator.sh`), builds the trusted library and the trusted `Vocabulary` and
`Challenge` targets, runs Comparator on every `challenges/*/config.json`, and uploads an
attestation (commit, tree, toolchain, Mathlib revision, tool revisions, per-challenge results,
logs). A version tag or GitHub release is created only after this workflow passes on the exact
commit.

**Per commit (CI).** `scripts/check-challenges.sh` builds `Vocabulary` and `Solution` without
warnings, and `Challenge`, and checks that each solution theorem uses exactly the permitted
axioms. This shows that the files elaborate and the solutions are sorry-free; it does not compare
statements. `python3 scripts/challenge-prep.py check` checks the layout: module headers, the
generated vocabulary block, Lean core/Mathlib-only Challenge imports, and the Challenge size.

**Locally (any OS).** In a trusted checkout, after `lake build` at the root,
`challenges/<name>/check.sh` builds the three libraries, checks the solution axioms, checks that
`Vocabulary.lean` is a verbatim copy of the library file, and compares a structural fingerprint
(hashes of types, definition values and inductive shapes) of the challenge theorems and every
project constant they depend on, in the Challenge and in the Solution environment. This emulates
Comparator's statement check; it is not a substitute for it.

## Acceptance record

| Date | Commit | Check | Result |
|---|---|---|---|
| 2026-10-10 | release candidate | local `check.sh --strict`, macOS, Lean v4.35.0-rc3 | `headline` PASS (176 constants identical); `minimizer-sanity` PASS (178 constants identical); all solution axioms `propext`, `Classical.choice`, `Quot.sound` |
| 2026-10-10 | release candidate, `minimizer-sanity` folded into `headline`, vocabulary inlined | local `check.sh --strict`, macOS, Lean v4.35.0-rc3 | `headline` PASS (184 constants identical, seven theorems); all solution axioms `propext`, `Classical.choice`, `Quot.sound` |
| 2026-10-11 | `e6f310a` (v0.1.0) | release Comparator workflow (Linux), [run 38109472560](https://github.com/willmfeldman/one-phase-critical-dim/actions/runs/38109472560), Lean v4.35.0-rc3 | `headline` PASS (seven theorems); axiom check passed; attestation `comparator-attestation-v0.1.0.zip` on the [v0.1.0 release](https://github.com/willmfeldman/one-phase-critical-dim/releases/tag/v0.1.0) |
