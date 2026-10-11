# Third-party code

This project is released under the Apache License 2.0 (`LICENSE`). The files under
`OnePhaseDimension/Vendor/TauCeti/` are ported from TauCeti, an Apache-2.0 Lean project. Each of
those files keeps the upstream copyright line and authors in its header, and its module docstring
has a `## Provenance` section that names the upstream file and commit and says what was changed
(Apache-2.0 §4(b)). The upstream project ships no `NOTICE` file.

| Upstream | Commit | License | Upstream copyright | Files here (under `OnePhaseDimension/Vendor/TauCeti/`) |
|---|---|---|---|---|
| TauCeti, https://github.com/TauCetiProject/TauCeti | `b940fb6c25af27408a6a52481e681bf70515db70` | Apache-2.0 | © 2026 The Tau Ceti contributors | `HaarToSphere.lean` (from `TauCeti/MeasureTheory/Constructions/HaarToSphere.lean`); `Analysis/Calculus/DerivativeTest.lean`, `Analysis/Calculus/TaylorIntegral.lean`, `Analysis/InnerProductSpace/NormPow.lean`, and `Analysis/InnerProductSpace/Laplacian/{Basic, LocalExtr, MaximumPrinciple, WeakMaximumPrinciple, DriftMaximumPrinciple, BarrierMaximizer, LowerOrderMaximumPrinciple, HopfLemma, StrongMaximumPrinciple}.lean` (each from the file of the same path under `TauCeti/`) |

Everything else is original to this project. Mathlib, elliptic-bernoulli-foundations
(https://github.com/willmfeldman/elliptic-bernoulli-foundations, v0.4.0), bernoulli-rectifiability
(https://github.com/willmfeldman/bernoulli-rectifiability, v0.4.2) and
bernoulli-perron-variational (https://github.com/willmfeldman/bernoulli-perron-variational,
v0.2.1), with their own dependencies, are used as Lake dependencies (ordinary libraries; no code
copied from them). All are Apache-2.0.

The mathematics follows the preprint OpenAI, *The critical dimension for one-phase Bernoulli
minimizers* (September 24, 2026, https://github.com/openai/math). No code from that repository
(Lean or otherwise) is imported, copied, ported, or used here.
