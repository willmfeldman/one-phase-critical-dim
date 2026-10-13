/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import OnePhaseDimension.Statements.Headline
public import OnePhaseDimension.Statements.Cone
public import OnePhaseDimension.Statements.Certificate
public import OnePhaseDimension.Statements.CertificateGen
public import OnePhaseDimension.Statements.Stability
public import OnePhaseDimension.Statements.Exclusion
public import OnePhaseDimension.Sanity.Textbook.Defs
public import OnePhaseDimension.Sanity.Textbook.Encoding
public import OnePhaseDimension.Sanity.Textbook.Dilation
public import OnePhaseDimension.Sanity.Textbook.ZeroExtension
public import OnePhaseDimension.Sanity.Textbook.H10Ball
public import OnePhaseDimension.Sanity.Textbook.Equivalence
public import OnePhaseDimension.Registry.Regularity
public import OnePhaseDimension.Registry.Blowup
public import OnePhaseDimension.Registry.Chart
public import OnePhaseDimension.Certificate.Graph
public import OnePhaseDimension.Certificate.Eval
public import OnePhaseDimension.Certificate.Ops
public import OnePhaseDimension.Certificate.Projection
public import OnePhaseDimension.Certificate.Derivation
public import OnePhaseDimension.Certificate.DerivationSound
public import OnePhaseDimension.Certificate.Tangency
public import OnePhaseDimension.Certificate.Matching
public import OnePhaseDimension.Certificate.Polynomials
public import OnePhaseDimension.Certificate.Kernel
public import OnePhaseDimension.Certificate.Data.TableII.Spike
public import OnePhaseDimension.Certificate.Spike.Expand
public import OnePhaseDimension.Certificate.Data.Types
public import OnePhaseDimension.Certificate.Data.TableI
public import OnePhaseDimension.Certificate.Data.TableII
public import OnePhaseDimension.Certificate.Data.TableChecks
public import OnePhaseDimension.Certificate.Collect.InteriorPoly
public import OnePhaseDimension.Certificate.Collect.InteriorFamF
public import OnePhaseDimension.Certificate.Collect.InteriorFamU
public import OnePhaseDimension.Certificate.Collect.InteriorFamK
public import OnePhaseDimension.Certificate.Collect.InteriorFamM
public import OnePhaseDimension.Certificate.Collect.InteriorFamP
public import OnePhaseDimension.Certificate.Collect.InteriorTotal
public import OnePhaseDimension.Certificate.Data.RemainderA
public import OnePhaseDimension.Certificate.Data.RemainderB
public import OnePhaseDimension.Certificate.Data.Remainder
public import OnePhaseDimension.Certificate.Collect.Gram
public import OnePhaseDimension.Certificate.Collect.Gram.Block00
public import OnePhaseDimension.Certificate.Collect.Gram.Block01
public import OnePhaseDimension.Certificate.Collect.Gram.Block02
public import OnePhaseDimension.Certificate.Collect.Gram.Block03
public import OnePhaseDimension.Certificate.Collect.Gram.Block04
public import OnePhaseDimension.Certificate.Collect.Gram.Block05
public import OnePhaseDimension.Certificate.Collect.Gram.Block06
public import OnePhaseDimension.Certificate.Collect.Gram.Block07
public import OnePhaseDimension.Certificate.Collect.Gram.Block08
public import OnePhaseDimension.Certificate.Collect.Gram.Block09
public import OnePhaseDimension.Certificate.Collect.Gram.Block10
public import OnePhaseDimension.Certificate.Collect.Gram.Block11
public import OnePhaseDimension.Certificate.Collect.Gram.Block12
public import OnePhaseDimension.Certificate.Collect.Gram.Block13
public import OnePhaseDimension.Certificate.Collect.Gram.Block14
public import OnePhaseDimension.Certificate.Collect.Gram.Block15
public import OnePhaseDimension.Certificate.Collect.Gram.Block16
public import OnePhaseDimension.Certificate.Collect.Gram.Block17
public import OnePhaseDimension.Certificate.Collect.Gram.Block18
public import OnePhaseDimension.Certificate.Collect.KeyTypes
public import OnePhaseDimension.Certificate.Collect.Remainder
public import OnePhaseDimension.Certificate.Collect.Bounds
public import OnePhaseDimension.Certificate.Interior
public import OnePhaseDimension.Certificate.Boundary.Poly4
public import OnePhaseDimension.Certificate.Boundary.DiagEval
public import OnePhaseDimension.Certificate.Boundary.Kernel
public import OnePhaseDimension.Certificate.Boundary.DiagBound
public import OnePhaseDimension.Certificate.Boundary.Reduce
public import OnePhaseDimension.Certificate.Boundary
public import OnePhaseDimension.Certificate.Collect.Sound
public import OnePhaseDimension.Certificate.Collect.GramPSD
public import OnePhaseDimension.Certificate.Collect.GramSound
public import OnePhaseDimension.Certificate.Collect.GammaNonneg
public import OnePhaseDimension.Certificate.Collect.InteriorSound
public import OnePhaseDimension.Certificate.Collect.InteriorRows
public import OnePhaseDimension.Certificate.Collect.RoundingA1
public import OnePhaseDimension.Certificate.Collect.RoundingA2
public import OnePhaseDimension.Certificate.Collect.RoundingB1
public import OnePhaseDimension.Certificate.Collect.RoundingB2
public import OnePhaseDimension.Certificate.Collect.Rounding
public import OnePhaseDimension.Certificate.InteriorSplit
public import OnePhaseDimension.Certificate.InteriorBridge
public import OnePhaseDimension.Certificate.Main
public import OnePhaseDimension.Certificate.ToGen
public import OnePhaseDimension.Certificate.GenBridge
public import OnePhaseDimension.Certificate.Bounds.TensorBounds
public import OnePhaseDimension.Certificate.Bounds.Contraction
public import OnePhaseDimension.Certificate.Bounds.GraphShapes
public import OnePhaseDimension.Certificate.Bounds.GraphBound
public import OnePhaseDimension.Certificate.Bounds.GraphBoundChecks
public import OnePhaseDimension.Geometry.Symmetry
public import OnePhaseDimension.Geometry.Euler
public import OnePhaseDimension.Geometry.JetNorm
public import OnePhaseDimension.Geometry.Jets
public import OnePhaseDimension.Geometry.JetBochner
public import OnePhaseDimension.Geometry.BoundaryJets
public import OnePhaseDimension.Geometry.BoundaryData
public import OnePhaseDimension.Vendor.TauCeti.HaarToSphere
public import OnePhaseDimension.Geometry.Rotation
public import OnePhaseDimension.Geometry.Transport
public import OnePhaseDimension.Geometry.FrameChange
public import OnePhaseDimension.Geometry.Homogeneous
public import OnePhaseDimension.Geometry.Polar
public import OnePhaseDimension.Stability.FluxFunctional
public import OnePhaseDimension.Stability.Hadamard
public import OnePhaseDimension.Stability.Gluing
public import OnePhaseDimension.Stability.HadamardField
public import OnePhaseDimension.Stability.Competitor
public import OnePhaseDimension.Flux.Algebra
public import OnePhaseDimension.Flux.Fields
public import OnePhaseDimension.Flux.Generator
public import OnePhaseDimension.Flux.Interior
public import OnePhaseDimension.Stability.SuperlevelCalculus
public import OnePhaseDimension.Stability.SecondVariation
public import OnePhaseDimension.Vendor.TauCeti.Analysis.Calculus.TaylorIntegral
public import OnePhaseDimension.Vendor.TauCeti.Analysis.Calculus.DerivativeTest
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.NormPow
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.LocalExtr
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.MaximumPrinciple
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.BarrierMaximizer
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.StrongMaximumPrinciple
public import OnePhaseDimension.Geometry.Hopf
public import OnePhaseDimension.Geometry.GradientBound
public import OnePhaseDimension.Geometry.GradientBoundSuspension
public import OnePhaseDimension.Stability.Hardy
public import OnePhaseDimension.Stability.ConeScaling
public import OnePhaseDimension.Stability.Spherical
public import OnePhaseDimension.Flux.Parity
public import OnePhaseDimension.Flux.Boundary
public import OnePhaseDimension.Flux.Bounds
public import OnePhaseDimension.Geometry.SphereGreen
public import OnePhaseDimension.Cutoff.WeightedBochner
public import OnePhaseDimension.Geometry.Suspension
public import OnePhaseDimension.Cutoff.SuspendedMeasure
public import OnePhaseDimension.Cutoff.SuspendedCutoff
public import OnePhaseDimension.Reduction.Homogeneity
public import OnePhaseDimension.Reduction.Bridges
public import OnePhaseDimension.Reduction.HalfSpace
public import OnePhaseDimension.Reduction.Regular
public import OnePhaseDimension.Reduction.Component
public import OnePhaseDimension.Reduction.Interface
public import OnePhaseDimension.Reduction.Isometry
public import OnePhaseDimension.Reduction.OneDim
public import OnePhaseDimension.LowDim.DimTwo
public import OnePhaseDimension.LowDim.DimThree
public import OnePhaseDimension.LowDim.DimFour
public import OnePhaseDimension.LowDim.CertificateThree.Boundary
public import OnePhaseDimension.LowDim.CertificateThree.Coeffs
public import OnePhaseDimension.LowDim.CertificateThree.Explicit
public import OnePhaseDimension.LowDim.CertificateThree.Interior
public import OnePhaseDimension.LowDim.CertificateThree.Rotation
public import OnePhaseDimension.LowDim.CertificateTwo
public import OnePhaseDimension.LowDim.SOS.Assembly
public import OnePhaseDimension.LowDim.SOS.Data.Blocks0
public import OnePhaseDimension.LowDim.SOS.Data.Blocks1
public import OnePhaseDimension.LowDim.SOS.Data.Blocks2
public import OnePhaseDimension.LowDim.SOS.Data.Blocks3
public import OnePhaseDimension.LowDim.SOS.Data.Mult0
public import OnePhaseDimension.LowDim.SOS.Data.QForm
public import OnePhaseDimension.LowDim.SOS.Data.Residual
public import OnePhaseDimension.LowDim.SOS.Data.Scale
public import OnePhaseDimension.LowDim.SOS.Gram
public import OnePhaseDimension.LowDim.SOS.Identity
public import OnePhaseDimension.LowDim.SOS.InteriorCheck
public import OnePhaseDimension.LowDim.SOS.Poly
public import OnePhaseDimension.LowDim.SOS.Reify
public import OnePhaseDimension.Reduction.Translation
public import OnePhaseDimension.Reduction.Product
public import OnePhaseDimension.Reduction.Slice
public import OnePhaseDimension.Reduction.SuspensionMinimality
public import OnePhaseDimension.Reduction.FactorMinimality
public import OnePhaseDimension.Reduction.DomainVariationDensity
public import OnePhaseDimension.Reduction.DomainVariationFlow
public import OnePhaseDimension.Reduction.DomainVariation
public import OnePhaseDimension.Reduction.Variational
public import OnePhaseDimension.Reduction.BlowupHomogeneity
public import OnePhaseDimension.Reduction.Lattice
public import OnePhaseDimension.Reduction.BlowupCompactness
public import OnePhaseDimension.Cutoff.Cutoffs
public import OnePhaseDimension.Cutoff.Comparison
public import OnePhaseDimension.Cutoff.Original
public import OnePhaseDimension.Cutoff.Suspended
public import OnePhaseDimension.Cutoff.Exclusion
public import OnePhaseDimension.Main
public import OnePhaseDimension.Certificate.Collect.Gram.Block04GramRef04Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block04GramRef04Part1
public import OnePhaseDimension.Certificate.Collect.Gram.Block08GramRef08Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block08GramRef08Part1
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C0
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C13
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C21
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C30
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C41
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C58
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C6
public import OnePhaseDimension.Certificate.Collect.Gram.Block11GramRef11Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block11GramRef11Part1
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C0
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C15
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C24
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C35
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C51
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C7
public import OnePhaseDimension.Certificate.Collect.Gram.Block12GramRef12Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block12GramRef12Part1
public import OnePhaseDimension.Certificate.Collect.Gram.Block13C0
public import OnePhaseDimension.Certificate.Collect.Gram.Block13C25
public import OnePhaseDimension.Certificate.Collect.Gram.Block15GramRef15Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block15GramRef15Part1
public import OnePhaseDimension.Certificate.Collect.Gram.Block16GramRef16Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block16GramRef16Part1
public import OnePhaseDimension.Certificate.Data.TableII.Boundary
public import OnePhaseDimension.Certificate.Data.TableII.Rank012
public import OnePhaseDimension.Certificate.Data.TableII.Rank3A
public import OnePhaseDimension.Certificate.Data.TableII.Rank3B
public import OnePhaseDimension.Certificate.Spike.ExpandHook

/-!
# Flatness of one-homogeneous one-phase minimizers in dimensions at most six

Root module: imports every module of the library. The kernel regression checks of the
certificate engine (`OnePhaseDimension.Certificate.Spike.*`, built by
`lake build OnePhaseDimensionChecks`) form a separate library and are not imported here.

## Main statements

* `OnePhaseDimension.headline`: for `1 ≤ d ≤ 6`, every nonnegative, nonzero, one-homogeneous
  global minimizer of the one-phase Bernoulli energy in `ℝᵈ` is flat (`HeadlineStatement`).
* `OnePhaseDimension.flat_of_oneHomogeneous_of_le_six`: the same, with explicit hypotheses.
* `OnePhaseDimension.exclusion`: there is no working cone.
* `OnePhaseDimension.Textbook.isLocalEnergyMinimizer_univ_one_iff_textbookMin`: the minimizer
  class used here coincides with the textbook class of Alt and Caffarelli.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
-/
