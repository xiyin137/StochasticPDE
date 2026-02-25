/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/

-- Import the top-level results (these transitively pull in everything)
import StochasticPDE.ItoCalculus.ItoFormulaProof
import StochasticPDE.ItoCalculus.ItoProcessCore
import StochasticPDE.ItoCalculus.ItoFormulaCoreBridge
import StochasticPDE.ItoCalculus.StochasticIntegration
import StochasticPDE.ItoCalculus.IsometryTheorems

/-!
# Itô Calculus

Self-contained module providing a complete formalization of Itô calculus,
depending only on Mathlib.

## Main Results

* `ItoFormulaProof` — Complete proof of the Itô formula (0 sorrys)
* `StochasticIntegration` — Itô integral, isometry, SDEs
* `BrownianMotion` — Wiener process definition

## Structure

### Foundation
* `Basic` — Filtrations, adapted processes, martingales
* `BrownianMotion` — Wiener process, cylindrical Wiener process

### Probability Infrastructure
* `Probability.Basic` — Measure-theoretic probability helpers
* `Probability.IndependenceHelpers` — Independence bridge lemmas
* `Probability.Pythagoras` — L² Pythagorean theorem

### Simple Process Infrastructure
* `SimpleProcessDef` — Simple process definition and evaluation
* `SimpleProcessLinear` — Linearity of simple process integration
* `CommonRefinement` — Common refinement of partitions
* `MergedValueAtTime` — Value extraction at partition points
* `SetIntegralHelpers` — Set integral helper lemmas
* `SimpleIntegralMartingale` — Simple integral martingale property

### Itô Integral
* `L2LimitInfrastructure` — L² limit infrastructure
* `ItoIntegralProperties` — Itô integral properties
* `IsometryAt` — Isometry at partition level
* `IsometryTheorems` — Full isometry theorems
* `ConditionalIsometry` — Conditional isometry results
* `ItoProcessCore` — Core/regularity split for Itô processes + compatibility bridge
* `ItoFormulaCoreBridge` — Itô formula adapter theorem for `ItoProcessCore`
* `GronwallForSDE` — Gronwall-type lemma for SDEs
* `ProductL2Convergence` — Product L² convergence
* `IteratedProductConvergence` — Iterated product convergence

### Stochastic Integration
* `StochasticIntegration` — Itô integral, Itô isometry, SDEs

### Itô Formula
* `ItoFormulaInfrastructure` — Infrastructure for the Itô formula
* `ItoFormulaDecomposition` — Taylor decomposition B₁+2B₂+B₃
* `QuarticBound` — Quartic moment bounds
* `QuadraticVariation` — Quadratic variation convergence
* `TaylorRemainder` — Taylor remainder estimates
* `QVConvergence` — QV convergence theorems
* `WeightedQVBound` — Weighted quadratic variation L² bound
* `ItoFormulaProof` — Complete Itô formula proof

### Kolmogorov-Chentsov Theorem
* `KolmogorovChentsov.DyadicPartition` — Dyadic interval infrastructure
* `KolmogorovChentsov.MomentToTail` — Markov inequality for p-th moments
* `KolmogorovChentsov.DyadicIncrement` — Dyadic increment bounds + Borel-Cantelli
* `KolmogorovChentsov.ContinuousModification` — KC theorem

### Derived Properties
* `AdaptedLimit` — L² limits of adapted processes
* `SIContinuity` — Stochastic integral continuous modification
* `ProcessContinuity` — Itô process path continuity
* `RemainderIntegrability` — Itô remainder integrability
-/
