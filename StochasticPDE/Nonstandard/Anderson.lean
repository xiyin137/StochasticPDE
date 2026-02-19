/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/

import StochasticPDE.Nonstandard.Anderson.RandomWalkMoments
import StochasticPDE.Nonstandard.Anderson.MaximalInequality
import StochasticPDE.Nonstandard.Anderson.SContinuity
import StochasticPDE.Nonstandard.Anderson.SContinuityAS
import StochasticPDE.Nonstandard.Anderson.LocalCLT
import StochasticPDE.Nonstandard.Anderson.AndersonTheorem
import StochasticPDE.Nonstandard.Anderson.ItoCorrespondence
import StochasticPDE.Nonstandard.Anderson.HyperfiniteSDE
import StochasticPDE.Nonstandard.Anderson.SDESolution
import StochasticPDE.Nonstandard.Anderson.ExplicitSolutions

/-!
# Anderson's Theorem and Stochastic Calculus

This module provides the complete infrastructure for Anderson's theorem and
nonstandard stochastic calculus, establishing the connection between hyperfinite
random walks and classical Brownian motion/SDEs.

## Contents

### Probability Infrastructure
* `RandomWalkMoments` - Second moment E[S_k²] = k and Chebyshev bounds
* `MaximalInequality` - P(max |S_i| > M) ≤ (k+1)²/M²
* `SContinuity` - Increment variance and modulus of continuity bounds
* `SContinuityAS` - S-continuity almost surely via Borel-Cantelli
* `LocalCLT` - Local central limit theorem infrastructure

### Anderson's Theorem
* `AndersonTheorem` - Main theorem: st_* μ_L = μ_W (Loeb pushforward = Wiener measure)

### Itô Calculus
* `ItoCorrespondence` - st(Σ Hₖ·ΔWₖ) = ∫ H dW (hyperfinite → Itô integral)

### Stochastic Differential Equations
* `HyperfiniteSDE` - Hyperfinite SDEs as difference equations
* `SDESolution` - Standard part gives classical SDE solutions
* `ExplicitSolutions` - Explicit formulas for GBM and OU processes (requires Itô's lemma)

## Main Results

### Fully Proven (No Sorries)
* `sum_partialSumFin_sq` - Σ S_k² = k · 2^n
* `chebyshev_count`, `chebyshev_prob` - Chebyshev bound
* `maximal_count`, `maximal_prob` - Maximal inequality
* `sum_windowIncrement_sq` - E[(S_{k+h} - S_k)²] = h
* `modulus_bound_prob` - P(max increment > M) ≤ numWindows·h/M²

### Infrastructure (With Sorries for Detailed Calculations)
* `violationProbGlobalThreshold_bound` - P(violation) ≤ 1/C² for Borel-Cantelli
* `levyModulus_implies_S_continuous` - Lévy modulus ⟹ S-continuity
* `local_clt_error_bound` - Binomial → Gaussian convergence
* `anderson_theorem` - st_* μ_L = μ_W
* `ito_correspondence` - st(hyperfinite integral) = Itô integral
* `standardPart_satisfies_sde` - Standard part solves classical SDE

## The Nonstandard Approach

The key insight is that stochastic calculus becomes elementary in the hyperfinite setting:

1. **Brownian motion**: B(t) = st(W_⌊t/dt⌋) where W is a hyperfinite random walk
2. **Itô integral**: ∫ H dW = st(Σ Hₖ·ΔWₖ) - a pathwise sum
3. **Itô's lemma**: Just Taylor series with Δ² = dt (not 0!)
4. **SDEs**: dX = a(X)dt + b(X)dW becomes X_{k+1} = X_k + a(X_k)dt + b(X_k)ΔW_k

## References

* Anderson, R. M. "A nonstandard representation for Brownian motion and Itô integration" (1976)
* Lindstrøm, T. "Hyperfinite stochastic integration" (1980s)
* Albeverio, S. et al. "Nonstandard Methods in Stochastic Analysis and Mathematical Physics"
* Lévy's modulus of continuity theorem
* Feller, W. "An Introduction to Probability Theory" (local CLT)
-/
