/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.EKMS.Basic
import StochasticPDE.EKMS.OneSidedMinimizers
import StochasticPDE.EKMS.TwoSidedMinimizers
import StochasticPDE.EKMS.InvariantMeasure
import StochasticPDE.EKMS.Hyperbolicity

/-!
# EKMS Theory for Burgers Equation

This module provides a comprehensive formalization of the E-Khanin-Mazel-Sinai (EKMS)
theory of invariant measures for the randomly forced Burgers equation.

## Overview

The EKMS theory establishes the existence and uniqueness of invariant measures
for the stochastic Burgers equation in the inviscid limit:

  ∂_t u + ∂_x(u²/2) = f(x, t)

where f(x, t) = Σ_k F_k(x) Ḃ_k(t) is a random force with independent Wiener processes.

## Main Files

* `Basic` - Probability space, forcing, action functional, variational principle
* `OneSidedMinimizers` - One-sided minimizers and their uniqueness (Theorem 1.1)
* `TwoSidedMinimizers` - Two-sided minimizers, main shock (Theorems 5.1, 5.2)
* `InvariantMeasure` - Construction and uniqueness (Theorems 1.2, 1.3, 4.2)
* `Hyperbolicity` - Pesin theory and unstable manifolds (Theorem 1.4)

## Key Results Formalized

### One-Sided Minimizers (Section 3)
* **Theorem 1.1**: With probability 1, except for countably many x, there exists
  a unique one-sided minimizer ξ with ξ(0) = x.
* **Lemma 3.1**: Uniform velocity bounds for minimizers.
* **Lemma 3.4**: Two distinct minimizers cannot intersect (consequence of randomness).

### Two-Sided Minimizers and Main Shock (Section 5)
* **Theorem 5.1**: Under non-degeneracy (A1), the two-sided minimizer exists a.s.
* **Theorem 5.2**: The two-sided minimizer and main shock are unique a.s.
* **Lemma 5.2**: Basic collision lemma - positive probability of merging.

### Invariant Measures (Section 4)
* **Theorem 1.2**: μ = δ_{Φ(ω)} × P is the unique invariant measure with projection P.
* **Theorem 1.3**: κ = ∫ μ is the unique stationary distribution.
* **Theorem 4.2**: Uniqueness via "one force, one solution" principle.

### Hyperbolicity (Section 6)
* **Theorem 1.4**: The graph of Φ₀(ω) lies in the unstable manifold of y_ω.
* The two-sided minimizer is a hyperbolic trajectory with Lyapunov exponents.

## Connection to Other Files

This formalization connects to:
* `SPDE.Basic` - Filtrations, martingales, stopping times
* `SPDE.SPDE` - Abstract SPDE framework
* `SPDE.Examples.Burgers` - Burgers equation basics
* `SPDE.Examples.KPZ` - KPZ equation (related via Cole-Hopf)

## References

* E, Khanin, Mazel, Sinai, "Invariant measures for Burgers equation with
  stochastic forcing", Annals of Mathematics 151 (2000), 877-960.
* Bec, Khanin, "Burgers turbulence", Physics Reports 447 (2007), 1-66.
* Hairer, "Ergodicity of stochastic differential equations driven by
  fractional Brownian motion", Annals of Probability 33 (2005).

## TODO

- [ ] Complete proof of velocity bound (Lemma 3.1)
- [ ] Complete proof of no-intersection lemma (Lemma 3.4)
- [ ] Complete proof of collision lemma (Lemma 5.2)
- [ ] Complete proof of uniqueness (Theorem 4.2)
- [ ] Connect to viscous Burgers (Section 8)
- [ ] Formalize tail probability estimates [EKMS]
-/

namespace SPDE.EKMS

-- Re-export key definitions and theorems

-- From Basic
export EKMSProbabilitySpace (Ω measurableSpace P isProbability)
export EKMSForcing (potentials B potential potentialDerivative)
export ActionFunctional (action decomposition)
export VariationalPrinciple (A minimizer solution)

-- From OneSidedMinimizers
export OneSidedMinimizer (curve velocity endpoint endpointVelocity)
export VelocityBound (constants bound_holds)

-- From TwoSidedMinimizers
export TwoSidedMinimizer (curve velocity position)
export MainShock (position continuous)
export CollisionLemma (nondegen p₀ p₀_pos)

-- From InvariantMeasure
export StationaryDistribution (measure markov_invariant)
export InvariantMeasureOnProduct (measure projection_P invariant)

-- From Hyperbolicity
export LyapunovExponents (lambda_plus lambda_minus)
export StableManifold (manifold)
export UnstableManifold (manifold)

end SPDE.EKMS
