/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/

import StochasticPDE.ItoCalculus
import StochasticPDE.RegularityStructures
import StochasticPDE.SPDE
import StochasticPDE.Examples
import StochasticPDE.EKMS

/-!
# Stochastic Partial Differential Equations

This module provides a rigorous formalization of stochastic PDEs (SPDEs)
and Martin Hairer's theory of regularity structures in Lean 4 using Mathlib.

## Overview

Stochastic PDEs are PDEs driven by random noise, typically space-time white noise.
Many physically important SPDEs are "singular" - the nonlinearities are not
classically defined due to the roughness of the solution.

Martin Hairer's theory of regularity structures (Fields Medal 2014) provides
a systematic framework for making sense of these singular SPDEs.

## Main Files

* `Basic.lean` - Filtrations, adapted processes, martingales
* `BrownianMotion.lean` - Wiener process, cylindrical Wiener process
* `StochasticIntegration.lean` - Itô integral, Itô formula, SDEs
* `RegularityStructures.lean` - Regularity structures, models, reconstruction
* `SPDE.lean` - Abstract SPDEs, solutions, well-posedness
* `Examples/Phi4.lean` - The Φ⁴ model
* `Examples/YangMills2D.lean` - 2D Yang-Mills theory
* `Examples/Burgers.lean` - The stochastic Burgers equation
* `EKMS/` - EKMS theory of invariant measures for Burgers equation

## Key Concepts

### Regularity Structures

A regularity structure is a triple (A, T, G) where:
- A is an index set (homogeneities)
- T = ⊕_{α ∈ A} T_α is a graded vector space
- G is a structure group acting on T

### Models

A model (Π, Γ) provides:
- Π_x : T → S'(ℝ^d) - reconstruction at each point
- Γ_{xy} : T → T - translation between points

### The Reconstruction Theorem

The reconstruction operator R maps modelled distributions
to actual distributions, recovering classical solutions.

## Physical Applications

### The Φ⁴ Model

The dynamic Φ⁴ model: ∂_t φ = Δφ - φ³ + ξ

This is the stochastic quantization of scalar field theory.
In d = 2, 3 it requires renormalization to be well-defined.

### 2D Yang-Mills Theory

The stochastic Yang-Mills equation: ∂_t A = -d*_A F_A + ξ

This defines Langevin dynamics for the Yang-Mills measure,
a key object in gauge theory and QFT.

### EKMS Theory for Burgers Equation

The E-Khanin-Mazel-Sinai theory establishes the existence and uniqueness
of invariant measures for the randomly forced inviscid Burgers equation:

  ∂_t u + ∂_x(u²/2) = f(x, t)

Key results formalized:
- One-sided minimizers and their uniqueness (Theorem 1.1)
- Two-sided minimizers and the main shock (Theorems 5.1, 5.2)
- The unique invariant measure via "one force, one solution" (Theorem 4.2)
- Hyperbolicity and Pesin theory (Theorem 1.4)

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014)
* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
* Chandra, Chevyrev, Hairer, Shen, "Langevin dynamic for the 2D Yang-Mills measure"
* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus"
* E, Khanin, Mazel, Sinai, "Invariant measures for Burgers equation with
  stochastic forcing" (Annals of Mathematics 2000)

-/

-- All definitions are accessible via their fully qualified names
-- e.g., SPDE.Filtration, SPDE.BrownianMotion, SPDE.RegularityStructure, etc.
