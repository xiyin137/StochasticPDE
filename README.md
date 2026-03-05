# StochasticPDE

A rigorous formalization of stochastic partial differential equations (SPDEs), stochastic calculus, and Martin Hairer's theory of regularity structures in Lean 4 using Mathlib.

## Overview

This project provides machine-checked proofs for core results in stochastic analysis, from foundational stochastic calculus (Brownian motion, Itô integration, Itô formula) through to the theory of regularity structures and singular SPDEs. The formalization emphasizes mathematical rigor: no axiom smuggling, no placeholder definitions, and proper definitions throughout; remaining `sorry`s are tracked explicitly outside critical proof paths.

## Main Components

### Itô Calculus (`ItoCalculus/`)

Self-contained module (37+ files, ~26k lines, depends only on Mathlib) providing a complete formalization of Itô calculus including a **fully proven Itô formula (0 sorrys, 0 axioms)** and a **Kolmogorov-Chentsov theorem** for continuous modifications.

The core Itô formula proof chain (33 files, ~24k lines) has been extracted into a standalone repository with a comprehensive README covering file structure, definitions, and proof architecture: **[`stochasticpde-itocalculus`](_split_repos/stochasticpde-itocalculus/)**.

The monorepo additionally includes SDE structures, Stratonovich integrals, semimartingale definitions, cylindrical/Q-Wiener processes, Ornstein-Uhlenbeck processes, Brownian bridges, and Grönwall-type infrastructure beyond the Itô formula proof chain.

**Main theorem** — `ito_formula_core`: For f C² in x and differentiable in t, applied to an Itô process X_t = X_0 + ∫μ ds + ∫σ dW with bounded coefficients, the remainder M_t = f(t,X_t) − f(0,X_0) − ∫[∂_t f + ∂_x f·μ + ½∂²_x f·σ²] ds is a **martingale**.

### Regularity Structures

| Module | Description |
|--------|-------------|
| `RegularityStructures/Trees/` | Multi-indices, tree symbols, homogeneity, formal sums |
| `RegularityStructures/Models/` | Admissible models, canonical models |
| `RegularityStructures/Reconstruction.lean` | Reconstruction theorem |
| `RegularityStructures/BPHZ.lean` | BPHZ renormalization framework |
| `RegularityStructures/FixedPoint.lean` | Fixed-point formulation for singular SPDEs |

### SPDEs and Applications

| Module | Description |
|--------|-------------|
| `SPDE.lean` | Abstract SPDE framework: mild/strong solutions, semigroup theory |
| `Examples/Phi4.lean` | Dynamic Φ⁴ model (stochastic quantization) |
| `Examples/KPZ.lean` | KPZ equation |
| `Examples/YangMills2D.lean` | 2D stochastic Yang-Mills |
| `Examples/Burgers.lean` | Stochastic Burgers equation |
| `Examples/StochasticHeat.lean` | Stochastic heat equation |

### EKMS Theory

| Module | Description |
|--------|-------------|
| `EKMS/Basic.lean` | Randomly forced Burgers equation, action minimizers |
| `EKMS/OneSidedMinimizers.lean` | One-sided minimizers and uniqueness |
| `EKMS/TwoSidedMinimizers.lean` | Two-sided minimizers and the main shock |
| `EKMS/InvariantMeasure.lean` | Unique invariant measure ("one force, one solution") |
| `EKMS/Hyperbolicity.lean` | Hyperbolicity and Pesin theory |

### Split Repositories

| Repository | Description |
|-----------|-------------|
| [`stochasticpde-itocalculus`](_split_repos/stochasticpde-itocalculus/) | Streamlined Itô formula proof (33 files, ~24k lines, 0 sorrys, 0 axioms) |
| [`stochasticpde-nonstandard`](https://github.com/xiyin137/stochasticpde-nonstandard) | Nonstandard analysis development |

## Building

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/) (v4.27.0-rc1)
- [elan](https://github.com/leanprover/elan) (Lean version manager)

### Build

```bash
git clone https://github.com/YourUsername/StochasticPDE.git
cd StochasticPDE

# Fetch Mathlib cache
lake exe cache get

# Build specific modules (recommended over bare `lake build`)
lake build StochasticPDE.ItoCalculus.ItoFormulaCoreBridge
```

## Project Status

Active research project. The Itô formula critical path is **fully proven (0 sorrys, 0 axioms)**. Remaining `sorry`s are tracked in [TODO.md](TODO.md) and are outside the critical proof chain.

See [TODO.md](TODO.md) for detailed status.

## References

- Hairer, M. "A theory of regularity structures." *Inventiones Mathematicae* (2014)
- Da Prato, G. and Zabczyk, J. *Stochastic Equations in Infinite Dimensions*
- Karatzas, I. and Shreve, S. *Brownian Motion and Stochastic Calculus*
- Chandra, Chevyrev, Hairer, Shen. "Langevin dynamic for the 2D Yang-Mills measure"
- E, Khanin, Mazel, Sinai. "Invariant measures for Burgers equation with stochastic forcing." *Annals of Mathematics* (2000)

## License

Apache 2.0 - see [LICENSE](LICENSE).
