# StochasticPDE

A rigorous formalization of stochastic partial differential equations (SPDEs), stochastic calculus, and Martin Hairer's theory of regularity structures in Lean 4 using Mathlib.

## Overview

This project provides machine-checked proofs for core results in stochastic analysis, from foundational stochastic calculus (Brownian motion, Ito integration, Ito formula) through to the theory of regularity structures and singular SPDEs. The formalization emphasizes mathematical rigor: no axiom smuggling, no placeholder definitions, and proper definitions throughout; remaining `sorry`s are tracked explicitly outside critical proof paths.

**~52,000 lines of Lean 4** across **99 files**.

## Main Components

### Ito Calculus (`ItoCalculus/`)

Self-contained module (37+ files, depends only on Mathlib) providing a complete formalization of Ito calculus including a **fully proven Ito formula (0 sorrys on the critical path)** and a **Kolmogorov-Chentsov theorem** for continuous modifications. All definitions have been audited for soundness — no axiom smuggling, no axioms, and all derivable properties (`stoch_integral_adapted`, `stoch_integral_measurable`, `stoch_integral_sq_integrable`) are proved as theorems rather than assumed as structure fields.

| Module | Description |
|--------|-------------|
| `ItoCalculus/Basic.lean` | Filtrations, adapted processes, martingales, local martingales, stopping times |
| `ItoCalculus/BrownianMotion.lean` | Wiener process, cylindrical Wiener process, Q-Wiener process, scaling/reflection |
| `ItoCalculus/StochasticIntegration.lean` | Ito integral (simple + L^2 limit), Ito formula, SDEs, Stratonovich integral |
| `ItoCalculus/Probability/` | Gaussian distributions, conditional expectation helpers, L^2 Pythagoras, independence |
| `ItoCalculus/ItoFormulaProof.lean` | Complete Ito formula proof (0 sorrys) |
| `ItoCalculus/ItoProcessCore.lean` | Core/regularity split for Ito processes with compatibility adapters |
| `ItoCalculus/ItoFormulaCoreBridge.lean` | Ito formula bridge theorems for `ItoProcessCore` with split regularity bundles |
| `ItoCalculus/KolmogorovChentsov/` | Kolmogorov-Chentsov theorem: Hölder continuous modifications (0 sorrys) |
| `ItoCalculus/AdaptedLimit.lean` | Measurability of L^2 limits under usual conditions |
| `ItoCalculus/RemainderIntegrability.lean` | Ito remainder integrability derived from boundedness (0 sorrys) |

### Key Proven Theorems

- **Ito formula**: `f(t, X_t) = f(0, X_0) + int_0^t [∂_t f + ∂_x f · μ + ½ ∂²_x f · σ²] ds + M_t` (**fully proven, 0 sorrys**)
- **Ito remainder martingale (derived hypotheses)**: `ito_formula_martingale_of_bounds` derives remainder integrability from boundedness + `X_0 ∈ L²`
- **Ito isometry**: `E[(int H dW)^2] = E[int H^2 ds]` (simple processes + L^2 extension)
- **Bilinear Ito isometry**: `E[(int H1 dW)(int H2 dW)] = E[int H1*H2 ds]`
- **Ito integral is a martingale** (set-integral characterization)
- **Ito integral linearity** in L^2
- **BM quadratic variation**: `[W]_t = t` (L^2 convergence of discrete approximations)
- **Weighted QV convergence** for adapted bounded processes
- **Ito process discrete QV L^2 convergence**
- **Core QV endpoint bounds**: split-core adapters with no legacy theorem-body delegation
- **Ito error decomposition** (telescope + Taylor identity for Ito formula)
- **Kolmogorov-Chentsov theorem**: processes with `E[|X_t - X_s|^p] ≤ M|t-s|^q` (q>1) have Hölder continuous modifications
- **Stochastic integral continuous modification** via KC (p=4, q=2)
- **Ito remainder integrability**: derived from boundedness, not assumed
- **BM scaling**: `c^{-1/2} W_{ct}` is a Brownian motion
- **BM reflection**: `-W` is a Brownian motion
- **Process L^2 increment bounds** for Ito processes

### Regularity Structures

| Module | Description |
|--------|-------------|
| `RegularityStructures/Trees/` | Multi-indices, tree symbols, homogeneity, formal sums (fully proven) |
| `RegularityStructures/Models/` | Admissible models (fully proven), canonical models |
| `RegularityStructures/Reconstruction.lean` | Reconstruction theorem (existence proven, uniqueness in progress) |
| `RegularityStructures/BPHZ.lean` | BPHZ renormalization framework |
| `RegularityStructures/FixedPoint.lean` | Fixed-point formulation for singular SPDEs |

### SPDEs and Applications

| Module | Description |
|--------|-------------|
| `SPDE.lean` | Abstract SPDE framework: mild/strong solutions, semigroup theory, well-posedness |
| `Examples/Phi4.lean` | The dynamic Phi^4 model (stochastic quantization of scalar field theory) |
| `Examples/KPZ.lean` | The KPZ equation |
| `Examples/YangMills2D.lean` | 2D stochastic Yang-Mills (Langevin dynamics for Yang-Mills measure) |
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

### Nonstandard Analysis Approach (`Nonstandard/`)

Anderson's (1976) construction of Brownian motion via hyperfinite random walks, formalized in Lean 4. Brownian motion is literally the standard part of a hyperfinite random walk: B(t) = st(W_{⌊tN⌋}/√N).

| Module | Description |
|--------|-------------|
| `Foundation/` | Hypernatural numbers, hyperfinite sums, internal sets, ℵ₁-saturation, arithmetic helpers (0 sorrys) |
| `Anderson/` | Local CLT, S-continuity a.s., maximal inequality, Anderson's theorem, Ito correspondence |
| `LoebMeasure/` | Loeb measure construction, σ-additivity via saturation, Wiener measure, path continuity (0 sorrys) |
| `HyperfiniteRandomWalk.lean` | Hyperfinite walk, quadratic variation = time exactly (0 sorrys) |
| `HyperfiniteStochasticIntegral.lean` | Hyperfinite Ito integral, Ito isometry exactly (0 sorrys) |

**Key proven results**: S-continuity a.s. (Loeb-almost-all paths continuous), local CLT (binomial → Gaussian), cylinder set probability convergence (general n, with continuous bounded test functions), wienerNestedIntegral properties (nonneg, ≤1, continuous), quadratic variation identity, SDE existence/uniqueness via Euler-Maruyama. **3 sorrys** remain on Anderson critical path (Riemann sum convergence helper, hT₁ coordinate alignment, uniform convergence). **7 additional sorrys** for Itô correspondence and explicit solutions (not on critical path).

### Proof Infrastructure

The `ItoCalculus/` module includes 25+ fully proven infrastructure files for the Ito formula proof chain:

- Common refinement and partition machinery
- Simple process integral definitions and linearity
- Set integral helpers and cross-term vanishing
- L^2 limit infrastructure
- Ito integral properties (isometry, martingale)
- Taylor remainder bounds
- Quadratic variation convergence
- Quartic moment bounds (L^4 estimates)
- Ito formula decomposition and error analysis
- Conditional isometry infrastructure
- Weighted QV L^2 bounds
- Gronwall lemma for SDEs

## Building

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/) (v4.27.0-rc1)
- [elan](https://github.com/leanprover/elan) (Lean version manager)

### Build

```bash
# Clone the repository
git clone https://github.com/YourUsername/StochasticPDE.git
cd StochasticPDE

# Fetch Mathlib cache (recommended, avoids rebuilding Mathlib from source)
lake exe cache get

# Build the project
lake build StochasticPDE
```

The first build fetches and compiles Mathlib dependencies, which may take significant time. Subsequent builds are incremental.

## Project Status

This is an active research project. The codebase contains `sorry` placeholders for results that are work in progress:

- **~108 total sorrys** across all files
- **0 sorrys** on the Ito formula critical path — **fully proven**
- **37+ files** in self-contained `ItoCalculus/` module (depends only on Mathlib)
- All definitions audited for soundness (no axioms, no axiom smuggling, zero computational results in structure fields)
- `stoch_integral_adapted`, `stoch_integral_measurable`, `stoch_integral_sq_integrable` all derived as theorems from L^2 limit + a.e. convergence + usual conditions
- `ItoProcessCore`/`ItoProcessRegularity` split is in place with core QV endpoint bounds and QV/helper/isometry/remainder-integrability adapters migrated to direct or regularity-first core proof bodies; `ito_formula_core` and `ito_formula_martingale_core` are now proved directly in the core bridge layer rather than one-line delegation to legacy theorem bodies, local reconstruction wrappers are normalized to `ItoProcessRegularity.ofSplit` + `toItoProcess`, redundant compatibility bundles (`ItoFormulaAssumptions`, `ItoProcessCoefficientJointMeasurability`) have been removed, redundant split-bundle parameters have been stripped from key QV helper lemmas, and the remaining local L4/measurability/single-increment QV helpers now run through regularity-first signatures

## Near-Term Roadmap

- Continue reducing assumption-heavy legacy `ItoProcess` adapter hypotheses while preserving theorem usability and statement compatibility
- Reduce assumption-heavy legacy `ItoProcess` entry points while keeping `ito_formula` and `ito_formula_martingale` statement-compatible
- Keep the Ito formula path sorry-free during migration and validate with full `lake build`

See [TODO.md](TODO.md) for detailed status and the sorry dependency chain.

## References

- Hairer, M. "A theory of regularity structures." *Inventiones Mathematicae* (2014)
- Da Prato, G. and Zabczyk, J. *Stochastic Equations in Infinite Dimensions*
- Karatzas, I. and Shreve, S. *Brownian Motion and Stochastic Calculus*
- Chandra, Chevyrev, Hairer, Shen. "Langevin dynamic for the 2D Yang-Mills measure"
- E, Khanin, Mazel, Sinai. "Invariant measures for Burgers equation with stochastic forcing." *Annals of Mathematics* (2000)

## License

Apache 2.0 - see [LICENSE](LICENSE).
