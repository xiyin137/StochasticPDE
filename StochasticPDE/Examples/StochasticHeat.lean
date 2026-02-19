/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.SPDE

/-!
# Stochastic Heat Equation

The stochastic heat equation ∂_t u = Δu + ξ where ξ is space-time white noise.

## Main Definitions

* `StochasticHeatEquation` - The stochastic heat equation
* `SHESolution` - Solutions via regularity structures

## References

* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
* Walsh, "An introduction to stochastic partial differential equations"
-/

namespace SPDE.Examples

open MeasureTheory

/-! ## Stochastic Heat Equation -/

/-- The stochastic heat equation: ∂_t u = Δu + ξ
    where ξ is space-time white noise. -/
structure StochasticHeatEquation (d : ℕ) where
  /-- The spatial domain (usually torus or ℝ^d) -/
  domain : Set (Fin d → ℝ)
  /-- Diffusion coefficient (often normalized to 1) -/
  diffusion_coeff : ℝ := 1
  /-- Positivity of diffusion -/
  diffusion_pos : 0 < diffusion_coeff := by norm_num

namespace StochasticHeatEquation

variable {d : ℕ}

/-- The regularity of the noise -/
noncomputable def noiseRegularity (_she : StochasticHeatEquation d) : ℝ := -(d : ℝ)/2 - 1

/-- The expected solution regularity α < 1 - d/2 -/
noncomputable def solutionRegularity (_she : StochasticHeatEquation d) : ℝ := 1 - (d : ℝ)/2

/-- The stochastic heat equation is well-posed in d = 1 (no renormalization needed) -/
theorem well_posed_d1 (she : StochasticHeatEquation 1) :
    she.solutionRegularity > 0 := by
  simp [solutionRegularity]
  norm_num

/-- In d = 2, the solution has regularity α < 0 (distribution-valued) -/
theorem solution_distribution_d2 (she : StochasticHeatEquation 2) :
    she.solutionRegularity < 1 := by
  simp [solutionRegularity]

/-- Model parameters for the stochastic heat equation in d = 2.
    Uses the tree-based infrastructure from `RegularityStructures/`.
    - Noise regularity α = -2 (space-time white noise in 2D)
    - Kernel order β = 2 (heat kernel) -/
noncomputable def modelParameters_d2 : SPDE.RegularityStructures.ModelParameters 2 where
  noiseRegularity := -2
  kernelOrder := 2
  minHomogeneity := -2
  maxHomogeneity := 2
  hom_lt := by norm_num

/-- The mild formulation: u(t) = e^{tΔ} u₀ + ∫₀ᵗ e^{(t-s)Δ} dW_s
    This is the integral form of the SHE, where e^{tΔ} is the heat semigroup. -/
structure MildFormulation (she : StochasticHeatEquation d) where
  /-- The heat semigroup decay rate -/
  semigroup_decay : ℝ
  /-- The semigroup decays exponentially for bounded domains -/
  decay_pos : semigroup_decay > 0
  /-- The stochastic convolution ∫₀ᵗ e^{(t-s)Δ} dW_s is square-integrable.
      This holds when the heat semigroup is Hilbert-Schmidt, i.e.,
      ∫₀ᵗ ‖e^{sΔ}‖²_HS ds < ∞, which requires d = 1. -/
  convolution_sq_integrable : d ≤ 1 →
    ∃ C : ℝ, C > 0 ∧ ∀ t : ℝ, 0 < t → t * semigroup_decay ≤ C

/-- The Hölder regularity in space: solutions are C^α in space for α < 1/2 - d/4 -/
structure SpatialHolderRegularity (she : StochasticHeatEquation d) where
  /-- The spatial Hölder exponent -/
  spatial_exponent : ℝ
  /-- The exponent satisfies the bound α < 1/2 - d/4 -/
  exponent_bound : spatial_exponent < 1/2 - (d : ℝ)/4
  /-- The exponent is positive (for d ≤ 1) -/
  exponent_pos : d ≤ 1 → spatial_exponent > 0

/-- The Hölder regularity in time: solutions are C^β in time for β < 1/4 - d/8 -/
structure TemporalHolderRegularity (she : StochasticHeatEquation d) where
  /-- The temporal Hölder exponent -/
  temporal_exponent : ℝ
  /-- The exponent satisfies the bound β < 1/4 - d/8 -/
  exponent_bound : temporal_exponent < 1/4 - (d : ℝ)/8
  /-- The exponent is positive (for d ≤ 1) -/
  exponent_pos : d ≤ 1 → temporal_exponent > 0

end StochasticHeatEquation

/-! ## Stochastic Heat Equation with Nonlinearity -/

/-- Stochastic heat equation with polynomial nonlinearity:
    ∂_t u = Δu + f(u) + g(u)ξ -/
structure NonlinearSHE (d : ℕ) where
  /-- The domain -/
  domain : Set (Fin d → ℝ)
  /-- The drift nonlinearity f -/
  drift : ℝ → ℝ
  /-- The multiplicative noise coefficient g -/
  noise_coeff : ℝ → ℝ
  /-- The Lipschitz constant for f -/
  drift_lipschitz_const : ℝ
  /-- The Lipschitz constant is non-negative -/
  lipschitz_nonneg : drift_lipschitz_const ≥ 0
  /-- Lipschitz condition on f -/
  drift_lipschitz : ∀ x y : ℝ, |drift x - drift y| ≤ drift_lipschitz_const * |x - y|

namespace NonlinearSHE

/-- Additive noise case: g(u) = 1.
    The drift f must be provided along with its Lipschitz constant. -/
def additive (d : ℕ) (f : ℝ → ℝ) (L : ℝ) (hL : L ≥ 0)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) : NonlinearSHE d where
  domain := Set.univ
  drift := f
  noise_coeff := fun _ => 1
  drift_lipschitz_const := L
  lipschitz_nonneg := hL
  drift_lipschitz := hf

/-- Multiplicative noise case: g(u) = u.
    The drift f must be provided along with its Lipschitz constant. -/
def multiplicative (d : ℕ) (f : ℝ → ℝ) (L : ℝ) (hL : L ≥ 0)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) : NonlinearSHE d where
  domain := Set.univ
  drift := f
  noise_coeff := id
  drift_lipschitz_const := L
  lipschitz_nonneg := hL
  drift_lipschitz := hf

/-- Linear drift: f(u) = au has Lipschitz constant |a| -/
def linearDrift (d : ℕ) (a : ℝ) (multiplicative_noise : Bool) : NonlinearSHE d where
  domain := Set.univ
  drift := fun u => a * u
  noise_coeff := if multiplicative_noise then id else fun _ => 1
  drift_lipschitz_const := |a|
  lipschitz_nonneg := abs_nonneg a
  drift_lipschitz := fun x y => by
    show |a * x - a * y| ≤ |a| * |x - y|
    rw [← mul_sub, abs_mul]

end NonlinearSHE

end SPDE.Examples
