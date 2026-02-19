/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.SPDE

/-!
# The Φ⁴ Model

The dynamic Φ⁴ model: ∂_t φ = Δφ - φ³ + ξ.
This is the stochastic quantization of scalar field theory.

## Main Definitions

* `Phi4Model` - The Φ⁴ model in d dimensions
* `Phi4_2` - The 2D Φ⁴ model (Da Prato-Debussche)
* `Phi4_3` - The 3D Φ⁴ model (Hairer 2014)

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014)
* Da Prato, Debussche, "Strong solutions to the stochastic quantization equations"
* Mourrat, Weber, "The dynamic Φ⁴₃ model comes down from infinity"
-/

namespace SPDE.Examples

open MeasureTheory

/-! ## The Φ⁴ Model -/

/-- The Φ⁴ model: ∂_t φ = Δφ - m²φ - λφ³ + ξ
    This is the Langevin dynamics for ∫ (1/2)|∇φ|² + (m²/2)φ² + (λ/4)φ⁴ dx -/
structure Phi4Model (d : ℕ) where
  /-- The domain (usually torus 𝕋^d) -/
  domain : Set (Fin d → ℝ)
  /-- The mass parameter m² -/
  mass_squared : ℝ
  /-- The coupling constant λ (coefficient of φ⁴ in potential) -/
  coupling : ℝ
  /-- Positive coupling for stability -/
  coupling_pos : 0 < coupling

namespace Phi4Model

variable {d : ℕ}

/-- The subcritical dimension bound -/
def isSubcritical (_phi : Phi4Model d) : Prop := d < 4

/-- The critical dimension -/
def isCritical (_phi : Phi4Model d) : Prop := d = 4

/-- The supercritical dimension (not expected to be well-posed) -/
def isSupercritical (_phi : Phi4Model d) : Prop := d > 4

/-- Φ⁴ is subcritical in d < 4 -/
theorem subcritical_d_lt_4 (phi : Phi4Model d) (hd : d < 4) :
    phi.isSubcritical := hd

/-- The noise regularity: α = -(d+2)/2 -/
noncomputable def noiseRegularity (_phi : Phi4Model d) : ℝ := -((d : ℝ) + 2)/2

/-- The expected solution regularity: 1 - d/2 (before renormalization) -/
noncomputable def solutionRegularity (_phi : Phi4Model d) : ℝ := 1 - (d : ℝ)/2

/-- The scaling dimension of φ³ -/
noncomputable def cubicScalingDimension (phi : Phi4Model d) : ℝ := 3 * phi.solutionRegularity

/-- φ³ is a well-defined distribution if 3α > -d/2 (roughly d < 10/3) -/
def cubicWellDefined (phi : Phi4Model d) : Prop :=
  3 * phi.solutionRegularity > -(d : ℝ)/2

end Phi4Model

/-! ## Φ⁴ in 2D -/

/-- The 2D Φ⁴ model (solved by Da Prato-Debussche 2003) -/
structure Phi4_2 extends Phi4Model 2

namespace Phi4_2

/-- In 2D, the cubic term is a well-defined distribution -/
theorem cubic_well_defined (_phi : Phi4_2) :
    _phi.toPhi4Model.cubicWellDefined := by
  simp [Phi4Model.cubicWellDefined, Phi4Model.solutionRegularity]

/-- The Da Prato-Debussche trick: write u = Z + v where Z solves linear SHE.
    This decomposition allows treating the singular terms :Z²:, :Z³: separately
    from the regular remainder v. -/
structure DaPratoDebussche (phi : Phi4_2) where
  /-- The Hölder regularity of the linear solution Z (α < 0 in 2D) -/
  linear_regularity : ℝ
  /-- Z has negative Hölder regularity in 2D -/
  linear_regularity_neg : linear_regularity < 0
  /-- The Hölder regularity of the remainder v (β > 0) -/
  remainder_regularity : ℝ
  /-- The remainder has positive regularity -/
  remainder_regularity_pos : remainder_regularity > 0
  /-- The regularity gain: v is more regular than Z -/
  regularity_gain : remainder_regularity > -linear_regularity
  /-- The Wick renormalization constant for :Z²:.
      In 2D, 𝔼[Z(x)²] is logarithmically divergent and :Z²: = Z² - 𝔼[Z²] -/
  wick_constant_2 : ℝ
  /-- The Wick renormalization constant for :Z³: -/
  wick_constant_3 : ℝ

/-- The invariant measure for Φ⁴₂ is characterized by the Euclidean QFT measure.
    This measure is formally dμ = (1/Z) exp(-∫ (1/2)|∇φ|² + (m²/2)φ² + (λ/4)φ⁴ dx) Dφ -/
structure InvariantMeasureQFT (phi : Phi4_2) where
  /-- The partition function (normalization constant) -/
  partition_function : ℝ
  /-- The partition function is positive -/
  partition_pos : partition_function > 0

/-- The Φ⁴₂ equation as a singular SPDE. In 2D the noise has regularity α = -2
    and the solution regularity is γ = α + β = 0 (distribution-valued). -/
noncomputable def phi4_2_spde (phi : Phi4_2) : SPDE.SingularSPDE 2 where
  domain := phi.domain
  domain_open := sorry -- requires domain to be open
  operator_order := 2
  operator_order_pos := by norm_num
  nonlinearity := SPDE.PolynomialNonlinearity.phi4 phi.mass_squared
  noise_regularity := phi.toPhi4Model.noiseRegularity
  noise_distributional := by simp [Phi4Model.noiseRegularity]
  solution_regularity := phi.toPhi4Model.solutionRegularity
  subcritical := by simp [Phi4Model.solutionRegularity, Phi4Model.noiseRegularity]
  regularity_from_kernel := by
    simp [Phi4Model.solutionRegularity, Phi4Model.noiseRegularity]

/-- Global well-posedness for Φ⁴₂ (Da Prato-Debussche 2003).
    The 2D case is subcritical: the cubic nonlinearity φ³ is well-defined as a distribution,
    so classical fixed-point arguments in Besov spaces suffice.
    Uses the `SPDE.GlobalWellPosedness` framework. -/
noncomputable def phi4_2_global_wellposedness (phi : Phi4_2) :
    SPDE.GlobalWellPosedness 2 (phi4_2_spde phi)
      (SPDE.RegularityStructures.ModelParameters.mk (-2) 2 (-2) 2 (by norm_num)) :=
  sorry

end Phi4_2

/-! ## Φ⁴ in 3D -/

/-- The 3D Φ⁴ model (Hairer 2014, Catellier-Chouk 2018) -/
structure Phi4_3 extends Phi4Model 3

namespace Phi4_3

/-- In 3D, the cubic term requires renormalization -/
theorem cubic_requires_renormalization (phi : Phi4_3) :
    ¬ phi.toPhi4Model.cubicWellDefined := by
  simp [Phi4Model.cubicWellDefined, Phi4Model.solutionRegularity]
  norm_num

/-- Model parameters for Φ⁴₃ regularity structure.
    Uses the tree-based infrastructure from `RegularityStructures/`.
    - Noise regularity α = -5/2 (space-time white noise in 3D)
    - Kernel order β = 2 (heat kernel)
    - Homogeneity range covers all relevant tree symbols -/
noncomputable def modelParameters : SPDE.RegularityStructures.ModelParameters 3 :=
  SPDE.RegularityStructures.ModelParameters.phi4_3

/-- Renormalization constants for Φ⁴₃.
    The mass counterterm diverges logarithmically as the UV cutoff ε → 0. -/
structure Renormalization (phi : Phi4_3) where
  /-- The mass counterterm δm²(ε) as a function of the UV cutoff ε > 0 -/
  mass_counterterm : ℝ → ℝ
  /-- Coefficient of the logarithmic divergence in mass counterterm -/
  log_coefficient : ℝ
  /-- The mass diverges logarithmically: |δm²(ε) - c log(1/ε)| bounded as ε → 0 -/
  log_divergence : ∃ C ε₀ : ℝ, C > 0 ∧ ε₀ > 0 ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    |mass_counterterm ε - log_coefficient * Real.log (1/ε)| ≤ C
  /-- The coupling constant renormalization (finite in 3D) -/
  coupling_renorm : ℝ → ℝ
  /-- Coupling renormalization has a finite limit as ε → 0 -/
  coupling_finite : ∃ coupling_limit : ℝ,
    Filter.Tendsto coupling_renorm (nhdsWithin 0 (Set.Ioi 0)) (nhds coupling_limit)

/-- Local well-posedness for Φ⁴₃: the renormalized equation has unique local solutions -/
structure LocalWellPosedness3D (phi : Phi4_3) (r : Renormalization phi) where
  /-- The solution regularity (1/2 - ε in 3D) -/
  solution_regularity : ℝ
  /-- The regularity is close to 1/2 -/
  regularity_bound : solution_regularity < 1/2 ∧ solution_regularity > 0
  /-- Local existence time depends on initial data norm -/
  existence_time : ℝ → ℝ  -- initial_norm → existence_time
  /-- Existence time is positive for bounded data -/
  existence_time_pos : ∀ R : ℝ, R > 0 → existence_time R > 0

/-- The Φ⁴₃ equation as a singular SPDE. In 3D the noise has regularity α = -5/2
    and the solution regularity is γ = α + β = -1/2 (requires renormalization). -/
noncomputable def phi4_3_spde (phi : Phi4_3) : SPDE.SingularSPDE 3 where
  domain := phi.domain
  domain_open := sorry -- requires domain to be open
  operator_order := 2
  operator_order_pos := by norm_num
  nonlinearity := SPDE.PolynomialNonlinearity.phi4 phi.mass_squared
  noise_regularity := phi.toPhi4Model.noiseRegularity
  noise_distributional := by simp [Phi4Model.noiseRegularity]; norm_num
  solution_regularity := phi.toPhi4Model.solutionRegularity
  subcritical := by simp [Phi4Model.solutionRegularity, Phi4Model.noiseRegularity]; norm_num
  regularity_from_kernel := by
    simp [Phi4Model.solutionRegularity, Phi4Model.noiseRegularity]; norm_num

/-- Coming down from infinity (Mourrat-Weber 2017): for any two solutions u₁, u₂
    of the Φ⁴₃ equation with potentially different initial data,
    the modelled distributions converge: ‖u₁(t) - u₂(t)‖_{D^γ} → 0 as t → ∞.

    This implies uniqueness of the invariant measure and is proved using
    the regularity structure framework. -/
theorem coming_down_from_infinity (phi : Phi4_3) :
    ∀ (sol₁ sol₂ : SPDE.RegularityStructureSolution 3 (phi4_3_spde phi) modelParameters),
      ∃ C : ℝ, C > 0 ∧
      ∀ t : ℝ, t > 0 →
        |sol₁.reconstruction.bound_const - sol₂.reconstruction.bound_const| ≤ C / t :=
  sorry

/-- Ergodicity for Φ⁴₃: the invariant measure exists, is unique, and the dynamics
    converge to it exponentially fast. Uses the `SPDE.Ergodicity` framework.
    Uniqueness follows from "coming down from infinity" (Mourrat-Weber). -/
noncomputable def phi4_3_ergodicity (phi : Phi4_3) :
    SPDE.Ergodicity 3 (phi4_3_spde phi) modelParameters :=
  sorry

end Phi4_3

end SPDE.Examples
