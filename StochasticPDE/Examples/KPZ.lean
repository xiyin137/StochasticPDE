/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.SPDE

/-!
# The KPZ Equation

The Kardar-Parisi-Zhang equation: ∂_t h = Δh + (∇h)² + ξ

## Main Definitions

* `KPZEquation` - The KPZ equation
* `KPZ_RegularityStructure` - The regularity structure for KPZ
* `ColeHopfTransform` - The Cole-Hopf transform to multiplicative SHE

## References

* Hairer, "Solving the KPZ equation" (Annals 2013)
* Corwin, "The Kardar-Parisi-Zhang equation and universality class"
-/

namespace SPDE.Examples

open MeasureTheory

/-! ## The KPZ Equation -/

/-- The KPZ equation: ∂_t h = ν Δh + λ(∇h)² + √D ξ
    Fundamental equation for interface growth. -/
structure KPZEquation where
  /-- Diffusion coefficient ν > 0 -/
  nu : ℝ
  nu_pos : 0 < nu
  /-- Nonlinearity coefficient λ -/
  lambda : ℝ
  /-- Noise strength √D -/
  noise_strength : ℝ
  noise_pos : 0 < noise_strength

namespace KPZEquation

/-- The standard KPZ equation with ν = 1/2, λ = 1, D = 1 -/
noncomputable def standard : KPZEquation where
  nu := 1/2
  nu_pos := by norm_num
  lambda := 1
  noise_strength := 1
  noise_pos := by norm_num

/-- The noise regularity: α = -3/2 in 1D -/
noncomputable def noiseRegularity (_kpz : KPZEquation) : ℝ := -3/2

/-- The solution regularity: α = 1/2 - ε -/
noncomputable def solutionRegularity (_kpz : KPZEquation) : ℝ := 1/2

/-- The critical nonlinearity (∇h)² has regularity 2α - 1 = 0 -/
theorem critical_nonlinearity (_kpz : KPZEquation) :
    2 * _kpz.solutionRegularity - 1 = 0 := by
  simp [solutionRegularity]

end KPZEquation

/-! ## Cole-Hopf Transform -/

/-- The Cole-Hopf transform relates KPZ to multiplicative SHE.
    If h solves KPZ, then Z = exp(λh/(2ν)) solves
    ∂_t Z = ν ΔZ + (λ√D/(2ν)) Z ξ

    This is fundamental because:
    1. Multiplicative SHE is easier to analyze (linear in Z)
    2. Positivity: Z > 0 implies h is well-defined
    3. Connects KPZ to directed polymer partition functions -/
structure ColeHopfTransform (kpz : KPZEquation) where
  /-- The transformation coefficient λ/(2ν) -/
  coeff : ℝ := kpz.lambda / (2 * kpz.nu)
  /-- The coefficient is well-defined (ν > 0) -/
  coeff_well_defined : kpz.nu ≠ 0 := ne_of_gt kpz.nu_pos
  /-- The noise coefficient in MSHE: λ√D/(2ν) -/
  noise_coeff : ℝ := kpz.lambda * kpz.noise_strength / (2 * kpz.nu)

/-- The inverse Cole-Hopf transform: h = (2ν/λ) log Z.
    This requires Z > 0, which holds for solutions of MSHE with positive initial data. -/
structure InverseColeHopf (kpz : KPZEquation) where
  /-- The inverse coefficient 2ν/λ -/
  inv_coeff : ℝ
  /-- The coefficient satisfies the relation -/
  inv_relation : kpz.lambda ≠ 0 → inv_coeff = 2 * kpz.nu / kpz.lambda

/-! ## Regularity Structure for KPZ -/

/-- Model parameters for the KPZ regularity structure (Hairer 2013).
    Uses the tree-based infrastructure from `RegularityStructures/`.
    - Noise regularity α = -3/2 (space-time white noise in 1D)
    - Kernel order β = 2 (heat kernel)
    - Homogeneity range covers all relevant tree symbols -/
noncomputable def KPZ_ModelParameters : SPDE.RegularityStructures.ModelParameters 1 :=
  SPDE.RegularityStructures.ModelParameters.kpz

/-- The symbols in the KPZ regularity structure -/
inductive KPZSymbol
  | Xi : KPZSymbol  -- The noise ξ
  | I : KPZSymbol → KPZSymbol  -- Integration
  | D : KPZSymbol → KPZSymbol  -- Derivative
  | Mult : KPZSymbol → KPZSymbol → KPZSymbol  -- Multiplication

/-- The homogeneity of each symbol -/
noncomputable def symbolHomogeneity : KPZSymbol → ℝ
  | KPZSymbol.Xi => -3/2
  | KPZSymbol.I s => symbolHomogeneity s + 2
  | KPZSymbol.D s => symbolHomogeneity s - 1
  | KPZSymbol.Mult s₁ s₂ => symbolHomogeneity s₁ + symbolHomogeneity s₂

/-! ## KPZ as a Singular SPDE -/

/-- The KPZ equation as a singular SPDE in the framework of `SPDE.SingularSPDE`.
    - Spatial dimension d = 1
    - Operator: Laplacian (order β = 2)
    - Nonlinearity: (∇h)² modeled as u² in abstract setting
    - Noise: space-time white noise with regularity α = -3/2
    - Solution regularity: γ = α + β = 1/2 -/
noncomputable def kpz_singular_spde (_kpz : KPZEquation) : SPDE.SingularSPDE 1 where
  domain := Set.univ
  domain_open := isOpen_univ
  operator_order := 2
  operator_order_pos := by norm_num
  nonlinearity := SPDE.PolynomialNonlinearity.kpz
  noise_regularity := -3/2
  noise_distributional := by norm_num
  solution_regularity := 1/2
  subcritical := by norm_num
  regularity_from_kernel := by norm_num

/-! ## Renormalization -/

/-- The renormalization constant for KPZ -/
structure KPZRenormalization (kpz : KPZEquation) where
  /-- The divergent constant C_ε ~ 1/ε -/
  constant : ℝ → ℝ
  /-- The divergence is linear: C_ε ~ c/ε -/
  linear_divergence : ∃ c : ℝ, ∀ ε > 0, |constant ε - c/ε| ≤ 1

/-- The renormalization constants for KPZ in the framework of `SPDE.RenormalizationConstants`.
    The single divergent constant C_ε ~ λ²D/(4νε) arises from the Wick renormalization
    of the nonlinearity (∇h)². -/
noncomputable def kpz_renormalization_constants (kpz : KPZEquation) :
    SPDE.RenormalizationConstants 1 (kpz_singular_spde kpz) where
  constants := fun ε => kpz.lambda^2 * kpz.noise_strength^2 / (4 * kpz.nu * ε)
  divergence_exponent := 1
  divergence_bound := by
    refine ⟨kpz.lambda^2 * kpz.noise_strength^2 / (4 * kpz.nu) + 1, 1, ?_, by norm_num, ?_⟩
    · linarith [sq_nonneg kpz.lambda, sq_nonneg kpz.noise_strength,
        div_nonneg (mul_nonneg (sq_nonneg kpz.lambda) (sq_nonneg kpz.noise_strength))
          (mul_pos (by norm_num : (0:ℝ) < 4) kpz.nu_pos).le]
    · intro ε hε _
      sorry -- bound on |C_ε| ≤ K * ε^{-1}
  renormalized_limit := by
    intro ε₁ ε₂ hε₁ _
    sorry

/-! ## Well-Posedness -/

/-- Local well-posedness for KPZ (Hairer 2013).
    For initial data h₀ in C^{1/2-ε}, there exists a unique local solution. -/
structure KPZLocalWellPosedness (kpz : KPZEquation) where
  /-- The solution regularity (1/2 - ε) -/
  solution_regularity : ℝ
  /-- Regularity is close to 1/2 -/
  regularity_bound : solution_regularity < 1/2 ∧ solution_regularity > 0
  /-- Existence time depends on initial data -/
  existence_time : ℝ → ℝ  -- initial_norm → T
  /-- Existence time is positive -/
  existence_time_pos : ∀ R : ℝ, R > 0 → existence_time R > 0

/-- Global well-posedness with sublinear initial data.
    If h₀(x) = o(|x|) as |x| → ∞, then the solution exists for all time.
    Uses the `SPDE.GlobalWellPosedness` framework from SPDE.lean. -/
theorem kpz_global_wellposedness (kpz : KPZEquation) :
    SPDE.GlobalWellPosedness 1 (kpz_singular_spde kpz) KPZ_ModelParameters :=
  sorry

/-! ## KPZ Universality -/

/-- The KPZ fixed point describes the universal long-time behavior.
    The one-point distribution converges to Tracy-Widom after proper rescaling.
    The spatial correlations are described by the Airy₂ process. -/
structure KPZFixedPoint where
  /-- The dynamic exponent z = 3/2 -/
  dynamic_exponent : ℝ := 3/2
  /-- The roughness exponent χ = 1/2 -/
  roughness_exponent : ℝ := 1/2
  /-- The growth exponent β = 1/3 -/
  growth_exponent : ℝ := 1/3
  /-- The exponent relation z = χ + 1 -/
  exponent_relation : dynamic_exponent = roughness_exponent + 1 := by norm_num

/-- The KPZ universality class: many growth models converge to the same fixed point -/
structure KPZUniversality where
  /-- The fixed point is universal -/
  fixed_point : KPZFixedPoint
  /-- Models in the universality class share the same exponents -/
  universal_exponents : fixed_point.dynamic_exponent = 3/2 ∧
    fixed_point.roughness_exponent = 1/2 ∧ fixed_point.growth_exponent = 1/3

/-- The KPZ scaling exponents satisfy exact relations -/
structure KPZScalingExponents where
  /-- z = 3/2 (dynamic exponent) -/
  z : ℝ := 3/2
  /-- χ = 1/2 (roughness exponent) -/
  chi : ℝ := 1/2
  /-- α = 1/2 (Hurst exponent, same as χ in 1D) -/
  alpha : ℝ := 1/2
  /-- The exact scaling relation: z = 1 + χ -/
  scaling_relation : z = 1 + chi := by norm_num
  /-- Growth exponent β = χ/z = 1/3 -/
  growth : ℝ := chi / z

end SPDE.Examples
