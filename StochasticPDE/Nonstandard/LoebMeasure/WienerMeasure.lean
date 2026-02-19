/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.PathContinuity
import StochasticPDE.Nonstandard.LoebMeasure.MathlibBridge
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Wiener Measure and Anderson's Theorem

This file develops the Wiener measure on C([0,1], ℝ) and states Anderson's theorem,
which shows that the pushforward of Loeb measure under the standard part map equals
Wiener measure.

## Main Definitions

* `PathSpace` - The space C([0,1], ℝ) of continuous functions from [0,1] to ℝ
* `CylinderSet` - Cylinder sets in path space determined by finite times
* `GaussianDensity` - The Gaussian density function for Brownian increments
* `WienerCylinderMeasure` - Measure of cylinder sets under Wiener measure

## Main Results (Statements)

* `anderson_theorem` - The pushforward of Loeb measure under the standard part map
  equals Wiener measure on cylinder sets.

## Implementation Notes

We define Wiener measure via its finite-dimensional distributions (cylinder sets).
The full Carathéodory extension requires the local CLT infrastructure to be completed.

## References

* Anderson, R. M. "A nonstandard representation for Brownian motion and Itô integration" (1976)
* Cutland, N. "Loeb Measures in Practice: Recent Advances" (2000)
-/

open Hyperreal Filter MeasureTheory Set

namespace SPDE.Nonstandard

/-! ## The Path Space

The path space C([0,1], ℝ) consists of continuous functions from [0,1] to ℝ,
equipped with the uniform topology (supremum norm).
-/

/-- The unit interval [0,1] as a type. -/
abbrev UnitInterval : Type := Icc (0 : ℝ) 1

/-- The path space: continuous functions from [0,1] to ℝ.
    This is the target space for Anderson's theorem. -/
abbrev PathSpace : Type := C(UnitInterval, ℝ)

/-- A path in PathSpace evaluated at a time t ∈ [0,1]. -/
noncomputable def PathSpace.eval (f : PathSpace) (t : UnitInterval) : ℝ := f t

/-- Paths start at zero (for standard Brownian motion). -/
def PathSpace.startsAtZero (f : PathSpace) : Prop :=
  f ⟨0, left_mem_Icc.mpr (by norm_num)⟩ = 0

/-! ## Cylinder Sets

Cylinder sets are determined by constraints on the path at finitely many times.
These are the basic measurable sets for Wiener measure.
-/

/-- A time point in [0,1] with its inclusion proof. -/
structure TimePoint where
  val : ℝ
  property : 0 ≤ val ∧ val ≤ 1

instance : Coe TimePoint UnitInterval where
  coe t := ⟨t.val, t.property⟩

/-- A single constraint: path at time t lies in interval [a, b]. -/
structure SingleConstraint where
  time : TimePoint
  lower : ℝ
  upper : ℝ
  bounds_valid : lower ≤ upper

/-- Check if a path satisfies a single constraint. -/
def PathSpace.satisfiesConstraint (f : PathSpace) (c : SingleConstraint) : Prop :=
  c.lower ≤ f c.time ∧ f c.time ≤ c.upper

/-- A finite cylinder constraint: path values at n times lie in specified intervals. -/
structure CylinderConstraint (n : ℕ) where
  /-- Ordered times 0 < t₁ < t₂ < ... < tₙ ≤ 1 -/
  times : Fin n → TimePoint
  /-- Lower bounds for each time -/
  lowers : Fin n → ℝ
  /-- Upper bounds for each time -/
  uppers : Fin n → ℝ
  /-- Bounds are valid -/
  bounds_valid : ∀ i, lowers i ≤ uppers i
  /-- Times are strictly increasing (for n > 0) -/
  times_increasing : ∀ i j, i < j → (times i).val < (times j).val

/-- A path satisfies a cylinder constraint if it lies in the specified intervals at each time. -/
def PathSpace.satisfiesCylinder {n : ℕ} (f : PathSpace) (c : CylinderConstraint n) : Prop :=
  ∀ i : Fin n, c.lowers i ≤ f (c.times i) ∧ f (c.times i) ≤ c.uppers i

/-- The cylinder set determined by a constraint. -/
def CylinderSet {n : ℕ} (c : CylinderConstraint n) : Set PathSpace :=
  { f | f.satisfiesCylinder c }

/-! ## Gaussian Density

The Brownian motion increment W(t) - W(s) has Gaussian distribution N(0, t-s).
-/

/-- The Gaussian density φ(x; σ²) = (1/√(2πσ²)) exp(-x²/(2σ²)) -/
noncomputable def gaussianDensity (variance : ℝ) (x : ℝ) : ℝ :=
  if variance ≤ 0 then 0
  else (1 / Real.sqrt (2 * Real.pi * variance)) * Real.exp (-x^2 / (2 * variance))

/-- The Gaussian density is nonnegative. -/
theorem gaussianDensity_nonneg (variance x : ℝ) : 0 ≤ gaussianDensity variance x := by
  unfold gaussianDensity
  split_ifs with h
  · exact le_refl 0
  · apply mul_nonneg
    · apply div_nonneg (by norm_num)
      apply Real.sqrt_nonneg
    · exact Real.exp_nonneg _

/-- Gaussian integral over ℝ equals 1 (when variance > 0). -/
theorem gaussianDensity_integral_eq_one {variance : ℝ} (hv : 0 < variance) :
    ∫ x, gaussianDensity variance x = 1 := by
  unfold gaussianDensity
  simp only [if_neg (not_le.mpr hv)]
  -- Rewrite -x^2 / (2 * variance) as -(1/(2*variance)) * x^2
  have h_rewrite : ∀ x : ℝ, -x^2 / (2 * variance) = -(1/(2 * variance)) * x^2 := by
    intro x; field_simp
  simp_rw [h_rewrite]
  -- Factor out the constant
  rw [integral_const_mul]
  -- Apply Mathlib's Gaussian integral: ∫ exp(-b * x²) = √(π/b) for b > 0
  rw [integral_gaussian (1 / (2 * variance))]
  -- Now simplify: (1/√(2πv)) * √(π/(1/(2v))) = (1/√(2πv)) * √(2πv) = 1
  have h_simp : Real.pi / (1 / (2 * variance)) = 2 * Real.pi * variance := by
    field_simp
  rw [h_simp]
  -- (1 / √(2πv)) * √(2πv) = 1
  have h2piv_pos : 0 < 2 * Real.pi * variance := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_self (Real.sqrt_ne_zero'.mpr h2piv_pos)]

/-! ## Wiener Measure on Cylinder Sets

The Wiener measure of a cylinder set is computed using the product of Gaussian densities
for the increments.
-/

/-- For a single-time cylinder constraint at time t with bounds [a, b],
    the Wiener measure is P(W(t) ∈ [a, b]) = ∫_a^b φ(x; t) dx where W(0) = 0. -/
noncomputable def wienerCylinderMeasure_single (t : ℝ) (a b : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else ∫ x in a..b, gaussianDensity t x

/-- Wiener measure is nonnegative. -/
theorem wienerCylinderMeasure_single_nonneg (t a b : ℝ) (hab : a ≤ b) :
    0 ≤ wienerCylinderMeasure_single t a b := by
  unfold wienerCylinderMeasure_single
  split_ifs
  · exact le_refl 0
  · apply intervalIntegral.integral_nonneg hab
    intro x _
    exact gaussianDensity_nonneg t x

/-! ## The Standard Part Map

For S-continuous hyperfinite paths, the standard part map sends them to continuous paths.
-/

/-- The standard part of an S-continuous hyperfinite walk as a continuous function on [0,1].
    This is the key map in Anderson's theorem. -/
noncomputable def standardPartMap (Ω : HyperfinitePathSpace) (path : ℕ → ℤ)
    (hS : HyperfiniteWalkPath.is_S_continuous Ω path) : PathSpace :=
  ⟨fun t => standardPartPath Ω path t.val, by
    -- Continuity follows from standardPartPath_continuous
    have hcont := standardPartPath_continuous Ω path hS
    exact hcont.comp (continuous_subtype_val.subtype_mk _)⟩

/-- The standard part map sends the walk to a path starting at 0 (when path 0 = 0). -/
theorem standardPartMap_startsAtZero (Ω : HyperfinitePathSpace) (path : ℕ → ℤ)
    (hS : HyperfiniteWalkPath.is_S_continuous Ω path) (h0 : path 0 = 0) :
    (standardPartMap Ω path hS).startsAtZero := by
  unfold standardPartMap PathSpace.startsAtZero standardPartPath hyperfiniteWalkValuePath
  -- The goal reduces to showing st(ofSeq(...)) = 0 at t = 0
  -- First, note that ↑(⟨0, _⟩ : UnitInterval) = 0
  show Hyperreal.st (Hyperreal.ofSeq (fun n =>
    Real.sqrt (1 / Ω.numSteps.toSeq n) *
      (path (min (Nat.floor ((0 : ℝ) * Ω.numSteps.toSeq n)) (Ω.numSteps.toSeq n)) : ℝ))) = 0
  -- At t = 0, the step index k = min(floor(0 * N), N) = 0, and path(0) = 0
  have hev : ∀ᶠ n in hyperfilter ℕ,
      Real.sqrt (1 / Ω.numSteps.toSeq n) *
        (path (min (Nat.floor ((0 : ℝ) * Ω.numSteps.toSeq n)) (Ω.numSteps.toSeq n)) : ℝ) = 0 := by
    apply Eventually.of_forall
    intro n
    simp only [zero_mul, Nat.floor_zero, zero_le, min_eq_left, h0, Int.cast_zero, mul_zero]
  have hzero : Hyperreal.ofSeq (fun n =>
      Real.sqrt (1 / Ω.numSteps.toSeq n) *
        (path (min (Nat.floor ((0 : ℝ) * Ω.numSteps.toSeq n)) (Ω.numSteps.toSeq n)) : ℝ)) = 0 :=
    Filter.Germ.coe_eq.mpr hev
  rw [hzero]
  exact Hyperreal.st_id_real 0

/-! ## Anderson's Theorem Statement

The main theorem states that the pushforward of Loeb measure under the standard part map
equals Wiener measure. We state this for cylinder sets, which form the basis of the topology.

The full proof requires completing the local CLT infrastructure.
-/

-- anderson_cylinder_convergence removed: was vacuously true (proved `True`).
-- The actual convergence statement is in AndersonTheorem.anderson_theorem_cylinder.

/-! ## Summary and Future Work

### What's Proven
1. Path space C([0,1], ℝ) is defined using Mathlib's ContinuousMap
2. Cylinder sets and constraints are defined
3. Gaussian density is defined with basic properties
4. Standard part map from S-continuous hyperfinite paths to PathSpace
5. standardPartMap_startsAtZero: paths start at 0

### What Requires Local CLT
1. gaussianDensity_integral_eq_one: Gaussian normalizes to 1
2. anderson_cylinder_convergence: Full statement connecting probabilities
3. Wiener measure as a genuine Mathlib `Measure` on PathSpace

### Anderson's Theorem (Full Statement)
```
theorem anderson :
    ∀ (Ω : HyperfinitePathSpace) (c : CylinderConstraint n),
    -- Pre-Loeb probability of the hyperfinite cylinder event
    -- equals the Wiener probability of the limiting cylinder set
    loebProb { path | standardPartMap Ω path ∈ CylinderSet c } =
      wienerCylinderMeasure c
```

The proof requires:
1. Local CLT: binomial probabilities → Gaussian densities
2. Dominated convergence to pass limits through integrals
3. Carathéodory extension to get full Wiener measure

-/

end SPDE.Nonstandard
