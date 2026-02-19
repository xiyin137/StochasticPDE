/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import StochasticPDE.Nonstandard.HyperfiniteRandomWalk
import StochasticPDE.Nonstandard.HyperfiniteIntegration

/-!
# Hyperfinite Stochastic Integration

This file develops the Itô integral via the hyperfinite approach. The key insight
is that the Itô integral becomes a simple finite sum in the hyperfinite setting:

  ∫₀ᵗ H dW ≈ Σₖ Hₖ · ΔWₖ

where the sum is over a hyperfinite number of terms.

## Main Ideas

In standard stochastic calculus, the Itô integral requires:
- Adapted processes
- L² integrability conditions
- Careful limit arguments

In the hyperfinite approach:
1. The random walk W has hyperfinite steps: ΔWₖ = ±dx where dx = √dt
2. The integrand H is evaluated at mesh points: Hₖ = H(tₖ)
3. The integral is a hyperfinite sum: Σₖ Hₖ · ΔWₖ
4. Taking standard parts yields the Itô integral

## Main Definitions

* `HyperfiniteStochasticIntegral` - The hyperfinite sum Σ Hₖ · ΔWₖ
* `quadraticVariation_stochastic` - Σ (Hₖ · ΔWₖ)²

## Main Results

* `stochastic_integral_quadratic_variation` - QV = Σ Hₖ² · dt (Itô isometry)
* `stochastic_integral_linearity` - Linearity properties

## References

* Lindstrøm, "Hyperfinite Stochastic Integration"
* Anderson, "A nonstandard representation for Brownian motion and Itô integration"
-/

open Hyperreal Finset

namespace SPDE.Nonstandard.StochasticIntegral

/-! ## Hyperfinite Stochastic Integral

The stochastic integral Σₖ Hₖ · ΔWₖ where ΔWₖ = ±dx.
-/

/-- A hyperfinite stochastic integral specification.
    Combines a random walk (the integrator) with an integrand. -/
structure HyperfiniteStochasticIntegral where
  /-- The underlying hyperfinite random walk (the Brownian motion approximation) -/
  walk : HyperfiniteWalk
  /-- The number of steps is infinite -/
  numSteps_infinite : Infinite walk.numSteps
  /-- The integrand as a function on step indices -/
  integrand : ℕ → ℝ*

namespace HyperfiniteStochasticIntegral

variable (I : HyperfiniteStochasticIntegral)

/-- Time step dt -/
noncomputable def dt : ℝ* := I.walk.dt

/-- Space step dx = √dt -/
noncomputable def dx : ℝ* := I.walk.dx

/-- The increment ΔWₖ = flips(k) · dx -/
noncomputable def increment (k : ℕ) : ℝ* :=
  I.walk.coins.flips k * I.dx

/-- Increment is ±dx -/
theorem increment_pm_dx (k : ℕ) :
    I.increment k = I.dx ∨ I.increment k = -I.dx := by
  unfold increment
  rcases I.walk.coins.flips_pm_one k with h | h
  · left; rw [h, one_mul]
  · right; rw [h, neg_one_mul]

/-- Increment squared equals dt -/
theorem increment_sq (k : ℕ) : (I.increment k)^2 = I.dt := by
  show (I.increment k)^2 = I.walk.dt
  rcases increment_pm_dx I k with h | h
  · simp only [h, dx]
    exact I.walk.dx_sq_eq_dt
  · simp only [h, neg_sq, dx]
    exact I.walk.dx_sq_eq_dt

/-- The hyperfinite stochastic integral up to step n: Σₖ₌₀ⁿ⁻¹ Hₖ · ΔWₖ -/
noncomputable def integral (n : ℕ) : ℝ* :=
  ∑ k ∈ range n, I.integrand k * I.increment k

/-- The integral starts at 0 -/
theorem integral_zero : I.integral 0 = 0 := by
  simp [integral]

/-- Recursive formula for the integral -/
theorem integral_succ (n : ℕ) :
    I.integral (n + 1) = I.integral n + I.integrand n * I.increment n := by
  simp [integral, sum_range_succ]

/-! ## Quadratic Variation (Itô Isometry)

The key property: Σ (Hₖ · ΔWₖ)² = Σ Hₖ² · dt
-/

/-- Quadratic variation of the stochastic integral up to step n -/
noncomputable def quadraticVariation (n : ℕ) : ℝ* :=
  ∑ k ∈ range n, (I.integrand k * I.increment k)^2

/-- Each term of QV equals Hₖ² · dt -/
theorem qv_term (k : ℕ) :
    (I.integrand k * I.increment k)^2 = (I.integrand k)^2 * I.dt := by
  rw [mul_pow, increment_sq]

/-- **Itô Isometry (hyperfinite version)**:
    The quadratic variation equals Σ Hₖ² · dt exactly. -/
theorem ito_isometry (n : ℕ) :
    I.quadraticVariation n = ∑ k ∈ range n, (I.integrand k)^2 * I.dt := by
  unfold quadraticVariation
  congr 1
  ext k
  exact qv_term I k

/-- Factoring out dt from the isometry -/
theorem ito_isometry' (n : ℕ) :
    I.quadraticVariation n = I.dt * ∑ k ∈ range n, (I.integrand k)^2 := by
  rw [ito_isometry, mul_sum]
  congr 1
  ext k
  ring

/-! ## Properties of the Stochastic Integral -/

/-- The integral is 0 when the integrand is 0 -/
theorem integral_zero_integrand (n : ℕ) (h : ∀ k, I.integrand k = 0) :
    I.integral n = 0 := by
  unfold integral
  apply sum_eq_zero
  intro k _
  rw [h k, zero_mul]

/-- Linearity: scalar multiplication -/
theorem integral_smul (c : ℝ*) (n : ℕ) :
    let I' : HyperfiniteStochasticIntegral := ⟨I.walk, I.numSteps_infinite, fun k => c * I.integrand k⟩
    I'.integral n = c * I.integral n := by
  simp only [integral, increment, dx]
  rw [mul_sum]
  congr 1
  ext k
  ring

end HyperfiniteStochasticIntegral

/-! ## Standard Integrands

When the integrand is a standard (non-hyperreal) function, we can connect
to standard stochastic integration via the standard part.
-/

/-- A stochastic integral with a standard integrand -/
noncomputable def standardIntegrand (walk : HyperfiniteWalk)
    (hN : Infinite walk.numSteps) (H : ℕ → ℝ) : HyperfiniteStochasticIntegral where
  walk := walk
  numSteps_infinite := hN
  integrand := fun k => (H k : ℝ*)

/-- The integral as a sequence (for taking standard parts) -/
noncomputable def integralSeq (walk : HyperfiniteWalk) (H : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, H k * (if walk.coins.flips k = 1 then 1 else -1) * st walk.dx

/-! ## Properties for Standard Indices

For standard (finite) step indices, the hyperfinite integral has simple properties.
-/

/-- For standard k, the hyperfinite stochastic integral is infinitesimal.

    This is because the integral is a sum of k terms, each of the form H(i) * (±dx),
    where dx is infinitesimal. The sum of finitely many infinitesimals is infinitesimal. -/
theorem integral_infinitesimal_of_standard (walk : HyperfiniteWalk)
    (hN : Infinite walk.numSteps) (H : ℕ → ℝ) (k : ℕ) :
    let I := standardIntegrand walk hN H
    Infinitesimal (I.integral k) := by
  -- The integral is Σᵢ₌₀^{k-1} H(i) * flips(i) * dx
  -- Each term is a standard real times an infinitesimal
  have hdt_inf : Infinitesimal walk.dt := walk.dt_infinitesimal hN
  have hdx_sq : walk.dx^2 = walk.dt := walk.dx_sq_eq_dt
  have hdx_pos : 0 < walk.dx := walk.dx_pos
  -- dx is infinitesimal: dx² = dt is infinitesimal and dx > 0
  have hdx_inf : Infinitesimal walk.dx := by
    rw [Infinitesimal, isSt_iff_abs_sub_lt_delta]
    intro δ hδ
    have hdt_lt : walk.dt < δ^2 := by
      have hδ2_pos : (0 : ℝ) < δ^2 := sq_pos_of_pos hδ
      exact lt_of_pos_of_infinitesimal hdt_inf (δ^2) hδ2_pos
    have hδ_pos' : (0 : ℝ*) < (δ : ℝ*) := by exact_mod_cast hδ
    calc |walk.dx - (0 : ℝ*)| = |walk.dx| := by rw [sub_zero]
      _ = walk.dx := abs_of_pos hdx_pos
      _ < (δ : ℝ*) := by
          have h : walk.dx^2 < (δ : ℝ*)^2 := by rw [hdx_sq]; exact_mod_cast hdt_lt
          -- From dx > 0, δ > 0, and dx² < δ², we get |dx| < |δ|, i.e., dx < δ
          have habs : |walk.dx| < |(δ : ℝ*)| := sq_lt_sq.mp h
          rwa [abs_of_pos hdx_pos, abs_of_pos hδ_pos'] at habs
  -- Each term H(i) * flips(i) * dx is infinitesimal
  unfold standardIntegrand HyperfiniteStochasticIntegral.integral
    HyperfiniteStochasticIntegral.increment HyperfiniteStochasticIntegral.dx
  -- Show that each term is infinitesimal
  have hterm : ∀ i, Infinitesimal ((H i : ℝ*) * (walk.coins.flips i * walk.dx)) := by
    intro i
    -- flips i = ±1, so flips i * dx = ±dx is infinitesimal
    have hflip_dx_inf : Infinitesimal (walk.coins.flips i * walk.dx) := by
      rcases walk.coins.flips_pm_one i with h | h
      · rw [h, one_mul]; exact hdx_inf
      · rw [h, neg_one_mul]
        exact hdx_inf.neg
    -- (H i : ℝ*) * infinitesimal = infinitesimal
    have hH_st : IsSt (H i : ℝ*) (H i) := isSt_refl_real (H i)
    have h := hH_st.mul hflip_dx_inf
    simp only [mul_zero] at h
    exact h
  -- Sum of k infinitesimals is infinitesimal
  induction k with
  | zero =>
    simp only [range_zero, sum_empty]
    exact infinitesimal_zero
  | succ k ih =>
    simp only at ih ⊢
    rw [sum_range_succ]
    exact ih.add (hterm k)

/-- For standard k, the integral is not infinite (trivial consequence). -/
theorem integral_not_infinite_of_standard (walk : HyperfiniteWalk)
    (hN : Infinite walk.numSteps) (H : ℕ → ℝ) (k : ℕ) :
    let I := standardIntegrand walk hN H
    ¬Hyperreal.Infinite (I.integral k) :=
  (integral_infinitesimal_of_standard walk hN H k).not_infinite

/-! ## Connection to Standard Itô Integral

The hyperfinite stochastic integral should equal the Itô integral after
taking standard parts and limits. This requires:

1. **Hypernatural step indices**: For times t > 0, the step index K = ⌊t/dt⌋
   is hyperfinite (infinite), not a standard natural.

2. **Loeb measure**: To make probabilistic statements about the integral,
   we need the Loeb measure construction from LoebMeasure.lean.

3. **L² bounds**: The integrand must be adapted and L²-bounded.

The formal theorem connecting st(hyperfinite integral) to the Itô integral
is a deep result (Anderson's theorem) that requires the full Loeb machinery.
We do not attempt to state it here without proper foundations.

**What we CAN prove without Loeb measure**:
- For standard k, the integral is infinitesimal (proven above)
- The Itô isometry holds exactly: Σ(H·ΔW)² = Σ H²·dt
- Linearity and basic algebraic properties

**What REQUIRES Loeb measure**:
- Convergence of st(integral at K) to Itô integral ∫₀ᵗ H dW
- Almost sure properties of paths
- L² convergence statements
-/

/-! ## Simple Integrands

For constant and linear integrands, we can compute explicitly.
-/

/-- For constant integrand H = c, the integral is c · Wₙ -/
theorem integral_const (walk : HyperfiniteWalk) (hN : Infinite walk.numSteps)
    (c : ℝ) (n : ℕ) :
    let I := standardIntegrand walk hN (fun _ => c)
    I.integral n = (c : ℝ*) * walk.walkAt n := by
  simp only [HyperfiniteStochasticIntegral.integral, standardIntegrand]
  simp only [HyperfiniteStochasticIntegral.increment, HyperfiniteStochasticIntegral.dx]
  rw [← mul_sum]
  congr 1
  unfold HyperfiniteWalk.walkAt
  rw [mul_comm, sum_mul]

/-- For constant integrand, QV = c² · n · dt -/
theorem qv_const (walk : HyperfiniteWalk) (hN : Infinite walk.numSteps)
    (c : ℝ) (n : ℕ) :
    let I := standardIntegrand walk hN (fun _ => c)
    I.quadraticVariation n = (c : ℝ*)^2 * (n : ℝ*) * walk.dt := by
  simp only [HyperfiniteStochasticIntegral.quadraticVariation, standardIntegrand,
             HyperfiniteStochasticIntegral.increment, HyperfiniteStochasticIntegral.dx]
  have h : ∀ k ∈ range n, ((c : ℝ*) * (walk.coins.flips k * walk.dx))^2 =
      (c : ℝ*)^2 * walk.dt := by
    intro k _
    rw [mul_pow, mul_pow]
    have hflip : (walk.coins.flips k)^2 = 1 := by
      rcases walk.coins.flips_pm_one k with hf | hf <;> simp [hf]
    rw [hflip, one_mul, walk.dx_sq_eq_dt]
  rw [sum_congr rfl h, sum_const, card_range]
  simp only [nsmul_eq_mul]
  ring

/-! ## Cross Variation

For two stochastic integrals, the cross variation structure.
-/

/-- Cross variation of two stochastic integrals -/
noncomputable def crossVariation (I J : HyperfiniteStochasticIntegral)
    (_hWalk : I.walk = J.walk) (n : ℕ) : ℝ* :=
  ∑ k ∈ range n, (I.integrand k * I.increment k) * (J.integrand k * J.increment k)

/-- Cross variation equals Σ Hₖ · Gₖ · dt when walks are the same -/
theorem cross_variation_eq (I J : HyperfiniteStochasticIntegral)
    (hWalk : I.walk = J.walk) (n : ℕ) :
    crossVariation I J (hWalk) n =
    ∑ k ∈ range n, I.integrand k * J.integrand k * I.dt := by
  unfold crossVariation
  congr 1
  ext k
  -- I.increment k = J.increment k since walks are the same
  have hinc : I.increment k = J.increment k := by
    simp only [HyperfiniteStochasticIntegral.increment,
               HyperfiniteStochasticIntegral.dx]
    rw [hWalk]
  rw [hinc]
  calc (I.integrand k * J.increment k) * (J.integrand k * J.increment k)
      = I.integrand k * J.integrand k * (J.increment k)^2 := by ring
    _ = I.integrand k * J.integrand k * J.dt := by rw [J.increment_sq]
    _ = I.integrand k * J.integrand k * I.dt := by
        have hdt : I.dt = J.dt := by
          simp only [HyperfiniteStochasticIntegral.dt]
          rw [hWalk]
        rw [hdt]

end SPDE.Nonstandard.StochasticIntegral
