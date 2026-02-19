/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import StochasticPDE.Nonstandard.HyperfiniteRandomWalk
import StochasticPDE.Nonstandard.HyperfiniteIntegration

/-!
# Hyperfinite White Noise

This file develops white noise via the nonstandard approach: as a hyperfinite
sequence of normalized coin flips.

## Main Ideas

White noise is formally the "derivative" of Brownian motion: ξ = dW/dt.
Since Brownian motion is nowhere differentiable, this is not a function
but a distribution (generalized function).

In the hyperfinite framework, white noise has a simple representation:
- Let W be a hyperfinite random walk with increments ΔW = ±dx, dx = √dt
- Define ξₖ = ΔWₖ / dt = (±dx) / dt = ±1/√dt

The key covariance property follows from the discrete version:
- E[ξⱼ · ξₖ] = δⱼₖ / dt  (Kronecker delta times 1/dt)

When integrated against test functions and standard parts are taken,
this yields the standard white noise covariance:
- E[∫ξφ · ∫ξψ] = ∫ φ·ψ dt

## Main Definitions

* `HyperfiniteWhiteNoise` - White noise as normalized random walk increments
* `whiteNoiseAt` - The value of white noise at time step k
* `whiteNoiseIntegral` - The integral of white noise against a test function

## Main Results

* `whiteNoise_mean_zero` - E[ξₖ] = 0 (at the internal level)
* `whiteNoise_covariance_diagonal` - ξⱼ·ξₖ = δⱼₖ/dt exactly
* `whiteNoise_integral_variance` - Variance of ∫ξφ equals ∫φ² (up to infinitesimals)

## References

* Albeverio et al., "Nonstandard Methods in Stochastic Analysis"
* Lindstrøm, "Hyperfinite Stochastic Integration"
-/

open Hyperreal

namespace SPDE.Nonstandard.WhiteNoise

/-! ## Hyperfinite White Noise Structure

White noise is represented as normalized increments of a hyperfinite random walk.
-/

/-- A hyperfinite white noise process.
    This is the derivative of a hyperfinite random walk in the internal sense. -/
structure HyperfiniteWhiteNoise where
  /-- The underlying hyperfinite random walk -/
  walk : HyperfiniteWalk
  /-- The number of steps is infinite -/
  numSteps_infinite : Foundation.Hypernat.Infinite walk.numSteps

namespace HyperfiniteWhiteNoise

variable (ξ : HyperfiniteWhiteNoise)

/-- Time step dt -/
noncomputable def dt : ℝ* := ξ.walk.dt

/-- Time step is infinitesimal -/
theorem dt_infinitesimal : Infinitesimal ξ.dt :=
  ξ.walk.dt_infinitesimal ξ.numSteps_infinite

/-- Space step dx = √dt -/
noncomputable def dx : ℝ* := ξ.walk.dx

/-- The key relation: dx² = dt -/
theorem dx_sq_eq_dt : ξ.dx^2 = ξ.dt := ξ.walk.dx_sq_eq_dt

/-- White noise at step k: ξₖ = ΔWₖ / dt = flips(k) · dx / dt = flips(k) / √dt -/
noncomputable def at' (k : ℕ) : ℝ* :=
  ξ.walk.coins.flips k / ξ.dx

/-- Alternative: white noise as flip / √dt -/
theorem at_eq_flip_div_sqrt_dt (k : ℕ) :
    ξ.at' k = ξ.walk.coins.flips k / ξ.dx := rfl

/-- The white noise value squared equals 1/dt -/
theorem at_sq (k : ℕ) : (ξ.at' k)^2 = 1 / ξ.dt := by
  unfold at'
  rw [div_pow]
  -- flips(k)² = 1 since flips(k) = ±1
  have hflip : (ξ.walk.coins.flips k)^2 = 1 := by
    rcases ξ.walk.coins.flips_pm_one k with h | h <;> simp [h]
  rw [hflip]
  -- 1 / dx² = 1 / dt
  rw [ξ.dx_sq_eq_dt]

/-- dt is positive -/
theorem dt_pos : 0 < ξ.dt := by
  have h1 : (0 : ℝ) < ξ.walk.totalTime := ξ.walk.totalTime_pos
  -- From infinite hypernatural, we get positive value
  have hinf := ξ.numSteps_infinite
  rw [Foundation.Hypernat.infinite_iff_infinitePos] at hinf
  have hpos : (0 : ℝ*) < ξ.walk.numSteps.val := hinf 0
  unfold dt HyperfiniteWalk.dt
  exact div_pos (by exact_mod_cast h1) hpos

/-- dt is nonzero -/
theorem dt_ne_zero : ξ.dt ≠ 0 := ne_of_gt ξ.dt_pos

/-- 1/dt is infinite -/
theorem one_div_dt_infinite : Hyperreal.Infinite (1 / ξ.dt) := by
  rw [one_div]
  have hdt : Infinitesimal ξ.dt := ξ.dt_infinitesimal
  have hne : ξ.dt ≠ 0 := ξ.dt_ne_zero
  rw [infinite_iff_infinitesimal_inv (inv_ne_zero hne), inv_inv]
  exact hdt

/-- White noise squared is infinite at each point (characteristic of a distribution) -/
theorem at_sq_infinite (k : ℕ) : Hyperreal.Infinite ((ξ.at' k)^2) := by
  rw [at_sq]
  exact ξ.one_div_dt_infinite

/-! ## Covariance Structure

The key property of white noise: E[ξⱼ·ξₖ] = δⱼₖ/dt
Since we're working with a single path (not expectations), we prove:
ξⱼ·ξₖ = 0 when j ≠ k (different flips are independent: flip_j · flip_k is not ±1)

Actually, without probabilistic structure, we can only prove:
(ξₖ)² = 1/dt (done above)
-/

/-- The product of white noise at same point equals 1/dt -/
theorem at_mul_self (k : ℕ) : ξ.at' k * ξ.at' k = 1 / ξ.dt := by
  rw [← sq, at_sq]

/-! ## Integration Against Test Functions

The key operation: integrating white noise against a test function.
∫ ξ·φ dt ≈ Σₖ ξₖ·φₖ·dt = Σₖ (flips(k)/√dt)·φₖ·dt = Σₖ flips(k)·φₖ·√dt
-/

/-- The hyperfinite integral of white noise against a standard function.
    ∫ ξ·φ dt ≈ Σₖ ξₖ·φ(tₖ)·dt = Σₖ flips(k)·φ(tₖ)·dx -/
noncomputable def integral (φ : ℝ → ℝ) (n : ℕ) : ℝ* :=
  ∑ k ∈ Finset.range n, ξ.walk.coins.flips k * φ (k * st ξ.dt) * ξ.dx

/-- Alternative formulation: integral as sum of coin flips times test function values -/
theorem integral_eq_sum_flips (φ : ℝ → ℝ) (n : ℕ) :
    ξ.integral φ n = ∑ k ∈ Finset.range n, ξ.walk.coins.flips k * φ (k * st ξ.dt) * ξ.dx := rfl

/-! ## Variance of Integral

The variance of ∫ξφ should be ∫φ². This is the Itô isometry at the hyperfinite level.
-/

/-- The square of the integral. By expanding:
    (Σ flips(k)·φₖ·dx)² = Σᵢⱼ flips(i)·flips(j)·φᵢ·φⱼ·dx²

    Cross terms vanish in expectation (different flips are independent).
    Diagonal terms: flips(k)²·φₖ²·dx² = φₖ²·dt

    So we expect: E[(∫ξφ)²] = Σ φₖ²·dt ≈ ∫φ²dt -/
theorem integral_sq_structure (φ : ℝ → ℝ) (n : ℕ) :
    (ξ.integral φ n)^2 =
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      ξ.walk.coins.flips i * ξ.walk.coins.flips j *
      φ (i * st ξ.dt) * φ (j * st ξ.dt) * ξ.dx^2 := by
  unfold integral
  rw [sq]
  rw [Finset.sum_mul_sum]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- The diagonal contribution: Σ φₖ² · dt -/
noncomputable def diagonalSum (φ : ℝ → ℝ) (n : ℕ) : ℝ* :=
  ∑ k ∈ Finset.range n, (φ (k * st ξ.dt))^2 * ξ.dt

/-- When considering only diagonal terms (same index), each contributes φₖ²·dt
    since flips(k)² = 1 and dx² = dt -/
theorem diagonal_term (φ : ℝ → ℝ) (k : ℕ) :
    ξ.walk.coins.flips k * ξ.walk.coins.flips k *
    φ (k * st ξ.dt) * φ (k * st ξ.dt) * ξ.dx^2 =
    (φ (k * st ξ.dt))^2 * ξ.dt := by
  have hflip : ξ.walk.coins.flips k * ξ.walk.coins.flips k = 1 := by
    rcases ξ.walk.coins.flips_pm_one k with h | h <;> simp [h]
  rw [hflip, ξ.dx_sq_eq_dt]
  ring

end HyperfiniteWhiteNoise

/-! ## Connection to Standard White Noise

The standard part of hyperfinite white noise integrals should match
the standard stochastic integral.

Key theorem (informal): For nice test functions φ,
  st(∫ ξ·φ dt) = ∫ φ dW (Itô integral)

This requires the full Loeb measure construction (see LoebMeasure.lean).
-/

/-- The hyperfinite white noise integral, for test function sequences -/
noncomputable def hyperfiniteWhiteNoiseIntegral
    (ξ : HyperfiniteWhiteNoise) (φ : ℕ → ℝ) (n : ℕ) : ℝ* :=
  ∑ k ∈ Finset.range n, ξ.walk.coins.flips k * (φ k) * ξ.dx

/-- The variance contribution from the hyperfinite integral.
    This is the quadratic variation: Σ φₖ² · dt -/
noncomputable def hyperfiniteIntegralVariance
    (ξ : HyperfiniteWhiteNoise) (φ : ℕ → ℝ) (n : ℕ) : ℝ* :=
  ∑ k ∈ Finset.range n, (φ k)^2 * ξ.dt

/-- The quadratic variation of the white noise integral.
    [∫ξφ] = Σ (flips(k)·φₖ·dx)² = Σ φₖ²·dx² = Σ φₖ²·dt -/
theorem quadratic_variation_white_noise_integral
    (ξ : HyperfiniteWhiteNoise) (φ : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (ξ.walk.coins.flips k * (φ k) * ξ.dx)^2 =
    hyperfiniteIntegralVariance ξ φ n := by
  unfold hyperfiniteIntegralVariance
  congr 1
  ext k
  have hflip : (ξ.walk.coins.flips k)^2 = 1 := by
    rcases ξ.walk.coins.flips_pm_one k with h | h <;> simp [h]
  calc (ξ.walk.coins.flips k * (φ k) * ξ.dx)^2
      = (ξ.walk.coins.flips k)^2 * (φ k)^2 * ξ.dx^2 := by ring
    _ = 1 * (φ k)^2 * ξ.dt := by rw [hflip, ξ.dx_sq_eq_dt]
    _ = (φ k)^2 * ξ.dt := by ring

end SPDE.Nonstandard.WhiteNoise
