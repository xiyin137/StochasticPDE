/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.EKMS.Basic

/-!
# One-Sided Minimizers in EKMS Theory

This file formalizes one-sided minimizers, the fundamental objects in the
EKMS construction of invariant measures for stochastic Burgers equation.

## Main Definitions

* `OneSidedMinimizer` - A curve ξ : (-∞, t] → ℝ minimizing the action
* `OneSidedMinimizerUniqueness` - Almost sure uniqueness except for countable set

## Main Results

* `OneSidedMinimizer.existence` - Existence of one-sided minimizers (Theorem 3.1)
* `OneSidedMinimizer.uniqueness` - A.s. uniqueness at generic points (Theorem 1.1)
* `velocity_bound` - Uniform bounds on minimizer velocities (Lemma 3.1)
-/

namespace SPDE.EKMS

open MeasureTheory

variable {prob : EKMSProbabilitySpace}

/-! ## One-Sided Minimizers -/

/-- A one-sided minimizer is a curve ξ : (-∞, t₀] → ℝ that minimizes the action
    with respect to all compact perturbations. -/
structure OneSidedMinimizer (forcing : EKMSForcing prob) (t₀ : ℝ) where
  /-- The curve ξ : (-∞, t₀] → ℝ -/
  curve : ℝ → ℝ
  /-- The velocity ξ̇ : (-∞, t₀] → ℝ -/
  velocity : ℝ → ℝ
  /-- The curve is continuous -/
  curve_continuous : Continuous curve
  /-- The velocity is continuous -/
  velocity_continuous : Continuous velocity
  /-- Endpoint at t₀ -/
  endpoint : ℝ
  /-- The curve ends at endpoint -/
  curve_endpoint : curve t₀ = endpoint
  /-- Minimization property (abstract) -/
  minimizing : True

namespace OneSidedMinimizer

variable {forcing : EKMSForcing prob} {t₀ : ℝ}

/-- The endpoint velocity ξ̇(t₀). -/
noncomputable def endpointVelocity (m : OneSidedMinimizer forcing t₀) : ℝ :=
  m.velocity t₀

/-- The solution value at the endpoint: u(endpoint, t₀) = ξ̇(t₀). -/
noncomputable def solution_at_endpoint (m : OneSidedMinimizer forcing t₀) : ℝ :=
  m.endpointVelocity

end OneSidedMinimizer

/-! ## Velocity Bounds (Lemma 3.1) -/

/-- Random constants T(ω, t) and C(ω, t) for velocity bounds. -/
structure VelocityBoundConstants (forcing : EKMSForcing prob) (_t : ℝ) where
  /-- The time lookback T(ω, t) -/
  T : prob.Ω → ℝ
  /-- The velocity bound C(ω, t) -/
  C : prob.Ω → ℝ
  /-- T is positive a.s. -/
  T_pos : ∀ᵐ ω ∂prob.P, T ω > 0
  /-- C is positive a.s. -/
  C_pos : ∀ᵐ ω ∂prob.P, C ω > 0
  /-- T is measurable -/
  T_measurable : Measurable T
  /-- C is measurable -/
  C_measurable : Measurable C

/-- Lemma 3.1 (EKMS): Uniform bound on minimizer velocities. -/
structure VelocityBound (forcing : EKMSForcing prob) (t : ℝ) where
  /-- The bound constants -/
  constants : VelocityBoundConstants forcing t
  /-- The bound holds for all minimizers -/
  bound_holds : ∀ᵐ ω ∂prob.P,
    ∀ t₁ : ℝ, t₁ < t - constants.T ω →
    ∀ m : OneSidedMinimizer forcing t,
    |m.endpointVelocity| ≤ constants.C ω

theorem velocity_bound_exists (forcing : EKMSForcing prob) (t : ℝ) :
    ∃ vb : VelocityBound forcing t, True := by
  sorry

/-! ## Existence of One-Sided Minimizers (Theorem 3.1) -/

/-- Theorem 3.1 (EKMS): With probability 1, for any (x, t) ∈ ℝ × ℝ,
    there exists at least one one-sided minimizer γ such that γ(t) = x. -/
theorem OneSidedMinimizer.existence (forcing : EKMSForcing prob) (t : ℝ) (x : ℝ) :
    ∀ᵐ _ω ∂prob.P, ∃ m : OneSidedMinimizer forcing t, m.endpoint = x := by
  sorry

/-! ## Uniqueness of One-Sided Minimizers (Theorem 1.1) -/

/-- The set J(ω, t) ⊆ ℝ of points with multiple one-sided minimizers.
    Theorem 1.1 states this is at most countable. -/
def jumpSet (forcing : EKMSForcing prob) (t : ℝ) (_ω : prob.Ω) : Set ℝ :=
  {x : ℝ | ∃ m₁ m₂ : OneSidedMinimizer forcing t,
    m₁.endpoint = x ∧ m₂.endpoint = x ∧
    m₁.endpointVelocity ≠ m₂.endpointVelocity}

/-- Theorem 1.1 (EKMS): With probability 1, except for a countable set of x values,
    there exists a unique one-sided minimizer ξ such that ξ(t) = x. -/
theorem OneSidedMinimizer.uniqueness (forcing : EKMSForcing prob) (t : ℝ) :
    ∀ᵐ ω ∂prob.P, (jumpSet forcing t ω).Countable := by
  sorry

/-! ## The Global Solution Map Φ -/

/-- The solution map Φ : Ω → D defined by patching together one-sided minimizers. -/
structure GlobalSolutionMap (forcing : EKMSForcing prob) (D : SkorohodSpace) where
  /-- The map Φ₀(ω) at time 0 -/
  Φ₀ : prob.Ω → (ℝ → ℝ)
  /-- Φ₀ is measurable -/
  measurable : ∀ x : ℝ, Measurable (fun ω => Φ₀ ω x)
  /-- Φ₀(ω) is in the Skorohod space D a.s. -/
  in_D : ∀ᵐ ω ∂prob.P, Φ₀ ω ∈ D.carrier
  /-- Φ₀ is defined via one-sided minimizers -/
  via_minimizers : ∀ᵐ ω ∂prob.P, ∀ x : ℝ, x ∉ jumpSet forcing 0 ω →
    ∃ m : OneSidedMinimizer forcing 0, m.endpoint = x ∧ Φ₀ ω x = m.endpointVelocity

/-- The solution from the past at (x, t). -/
noncomputable def solutionFromPast (forcing : EKMSForcing prob) (_t : ℝ) (x : ℝ)
    (_ω : prob.Ω) : ℝ :=
  x  -- Placeholder; actual definition requires minimizer construction

/-- Limits from finite interval minimizers converge to one-sided minimizers. -/
theorem finite_to_one_sided_limit (forcing : EKMSForcing prob) (t : ℝ) (x : ℝ) :
    ∀ᵐ _ω ∂prob.P,
    ∃ m : OneSidedMinimizer forcing t, m.endpoint = x := by
  exact OneSidedMinimizer.existence forcing t x

end SPDE.EKMS
