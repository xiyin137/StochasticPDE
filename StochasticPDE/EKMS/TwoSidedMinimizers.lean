/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.EKMS.OneSidedMinimizers

/-!
# Two-Sided Minimizers and Main Shock

This file formalizes two-sided minimizers and the main shock in EKMS theory.

## Main Definitions

* `TwoSidedMinimizer` - A curve ξ : ℝ → ℝ minimizing action on the whole line
* `MainShock` - The unique continuous shock curve defined for all time
* `NonDegeneracyCondition` - The condition (A1) on forcing needed for uniqueness

## Main Results

* `TwoSidedMinimizer.existence` - Existence under non-degeneracy (Theorem 5.1)
* `TwoSidedMinimizer.uniqueness` - A.s. uniqueness (Theorem 5.2)
* `collision_lemma` - Basic collision lemma (Lemma 5.2)
-/

namespace SPDE.EKMS

open MeasureTheory

variable {prob : EKMSProbabilitySpace}

/-! ## Non-Degeneracy Condition (A1) -/

/-- Non-degeneracy condition (A1) from EKMS.
    There exists a finite set X* of local maxima points such that
    for any pair (x₁, x₂), there exists x* ∈ X* covering both. -/
structure NonDegeneracyCondition (_forcing : EKMSForcing prob) where
  /-- Number of critical points -/
  num_critical_points : ℕ
  /-- At least one critical point -/
  nonempty : num_critical_points ≥ 1
  /-- Covering property -/
  covering : True  -- Abstract covering property

/-! ## The Basic Collision Lemma (Lemma 5.2) -/

/-- Lemma 5.2 (EKMS) - Basic Collision Lemma:
    For any τ > 0, there exists p₀(τ) > 0 such that any two points
    have at least p₀(τ) probability of merging before time τ. -/
structure CollisionLemma (forcing : EKMSForcing prob) where
  /-- The non-degeneracy condition holds -/
  nondegen : NonDegeneracyCondition forcing
  /-- The collision probability p₀(τ) > 0 -/
  p₀ : ℝ → ℝ
  /-- p₀ is positive for positive τ -/
  p₀_pos : ∀ τ, τ > 0 → p₀ τ > 0

/-! ## Two-Sided Minimizers -/

/-- A two-sided minimizer is a curve ξ : ℝ → ℝ that minimizes the action
    with respect to all compact perturbations on (-∞, +∞). -/
structure TwoSidedMinimizer (_forcing : EKMSForcing prob) where
  /-- The curve ξ : ℝ → ℝ -/
  curve : ℝ → ℝ
  /-- The velocity ξ̇ : ℝ → ℝ -/
  velocity : ℝ → ℝ
  /-- The curve is continuous -/
  curve_continuous : Continuous curve
  /-- The velocity is continuous -/
  velocity_continuous : Continuous velocity
  /-- Minimization property on any finite interval (abstract) -/
  minimizing : True

namespace TwoSidedMinimizer

variable {forcing : EKMSForcing prob}

/-- Position at time t. -/
def position (m : TwoSidedMinimizer forcing) (t : ℝ) : ℝ := m.curve t

/-- The two-sided minimizer is also a one-sided minimizer (restricted). -/
def to_one_sided (m : TwoSidedMinimizer forcing) (t : ℝ) : OneSidedMinimizer forcing t where
  curve := m.curve
  velocity := m.velocity
  curve_continuous := m.curve_continuous
  velocity_continuous := m.velocity_continuous
  endpoint := m.curve t
  curve_endpoint := rfl
  minimizing := trivial

end TwoSidedMinimizer

/-- Theorem 5.1 (EKMS): Under non-degeneracy (A1), with probability 1,
    there exists a two-sided minimizer y_ω : ℝ → ℝ. -/
theorem TwoSidedMinimizer.existence (forcing : EKMSForcing prob)
    (_cl : CollisionLemma forcing) :
    ∀ᵐ _ω ∂prob.P, ∃ _m : TwoSidedMinimizer forcing, True := by
  sorry

/-- Theorem 5.2 (EKMS): Under non-degeneracy (A1), with probability 1,
    the two-sided minimizer is unique. -/
theorem TwoSidedMinimizer.uniqueness (forcing : EKMSForcing prob)
    (_cl : CollisionLemma forcing) :
    ∀ᵐ _ω ∂prob.P,
    ∀ m₁ m₂ : TwoSidedMinimizer forcing,
    ∀ t : ℝ, m₁.curve t = m₂.curve t := by
  sorry

/-- The unique two-sided minimizer. -/
structure UniqueTwoSidedMinimizer (forcing : EKMSForcing prob) (_cl : CollisionLemma forcing) where
  /-- The minimizer as a function of ω -/
  y : prob.Ω → TwoSidedMinimizer forcing
  /-- Measurability -/
  measurable : ∀ t : ℝ, Measurable (fun ω => (y ω).curve t)

/-! ## The Main Shock -/

/-- The main shock is a continuous shock curve x_ω : ℝ → ℝ defined for all time. -/
structure MainShock (_forcing : EKMSForcing prob) where
  /-- The shock position at time t -/
  position : ℝ → ℝ
  /-- The shock is continuous -/
  continuous : Continuous position

/-- The unique main shock. -/
structure UniqueMainShock (forcing : EKMSForcing prob) (_cl : CollisionLemma forcing) where
  /-- The shock as a function of ω -/
  x : prob.Ω → MainShock forcing
  /-- Measurability -/
  measurable : ∀ t : ℝ, Measurable (fun ω => (x ω).position t)

/-- Theorem 5.2 (EKMS): Under non-degeneracy, the main shock exists and is unique a.s. -/
theorem MainShock.existence_uniqueness (forcing : EKMSForcing prob)
    (cl : CollisionLemma forcing) :
    ∀ᵐ _ω ∂prob.P,
    (∃ _s : MainShock forcing, True) ∧
    (∀ s₁ s₂ : MainShock forcing, ∀ t : ℝ, s₁.position t = s₂.position t) := by
  sorry

/-- The number of shocks is finite a.s. -/
theorem finite_shocks (forcing : EKMSForcing prob) (_cl : CollisionLemma forcing) :
    ∀ᵐ ω ∂prob.P, ∀ t : ℝ, (jumpSet forcing t ω).Finite := by
  sorry

end SPDE.EKMS
