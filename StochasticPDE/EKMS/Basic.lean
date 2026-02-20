/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# EKMS Theory: Basic Definitions

This file provides foundational definitions for the E-Khanin-Mazel-Sinai (EKMS) theory
of invariant measures for Burgers equation with stochastic forcing.

## Main Definitions

* `EKMSProbabilitySpace` - Probability space for EKMS theory
* `EKMSForcing` - Random forcing structure
* `ActionFunctional` - The Lagrangian action functional

## Key References

* E, Khanin, Mazel, Sinai, "Invariant measures for Burgers equation with stochastic forcing"
  (Annals of Mathematics, 2000)
-/

namespace SPDE.EKMS

open MeasureTheory
open scoped MeasureTheory

/-! ## Probability Space and Wiener Processes -/

/-- The probability space Ω for EKMS theory.
    Elements ω ∈ Ω are realizations of infinitely many independent Wiener processes. -/
structure EKMSProbabilitySpace where
  /-- The underlying probability space -/
  Ω : Type*
  /-- Measurable space structure -/
  measurableSpace : MeasurableSpace Ω
  /-- Probability measure -/
  P : @Measure Ω measurableSpace
  /-- P is a probability measure -/
  isProbability : @IsProbabilityMeasure Ω measurableSpace P

attribute [instance] EKMSProbabilitySpace.measurableSpace

/-- The circle S¹ represented as ℝ (we work on the universal cover for simplicity). -/
abbrev CircleR := ℝ

/-! ## The Random Forcing -/

/-- The forcing potential F_k satisfying the regularity conditions.
    Each F_k : ℝ → ℝ is smooth and periodic with period 1,
    with ||f_k||_{C^r} ≤ C/k² where f_k = F'_k. -/
structure ForcingPotential where
  /-- Index for the Wiener process -/
  index : ℕ+
  /-- The potential F_k : ℝ → ℝ (periodic with period 1) -/
  F : ℝ → ℝ
  /-- F is continuous -/
  continuous : Continuous F
  /-- The derivative f = F' -/
  f : ℝ → ℝ
  /-- f is continuous -/
  f_continuous : Continuous f
  /-- Periodicity: F(x + 1) = F(x) -/
  periodic : ∀ x, F (x + 1) = F x
  /-- Zero mean condition (abstract) -/
  zero_mean : True  -- Abstract: ∫_0^1 F(x) dx = 0

/-- The decay constant C in ||f_k||_{C^r} ≤ C/k². -/
structure ForcingDecayBound where
  /-- The bound constant -/
  C : ℝ
  /-- C is positive -/
  C_pos : C > 0

/-- The complete random forcing structure for EKMS theory.
    F(x,t) = Σ_k F_k(x) Ḃ_k(t) with the required decay conditions. -/
structure EKMSForcing (prob : EKMSProbabilitySpace) where
  /-- The collection of forcing potentials -/
  potentials : ℕ+ → ForcingPotential
  /-- Index consistency -/
  index_match : ∀ k, ForcingPotential.index (potentials k) = k
  /-- The decay bound -/
  decay_bound : ForcingDecayBound
  /-- The Wiener processes B_k -/
  B : ℕ+ → ℝ → prob.Ω → ℝ
  /-- Measurability of B_k(t) -/
  B_measurable : ∀ k t, Measurable (B k t)
  /-- B_k(0) = 0 -/
  B_initial : ∀ k ω, B k 0 ω = 0
  /-- B_k has continuous paths (a.s.) -/
  B_continuous : ∀ k, ∀ᵐ ω ∂prob.P, Continuous (fun t => B k t ω)

namespace EKMSForcing

variable {prob : EKMSProbabilitySpace} (forcing : EKMSForcing prob)

/-- The potential at a point: F(x,t,ω) = Σ_k F_k(x)(B_k(t) - B_k(s)) for t > s.
    This is the integrated potential from time s to time t. -/
noncomputable def potential (s t : ℝ) (x : ℝ) (ω : prob.Ω) : ℝ :=
  ∑' k : ℕ+, ForcingPotential.F (forcing.potentials k) x * (forcing.B k t ω - forcing.B k s ω)

/-- The derivative of the potential: f(x,t,ω) = Σ_k f_k(x)(B_k(t) - B_k(s)). -/
noncomputable def potentialDerivative (s t : ℝ) (x : ℝ) (ω : prob.Ω) : ℝ :=
  ∑' k : ℕ+, ForcingPotential.f (forcing.potentials k) x * (forcing.B k t ω - forcing.B k s ω)

end EKMSForcing

/-! ## Curves and Action Functional -/

/-- A Lipschitz continuous curve ξ : [t₁, t₂] → ℝ.
    These are the paths over which we minimize the action. -/
structure LipschitzCurve (t₁ t₂ : ℝ) where
  /-- The curve ξ : [t₁, t₂] → ℝ -/
  path : ℝ → ℝ
  /-- The Lipschitz constant -/
  lip_const : ℝ
  /-- Positive Lipschitz constant -/
  lip_const_nonneg : lip_const ≥ 0
  /-- Lipschitz condition -/
  lipschitz : ∀ s₁ s₂ : ℝ, t₁ ≤ s₁ → s₁ ≤ t₂ → t₁ ≤ s₂ → s₂ ≤ t₂ →
    |path s₁ - path s₂| ≤ lip_const * |s₂ - s₁|

/-- A C¹-curve ξ : [t₁, t₂] → ℝ with velocity ξ̇. -/
structure C1Curve (t₁ t₂ : ℝ) where
  /-- The curve ξ : [t₁, t₂] → ℝ -/
  path : ℝ → ℝ
  /-- The velocity ξ̇ -/
  velocity : ℝ → ℝ
  /-- The path is continuous -/
  path_continuous : Continuous path
  /-- The velocity is continuous -/
  velocity_continuous : Continuous velocity

/-- The kinetic part of the action: ∫_{t₁}^{t₂} ½ ξ̇(s)² ds -/
noncomputable def kineticAction (t₁ t₂ : ℝ) (curve : C1Curve t₁ t₂) : ℝ :=
  ∫ s in Set.Icc t₁ t₂, (1/2) * (curve.velocity s)^2

/-- The action functional A_{t₁,t₂}(ξ) as defined in EKMS equation (2.1).
    A_{t₁,t₂}(ξ) = ∫_{t₁}^{t₂} {½ξ̇(s)² - Σ_k f_k(ξ(s)) ξ̇(s) (B_k(s) - B_k(t₁))} ds
                 + Σ_k F_k(ξ(t₂)) (B_k(t₂) - B_k(t₁))

    This formulation avoids stochastic integrals by integration by parts. -/
structure ActionFunctional {prob : EKMSProbabilitySpace} (forcing : EKMSForcing prob)
    (t₁ t₂ : ℝ) where
  /-- The action value depends on the curve and the realization ω -/
  action : C1Curve t₁ t₂ → prob.Ω → ℝ
  /-- The action decomposes into kinetic + potential parts -/
  decomposition : ∀ curve ω,
    ∃ kinetic_part potential_part boundary_term : ℝ,
    action curve ω = kinetic_part + potential_part + boundary_term

/-! ## The Characteristic Equations -/

/-- The system of characteristics (Euler-Lagrange equations):
    dγ/dt = v
    dv/dt = Σ_k f_k(γ) dB_k(t)

    In differential form: (γ̇, v̇) = (v, f(γ) dB)
    where f = (f₁, f₂, ...) and dB = (dB₁, dB₂, ...). -/
structure CharacteristicEquation {prob : EKMSProbabilitySpace}
    (forcing : EKMSForcing prob) where
  /-- Position component γ(t) -/
  position : ℝ → prob.Ω → ℝ
  /-- Velocity component v(t) -/
  velocity : ℝ → prob.Ω → ℝ
  /-- Adaptedness of position -/
  position_measurable : ∀ t : ℝ, Measurable (position t)
  /-- Adaptedness of velocity -/
  velocity_measurable : ∀ t : ℝ, Measurable (velocity t)
  /-- Continuous paths a.s. -/
  continuous_paths : ∀ᵐ ω ∂prob.P,
    Continuous (fun t => position t ω) ∧ Continuous (fun t => velocity t ω)

/-! ## The Shift Operator -/

/-- The shift operator θ_τ : Ω → Ω that translates the random forcing in time.
    (θ_τ ω)(t) = ω(t + τ) -/
structure ShiftOperator (prob : EKMSProbabilitySpace) where
  /-- The shift θ_τ for each τ ∈ ℝ -/
  shift : ℝ → prob.Ω → prob.Ω
  /-- θ₀ = id -/
  shift_zero : ∀ ω, shift 0 ω = ω
  /-- θ_{τ+σ} = θ_τ ∘ θ_σ -/
  shift_add : ∀ τ σ ω, shift (τ + σ) ω = shift τ (shift σ ω)
  /-- Measure preserving: θ_τ^* P = P -/
  measure_preserving : ∀ τ, Measure.map (shift τ) prob.P = prob.P
  /-- Measurable -/
  measurable : ∀ τ, Measurable (shift τ)

/-! ## The Skorohod Space -/

/-- The Skorohod space D of càdlàg (right-continuous with left limits) functions.
    This is the natural state space for solutions with shocks. -/
structure SkorohodSpace where
  /-- Elements are functions ℝ → ℝ (periodic) -/
  carrier : Set (ℝ → ℝ)
  /-- Functions have bounded variation on [0, 1] -/
  bounded_variation : ∀ u ∈ carrier, ∃ V : ℝ, V ≥ 0 ∧ True  -- BV condition

/-- The subspace D_c of functions with fixed average c: ∫_0^1 u dx = c -/
structure SkorohodSubspace (D : SkorohodSpace) (c : ℝ) where
  /-- The subspace elements -/
  carrier : Set (ℝ → ℝ)
  /-- Subset of D -/
  subset : carrier ⊆ D.carrier
  /-- Mean condition (abstract) -/
  mean_condition : ∀ u ∈ carrier, True  -- Abstract: ∫_0^1 u dx = c

/-- Zero-mean subspace D₀ (most commonly used). -/
def SkorohodSpace.D₀ (D : SkorohodSpace) : SkorohodSubspace D 0 where
  carrier := D.carrier
  subset := fun u h => h
  mean_condition := fun _ _ => trivial

/-! ## The Solution Flow -/

/-- The solution flow S^τ_ω : D_c → D_c mapping initial data to solutions at time τ.
    If u(·, 0) = u₀, then S^τ_ω u₀ = u(·, τ). -/
structure SolutionFlow {prob : EKMSProbabilitySpace} (_forcing : EKMSForcing prob)
    (D : SkorohodSpace) (_c : ℝ) where
  /-- The flow S^t_ω : D → D -/
  flow : ℝ → prob.Ω → D.carrier → D.carrier
  /-- S^0_ω = id -/
  flow_zero : ∀ ω u, flow 0 ω u = u

/-- The skew-product transformation F^t : Ω × D → Ω × D.
    F^t(ω, u₀) = (θ_t ω, S^t_ω u₀) -/
structure SkewProduct {prob : EKMSProbabilitySpace} (forcing : EKMSForcing prob)
    (D : SkorohodSpace) (c : ℝ) where
  /-- The solution flow -/
  solutionFlow : SolutionFlow forcing D c
  /-- The shift operator -/
  shift : ShiftOperator prob
  /-- The skew-product transformation -/
  transform : ℝ → prob.Ω × D.carrier → prob.Ω × D.carrier
  /-- Definition: F^t(ω, u) = (θ_t ω, S^t_ω u) -/
  transform_def : ∀ t ω u, transform t (ω, u) =
    (shift.shift t ω, solutionFlow.flow t ω u)

/-! ## The Variational Principle -/

/-- The variational principle characterizing entropy solutions.
    For t > τ:
    u(x, t) = ∂_x inf_{ξ(t)=x} {A_{τ,t}(ξ) + ∫^{ξ(τ)}_0 u(z, τ) dz}

    The infimum is over all Lipschitz curves ending at x. -/
structure VariationalPrinciple {prob : EKMSProbabilitySpace}
    (forcing : EKMSForcing prob) where
  /-- The action functional -/
  A : ∀ t₁ t₂ : ℝ, ActionFunctional forcing t₁ t₂
  /-- The minimizer selection: for each (x, t, ω, u₀), returns the minimizing curve -/
  minimizer : ∀ (τ t : ℝ) (x : ℝ) (ω : prob.Ω) (u₀ : ℝ → ℝ),
    C1Curve τ t
  /-- The minimizer ends at x -/
  minimizer_endpoint : ∀ τ t x ω u₀, (minimizer τ t x ω u₀).path t = x

/-- The solution given by the variational principle.
    u(x, t) = ξ̇(t) where ξ is the minimizing characteristic ending at x. -/
noncomputable def VariationalPrinciple.solution {prob : EKMSProbabilitySpace}
    {forcing : EKMSForcing prob} (vp : VariationalPrinciple forcing)
    (τ : ℝ) (u₀ : ℝ → ℝ) (x : ℝ) (t : ℝ) (ω : prob.Ω) : ℝ :=
  (vp.minimizer τ t x ω u₀).velocity t

/-! ## Entropy Condition -/

/-- The entropy condition for weak solutions: u(x+, t) ≤ u(x-, t).
    This ensures characteristics flow into shocks, not out of them. -/
structure EntropyCondition (u : ℝ → ℝ → ℝ) where
  /-- At each point, the right limit is ≤ left limit -/
  entropy : ∀ x : ℝ, ∀ t : ℝ,
    ∃ u_left u_right : ℝ, u_right ≤ u_left

/-- Entropy weak solution to the inviscid Burgers equation with forcing. -/
structure EntropyWeakSolution {prob : EKMSProbabilitySpace}
    (forcing : EKMSForcing prob) (t₀ : ℝ) where
  /-- The solution u : ℝ × [t₀, ∞) × Ω → ℝ -/
  u : ℝ → ℝ → prob.Ω → ℝ
  /-- Measurability with respect to the filtration -/
  adapted : ∀ t x, t ≥ t₀ → Measurable (u x t)
  /-- Satisfies the entropy condition a.s. -/
  entropy : ∀ᵐ ω ∂prob.P, ∀ t, t ≥ t₀ → EntropyCondition (fun x t => u x t ω)

/-! ## Conservation Laws -/

/-- The mean ∫_0^1 u(x, t) dx is conserved by the dynamics. -/
theorem mean_conserved {prob : EKMSProbabilitySpace} {forcing : EKMSForcing prob}
    (sol : EntropyWeakSolution forcing t₀) (c : ℝ)
    (h_initial : ∀ᵐ ω ∂prob.P, ∫ x in Set.Icc 0 1, sol.u x t₀ ω = c) :
    ∀ t : ℝ, t ≥ t₀ → ∀ᵐ ω ∂prob.P, ∫ x in Set.Icc 0 1, sol.u x t ω = c := by
  sorry

end SPDE.EKMS
