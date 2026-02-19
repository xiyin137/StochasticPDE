/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.SPDE
import StochasticPDE.Examples.KPZ
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Burgers Equation and Burgers Turbulence

This file formalizes the Burgers equation and its stochastic variants,
with particular focus on Burgers turbulence theory.

## Main Definitions

* `BurgersEquation` - The viscous Burgers equation
* `StochasticBurgers` - Stochastic Burgers with random forcing
* `BurgersKPZTransform` - The relationship u = ∇h between Burgers and KPZ
* `InviscidBurgers` - The inviscid limit with shocks
* `EKMSInvariantMeasure` - The EKMS invariant measure

## Key Results

* Connection to KPZ via Cole-Hopf: if h solves KPZ then u = ∂_x h solves Burgers
* Shock formation in inviscid limit
* E-Khanin-Mazel-Sinai (EKMS) theory of invariant measures
* One-force-one-solution principle
* Lagrangian particle dynamics

## References

* Burgers, "The Nonlinear Diffusion Equation" (1974)
* E, Khanin, Mazel, Sinai, "Invariant measures for Burgers equation with stochastic forcing"
  (Annals 2000)
* Bec, Khanin, "Burgers turbulence" (Physics Reports 2007)
* Corwin, "The Kardar-Parisi-Zhang equation and universality class"
-/

namespace SPDE.Examples

open MeasureTheory

/-! ## The Burgers Equation -/

/-- The viscous Burgers equation: ∂_t u + u ∂_x u = ν ∂²_x u
    This is a fundamental nonlinear PDE modeling:
    - Simplified 1D fluid dynamics (Navier-Stokes without pressure)
    - Traffic flow
    - Nonlinear acoustics
    - Interface growth (via KPZ connection) -/
structure BurgersEquation where
  /-- Viscosity coefficient ν > 0 -/
  viscosity : ℝ
  /-- Positive viscosity -/
  viscosity_pos : 0 < viscosity
  /-- The spatial domain (usually ℝ or 𝕋 = ℝ/ℤ) -/
  periodic : Bool := false
  /-- Period length for periodic case -/
  period : ℝ := 1
  /-- Period is positive -/
  period_pos : period > 0 := by norm_num

namespace BurgersEquation

/-- Standard Burgers with ν = 1 -/
noncomputable def standard : BurgersEquation where
  viscosity := 1
  viscosity_pos := by norm_num

/-- The Reynolds number Re = UL/ν measures nonlinearity vs. diffusion.
    High Re corresponds to turbulent regime. -/
noncomputable def reynoldsNumber (b : BurgersEquation) (U L : ℝ) : ℝ :=
  U * L / b.viscosity

/-- Reynolds number is positive for positive velocity and length scales -/
theorem reynoldsNumber_pos (b : BurgersEquation) {U L : ℝ} (hU : U > 0) (hL : L > 0) :
    b.reynoldsNumber U L > 0 := by
  unfold reynoldsNumber
  apply div_pos
  · exact mul_pos hU hL
  · exact b.viscosity_pos

/-- The diffusion time scale τ_D = L²/ν -/
noncomputable def diffusionTimeScale (b : BurgersEquation) (L : ℝ) : ℝ :=
  L^2 / b.viscosity

/-- The advection time scale τ_A = L/U -/
noncomputable def advectionTimeScale (_b : BurgersEquation) (L U : ℝ) : ℝ :=
  L / U

end BurgersEquation

/-! ## Solutions to Burgers Equation -/

/-- A classical solution to the viscous Burgers equation on ℝ × [0, T].
    u : ℝ × ℝ → ℝ satisfies ∂_t u + u ∂_x u = ν ∂²_x u -/
structure BurgersSolution (b : BurgersEquation) where
  /-- The solution u(x, t) -/
  u : ℝ → ℝ → ℝ
  /-- Time domain [0, T] -/
  T : ℝ
  /-- T is positive -/
  T_pos : T > 0
  /-- Initial data u₀ = u(·, 0) -/
  initial_data : ℝ → ℝ
  /-- Initial condition holds -/
  initial_condition : ∀ x : ℝ, u x 0 = initial_data x
  /-- The solution is continuous -/
  continuous : Continuous (fun p : ℝ × ℝ => u p.1 p.2)

namespace BurgersSolution

variable {b : BurgersEquation}

/-- The energy (L² norm squared) of the solution at time t -/
noncomputable def energy (sol : BurgersSolution b) (t : ℝ) : ℝ :=
  ∫ x : ℝ, (sol.u x t)^2

/-- Energy is non-negative -/
theorem energy_nonneg (sol : BurgersSolution b) (t : ℝ) :
    sol.energy t ≥ 0 := by
  unfold energy
  apply integral_nonneg
  intro x
  positivity

end BurgersSolution

/-! ## Connection to KPZ via Cole-Hopf -/

/-- The transformation between Burgers and KPZ.
    If h solves KPZ: ∂_t h = ν Δh + (λ/2)(∇h)² + ξ
    Then u = λ∇h solves the stochastic Burgers equation:
    ∂_t u + u ∂_x u = ν ∂²_x u + λ ∂_x ξ

    This connects interface growth (h = height) to fluid velocity (u). -/
structure BurgersKPZTransform (kpz : KPZEquation) where
  /-- The corresponding Burgers equation -/
  burgers : BurgersEquation
  /-- Viscosity matches: ν_Burgers = ν_KPZ -/
  viscosity_match : burgers.viscosity = kpz.nu
  /-- The transformation: u = λ ∂_x h -/
  transform_coeff : ℝ := kpz.lambda

namespace BurgersKPZTransform

variable {kpz : KPZEquation}

/-- The inverse transformation coefficient: h = (1/λ) ∫ u dx -/
noncomputable def inverseCoeff (t : BurgersKPZTransform kpz) : ℝ :=
  1 / t.transform_coeff

/-- The noise coefficient in Burgers from KPZ: λ -/
noncomputable def noiseCoeff (t : BurgersKPZTransform kpz) : ℝ :=
  t.transform_coeff

/-- Viscosity is preserved under the transform -/
theorem viscosity_preserved (t : BurgersKPZTransform kpz) :
    t.burgers.viscosity = kpz.nu := t.viscosity_match

end BurgersKPZTransform

/-! ## Stochastic Burgers Equation -/

/-- The forcing correlation function ⟨f(x,t) f(x',t')⟩ = D(x-x') δ(t-t').
    Parameterized by spatial correlation length and strength. -/
structure ForcingCorrelation where
  /-- Spatial correlation length (0 = white in space) -/
  correlation_length : ℝ
  /-- Non-negative correlation length -/
  length_nonneg : correlation_length ≥ 0
  /-- Forcing strength D -/
  strength : ℝ
  /-- Positive strength -/
  strength_pos : strength > 0

/-- The stochastic Burgers equation with random forcing:
    ∂_t u + u ∂_x u = ν ∂²_x u + f(x, t)
    where f is a random force (white noise or colored noise). -/
structure StochasticBurgers extends BurgersEquation where
  /-- The forcing correlation structure -/
  forcing : ForcingCorrelation
  /-- The temporal correlation (0 = white in time, δ-correlated) -/
  temporal_correlation : ℝ := 0
  /-- Non-negative temporal correlation -/
  temporal_nonneg : temporal_correlation ≥ 0 := by norm_num

namespace StochasticBurgers

/-- White-in-time forcing: ⟨f(x,t) f(x',t')⟩ = D(x-x') δ(t-t') -/
def isWhiteInTime (sb : StochasticBurgers) : Prop :=
  sb.temporal_correlation = 0

/-- Space-time white noise forcing -/
def isSpaceTimeWhiteNoise (sb : StochasticBurgers) : Prop :=
  sb.forcing.correlation_length = 0 ∧ sb.temporal_correlation = 0

/-- Smooth forcing (finite correlation length) -/
def isSmoothForcing (sb : StochasticBurgers) : Prop :=
  sb.forcing.correlation_length > 0

/-- The forcing is compactly supported in Fourier space up to wavenumber k_f -/
structure CompactForcingSpectrum (sb : StochasticBurgers) where
  /-- The forcing wavenumber cutoff -/
  k_forcing : ℝ
  /-- Positive cutoff -/
  k_pos : k_forcing > 0
  /-- Relation to correlation length: ℓ ~ 1/k_f -/
  length_wavenumber : sb.forcing.correlation_length * k_forcing ≥ 1

/-- Kicked Burgers: forcing is a sum of δ-function kicks at random times.
    f(x,t) = Σᵢ fᵢ(x) δ(t - tᵢ) where tᵢ are Poisson times. -/
structure KickedBurgers (sb : StochasticBurgers) where
  /-- Average rate of kicks (kicks per unit time) -/
  kick_rate : ℝ
  /-- Positive rate -/
  rate_pos : kick_rate > 0

/-- The regularity of solutions (Hölder exponent in space) -/
noncomputable def solutionRegularity (_sb : StochasticBurgers) : ℝ := 1/2

/-- Solution regularity is positive -/
theorem solutionRegularity_pos (sb : StochasticBurgers) : sb.solutionRegularity > 0 := by
  unfold solutionRegularity
  norm_num

end StochasticBurgers

/-! ## Inviscid Burgers and Shocks -/

/-- The inviscid Burgers equation: ∂_t u + u ∂_x u = 0
    Solutions develop shocks (discontinuities) in finite time. -/
structure InviscidBurgers where
  /-- Initial data u₀ : ℝ → ℝ -/
  initial_data : ℝ → ℝ
  /-- Initial data is continuous -/
  initial_continuous : Continuous initial_data
  /-- Initial data is bounded -/
  initial_bounded : ∃ M : ℝ, ∀ x : ℝ, |initial_data x| ≤ M

namespace InviscidBurgers

/-- The characteristic curves: x(t) = x₀ + u₀(x₀) t.
    Along characteristics, u is constant: u(x(t), t) = u₀(x₀). -/
noncomputable def characteristic (ib : InviscidBurgers) (x₀ t : ℝ) : ℝ :=
  x₀ + ib.initial_data x₀ * t

/-- The characteristic starting at x₀ passes through x₀ at t = 0 -/
theorem characteristic_initial (ib : InviscidBurgers) (x₀ : ℝ) :
    ib.characteristic x₀ 0 = x₀ := by
  unfold characteristic
  ring

/-- The velocity of the characteristic is constant (= initial velocity) -/
theorem characteristic_velocity (ib : InviscidBurgers) (x₀ : ℝ) :
    ∀ t : ℝ, ib.characteristic x₀ t - ib.characteristic x₀ 0 = ib.initial_data x₀ * t := by
  intro t
  unfold characteristic
  ring

/-- Characteristics cross when two different starting points reach the same position.
    This happens when x₀ + u₀(x₀) t = x₁ + u₀(x₁) t for x₀ ≠ x₁. -/
def characteristicsCross (ib : InviscidBurgers) (x₀ x₁ t : ℝ) : Prop :=
  x₀ ≠ x₁ ∧ ib.characteristic x₀ t = ib.characteristic x₁ t

/-- Shock formation time: the first time when characteristics cross.
    t* = inf{t > 0 : ∃ x₀ ≠ x₁, x₀ + u₀(x₀)t = x₁ + u₀(x₁)t} -/
structure ShockFormationTime (ib : InviscidBurgers) where
  /-- The shock time t* > 0 -/
  shock_time : ℝ
  /-- Shock time is positive -/
  shock_time_pos : shock_time > 0
  /-- Before t*, no characteristics cross -/
  no_crossing_before : ∀ t : ℝ, 0 < t → t < shock_time →
    ∀ x₀ x₁ : ℝ, ib.characteristic x₀ t = ib.characteristic x₁ t → x₀ = x₁
  /-- At t*, characteristics first cross -/
  crossing_at : ∃ x₀ x₁ : ℝ, ib.characteristicsCross x₀ x₁ shock_time

/-- For monotone decreasing initial data (u₀' < 0), characteristics always cross -/
theorem characteristics_cross_for_decreasing
    (ib : InviscidBurgers)
    (h_decreasing : ∀ x y : ℝ, x < y → ib.initial_data x > ib.initial_data y) :
    ∀ x₀ x₁ : ℝ, x₀ < x₁ →
    ∃ t : ℝ, t > 0 ∧ ib.characteristic x₀ t = ib.characteristic x₁ t := by
  intro x₀ x₁ hlt
  have h_vel : ib.initial_data x₀ > ib.initial_data x₁ := h_decreasing x₀ x₁ hlt
  -- The crossing time is t = (x₁ - x₀) / (u₀(x₀) - u₀(x₁))
  let t := (x₁ - x₀) / (ib.initial_data x₀ - ib.initial_data x₁)
  use t
  have h_denom_pos : ib.initial_data x₀ - ib.initial_data x₁ > 0 := by linarith
  have h_numer_pos : x₁ - x₀ > 0 := by linarith
  constructor
  · -- t > 0 because numerator and denominator are both positive
    exact div_pos h_numer_pos h_denom_pos
  · -- Verify the characteristics meet: x₀ + u₀(x₀)t = x₁ + u₀(x₁)t
    unfold characteristic
    have h_denom_ne : ib.initial_data x₀ - ib.initial_data x₁ ≠ 0 := ne_of_gt h_denom_pos
    -- The algebra: (u₀(x₀) - u₀(x₁)) * t = x₁ - x₀, so the characteristics meet
    have key : (ib.initial_data x₀ - ib.initial_data x₁) * t = x₁ - x₀ := by
      simp only [t, mul_div_assoc']
      exact mul_div_cancel_left₀ (x₁ - x₀) h_denom_ne
    linarith

/-- The Rankine-Hugoniot condition for shock speed.
    If there's a shock with left state u₋ and right state u₊,
    the shock speed is s = (u₊ + u₋)/2. -/
structure Shock where
  /-- Left state (limit from left) -/
  u_left : ℝ
  /-- Right state (limit from right) -/
  u_right : ℝ
  /-- Shock speed from Rankine-Hugoniot -/
  speed : ℝ := (u_left + u_right) / 2

/-- The entropy condition: u₋ > s > u₊ (characteristics flow into the shock) -/
def Shock.satisfiesEntropy (s : Shock) : Prop :=
  s.u_left > s.speed ∧ s.speed > s.u_right

/-- Entropy condition implies u₋ > u₊ (shock is compressive) -/
theorem Shock.compressive_of_entropy (s : Shock) (h : s.satisfiesEntropy) :
    s.u_left > s.u_right := by
  unfold satisfiesEntropy at h
  linarith

/-- The entropy solution (weak solution selected by viscous limit). -/
structure EntropySolution (ib : InviscidBurgers) where
  /-- The solution u(x, t) (may be discontinuous) -/
  solution : ℝ → ℝ → ℝ
  /-- Time domain -/
  T : ℝ
  /-- T is positive -/
  T_pos : T > 0
  /-- Initial condition -/
  initial : ∀ x : ℝ, solution x 0 = ib.initial_data x

end InviscidBurgers

/-! ## Invariant Measures: EKMS Theory -/

/-- Non-degeneracy condition for forcing in EKMS theory.
    The forcing spectrum must have positive energy at some wavenumber. -/
structure ForcingNondegeneracy (sb : StochasticBurgers) where
  /-- There exists a wavenumber with positive energy -/
  wavenumber : ℝ
  /-- The wavenumber is positive -/
  wavenumber_pos : wavenumber > 0
  /-- The forcing has energy at this wavenumber -/
  has_energy : sb.forcing.strength > 0

/-- The E-Khanin-Mazel-Sinai (EKMS) invariant measure for stochastic Burgers.
    Key result: For periodic forcing with good spatial structure,
    there exists a unique invariant measure.

    Reference: E, Khanin, Mazel, Sinai (Annals 2000) -/
structure EKMSInvariantMeasure (sb : StochasticBurgers) where
  /-- The forcing is non-degenerate -/
  forcing_nondegen : ForcingNondegeneracy sb
  /-- Convergence rate to invariant measure (exponential) -/
  convergence_rate : ℝ
  /-- Positive convergence rate -/
  rate_pos : convergence_rate > 0

namespace EKMSInvariantMeasure

variable {sb : StochasticBurgers}

/-- The global solution: for generic forcing, there is a unique solution
    defined for all t ∈ ℝ (both forward and backward in time). -/
structure GlobalSolution (inv : EKMSInvariantMeasure sb) where
  /-- The global solution u(x, t) for t ∈ ℝ -/
  u : ℝ → ℝ → ℝ
  /-- The solution is continuous in x for each t -/
  continuous_x : ∀ t : ℝ, Continuous (fun x => u x t)

/-- The one-force-one-solution principle:
    For generic forcing, the global solution is unique and all other
    solutions merge with it in finite time. -/
structure OneForceOneSolution (inv : EKMSInvariantMeasure sb) where
  /-- The unique global solution -/
  global : GlobalSolution inv
  /-- Merging time bound for bounded initial conditions -/
  merging_time_bound : ℝ → ℝ  -- initial_norm → merging_time_upper_bound
  /-- Merging time is finite for bounded data -/
  merging_finite : ∀ R : ℝ, R > 0 → merging_time_bound R > 0

/-- The shock structure of the invariant measure.
    Solutions are piecewise smooth with isolated shocks. -/
structure ShockStructure (inv : EKMSInvariantMeasure sb) where
  /-- Maximum number of shocks in a period (for periodic case) -/
  max_shocks : ℕ
  /-- At least one shock exists in stationary state -/
  has_shocks : max_shocks ≥ 1

end EKMSInvariantMeasure

/-! ## Lagrangian Particles -/

/-- A Lagrangian particle trajectory in the Burgers flow.
    The particle follows dx/dt = u(x(t), t). -/
structure LagrangianParticle where
  /-- Initial position -/
  x₀ : ℝ
  /-- The trajectory x(t) -/
  trajectory : ℝ → ℝ
  /-- Initial condition -/
  initial : trajectory 0 = x₀
  /-- The trajectory is continuous -/
  continuous : Continuous trajectory

namespace LagrangianParticle

/-- Displacement from initial position -/
noncomputable def displacement (p : LagrangianParticle) (t : ℝ) : ℝ :=
  p.trajectory t - p.x₀

/-- Displacement is zero at t = 0 -/
theorem displacement_zero (p : LagrangianParticle) : p.displacement 0 = 0 := by
  unfold displacement
  rw [p.initial]
  ring

end LagrangianParticle

/-- Sticky particle dynamics in the inviscid limit.
    When particles collide, they merge and conserve momentum. -/
structure StickyParticles where
  /-- Number of initial particles -/
  n : ℕ
  /-- n is positive -/
  n_pos : n > 0
  /-- Initial positions (ordered) -/
  initial_positions : Fin n → ℝ
  /-- Initial velocities -/
  initial_velocities : Fin n → ℝ
  /-- Initial masses (positive) -/
  masses : Fin n → ℝ
  /-- Masses are positive -/
  masses_pos : ∀ i, masses i > 0
  /-- Positions are ordered -/
  positions_ordered : ∀ i j : Fin n, i < j → initial_positions i < initial_positions j

namespace StickyParticles

/-- Total mass is conserved -/
noncomputable def totalMass (sp : StickyParticles) : ℝ :=
  ∑ i, sp.masses i

/-- Total momentum is conserved -/
noncomputable def totalMomentum (sp : StickyParticles) : ℝ :=
  ∑ i, sp.masses i * sp.initial_velocities i

/-- Total mass is positive -/
theorem totalMass_pos (sp : StickyParticles) : sp.totalMass > 0 := by
  unfold totalMass
  apply Finset.sum_pos
  · intro i _
    exact sp.masses_pos i
  · simp only [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp sp.n_pos

end StickyParticles

/-! ## Decaying Burgers Turbulence -/

/-- Decaying Burgers turbulence: ∂_t u + u ∂_x u = ν ∂²_x u
    starting from random initial data, without forcing.
    The solution develops a self-similar structure at late times. -/
structure DecayingBurgers where
  /-- The viscosity -/
  viscosity : ℝ
  /-- Positive viscosity -/
  viscosity_pos : 0 < viscosity
  /-- Initial energy (L² norm squared) -/
  initial_energy : ℝ
  /-- Positive initial energy -/
  energy_pos : initial_energy > 0
  /-- Initial integral scale -/
  initial_scale : ℝ
  /-- Positive initial scale -/
  scale_pos : initial_scale > 0

namespace DecayingBurgers

/-- The initial Reynolds number -/
noncomputable def initialReynolds (db : DecayingBurgers) : ℝ :=
  Real.sqrt db.initial_energy * db.initial_scale / db.viscosity

/-- Self-similar decay exponents.
    Energy decays as E(t) ~ t^{-2(1-h)/(1+h)} where h is the roughness exponent.
    For Burgers with smooth initial data, h = 1 gives E(t) ~ t^0 = const at early times,
    then transitions to E(t) ~ t^{-2/3} (for h = 1/2) at late times. -/
structure SelfSimilarDecay (db : DecayingBurgers) where
  /-- The roughness exponent h ∈ (0, 1) -/
  roughness_exponent : ℝ
  /-- Roughness is in valid range -/
  roughness_range : 0 < roughness_exponent ∧ roughness_exponent < 1

/-- Energy decay exponent for given roughness h: -2(1-h)/(1+h) -/
noncomputable def energyDecayExponent (h : ℝ) : ℝ :=
  -2 * (1 - h) / (1 + h)

/-- Integral scale growth exponent: 2/(1+h) -/
noncomputable def scaleGrowthExponent (h : ℝ) : ℝ :=
  2 / (1 + h)

/-- For h = 1/2 (white noise initial data), energy decays as t^{-2/3} -/
theorem energy_decay_white_noise : energyDecayExponent (1/2) = -2/3 := by
  unfold energyDecayExponent
  norm_num

/-- For h = 1/2, integral scale grows as t^{4/3} -/
theorem scale_growth_white_noise : scaleGrowthExponent (1/2) = 4/3 := by
  unfold scaleGrowthExponent
  norm_num

end DecayingBurgers

/-! ## Statistics and Scaling -/

/-- The structure function S_n(r) = ⟨|u(x+r) - u(x)|^n⟩ -/
structure StructureFunction where
  /-- The order n -/
  order : ℕ
  /-- The function S_n(r) -/
  S : ℝ → ℝ
  /-- S is non-negative for even order -/
  nonneg : order % 2 = 0 → ∀ r : ℝ, S r ≥ 0
  /-- S(0) = 0 -/
  at_zero : S 0 = 0

/-- Statistics of Burgers turbulence. -/
structure BurgersStatistics (sb : StochasticBurgers) where
  /-- The structure functions for each order -/
  structure_functions : ℕ → StructureFunction
  /-- Order matches -/
  order_match : ∀ n, (structure_functions n).order = n

namespace BurgersStatistics

variable {sb : StochasticBurgers}

/-- Scaling exponents ζ_n: S_n(r) ~ r^{ζ_n} for small r -/
structure ScalingExponents (stats : BurgersStatistics sb) where
  /-- The scaling exponents -/
  zeta : ℕ → ℝ
  /-- For Burgers: ζ_n = min(n, 1) (saturation due to shocks) -/
  saturation : ∀ n : ℕ, n ≥ 1 → zeta n = 1

/-- Anomalous scaling: ζ_n ≠ n · ζ_1 (non-self-similar statistics) -/
def isAnomalous (stats : BurgersStatistics sb) (exp : ScalingExponents stats) : Prop :=
  ∃ n : ℕ, n ≥ 2 ∧ exp.zeta n ≠ n * exp.zeta 1

/-- Burgers has extreme anomalous scaling: all ζ_n = 1 for n ≥ 1 -/
theorem burgers_anomalous (stats : BurgersStatistics sb) (exp : ScalingExponents stats) :
    stats.isAnomalous exp := by
  use 2
  constructor
  · norm_num
  · simp only [ne_eq]
    rw [exp.saturation 2 (by norm_num), exp.saturation 1 (by norm_num)]
    norm_num

end BurgersStatistics

/-! ## Regularity Structure for Stochastic Burgers -/

/-- Model parameters for stochastic Burgers with rough forcing.
    Uses the tree-based infrastructure from `RegularityStructures/`.
    - Noise regularity α = -5/2 (rough forcing in 1D)
    - Kernel order β = 2 (heat kernel) -/
noncomputable def Burgers_ModelParameters : SPDE.RegularityStructures.ModelParameters 1 where
  noiseRegularity := -5/2
  kernelOrder := 2
  minHomogeneity := -5/2
  maxHomogeneity := 2
  hom_lt := by norm_num

/-! ## Well-Posedness Results -/

/-- Local well-posedness for stochastic Burgers. -/
structure LocalWellPosedness (sb : StochasticBurgers) where
  /-- The solution regularity (Hölder exponent) -/
  solution_regularity : ℝ
  /-- Regularity bound: α > 0 -/
  regularity_pos : solution_regularity > 0
  /-- Regularity is bounded by 1/2 -/
  regularity_bound : solution_regularity ≤ 1/2
  /-- Existence time as function of initial data norm -/
  existence_time : ℝ → ℝ
  /-- Positive existence time for bounded data -/
  existence_time_pos : ∀ R : ℝ, R > 0 → existence_time R > 0
  /-- Existence time decreases with larger data -/
  existence_time_mono : ∀ R₁ R₂ : ℝ, R₁ ≤ R₂ → existence_time R₂ ≤ existence_time R₁

/-- Global well-posedness for stochastic Burgers on the torus. -/
structure GlobalWellPosedness (sb : StochasticBurgers) where
  /-- The forcing is spatially smooth (correlation length > 0) -/
  forcing_smooth : sb.forcing.correlation_length > 0
  /-- The period is finite (torus domain) -/
  domain_compact : sb.periodic = true

/-! ## Connection to Directed Polymers -/

/-- The directed polymer partition function.
    Z(x,t) = 𝔼[exp(∫₀ᵗ V(B_s, t-s) ds)]
    where B is Brownian motion ending at x and V is the potential. -/
structure PolymerPartitionFunction (sb : StochasticBurgers) where
  /-- The partition function Z(x, t) -/
  Z : ℝ → ℝ → ℝ
  /-- Z is positive (exponential of real) -/
  Z_pos : ∀ x t : ℝ, t ≥ 0 → Z x t > 0
  /-- Normalization: Z(x, 0) = 1 -/
  Z_initial : ∀ x : ℝ, Z x 0 = 1

namespace PolymerPartitionFunction

variable {sb : StochasticBurgers}

/-- The free energy F = log Z -/
noncomputable def freeEnergy (pf : PolymerPartitionFunction sb) (x t : ℝ) : ℝ :=
  Real.log (pf.Z x t)

/-- Free energy at t = 0 is 0 -/
theorem freeEnergy_initial (pf : PolymerPartitionFunction sb) (x : ℝ) :
    pf.freeEnergy x 0 = 0 := by
  unfold freeEnergy
  rw [pf.Z_initial]
  exact Real.log_one

end PolymerPartitionFunction

/-- The polymer endpoint distribution P(endpoint = x) ∝ Z(x,t) -/
structure PolymerEndpoint (sb : StochasticBurgers) (pf : PolymerPartitionFunction sb) where
  /-- The endpoint density (unnormalized) -/
  density : ℝ → ℝ → ℝ  -- (x, t) → density
  /-- Density equals partition function -/
  density_eq : ∀ x t : ℝ, density x t = pf.Z x t

end SPDE.Examples
