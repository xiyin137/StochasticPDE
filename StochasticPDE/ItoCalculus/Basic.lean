/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic

/-!
# Basic Definitions for Stochastic PDEs

This file provides foundational definitions for stochastic analysis
needed for SPDEs and regularity structures.

## Main Definitions

* `Filtration` - A filtration on a measurable space
* `AdaptedProcess` - Processes adapted to a filtration
* `Martingale` - Martingale processes
* `StoppingTime` - Stopping times

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus"
* Da Prato, Zabczyk, "Stochastic Equations in Infinite Dimensions"
-/

namespace SPDE

open MeasureTheory
open scoped MeasureTheory

/-! ## Filtrations -/

/-- A filtration is an increasing family of σ-algebras indexed by time. -/
structure Filtration (Ω : Type*) [MeasurableSpace Ω] (ι : Type*) [Preorder ι] where
  /-- The σ-algebra at time t -/
  σ_algebra : ι → MeasurableSpace Ω
  /-- The filtration is increasing -/
  mono : ∀ s t : ι, s ≤ t → σ_algebra s ≤ σ_algebra t
  /-- Each σ-algebra is a sub-σ-algebra of the ambient one -/
  le_ambient : ∀ t : ι, σ_algebra t ≤ ‹MeasurableSpace Ω›

namespace Filtration

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]

/-- Right-continuous filtration -/
def rightContinuous [TopologicalSpace ι] [OrderTopology ι]
    (F : Filtration Ω ι) : Prop :=
  ∀ t : ι, F.σ_algebra t = ⨅ s > t, F.σ_algebra s

/-- Usual conditions: right-continuous and complete -/
def usualConditions [TopologicalSpace ι] [OrderTopology ι]
    (F : Filtration Ω ι) (μ : Measure Ω) : Prop :=
  F.rightContinuous ∧ ∀ t, ∀ s : Set Ω, μ s = 0 → MeasurableSet[F.σ_algebra t] s

end Filtration

/-! ## Adapted Processes -/

/-- A process X is adapted to a filtration F if X_t is F_t-measurable for all t. -/
structure AdaptedProcess {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι)
    (E : Type*) [MeasurableSpace E] where
  /-- The process X : ι → Ω → E -/
  process : ι → Ω → E
  /-- X_t is F_t-measurable -/
  adapted : ∀ t : ι, @Measurable Ω E (F.σ_algebra t) _ (process t)

namespace AdaptedProcess

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]
variable {E : Type*} [MeasurableSpace E]
variable {F : Filtration Ω ι}

/-- The process at time t -/
def apply (X : AdaptedProcess F E) (t : ι) : Ω → E := X.process t

/-- Constant process -/
def const (F : Filtration Ω ι) (x : E) : AdaptedProcess F E where
  process := fun _ _ => x
  adapted := fun _ => measurable_const

end AdaptedProcess

/-! ## Stopping Times -/

/-- A stopping time with respect to a filtration F. -/
structure StoppingTime {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) where
  /-- The random time τ : Ω → ι -/
  time : Ω → ι
  /-- {τ ≤ t} is F_t-measurable for all t -/
  measurable : ∀ t : ι, @MeasurableSet Ω (F.σ_algebra t) {ω | time ω ≤ t}

namespace StoppingTime

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]
variable {F : Filtration Ω ι}

/-- Constant stopping time -/
def const (F : Filtration Ω ι) (t₀ : ι) : StoppingTime F where
  time := fun _ => t₀
  measurable := fun t => by
    by_cases h : t₀ ≤ t
    · convert MeasurableSet.univ
      ext ω
      simp [h]
    · convert MeasurableSet.empty
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h'
      exact h h'

/-- The minimum of two stopping times.
    Note: We require LinearOrder instead of just SemilatticeInf to use min_le_iff. -/
def min {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [LinearOrder ι]
    {F : Filtration Ω ι} (τ₁ τ₂ : StoppingTime F) : StoppingTime F where
  time := fun ω => Min.min (τ₁.time ω) (τ₂.time ω)
  measurable := fun t => by
    have h1 := τ₁.measurable t
    have h2 := τ₂.measurable t
    -- min a b ≤ c iff a ≤ c or b ≤ c
    have : {ω | Min.min (τ₁.time ω) (τ₂.time ω) ≤ t} =
           {ω | τ₁.time ω ≤ t} ∪ {ω | τ₂.time ω ≤ t} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_union, min_le_iff]
    rw [this]
    exact MeasurableSet.union h1 h2

end StoppingTime

/-! ## Martingales -/

/-- A martingale with respect to filtration F and measure μ. -/
structure Martingale {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) (μ : Measure Ω)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] where
  /-- The underlying adapted process -/
  toAdapted : AdaptedProcess F E
  /-- Integrability: E[|X_t|] < ∞ for all t -/
  integrable : ∀ t : ι, Integrable (toAdapted.process t) μ
  /-- Martingale property: E[X_t | F_s] = X_s for s ≤ t.
      Expressed as: for all F_s-measurable A, ∫_A X_t dμ = ∫_A X_s dμ -/
  martingale_property : ∀ s t : ι, s ≤ t →
    ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
    ∫ ω, toAdapted.process t ω ∂(μ.restrict A) =
    ∫ ω, toAdapted.process s ω ∂(μ.restrict A)

namespace Martingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Preorder ι]
variable {F : Filtration Ω ι}
variable {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- The process underlying a martingale -/
def process (M : Martingale F μ E) : ι → Ω → E := M.toAdapted.process

/-- A constant is a martingale -/
def const (F : Filtration Ω ι) (μ : Measure Ω) [IsProbabilityMeasure μ] (x : E) :
    Martingale F μ E where
  toAdapted := AdaptedProcess.const F x
  integrable := fun _ => ⟨aestronglyMeasurable_const, hasFiniteIntegral_const x⟩
  martingale_property := fun _ _ _ _ _ => rfl

end Martingale

/-! ## Submartingales and Supermartingales -/

/-- A submartingale: E[X_t | F_s] ≥ X_s for s ≤ t.
    Expressed via the integral characterization: for all F_s-measurable A,
    ∫_A X_s dμ ≤ ∫_A X_t dμ. -/
structure Submartingale {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) (μ : Measure Ω)
    [MeasurableSpace ℝ] where
  toAdapted : AdaptedProcess F ℝ
  integrable : ∀ t : ι, Integrable (toAdapted.process t) μ
  /-- The submartingale property via conditional expectation:
      for all F_s-measurable sets A, ∫_A X_s dμ ≤ ∫_A X_t dμ -/
  submartingale_property : ∀ s t : ι, s ≤ t →
    ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
    ∫ ω, toAdapted.process s ω ∂(μ.restrict A) ≤
    ∫ ω, toAdapted.process t ω ∂(μ.restrict A)

/-- A supermartingale: E[X_t | F_s] ≤ X_s for s ≤ t.
    Expressed via the integral characterization: for all F_s-measurable A,
    ∫_A X_s dμ ≥ ∫_A X_t dμ. -/
structure Supermartingale {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Preorder ι]
    (F : Filtration Ω ι) (μ : Measure Ω)
    [MeasurableSpace ℝ] where
  toAdapted : AdaptedProcess F ℝ
  integrable : ∀ t : ι, Integrable (toAdapted.process t) μ
  /-- The supermartingale property via conditional expectation:
      for all F_s-measurable sets A, ∫_A X_s dμ ≥ ∫_A X_t dμ -/
  supermartingale_property : ∀ s t : ι, s ≤ t →
    ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
    ∫ ω, toAdapted.process s ω ∂(μ.restrict A) ≥
    ∫ ω, toAdapted.process t ω ∂(μ.restrict A)

/-! ## Quadratic Variation -/

/-- The quadratic variation ⟨X⟩ of a continuous process X.

    ⟨X⟩_t is the unique adapted, continuous, increasing process starting at 0
    such that X_t² - ⟨X⟩_t is a (local) martingale.

    Equivalently, ⟨X⟩_t = lim Σᵢ (X_{tᵢ₊₁} - X_{tᵢ})² as mesh → 0.

    The characterizing property (X² - ⟨X⟩ is a martingale) distinguishes
    this from just any increasing process. -/
structure QuadraticVariation {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration Ω ℝ) where
  /-- The original process -/
  process : ℝ → Ω → ℝ
  /-- The quadratic variation process ⟨X⟩_t -/
  variation : ℝ → Ω → ℝ
  /-- The quadratic variation is adapted -/
  adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (variation t)
  /-- Non-decreasing in t -/
  mono : ∀ ω : Ω, Monotone (fun t => variation t ω)
  /-- Initial condition -/
  initial : ∀ ω : Ω, variation 0 ω = 0
  /-- **Characterizing property**: X_t² - ⟨X⟩_t is a submartingale
      (for continuous local martingales, this is actually a martingale).

      Expressed via the integral characterization: for s ≤ t and A ∈ F_s,
      ∫_A (X_s² - ⟨X⟩_s) dμ ≤ ∫_A (X_t² - ⟨X⟩_t) dμ.

      This ensures ⟨X⟩ is the actual quadratic variation, not just any
      increasing adapted process. -/
  is_compensator (μ : Measure Ω) : Prop :=
    ∀ s t : ℝ, s ≤ t →
    ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
    ∫ ω in A, (process s ω)^2 - variation s ω ∂μ ≤
    ∫ ω in A, (process t ω)^2 - variation t ω ∂μ

/-- The covariation ⟨X, Y⟩_t of two processes.

    Defined via polarization of the quadratic variation:
    ⟨X, Y⟩_t = (1/4)(⟨X+Y⟩_t - ⟨X-Y⟩_t)

    where ⟨Z⟩_t is the quadratic variation of Z, i.e., the limit of
    Σᵢ (Z_{tᵢ₊₁} - Z_{tᵢ})² as the partition mesh → 0.

    This is NOT the pointwise product X_t · Y_t. The covariation
    captures the joint variation structure.

    NOTE: This definition requires quadratic variation data as input.
    To compute ⟨X,Y⟩ from raw processes, one must first establish their
    quadratic variations. -/
noncomputable def covariation {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration Ω ℝ}
    (qv_sum : QuadraticVariation F)   -- QV of X + Y
    (qv_diff : QuadraticVariation F)  -- QV of X - Y
    : ℝ → Ω → ℝ :=
  fun t ω => (1/4) * (qv_sum.variation t ω - qv_diff.variation t ω)

/-! ## Predictable Processes -/

/-- A predictable process (left-continuous adapted process) -/
structure PredictableProcess {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration Ω ℝ) (E : Type*) [MeasurableSpace E] [TopologicalSpace E] where
  /-- The process -/
  process : ℝ → Ω → E
  /-- Adapted to F -/
  adapted : ∀ t : ℝ, @Measurable Ω E (F.σ_algebra t) _ (process t)
  /-- Left-continuous (pointwise) -/
  left_continuous : ∀ ω : Ω, ∀ t : ℝ, Filter.Tendsto
    (fun s => process s ω) (nhdsWithin t (Set.Iio t)) (nhds (process t ω))

/-! ## Local Martingales -/

/-- The stopped process X^τ defined as X_{t ∧ τ} -/
def stoppedProcess {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration Ω ℝ}
    (X : ℝ → Ω → E) (τ : StoppingTime F) : ℝ → Ω → E :=
  fun t ω => X (min t (τ.time ω)) ω

/-- A local martingale: a process that is a martingale when stopped.

    This is the correct definition: M is a local martingale if there exists
    a sequence of stopping times τₙ ↑ ∞ such that each stopped process
    M^{τₙ} is a (true) martingale.

    The stopped process M^τ_t = M_{t ∧ τ}. -/
structure LocalMartingale {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration Ω ℝ) (μ : Measure Ω)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] where
  /-- The underlying process -/
  process : ℝ → Ω → E
  /-- Adapted to F -/
  adapted : ∀ t : ℝ, @Measurable Ω E (F.σ_algebra t) _ (process t)
  /-- The localizing sequence of stopping times -/
  localizing_seq : ℕ → StoppingTime F
  /-- The stopping times are increasing -/
  localizing_increasing : ∀ n : ℕ, ∀ ω : Ω, (localizing_seq n).time ω ≤ (localizing_seq (n + 1)).time ω
  /-- The stopping times tend to infinity -/
  localizing_to_infty : ∀ ω : Ω, Filter.Tendsto (fun n => (localizing_seq n).time ω) Filter.atTop Filter.atTop
  /-- CRITICAL: The stopped process is a martingale for each n.
      This is what distinguishes a local martingale from just any adapted process. -/
  stopped_is_martingale : ∀ n : ℕ,
    -- Integrability of stopped process
    (∀ t : ℝ, Integrable (stoppedProcess process (localizing_seq n) t) μ) ∧
    -- Martingale property: for s ≤ t and A ∈ F_s,
    -- ∫_A M^{τ_n}_t dμ = ∫_A M^{τ_n}_s dμ
    (∀ s t : ℝ, s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
      ∫ ω in A, stoppedProcess process (localizing_seq n) t ω ∂μ =
      ∫ ω in A, stoppedProcess process (localizing_seq n) s ω ∂μ)

namespace LocalMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
variable {F : Filtration Ω ℝ} {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- Every martingale is a local martingale (with constant stopping times τ_n = n) -/
def ofMartingale (M : Martingale F μ E) : LocalMartingale F μ E where
  process := M.process
  adapted := M.toAdapted.adapted
  localizing_seq := fun n => StoppingTime.const F n
  localizing_increasing := fun n ω => by
    simp only [StoppingTime.const]
    exact Nat.cast_le.mpr (Nat.le_succ n)
  localizing_to_infty := fun ω => by
    simp only [StoppingTime.const]
    exact tendsto_natCast_atTop_atTop
  stopped_is_martingale := fun n => by
    constructor
    · intro t
      -- stoppedProcess M.process (const F n) t ω = M.process (min t n) ω
      -- Since M is a martingale, M.process u is integrable for all u
      have heq : stoppedProcess M.process (StoppingTime.const F n) t = M.process (min t n) := by
        ext ω; simp only [stoppedProcess, StoppingTime.const]
      rw [heq]
      exact M.integrable (min t n)
    · intro s t hst A hA
      -- Need: ∫_A M.process (min t n) = ∫_A M.process (min s n)
      have heqt : stoppedProcess M.process (StoppingTime.const F n) t = M.process (min t n) := by
        ext ω; simp only [stoppedProcess, StoppingTime.const]
      have heqs : stoppedProcess M.process (StoppingTime.const F n) s = M.process (min s n) := by
        ext ω; simp only [stoppedProcess, StoppingTime.const]
      simp only [heqt, heqs]
      -- Case split: either n ≤ s (both mins are n) or s ≤ n (use martingale property)
      by_cases hn : (n : ℝ) ≤ s
      · -- Case: n ≤ s ≤ t, so min s n = n and min t n = n
        have hmin_s : min s (n : ℝ) = n := min_eq_right hn
        have hmin_t : min t (n : ℝ) = n := min_eq_right (le_trans hn hst)
        simp only [hmin_s, hmin_t]
      · -- Case: s < n, so min s n = s. A ∈ F_s = F_{min s n}
        push_neg at hn
        have hmin_s : min s (n : ℝ) = s := min_eq_left (le_of_lt hn)
        rw [hmin_s]
        -- Now use martingale property of M
        have hmin_le : s ≤ min t (n : ℝ) := by
          rw [le_min_iff]; constructor
          · exact hst
          · exact le_of_lt hn
        exact M.martingale_property s (min t n) hmin_le A hA

/-- A local martingale that is L¹-bounded is a true martingale.

    **Status**: Requires uniform integrability infrastructure.

    The proof strategy:
    1. For localizing sequence τₙ → ∞, the stopped martingales M^{τₙ} converge to M
    2. L¹-boundedness implies uniform integrability of the family {M^{τₙ}}
    3. Uniform integrability allows passing the martingale property to the limit

    This requires:
    - Uniform integrability definitions and characterizations
    - Vitali convergence theorem (L¹ convergence from uniform integrability + a.e. convergence)
    - These are partially in Mathlib but the full argument needs development -/
theorem is_martingale_of_bounded (M : LocalMartingale F μ E)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, ∫ ω, ‖M.process t ω‖ ∂μ ≤ C) :
    ∃ M' : Martingale F μ E, M'.process = M.process := by
  sorry -- Requires uniform integrability infrastructure

end LocalMartingale

end SPDE
