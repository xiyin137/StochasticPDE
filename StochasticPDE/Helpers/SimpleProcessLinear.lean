/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Helpers.CommonRefinement

/-!
# Simple Process Linear Combination Infrastructure

This file provides infrastructure for scaling simple processes and combining
simple process stochastic integrals.

## Main Definitions

* `SimpleProcess.scale` — Scale values of a simple process by a constant

## Main Results

* `stochasticIntegral_at_scale` — Scaling commutes with stochastic integration
* `exists_linear_simple_integral` — Linear combination of simple process integrals
  is also a simple process integral (via common refinement)

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-! ## Scaling simple processes -/

/-- Scale a simple process by a constant: multiply all values by `c`.
    The partition times are unchanged. -/
def scale (c : ℝ) (H : SimpleProcess F) : SimpleProcess F where
  n := H.n
  times := H.times
  values := fun i ω => c * H.values i ω
  increasing := H.increasing
  adapted := fun i => measurable_const.mul (H.adapted i)

/-- Scaling commutes with the time-parameterized stochastic integral (pointwise). -/
theorem stochasticIntegral_at_scale (c : ℝ) (H : SimpleProcess F)
    (W : BrownianMotion Ω μ) (t : ℝ) (ω : Ω) :
    (H.scale c).stochasticIntegral_at W t ω =
    c * H.stochasticIntegral_at W t ω := by
  unfold stochasticIntegral_at scale
  simp only
  rw [Finset.mul_sum]
  congr 1; ext i
  by_cases h : (i : ℕ) + 1 < H.n
  · simp only [dif_pos h]
    by_cases h_full : H.times ⟨(i : ℕ) + 1, h⟩ ≤ t
    · simp only [if_pos h_full]; ring
    · simp only [if_neg h_full]
      by_cases h_start : H.times i ≤ t
      · simp only [if_pos h_start]; ring
      · simp only [if_neg h_start]; ring
  · simp only [dif_neg h]; ring

/-- Scaling commutes with the full stochastic integral (pointwise). -/
theorem stochasticIntegral_scale (c : ℝ) (H : SimpleProcess F)
    (W : BrownianMotion Ω μ) (ω : Ω) :
    (H.scale c).stochasticIntegral W ω =
    c * H.stochasticIntegral W ω := by
  unfold stochasticIntegral scale
  simp only
  rw [Finset.mul_sum]
  congr 1; ext i
  by_cases h : (i : ℕ) + 1 < H.n
  · simp only [dif_pos h]; ring
  · simp only [dif_neg h]; ring

/-- Scaled process preserves adaptedness at BM filtration times. -/
theorem scale_adapted_BM (c : ℝ) (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (hH : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i)) :
    ∀ i : Fin (H.scale c).n,
      @Measurable Ω ℝ (W.F.σ_algebra ((H.scale c).times i)) _ ((H.scale c).values i) := by
  intro i
  simp only [scale]
  exact measurable_const.mul (hH i)

/-- Scaled process preserves boundedness. -/
theorem scale_bounded (c : ℝ) (H : SimpleProcess F)
    (hH : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C) :
    ∀ i : Fin (H.scale c).n, ∃ C : ℝ, ∀ ω, |(H.scale c).values i ω| ≤ C := by
  intro i
  obtain ⟨C, hC⟩ := hH i
  exact ⟨|c| * C, fun ω => by
    simp only [scale, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)⟩

/-- Scaled process preserves nonneg partition times. -/
theorem scale_nonneg_times (c : ℝ) (H : SimpleProcess F)
    (hH : ∀ i : Fin H.n, 0 ≤ H.times i) :
    ∀ i : Fin (H.scale c).n, 0 ≤ (H.scale c).times i := hH

/-! ## Linear combination of simple process integrals

The key technical result: a linear combination of two simple process
stochastic integrals can be expressed as the stochastic integral of a single
simple process on the common refinement of their partitions.

The proof works by:
1. Refining both partitions to the common refinement (union of time points)
2. Showing that refinement preserves the stochastic integral (telescoping)
3. On the common refinement, combining values pointwise

Since the partition refinement involves sorting and deduplicating `Finset ℝ`
elements and re-indexing through `Fin`, the construction is encapsulated
in this single lemma. -/

/-- Linear combination of two simple process integrals is a simple process integral.

    Given simple processes H₁, H₂ and constants a, b, there exists a simple process
    H on the common refinement whose stochastic integral at any time t equals
    `a * ∫H₁ dW(t) + b * ∫H₂ dW(t)` pointwise.

    The combined process inherits adaptedness, boundedness, and nonneg times
    from H₁ and H₂. -/
theorem exists_linear_simple_integral (H₁ H₂ : SimpleProcess F)
    (W : BrownianMotion Ω μ) (a b : ℝ) :
    ∃ H : SimpleProcess F,
      (∀ t ω, H.stochasticIntegral_at W t ω =
        a * H₁.stochasticIntegral_at W t ω + b * H₂.stochasticIntegral_at W t ω) ∧
      -- Adapted at BM times (if originals are)
      ((∀ i : Fin H₁.n, @Measurable Ω ℝ (W.F.σ_algebra (H₁.times i)) _ (H₁.values i)) →
       (∀ i : Fin H₂.n, @Measurable Ω ℝ (W.F.σ_algebra (H₂.times i)) _ (H₂.values i)) →
        ∀ i : Fin H.n, @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i)) ∧
      -- Bounded (if originals are)
      ((∀ i : Fin H₁.n, ∃ C : ℝ, ∀ ω, |H₁.values i ω| ≤ C) →
       (∀ i : Fin H₂.n, ∃ C : ℝ, ∀ ω, |H₂.values i ω| ≤ C) →
        ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C) ∧
      -- Nonneg times (if originals are)
      ((∀ i : Fin H₁.n, 0 ≤ H₁.times i) → (∀ i : Fin H₂.n, 0 ≤ H₂.times i) →
        ∀ i : Fin H.n, 0 ≤ H.times i) := by
  refine ⟨mergedProcess H₁ H₂ a b,
    fun t ω => mergedProcess_integral_eq H₁ H₂ W a b t ω, ?_, ?_, ?_⟩
  · -- Adaptedness: merged process values are adapted at merged partition times
    intro hH₁ hH₂ i
    -- values i ω = a * H₁.valueAtTime(s) ω + b * H₂.valueAtTime(s) ω
    -- where s = (mergedProcess).times i
    -- Need measurability at W.F.σ_algebra((mergedProcess).times i)
    exact (measurable_const.mul
      (valueAtTime_measurable_filtration H₁ _ hH₁)).add
      (measurable_const.mul
      (valueAtTime_measurable_filtration H₂ _ hH₂))
  · -- Boundedness: merged process values are bounded
    intro hH₁ hH₂ i
    -- values i ω = a * H₁.valueAtTime(s) ω + b * H₂.valueAtTime(s) ω
    obtain ⟨C₁, hC₁⟩ := valueAtTime_bounded H₁ _ hH₁
    obtain ⟨C₂, hC₂⟩ := valueAtTime_bounded H₂ _ hH₂
    exact ⟨|a| * C₁ + |b| * C₂, fun ω => by
      calc |(mergedProcess H₁ H₂ a b).values i ω|
          = |a * H₁.valueAtTime _ ω + b * H₂.valueAtTime _ ω| := rfl
        _ ≤ |a * H₁.valueAtTime _ ω| + |b * H₂.valueAtTime _ ω| := abs_add_le _ _
        _ = |a| * |H₁.valueAtTime _ ω| + |b| * |H₂.valueAtTime _ ω| := by
            rw [abs_mul, abs_mul]
        _ ≤ |a| * C₁ + |b| * C₂ := add_le_add
            (mul_le_mul_of_nonneg_left (hC₁ ω) (abs_nonneg a))
            (mul_le_mul_of_nonneg_left (hC₂ ω) (abs_nonneg b))⟩
  · -- Nonneg times: merged partition times are nonneg
    intro hH₁ hH₂ i
    -- (mergedProcess).times i ∈ mergedFinset H₁ H₂ = partitionFinset H₁ ∪ partitionFinset H₂
    have hmem := mergedProcess_times_mem H₁ H₂ a b i
    simp only [mergedFinset, Finset.mem_union, partitionFinset, Finset.mem_image,
      Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [← hj]; exact hH₁ j
    · rw [← hj]; exact hH₂ j

end SimpleProcess

end SPDE
