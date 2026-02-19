/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Probability.IndependenceHelpers
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Set Integral Helpers for Stochastic Calculus

This file provides set integral lemmas for products of adapted and independent
random variables, which are crucial for proving:
1. BM quadratic variation [W]_t = t
2. Simple stochastic integral martingale property

## Main Results

* `setIntegral_mul_zero_of_adapted_and_indep_zero_mean` -
  For A ∈ F_s, g F_s-measurable, h independent of F_s with E[h] = 0:
  ∫_A g·h dμ = 0

* `setIntegral_of_indep_composition` -
  For A ∈ F_s, f∘Y where Y is independent of F_s:
  ∫_A (f∘Y) dμ = E[f∘Y] · μ(A)

## Key Technique

The proofs convert set integrals to full integrals using indicator functions:
  ∫_A g·h dμ = ∫ (1_A · g) · h dμ
Then the product 1_A · g is still F_s-measurable, allowing factorization.

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Section 1.5
-/

namespace SPDE.Probability

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-! ## Indicator function measurability -/

/-- The indicator of an m-measurable set applied to an m-measurable function
    is m-measurable. -/
theorem measurable_indicator_of_measurable
    {m : MeasurableSpace Ω}
    {g : Ω → ℝ} {A : Set Ω}
    (hg : @Measurable Ω ℝ m _ g)
    (hA : @MeasurableSet Ω m A) :
    @Measurable Ω ℝ m _ (A.indicator g) :=
  hg.indicator hA

/-- The indicator of an m-measurable set is m-measurable (as a {0,1}-valued function). -/
theorem measurable_indicator_one
    {m : MeasurableSpace Ω}
    {A : Set Ω}
    (hA : @MeasurableSet Ω m A) :
    @Measurable Ω ℝ m _ (A.indicator (fun _ => (1 : ℝ))) :=
  measurable_const.indicator hA

/-! ## Set integral = integral with indicator -/

/-- Key identity: A.indicator (g * h) = (A.indicator g) * h -/
theorem indicator_mul_right_eq
    {g h : Ω → ℝ} {A : Set Ω} :
    A.indicator (fun ω => g ω * h ω) = fun ω => A.indicator g ω * h ω := by
  ext ω
  simp only [Set.indicator]
  split_ifs with hA
  · rfl
  · simp

/-! ## Main lemma: set integral vanishing for adapted × independent zero-mean -/

/-- For A ∈ F_s, g F_s-measurable, h independent of F_s with E[h] = 0:
    ∫_A g·h dμ = 0.

    This is the key lemma for proving:
    - BM quadratic variation (cross term ∫_A W_s · ΔW dμ = 0)
    - Simple stochastic integral martingale (∫_A Hᵢ·ΔWᵢ dμ = 0 for future increments)

    **Proof**: Convert ∫_A g·h = ∫ (1_A·g)·h. Since 1_A·g is F_s-measurable
    and h is independent of F_s with zero mean, the integral factorizes to
    E[1_A·g] · E[h] = E[1_A·g] · 0 = 0. -/
theorem setIntegral_mul_zero_of_adapted_and_indep_zero_mean
    {m : MeasurableSpace Ω}
    (hm : m ≤ m₀)
    {g h : Ω → ℝ} {A : Set Ω}
    (hg : @Measurable Ω ℝ m _ g)
    (hA : @MeasurableSet Ω m A)
    (hg_int : Integrable g (μ.restrict A))
    (hh_int : Integrable h μ)
    (hindep : @Indep Ω m (MeasurableSpace.comap h inferInstance) m₀ μ)
    (hmean : ∫ ω, h ω ∂μ = 0)
    [IsProbabilityMeasure μ] :
    ∫ ω in A, g ω * h ω ∂μ = 0 := by
  -- Step 1: Convert set integral to full integral with indicator
  -- ∫_A g·h dμ = ∫ A.indicator(g·h) dμ
  rw [← integral_indicator (hm A hA)]
  -- Step 2: Rewrite indicator(g·h) = indicator(g) · h
  -- Uses Mathlib's Set.indicator_mul_left pointwise under the integral
  simp_rw [Set.indicator_mul_left]
  -- Step 3: Apply integral_mul_zero_of_indep_zero_mean
  -- Need: A.indicator g is m-measurable
  have hig_meas : @Measurable Ω ℝ m _ (A.indicator g) :=
    measurable_indicator_of_measurable hg hA
  -- Need: A.indicator g is integrable
  have hig_int : Integrable (A.indicator g) μ := by
    rwa [integrable_indicator_iff (hm A hA)]
  exact integral_mul_zero_of_indep_zero_mean hm hig_meas hig_int hh_int hindep hmean

/-- Variant with the factors swapped: ∫_A h·g dμ = 0. -/
theorem setIntegral_mul_zero_of_indep_zero_mean_and_adapted
    {m : MeasurableSpace Ω}
    (hm : m ≤ m₀)
    {g h : Ω → ℝ} {A : Set Ω}
    (hg : @Measurable Ω ℝ m _ g)
    (hA : @MeasurableSet Ω m A)
    (hg_int : Integrable g (μ.restrict A))
    (hh_int : Integrable h μ)
    (hindep : @Indep Ω m (MeasurableSpace.comap h inferInstance) m₀ μ)
    (hmean : ∫ ω, h ω ∂μ = 0)
    [IsProbabilityMeasure μ] :
    ∫ ω in A, h ω * g ω ∂μ = 0 := by
  simp_rw [mul_comm (h _) (g _)]
  exact setIntegral_mul_zero_of_adapted_and_indep_zero_mean hm hg hA hg_int hh_int hindep hmean

/-! ## Set integral factorization for independent functions -/

/-- For A ∈ F_s and f independent of F_s:
    ∫_A f² dμ = E[f²] · μ(A)

    This is needed for the quadratic variation proof where we compute
    ∫_A (ΔW)² dμ = E[(ΔW)²] · μ(A) = (t-s) · μ(A). -/
theorem setIntegral_sq_of_indep_eq_measure_mul_integral
    {m : MeasurableSpace Ω}
    (hm : m ≤ m₀)
    {f : Ω → ℝ}
    (hf_meas : @Measurable Ω ℝ m₀ _ f)
    (hf_sq_int : Integrable (fun ω => (f ω)^2) μ)
    (hindep : @Indep Ω m (MeasurableSpace.comap f inferInstance) m₀ μ)
    (A : Set Ω) (hA : @MeasurableSet Ω m A)
    [IsProbabilityMeasure μ] [SigmaFinite (μ.trim hm)] :
    ∫ ω in A, (f ω)^2 ∂μ = (μ A).toReal * ∫ ω, (f ω)^2 ∂μ := by
  -- f² generates a coarser σ-algebra than f: comap(f²) ≤ comap(f)
  have hle : MeasurableSpace.comap (fun ω => (f ω)^2) inferInstance ≤
      MeasurableSpace.comap f inferInstance := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨(fun x => x ^ 2) ⁻¹' t, (measurable_id.pow_const 2) ht, rfl⟩
  -- So f² is independent of m
  have hindep_sq : @Indep Ω m (MeasurableSpace.comap (fun ω => (f ω)^2) inferInstance) m₀ μ :=
    indep_of_indep_of_le_right hindep hle
  -- f² is measurable w.r.t. its own comap
  have hf_sq_sm : StronglyMeasurable[MeasurableSpace.comap (fun ω => (f ω)^2) inferInstance]
      (fun ω => (f ω)^2) :=
    stronglyMeasurable_comap_self _
  -- Apply the existing set integral lemma
  have hcomap_le : MeasurableSpace.comap (fun ω => (f ω)^2) inferInstance ≤ m₀ :=
    comap_le_of_measurable' (hf_meas.pow_const 2)
  exact setIntegral_of_indep_eq_measure_mul_integral hcomap_le hm hf_sq_sm hf_sq_int
    hindep_sq.symm A hA

end SPDE.Probability
