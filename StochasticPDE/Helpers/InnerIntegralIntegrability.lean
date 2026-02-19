/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Inner Integral Integrability Infrastructure

This file provides infrastructure for proving integrability of "inner integral" functions
of the form `ω ↦ ∫ s in [0,t], f(s,ω) ∂vol` in the outer variable ω.

## Main Results

* `inner_sq_integral_integrable_of_sub_interval` — If `ω ↦ ∫₀ᵀ f²` is integrable,
  then so is `ω ↦ ∫₀ᵗ f²` for t ≤ T.
* `inner_product_integral_integrable` — Integrability of `ω ↦ ∫₀ᵗ f·g`.
* `inner_integral_quadratic_split_ae` — Inner integral of quadratic expansion splits a.e.

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

open MeasureTheory MeasurableSpace Set

namespace InnerIntegral

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Strong measurability of inner integral functions -/

/-- The inner integral `ω ↦ ∫ s in Icc 0 t, f(s,ω) ∂vol` is strongly measurable
    when `f` is jointly measurable. Uses Fubini/Tonelli via
    `StronglyMeasurable.integral_prod_left'`. -/
theorem stronglyMeasurable_inner_integral
    {f : ℝ → Ω → ℝ}
    (hjm : Measurable (Function.uncurry f))
    (t : ℝ) :
    StronglyMeasurable (fun ω => ∫ s in Icc 0 t, f s ω ∂volume) :=
  hjm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Icc 0 t))

/-- Variant for squared functions. -/
theorem stronglyMeasurable_inner_sq_integral
    {f : ℝ → Ω → ℝ}
    (hjm : Measurable (Function.uncurry f))
    (t : ℝ) :
    StronglyMeasurable (fun ω => ∫ s in Icc 0 t, (f s ω) ^ 2 ∂volume) :=
  stronglyMeasurable_inner_integral (hjm.pow_const 2) t

/-- Variant for product of two jointly measurable functions. -/
theorem stronglyMeasurable_inner_product_integral
    {f g : ℝ → Ω → ℝ}
    (hjm_f : Measurable (Function.uncurry f))
    (hjm_g : Measurable (Function.uncurry g))
    (t : ℝ) :
    StronglyMeasurable (fun ω => ∫ s in Icc 0 t, f s ω * g s ω ∂volume) :=
  stronglyMeasurable_inner_integral (hjm_f.mul hjm_g) t

/-! ## Main integrability results -/

/-- If `ω ↦ ∫₀ᵀ f² ∂s` is integrable over Ω, then so is `ω ↦ ∫₀ᵗ f² ∂s` for t ≤ T.

    Proof: Joint measurability gives AEStronglyMeasurable of the inner integral.
    The inner integral on [0,t] is bounded a.e. by the inner integral on [0,T]
    (nonneg integrand on subset, IntegrableOn a.e. from Tonelli). -/
theorem inner_sq_integral_integrable_of_sub_interval
    {f : ℝ → Ω → ℝ}
    (hjm : Measurable (Function.uncurry f))
    {t T : ℝ} (_ht0 : 0 ≤ t) (htT : t ≤ T)
    (hsq : Integrable (fun ω => ∫ s in Icc 0 T, (f s ω) ^ 2 ∂volume) μ) :
    Integrable (fun ω => ∫ s in Icc 0 t, (f s ω) ^ 2 ∂volume) μ := by
  apply Integrable.mono' hsq
  · exact (stronglyMeasurable_inner_sq_integral hjm t).aestronglyMeasurable
  · -- Bound: ‖∫₀ᵗ f²‖ ≤ ∫₀ᵀ f² a.e.
    -- For a.e. ω, f²(·,ω) is IntegrableOn [0,T] (from Tonelli + hsq).
    -- Then ∫₀ᵗ f² ≤ ∫₀ᵀ f² by subset monotonicity for nonneg integrands.
    -- For ω where IntegrableOn fails, both Bochner integrals are 0, so bound holds.
    sorry

/-- Integrability of `ω ↦ ∫₀ᵗ f·g ∂s` from integrability of `∫₀ᵀ f²` and `∫₀ᵀ g²`.
    Uses AM-GM: |f·g| ≤ (f² + g²)/2. -/
theorem inner_product_integral_integrable
    {f g : ℝ → Ω → ℝ}
    (hjm_f : Measurable (Function.uncurry f))
    (hjm_g : Measurable (Function.uncurry g))
    {t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hsq_f : Integrable (fun ω => ∫ s in Icc 0 T, (f s ω) ^ 2 ∂volume) μ)
    (hsq_g : Integrable (fun ω => ∫ s in Icc 0 T, (g s ω) ^ 2 ∂volume) μ) :
    Integrable (fun ω => ∫ s in Icc 0 t, f s ω * g s ω ∂volume) μ := by
  have hI₁ := inner_sq_integral_integrable_of_sub_interval hjm_f ht0 htT hsq_f
  have hI₂ := inner_sq_integral_integrable_of_sub_interval hjm_g ht0 htT hsq_g
  apply Integrable.mono' (hI₁.add hI₂)
  · exact (stronglyMeasurable_inner_product_integral hjm_f hjm_g t).aestronglyMeasurable
  · -- Bound: |∫ fg| ≤ ∫ |fg| ≤ ∫ (f²+g²)/2 ≤ ∫f² + ∫g²
    -- This holds a.e. ω where the inner functions are IntegrableOn.
    sorry

/-! ## Inner integral splitting (for a.e. ω) -/

/-- For a.e. ω, f(·,ω)² is IntegrableOn [0,t] when ∫₀ᵀ f² is integrable over Ω.

    Proof: By Tonelli, ∫⁻ f² on [0,T] is finite a.e. With joint measurability,
    this gives IntegrableOn of f² a.e., and restriction to [0,t] ⊆ [0,T] preserves it. -/
theorem integrableOn_sq_ae_of_square_integrable
    {f : ℝ → Ω → ℝ}
    (_hjm : Measurable (Function.uncurry f))
    {t T : ℝ} (_ht0 : 0 ≤ t) (_htT : t ≤ T)
    (_hsq : Integrable (fun ω => ∫ s in Icc 0 T, (f s ω) ^ 2 ∂volume) μ) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun s => (f s ω) ^ 2) (Icc 0 t) volume := by
  sorry

/-- For a.e. ω, f(·,ω) is IntegrableOn [0,t] when ∫₀ᵀ f² is integrable over Ω.
    Follows from f² integrable (L²⊂L¹ on finite measure intervals). -/
theorem integrableOn_ae_of_square_integrable
    {f : ℝ → Ω → ℝ}
    (hjm : Measurable (Function.uncurry f))
    {t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hsq : Integrable (fun ω => ∫ s in Icc 0 T, (f s ω) ^ 2 ∂volume) μ) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun s => f s ω) (Icc 0 t) volume := by
  sorry

/-- For a.e. ω, f(·,ω)·g(·,ω) is IntegrableOn [0,t] when ∫₀ᵀ f² and ∫₀ᵀ g² are integrable.
    By AM-GM: |fg| ≤ (f²+g²)/2. -/
theorem integrableOn_product_ae_of_square_integrable
    {f g : ℝ → Ω → ℝ}
    (hjm_f : Measurable (Function.uncurry f))
    (hjm_g : Measurable (Function.uncurry g))
    {t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hsq_f : Integrable (fun ω => ∫ s in Icc 0 T, (f s ω) ^ 2 ∂volume) μ)
    (hsq_g : Integrable (fun ω => ∫ s in Icc 0 T, (g s ω) ^ 2 ∂volume) μ) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun s => f s ω * g s ω) (Icc 0 t) volume := by
  sorry

/-- For a.e. ω, the inner integral of a quadratic expansion splits.
    This is the key technical lemma for `hRHS` in `combined_sq_integral_eq`. -/
theorem inner_integral_quadratic_split_ae
    {f g : ℝ → Ω → ℝ}
    (hjm_f : Measurable (Function.uncurry f))
    (hjm_g : Measurable (Function.uncurry g))
    {T : ℝ} (_hT : 0 ≤ T)
    (hsq_f : Integrable (fun ω => ∫ s in Icc 0 T, (f s ω) ^ 2 ∂volume) μ)
    (hsq_g : Integrable (fun ω => ∫ s in Icc 0 T, (g s ω) ^ 2 ∂volume) μ)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    (a b : ℝ) :
    ∀ᵐ ω ∂μ,
      ∫ s in Icc 0 t,
        (a ^ 2 * (f s ω) ^ 2 +
         2 * a * b * (f s ω * g s ω) +
         b ^ 2 * (g s ω) ^ 2) ∂volume =
      a ^ 2 * ∫ s in Icc 0 t, (f s ω) ^ 2 ∂volume +
      2 * a * b * ∫ s in Icc 0 t, f s ω * g s ω ∂volume +
      b ^ 2 * ∫ s in Icc 0 t, (g s ω) ^ 2 ∂volume := by
  -- For a.e. ω, f², g², fg are IntegrableOn [0,t]
  have hion_fsq := integrableOn_sq_ae_of_square_integrable hjm_f ht0 htT hsq_f
  have hion_gsq := integrableOn_sq_ae_of_square_integrable hjm_g ht0 htT hsq_g
  have hion_fg := integrableOn_product_ae_of_square_integrable hjm_f hjm_g ht0 htT hsq_f hsq_g
  filter_upwards [hion_fsq, hion_gsq, hion_fg] with ω hf_sq' hg_sq' hfg'
  -- Restore IntegrableOn types
  have hf_sq : IntegrableOn (fun s => (f s ω) ^ 2) (Icc 0 t) volume := hf_sq'
  have hg_sq : IntegrableOn (fun s => (g s ω) ^ 2) (Icc 0 t) volume := hg_sq'
  have hfg : IntegrableOn (fun s => f s ω * g s ω) (Icc 0 t) volume := hfg'
  -- IntegrableOn for scaled terms
  have h1 : IntegrableOn (fun s => a ^ 2 * (f s ω) ^ 2) (Icc 0 t) volume :=
    hf_sq.const_mul _
  have h2 : IntegrableOn (fun s => 2 * a * b * (f s ω * g s ω)) (Icc 0 t) volume :=
    hfg.const_mul _
  have h3 : IntegrableOn (fun s => b ^ 2 * (g s ω) ^ 2) (Icc 0 t) volume :=
    hg_sq.const_mul _
  -- Split the integral using integral_add + integral_const_mul
  -- Use `simp only` instead of `rw` to handle beta-equivalence in pattern matching
  have h12 : IntegrableOn (fun s => a ^ 2 * (f s ω) ^ 2 + 2 * a * b * (f s ω * g s ω))
      (Icc 0 t) volume := h1.add h2
  simp only [integral_add h12 h3, integral_add h1 h2, integral_const_mul]

end InnerIntegral
