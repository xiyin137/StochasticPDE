/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.ProductL2Convergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Iterated Integral Product Convergence

If Fₙ → f and Gₙ → g in L²([0,t] × Ω), then E[∫₀ᵗ Fₙ·Gₙ] → E[∫₀ᵗ f·g].

## Main Results

* `iterated_product_integral_tendsto` — the main convergence theorem

## Strategy

Work on the product space (vol_t × μ), convert iterated integrals to product integrals
via Fubini (`integral_prod_symm`), apply `product_integral_tendsto_of_L2_tendsto`,
and convert back.

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Product integrability helpers -/

/-- Bounded jointly measurable functions are integrable on a finite product measure. -/
theorem bounded_integrable_prod {t : ℝ} [IsFiniteMeasure μ]
    {f : ℝ → Ω → ℝ}
    (hf_jm : Measurable (Function.uncurry f))
    (hf_bdd : ∃ C, ∀ s ω, |f s ω| ≤ C) :
    Integrable (fun p : ℝ × Ω => f p.1 p.2)
      ((volume.restrict (Icc 0 t)).prod μ) := by
  obtain ⟨C, hC⟩ := hf_bdd
  haveI : Fact (volume (Icc 0 t) < ⊤) := ⟨measure_Icc_lt_top⟩
  apply (integrable_const C).mono' hf_jm.aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs]
  dsimp [Function.uncurry]
  exact hC p.1 p.2

/-- Squared bounded jointly measurable functions are integrable on a finite product measure. -/
theorem bounded_sq_integrable_prod {t : ℝ} [IsFiniteMeasure μ]
    {f : ℝ → Ω → ℝ}
    (hf_jm : Measurable (Function.uncurry f))
    (hf_bdd : ∃ C, ∀ s ω, |f s ω| ≤ C) :
    Integrable (fun p : ℝ × Ω => (f p.1 p.2) ^ 2)
      ((volume.restrict (Icc 0 t)).prod μ) := by
  obtain ⟨C, hC⟩ := hf_bdd
  haveI : Fact (volume (Icc 0 t) < ⊤) := ⟨measure_Icc_lt_top⟩
  apply (integrable_const (C ^ 2)).mono' (hf_jm.pow_const 2).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_pow]
  dsimp [Function.uncurry]
  exact pow_le_pow_left₀ (abs_nonneg _) (hC p.1 p.2) 2

/-- Difference of bounded and L² function has square integrable on product measure. -/
theorem diff_sq_integrable_prod {t : ℝ} [IsFiniteMeasure μ]
    {f g : ℝ → Ω → ℝ}
    (hf_jm : Measurable (Function.uncurry f))
    (hg_jm : Measurable (Function.uncurry g))
    (hf_bdd : ∃ C, ∀ s ω, |f s ω| ≤ C)
    (hg_sq : Integrable (fun p : ℝ × Ω => (g p.1 p.2) ^ 2)
      ((volume.restrict (Icc 0 t)).prod μ)) :
    Integrable (fun p : ℝ × Ω => (f p.1 p.2 - g p.1 p.2) ^ 2)
      ((volume.restrict (Icc 0 t)).prod μ) := by
  -- (f - g)² ≤ 2(f² + g²)
  have hf_sq := bounded_sq_integrable_prod (μ := μ) (t := t) hf_jm hf_bdd
  apply ((hf_sq.add hg_sq).const_mul 2).mono'
    ((hf_jm.sub hg_jm).pow_const 2).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  dsimp [Function.uncurry]
  have h : (f p.1 p.2 - g p.1 p.2) ^ 2 ≤
      2 * ((f p.1 p.2) ^ 2 + (g p.1 p.2) ^ 2) := by nlinarith [sq_nonneg (f p.1 p.2 + g p.1 p.2)]
  linarith

/-! ## Main convergence theorem -/

/-- Iterated integral product convergence from L² convergence on [0,t] × Ω.

    If E[∫₀ᵗ (Fₙ-f)²] → 0 and E[∫₀ᵗ (Gₙ-g)²] → 0, then
    E[∫₀ᵗ Fₙ·Gₙ] → E[∫₀ᵗ f·g].

    Proof: On the product space [0,t] × Ω with product measure, this is
    just L² convergence implies product integral convergence, applied via
    `product_integral_tendsto_of_L2_tendsto` and converted by Fubini. -/
theorem iterated_product_integral_tendsto [IsProbabilityMeasure μ]
    {f g : ℝ → Ω → ℝ} {F G : ℕ → ℝ → Ω → ℝ}
    {t : ℝ} (_ht : 0 ≤ t)
    -- Joint measurabilities
    (hf_jm : Measurable (Function.uncurry f))
    (hg_jm : Measurable (Function.uncurry g))
    (hF_jm : ∀ n, Measurable (Function.uncurry (F n)))
    (hG_jm : ∀ n, Measurable (Function.uncurry (G n)))
    -- Product space square integrabilities (for f and g)
    (hf_sq_prod : Integrable (fun p : ℝ × Ω => (f p.1 p.2) ^ 2)
      ((volume.restrict (Icc 0 t)).prod μ))
    (hg_sq_prod : Integrable (fun p : ℝ × Ω => (g p.1 p.2) ^ 2)
      ((volume.restrict (Icc 0 t)).prod μ))
    -- Uniform bounds on F, G
    (hF_bdd : ∀ n, ∃ C, ∀ s ω, |F n s ω| ≤ C)
    (hG_bdd : ∀ n, ∃ C, ∀ s ω, |G n s ω| ≤ C)
    -- L² convergence (iterated form)
    (hF_conv : Tendsto (fun n => ∫ ω, (∫ s in Icc 0 t,
      (F n s ω - f s ω) ^ 2 ∂volume) ∂μ) atTop (nhds 0))
    (hG_conv : Tendsto (fun n => ∫ ω, (∫ s in Icc 0 t,
      (G n s ω - g s ω) ^ 2 ∂volume) ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, (∫ s in Icc 0 t,
      F n s ω * G n s ω ∂volume) ∂μ) atTop
      (nhds (∫ ω, (∫ s in Icc 0 t, f s ω * g s ω ∂volume) ∂μ)) := by
  -- Set up the product measure
  set ν := (volume.restrict (Icc 0 t)).prod μ with hν
  -- Finite measure instances
  haveI : Fact (volume (Icc 0 t) < ⊤) := ⟨measure_Icc_lt_top⟩
  haveI : IsFiniteMeasure (volume.restrict (Icc 0 t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  -- Product integrability: F_n * G_n (bounded)
  have hFG_prod : ∀ n, Integrable (fun p : ℝ × Ω => F n p.1 p.2 * G n p.1 p.2) ν := by
    intro n
    obtain ⟨C₁, hC₁⟩ := hF_bdd n
    obtain ⟨C₂, hC₂⟩ := hG_bdd n
    apply (integrable_const (C₁ * C₂)).mono' ((hF_jm n).mul (hG_jm n)).aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    dsimp [Function.uncurry]
    exact mul_le_mul (hC₁ p.1 p.2) (hC₂ p.1 p.2) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hC₁ p.1 p.2))
  -- Product integrability: f * g (from AM-GM with f², g²)
  have hfg_prod : Integrable (fun p : ℝ × Ω => f p.1 p.2 * g p.1 p.2) ν := by
    apply (hf_sq_prod.add hg_sq_prod).mono' (hf_jm.mul hg_jm).aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    simp only [Pi.add_apply]
    dsimp [Function.uncurry]
    nlinarith [sq_nonneg (|f p.1 p.2| - |g p.1 p.2|),
      sq_abs (f p.1 p.2), sq_abs (g p.1 p.2)]
  -- Product integrability: (F_n - f)² and (G_n - g)²
  have hFsub_sq_prod : ∀ n,
      Integrable (fun p : ℝ × Ω => (F n p.1 p.2 - f p.1 p.2) ^ 2) ν :=
    fun n => diff_sq_integrable_prod (hF_jm n) hf_jm (hF_bdd n) hf_sq_prod
  have hGsub_sq_prod : ∀ n,
      Integrable (fun p : ℝ × Ω => (G n p.1 p.2 - g p.1 p.2) ^ 2) ν :=
    fun n => diff_sq_integrable_prod (hG_jm n) hg_jm (hG_bdd n) hg_sq_prod
  -- Cross-product integrabilities (for product_integral_tendsto_of_L2_tendsto)
  have hcross : ∀ n, Integrable (fun p : ℝ × Ω =>
      (F n p.1 p.2 - f p.1 p.2) * (G n p.1 p.2 - g p.1 p.2)) ν := by
    intro n
    apply ((hFsub_sq_prod n).add (hGsub_sq_prod n)).mono'
      (((hF_jm n).sub hf_jm).mul ((hG_jm n).sub hg_jm)).aestronglyMeasurable
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    dsimp [Function.uncurry]
    nlinarith [sq_nonneg (|F n p.1 p.2 - f p.1 p.2| - |G n p.1 p.2 - g p.1 p.2|),
      sq_abs (F n p.1 p.2 - f p.1 p.2), sq_abs (G n p.1 p.2 - g p.1 p.2)]
  have hFg : ∀ n, Integrable (fun p : ℝ × Ω =>
      (F n p.1 p.2 - f p.1 p.2) * g p.1 p.2) ν := by
    intro n
    apply ((hFsub_sq_prod n).add hg_sq_prod).mono'
      (((hF_jm n).sub hf_jm).mul hg_jm).aestronglyMeasurable
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    dsimp [Function.uncurry]
    nlinarith [sq_nonneg (|F n p.1 p.2 - f p.1 p.2| - |g p.1 p.2|),
      sq_abs (F n p.1 p.2 - f p.1 p.2), sq_abs (g p.1 p.2)]
  have hfG : ∀ n, Integrable (fun p : ℝ × Ω =>
      f p.1 p.2 * (G n p.1 p.2 - g p.1 p.2)) ν := by
    intro n
    apply (hf_sq_prod.add (hGsub_sq_prod n)).mono'
      (hf_jm.mul ((hG_jm n).sub hg_jm)).aestronglyMeasurable
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    dsimp [Function.uncurry]
    nlinarith [sq_nonneg (|f p.1 p.2| - |G n p.1 p.2 - g p.1 p.2|),
      sq_abs (f p.1 p.2), sq_abs (G n p.1 p.2 - g p.1 p.2)]
  -- Convert L² convergence from iterated to product integral via Fubini
  have hF_conv_prod : Tendsto
      (fun n => ∫ p, (F n p.1 p.2 - f p.1 p.2) ^ 2 ∂ν) atTop (nhds 0) := by
    -- integral_prod_symm converts product → iterated: ∫ ν = ∫ ω (∫ s ...)
    have h_eq : ∀ n, ∫ p, (F n p.1 p.2 - f p.1 p.2) ^ 2 ∂ν =
        ∫ ω, (∫ s in Icc 0 t, (F n s ω - f s ω) ^ 2 ∂volume) ∂μ := by
      intro n; exact integral_prod_symm _ (hFsub_sq_prod n)
    simp_rw [h_eq]; exact hF_conv
  have hG_conv_prod : Tendsto
      (fun n => ∫ p, (G n p.1 p.2 - g p.1 p.2) ^ 2 ∂ν) atTop (nhds 0) := by
    have h_eq : ∀ n, ∫ p, (G n p.1 p.2 - g p.1 p.2) ^ 2 ∂ν =
        ∫ ω, (∫ s in Icc 0 t, (G n s ω - g s ω) ^ 2 ∂volume) ∂μ := by
      intro n; exact integral_prod_symm _ (hGsub_sq_prod n)
    simp_rw [h_eq]; exact hG_conv
  -- Apply product_integral_tendsto_of_L2_tendsto on the product space
  have h_prod := product_integral_tendsto_of_L2_tendsto
    hf_sq_prod hg_sq_prod hFG_prod hfg_prod hFsub_sq_prod hGsub_sq_prod
    hcross hFg hfG hF_conv_prod hG_conv_prod
  -- Convert conclusion from product to iterated integrals via Fubini
  have h_eq_lim : ∫ p, f p.1 p.2 * g p.1 p.2 ∂ν =
      ∫ ω, (∫ s in Icc 0 t, f s ω * g s ω ∂volume) ∂μ :=
    integral_prod_symm _ hfg_prod
  have h_eq_n : ∀ n, ∫ p, F n p.1 p.2 * G n p.1 p.2 ∂ν =
      ∫ ω, (∫ s in Icc 0 t, F n s ω * G n s ω ∂volume) ∂μ :=
    fun n => integral_prod_symm _ (hFG_prod n)
  rw [h_eq_lim] at h_prod
  simp_rw [h_eq_n] at h_prod
  exact h_prod
