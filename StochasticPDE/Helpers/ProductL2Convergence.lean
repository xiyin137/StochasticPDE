/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Product L² Convergence

This file provides the key analysis lemma: if Fₙ → f and Gₙ → g in L²,
then ∫ Fₙ·Gₙ → ∫ f·g.

## Main Results

* `integral_cauchy_schwarz_sq` — (∫ f·g)² ≤ (∫ f²)·(∫ g²)
* `product_integral_tendsto_of_L2_tendsto` — L² convergence implies product integral convergence

## Strategy

The Cauchy-Schwarz inequality is proved via the discriminant method:
for all t, 0 ≤ ∫(f+tg)², which gives (∫fg)² ≤ (∫f²)(∫g²).

Product convergence uses: FₙGₙ - fg = (Fₙ-f)(Gₙ-g) + (Fₙ-f)g + f(Gₙ-g), and
each term's integral → 0 by Cauchy-Schwarz.

## References

* Rudin, "Real and Complex Analysis", Chapter 3
-/

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Integral Cauchy-Schwarz inequality -/

/-- Cauchy-Schwarz inequality for integrals: (∫ f·g)² ≤ (∫ f²)·(∫ g²).

    Proof: For all t ∈ ℝ, 0 ≤ ∫(f+tg)² = ∫f² + 2t·∫fg + t²·∫g².
    The quadratic is non-negative, so discriminant ≤ 0. -/
theorem integral_cauchy_schwarz_sq
    {f g : Ω → ℝ}
    (hf_sq : Integrable (fun ω => (f ω) ^ 2) μ)
    (hg_sq : Integrable (fun ω => (g ω) ^ 2) μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤
    (∫ ω, (f ω) ^ 2 ∂μ) * (∫ ω, (g ω) ^ 2 ∂μ) := by
  set A := ∫ ω, (g ω) ^ 2 ∂μ with hA_def
  set B := ∫ ω, f ω * g ω ∂μ with hB_def
  set C := ∫ ω, (f ω) ^ 2 ∂μ with hC_def
  -- ∀ t, 0 ≤ A·t² + 2B·t + C
  have hquad : ∀ t : ℝ, 0 ≤ A * t ^ 2 + 2 * B * t + C := by
    intro t
    have hfg_t : Integrable (fun ω => (2 * t) * (f ω * g ω)) μ := hfg.const_mul _
    have hg_t : Integrable (fun ω => t ^ 2 * (g ω) ^ 2) μ := hg_sq.const_mul _
    have h_nn : 0 ≤ ∫ ω, (f ω + t * g ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg _)
    have h_eq : ∫ ω, (f ω + t * g ω) ^ 2 ∂μ = A * t ^ 2 + 2 * B * t + C :=
      calc ∫ ω, (f ω + t * g ω) ^ 2 ∂μ
          = ∫ ω, ((f ω) ^ 2 + (2 * t) * (f ω * g ω) + t ^ 2 * (g ω) ^ 2) ∂μ := by
            congr 1; ext ω; ring
        _ = (∫ ω, ((f ω) ^ 2 + (2 * t) * (f ω * g ω)) ∂μ) +
            (∫ ω, t ^ 2 * (g ω) ^ 2 ∂μ) :=
            integral_add (hf_sq.add hfg_t) hg_t
        _ = ((∫ ω, (f ω) ^ 2 ∂μ) + (∫ ω, (2 * t) * (f ω * g ω) ∂μ)) +
            (∫ ω, t ^ 2 * (g ω) ^ 2 ∂μ) := by
            congr 1; exact integral_add hf_sq hfg_t
        _ = C + (2 * t) * B + t ^ 2 * A := by
            rw [integral_const_mul, integral_const_mul]
        _ = A * t ^ 2 + 2 * B * t + C := by ring
    linarith
  -- Non-negative quadratic has non-positive discriminant
  by_cases hA_pos : A = 0
  · -- A = 0: quadratic is 2Bt + C ≥ 0, forcing B = 0
    rw [hA_pos, mul_zero]
    by_contra hB
    push_neg at hB
    have hB_ne : B ≠ 0 := by intro h; rw [h] at hB; simp at hB
    have hquad' : ∀ t : ℝ, 0 ≤ 2 * B * t + C := by
      intro t; have := hquad t; rw [hA_pos] at this; linarith
    have := hquad' (-(C + 1) / (2 * B))
    have h_calc : 2 * B * (-(C + 1) / (2 * B)) + C = -1 := by field_simp; ring
    linarith
  · -- A > 0 case: evaluate at t = -B/A
    have hA_nn : 0 ≤ A := integral_nonneg (fun ω => sq_nonneg _)
    have hA_pos' : 0 < A := lt_of_le_of_ne hA_nn (Ne.symm hA_pos)
    have heval := hquad (-B / A)
    have h_calc : A * (-B / A) ^ 2 + 2 * B * (-B / A) + C = C - B ^ 2 / A := by
      field_simp; ring
    rw [h_calc] at heval
    have : B ^ 2 / A ≤ C := by linarith
    rw [div_le_iff₀ hA_pos'] at this; linarith

/-- Absolute value form: |∫fg| ≤ √(∫f²) · √(∫g²). -/
theorem abs_integral_mul_le_sqrt_integral_sq
    {f g : Ω → ℝ}
    (hf_sq : Integrable (fun ω => (f ω) ^ 2) μ)
    (hg_sq : Integrable (fun ω => (g ω) ^ 2) μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    |∫ ω, f ω * g ω ∂μ| ≤
    Real.sqrt (∫ ω, (f ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (g ω) ^ 2 ∂μ) := by
  have hCS := integral_cauchy_schwarz_sq hf_sq hg_sq hfg
  have hf_nn : 0 ≤ ∫ ω, (f ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hg_nn : 0 ≤ ∫ ω, (g ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_mul hf_nn]
  exact Real.sqrt_le_sqrt (by rw [sq_abs]; exact hCS)

/-! ## Helpers for product L² convergence -/

/-- If xₙ² → 0, then xₙ → 0. Uses continuity of √ at 0. -/
private lemma tendsto_zero_of_sq_tendsto_zero {x : ℕ → ℝ}
    (h : Tendsto (fun n => (x n) ^ 2) atTop (nhds 0)) :
    Tendsto x atTop (nhds 0) := by
  -- √(xₙ²) → √0 = 0 by continuity of √, and √(xₙ²) = |xₙ|
  have h_abs : Tendsto (fun n => |x n|) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => Real.sqrt ((x n) ^ 2)) atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h
      rwa [Function.comp_def, Real.sqrt_zero] at this
    exact h1.congr (fun n => Real.sqrt_sq_eq_abs _)
  -- |xₙ| → 0 implies xₙ → 0 via Metric.tendsto_atTop
  rw [Metric.tendsto_atTop] at h_abs ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h_abs ε hε
  exact ⟨N, fun n hn => by
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this ⊢
    rwa [abs_abs] at this⟩

/-- Cauchy-Schwarz squeeze: if ∫(Fₙ-f)² → 0 and g ∈ L², then ∫(Fₙ-f)·g → 0.
    Uses (∫(Fₙ-f)·g)² ≤ (∫(Fₙ-f)²)·(∫g²) → 0. -/
private lemma integral_mul_tendsto_zero_of_L2_and_sq
    {f : Ω → ℝ} {G : ℕ → Ω → ℝ}
    (hG_sq : ∀ n, Integrable (fun ω => (G n ω) ^ 2) μ)
    (hf_sq : Integrable (fun ω => (f ω) ^ 2) μ)
    (hfG : ∀ n, Integrable (fun ω => G n ω * f ω) μ)
    (hG_tendsto : Tendsto (fun n => ∫ ω, (G n ω) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, G n ω * f ω ∂μ) atTop (nhds 0) := by
  apply tendsto_zero_of_sq_tendsto_zero
  -- (∫Gₙf)² ≤ (∫Gₙ²)(∫f²), and (∫Gₙ²)(∫f²) → 0·(∫f²) = 0
  have hCS : ∀ n, (∫ ω, G n ω * f ω ∂μ) ^ 2 ≤
      (∫ ω, (G n ω) ^ 2 ∂μ) * (∫ ω, (f ω) ^ 2 ∂μ) :=
    fun n => integral_cauchy_schwarz_sq (hG_sq n) hf_sq (hfG n)
  have h_bound : Tendsto (fun n => (∫ ω, (G n ω) ^ 2 ∂μ) * (∫ ω, (f ω) ^ 2 ∂μ))
      atTop (nhds 0) := by
    have : (0 : ℝ) = 0 * (∫ ω, (f ω) ^ 2 ∂μ) := by ring
    rw [this]; exact hG_tendsto.mul_const _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds h_bound
    (fun n => sq_nonneg _)
    hCS

/-- Variant for when both factors converge to 0 in L². -/
private lemma integral_mul_tendsto_zero_of_both_L2
    {F G : ℕ → Ω → ℝ}
    (hF_sq : ∀ n, Integrable (fun ω => (F n ω) ^ 2) μ)
    (hG_sq : ∀ n, Integrable (fun ω => (G n ω) ^ 2) μ)
    (hFG : ∀ n, Integrable (fun ω => F n ω * G n ω) μ)
    (hF_tendsto : Tendsto (fun n => ∫ ω, (F n ω) ^ 2 ∂μ) atTop (nhds 0))
    (hG_tendsto : Tendsto (fun n => ∫ ω, (G n ω) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, F n ω * G n ω ∂μ) atTop (nhds 0) := by
  apply tendsto_zero_of_sq_tendsto_zero
  have hCS : ∀ n, (∫ ω, F n ω * G n ω ∂μ) ^ 2 ≤
      (∫ ω, (F n ω) ^ 2 ∂μ) * (∫ ω, (G n ω) ^ 2 ∂μ) :=
    fun n => integral_cauchy_schwarz_sq (hF_sq n) (hG_sq n) (hFG n)
  have h_bound : Tendsto (fun n => (∫ ω, (F n ω) ^ 2 ∂μ) * (∫ ω, (G n ω) ^ 2 ∂μ))
      atTop (nhds 0) := by
    have : (0 : ℝ) = 0 * 0 := by ring
    rw [this]; exact hF_tendsto.mul hG_tendsto
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds h_bound
    (fun n => sq_nonneg _)
    hCS

/-! ## Product L² convergence -/

/-- Product L² convergence: if Fₙ → f and Gₙ → g in L², then ∫ Fₙ·Gₙ → ∫ f·g.

    Uses the decomposition FₙGₙ - fg = (Fₙ-f)(Gₙ-g) + (Fₙ-f)g + f(Gₙ-g) and
    Cauchy-Schwarz to bound each term.

    The cross-product integrability hypotheses (hcross, hFg, hfG) are necessary
    for splitting the integral. In practice, these follow from L² integrability
    of each factor (Hölder's inequality). -/
theorem product_integral_tendsto_of_L2_tendsto
    {f g : Ω → ℝ} {F G : ℕ → Ω → ℝ}
    (hf_sq : Integrable (fun ω => (f ω) ^ 2) μ)
    (hg_sq : Integrable (fun ω => (g ω) ^ 2) μ)
    (hFG_int : ∀ n, Integrable (fun ω => F n ω * G n ω) μ)
    (hfg_int : Integrable (fun ω => f ω * g ω) μ)
    (hFsub_sq : ∀ n, Integrable (fun ω => (F n ω - f ω) ^ 2) μ)
    (hGsub_sq : ∀ n, Integrable (fun ω => (G n ω - g ω) ^ 2) μ)
    -- Cross-product integrabilities (for splitting the integral)
    (hcross : ∀ n, Integrable (fun ω => (F n ω - f ω) * (G n ω - g ω)) μ)
    (hFg : ∀ n, Integrable (fun ω => (F n ω - f ω) * g ω) μ)
    (hfG : ∀ n, Integrable (fun ω => f ω * (G n ω - g ω)) μ)
    (hF_tendsto : Tendsto (fun n => ∫ ω, (F n ω - f ω) ^ 2 ∂μ) atTop (nhds 0))
    (hG_tendsto : Tendsto (fun n => ∫ ω, (G n ω - g ω) ^ 2 ∂μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω, F n ω * G n ω ∂μ) atTop
      (nhds (∫ ω, f ω * g ω ∂μ)) := by
  -- Show the difference → 0, then convert
  suffices h_diff : Tendsto (fun n => ∫ ω, F n ω * G n ω ∂μ - ∫ ω, f ω * g ω ∂μ)
      atTop (nhds 0) from tendsto_sub_nhds_zero_iff.mp h_diff
  -- Decompose: ∫(FₙGₙ - fg) = ∫(Fₙ-f)(Gₙ-g) + ∫(Fₙ-f)g + ∫f(Gₙ-g)
  have h_decomp : ∀ n,
      ∫ ω, F n ω * G n ω ∂μ - ∫ ω, f ω * g ω ∂μ =
      ∫ ω, (F n ω - f ω) * (G n ω - g ω) ∂μ +
      ∫ ω, (F n ω - f ω) * g ω ∂μ +
      ∫ ω, f ω * (G n ω - g ω) ∂μ := by
    intro n
    have h1 : ∫ ω, F n ω * G n ω ∂μ - ∫ ω, f ω * g ω ∂μ =
        ∫ ω, (F n ω * G n ω - f ω * g ω) ∂μ :=
      (integral_sub (hFG_int n) hfg_int).symm
    have h2 : (fun ω => F n ω * G n ω - f ω * g ω) =
        (fun ω => (F n ω - f ω) * (G n ω - g ω) + (F n ω - f ω) * g ω +
          f ω * (G n ω - g ω)) := by ext ω; ring
    have h3 : ∫ ω, ((F n ω - f ω) * (G n ω - g ω) + (F n ω - f ω) * g ω +
        f ω * (G n ω - g ω)) ∂μ =
        (∫ ω, ((F n ω - f ω) * (G n ω - g ω) + (F n ω - f ω) * g ω) ∂μ) +
        ∫ ω, f ω * (G n ω - g ω) ∂μ :=
      integral_add ((hcross n).add (hFg n)) (hfG n)
    have h4 : ∫ ω, ((F n ω - f ω) * (G n ω - g ω) + (F n ω - f ω) * g ω) ∂μ =
        (∫ ω, (F n ω - f ω) * (G n ω - g ω) ∂μ) +
        ∫ ω, (F n ω - f ω) * g ω ∂μ :=
      integral_add (hcross n) (hFg n)
    rw [h1, h2, h3, h4]
  simp_rw [h_decomp]
  -- Show: sum of three terms → 0
  have h_zero : (0 : ℝ) = 0 + 0 + 0 := by ring
  rw [h_zero]
  apply Tendsto.add
  apply Tendsto.add
  -- Term 1: ∫(Fₙ-f)(Gₙ-g) → 0 (both factors → 0 in L²)
  · exact integral_mul_tendsto_zero_of_both_L2
      hFsub_sq hGsub_sq hcross hF_tendsto hG_tendsto
  -- Term 2: ∫(Fₙ-f)g → 0 (first factor → 0 in L², second is fixed in L²)
  · exact integral_mul_tendsto_zero_of_L2_and_sq
      hFsub_sq hg_sq hFg hF_tendsto
  -- Term 3: ∫f(Gₙ-g) → 0 (first is fixed in L², second → 0 in L²)
  · have hfG' : ∀ n, Integrable (fun ω => (G n ω - g ω) * f ω) μ := by
      intro n; have := hfG n; rwa [show (fun ω => f ω * (G n ω - g ω)) =
        (fun ω => (G n ω - g ω) * f ω) from by ext ω; ring] at this
    have h := integral_mul_tendsto_zero_of_L2_and_sq
      hGsub_sq hf_sq hfG' hG_tendsto
    refine h.congr (fun n => ?_)
    congr 1; ext ω; ring
