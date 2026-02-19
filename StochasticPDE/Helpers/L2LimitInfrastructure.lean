/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# L² Limit Infrastructure

This file provides the bridge between L² convergence and set integral convergence,
which is needed to show that the L² limit of martingales is a martingale.

## Main Results

* `sq_integral_abs_le_integral_sq` — On a probability space, `(∫|g|)² ≤ ∫g²`
* `abs_setIntegral_le_sqrt_integral_sq` — `|∫_A g| ≤ √(∫g²)`
* `setIntegral_tendsto_of_L2_tendsto` — L² convergence implies set integral convergence
* `martingale_setIntegral_eq_of_L2_limit` — Martingale property under L² limits

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 1
-/

namespace SPDE

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Jensen-type inequality: (E[|X|])² ≤ E[X²] on probability spaces -/

/-- On a probability space, `(∫|g|)² ≤ ∫g²`.

    Proof: Apply `variance_nonneg` and `variance_eq_sub` to `|g|`:
    `0 ≤ Var[|g|] = E[|g|²] - (E[|g|])² = E[g²] - (E[|g|])²` -/
theorem sq_integral_abs_le_integral_sq [IsProbabilityMeasure μ]
    {g : Ω → ℝ} (hg_int : Integrable g μ)
    (hg_sq_int : Integrable (fun ω => g ω ^ 2) μ) :
    (∫ ω, |g ω| ∂μ) ^ 2 ≤ ∫ ω, g ω ^ 2 ∂μ := by
  -- |g| is AEStronglyMeasurable
  have habs_asm : AEStronglyMeasurable (fun ω => |g ω|) μ :=
    (hg_int.abs).aestronglyMeasurable
  -- |g| ∈ L² (since |g|² = g² is integrable)
  have habs_memLp : MemLp (fun ω => |g ω|) 2 μ := by
    rw [memLp_two_iff_integrable_sq habs_asm]
    convert hg_sq_int using 1
    ext ω; exact sq_abs (g ω)
  -- Var[|g|] ≥ 0
  have hvar := variance_nonneg (fun ω => |g ω|) μ
  -- Var[|g|] = E[|g|²] - (E[|g|])²
  rw [variance_eq_sub habs_memLp] at hvar
  -- E[|g|²] = E[g²]
  have h_abs_sq : (μ[(fun ω => |g ω|) ^ 2]) = ∫ ω, g ω ^ 2 ∂μ := by
    congr 1; ext ω; simp [sq_abs]
  rw [h_abs_sq] at hvar
  -- 0 ≤ E[g²] - (E[|g|])² means (E[|g|])² ≤ E[g²]
  linarith

/-! ## Set integral bound from L² norm -/

/-- On a probability space, `|∫_A g| ≤ √(∫g²)`.

    Proof: |∫_A g| ≤ ∫_A |g| ≤ ∫|g| ≤ √(∫g²). -/
theorem abs_setIntegral_le_sqrt_integral_sq [IsProbabilityMeasure μ]
    {g : Ω → ℝ} (hg_int : Integrable g μ)
    (hg_sq_int : Integrable (fun ω => g ω ^ 2) μ)
    (A : Set Ω) :
    |∫ ω in A, g ω ∂μ| ≤ Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have habs_int : Integrable (fun ω => |g ω|) μ := hg_int.abs
  -- Step 1: |∫_A g| ≤ ∫_A |g|
  have h1 : |∫ ω in A, g ω ∂μ| ≤ ∫ ω in A, |g ω| ∂μ := by
    rw [show |∫ ω in A, g ω ∂μ| = ‖∫ ω in A, g ω ∂μ‖ from (Real.norm_eq_abs _).symm]
    calc ‖∫ ω in A, g ω ∂μ‖ ≤ ∫ ω in A, ‖g ω‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ ω in A, |g ω| ∂μ := by congr 1
  -- Step 2: ∫_A |g| ≤ ∫ |g|
  have h2 : ∫ ω in A, |g ω| ∂μ ≤ ∫ ω, |g ω| ∂μ :=
    setIntegral_le_integral habs_int (ae_of_all μ (fun ω => abs_nonneg _))
  -- Step 3: ∫|g| ≤ √(∫g²)
  have h3 : ∫ ω, |g ω| ∂μ ≤ Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
    have hsq := sq_integral_abs_le_integral_sq hg_int hg_sq_int
    have h_nn : 0 ≤ ∫ ω, |g ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
    rw [← Real.sqrt_sq h_nn]
    exact Real.sqrt_le_sqrt hsq
  linarith

/-! ## L² convergence implies set integral convergence -/

/-- If `∫(f_n - f)² → 0` then for any measurable set A, `∫_A f_n → ∫_A f`. -/
theorem setIntegral_tendsto_of_L2_tendsto [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf_int : Integrable f μ)
    (hF_int : ∀ n, Integrable (F n) μ)
    (hF_sq_int : ∀ n, Integrable (fun ω => (F n ω - f ω) ^ 2) μ)
    (hL2 : Filter.Tendsto (fun n => ∫ ω, (F n ω - f ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0))
    (A : Set Ω) (_hA : MeasurableSet A) :
    Filter.Tendsto (fun n => ∫ ω in A, F n ω ∂μ)
      Filter.atTop (nhds (∫ ω in A, f ω ∂μ)) := by
  -- Suffices: |∫_A F_n - ∫_A f| → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Since ∫(F_n - f)² → 0, find N such that ∫(F_n - f)² < ε² for n ≥ N
  rw [Metric.tendsto_atTop] at hL2
  obtain ⟨N, hN⟩ := hL2 (ε ^ 2) (sq_pos_of_pos hε)
  use N
  intro n hn
  rw [Real.dist_eq]
  -- Key: |∫_A F_n - ∫_A f| = |∫_A (F_n - f)| ≤ √(∫(F_n - f)²)
  have hgn_int : Integrable (fun ω => F n ω - f ω) μ := (hF_int n).sub hf_int
  -- ∫_A F_n - ∫_A f = ∫_A (F_n - f)
  rw [show ∫ ω in A, F n ω ∂μ - ∫ ω in A, f ω ∂μ =
      ∫ ω in A, (F n ω - f ω) ∂μ from
    (integral_sub (hF_int n).integrableOn hf_int.integrableOn).symm]
  -- Apply key bound
  have hbound := abs_setIntegral_le_sqrt_integral_sq hgn_int (hF_sq_int n) A
  -- √(∫(F_n - f)²) < ε
  have hL2n := hN n hn
  rw [Real.dist_eq, sub_zero] at hL2n
  have h_sq_nn : 0 ≤ ∫ ω, (F n ω - f ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have h_val : ∫ ω, (F n ω - f ω) ^ 2 ∂μ < ε ^ 2 := by
    rwa [abs_of_nonneg h_sq_nn] at hL2n
  have hsqrt_bound : Real.sqrt (∫ ω, (F n ω - f ω) ^ 2 ∂μ) < ε :=
    calc Real.sqrt (∫ ω, (F n ω - f ω) ^ 2 ∂μ)
        < Real.sqrt (ε ^ 2) := Real.sqrt_lt_sqrt h_sq_nn h_val
      _ = ε := Real.sqrt_sq (le_of_lt hε)
  linarith

/-! ## Martingale property under L² limits -/

/-- If processes M_n satisfy the martingale set-integral property and converge to M in L²,
    then M also satisfies the martingale set-integral property.

    This is the core theorem for proving that the Itô integral is a martingale. -/
theorem martingale_setIntegral_eq_of_L2_limit [IsProbabilityMeasure μ]
    {M : ℝ → Ω → ℝ} {M_n : ℕ → ℝ → Ω → ℝ}
    {s t : ℝ}
    (hM_int_s : Integrable (M s) μ) (hM_int_t : Integrable (M t) μ)
    (hMn_int_s : ∀ n, Integrable (M_n n s) μ)
    (hMn_int_t : ∀ n, Integrable (M_n n t) μ)
    (hMn_sq_int_s : ∀ n, Integrable (fun ω => (M_n n s ω - M s ω) ^ 2) μ)
    (hMn_sq_int_t : ∀ n, Integrable (fun ω => (M_n n t ω - M t ω) ^ 2) μ)
    (hL2_s : Filter.Tendsto (fun n => ∫ ω, (M_n n s ω - M s ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0))
    (hL2_t : Filter.Tendsto (fun n => ∫ ω, (M_n n t ω - M t ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0))
    {A : Set Ω} (hA : MeasurableSet A)
    (h_mart : ∀ n, ∫ ω in A, M_n n t ω ∂μ = ∫ ω in A, M_n n s ω ∂μ) :
    ∫ ω in A, M t ω ∂μ = ∫ ω in A, M s ω ∂μ := by
  -- ∫_A M_n(t) → ∫_A M(t)
  have h_conv_t := setIntegral_tendsto_of_L2_tendsto
    hM_int_t hMn_int_t hMn_sq_int_t hL2_t A hA
  -- ∫_A M_n(s) → ∫_A M(s)
  have h_conv_s := setIntegral_tendsto_of_L2_tendsto
    hM_int_s hMn_int_s hMn_sq_int_s hL2_s A hA
  -- Both sequences have the same values (by martingale property)
  have h_eq : (fun n => ∫ ω in A, M_n n t ω ∂μ) = (fun n => ∫ ω in A, M_n n s ω ∂μ) := by
    ext n; exact h_mart n
  -- By uniqueness of limits
  exact tendsto_nhds_unique (h_eq ▸ h_conv_t) h_conv_s

/-! ## Young's inequality with parameter -/

/-- Young's inequality with parameter: `|a| * |b| ≤ t/2 * a² + 1/(2t) * b²` for `t > 0`.
    Proof: multiply by `2t` and use `(t*|a| - |b|)² ≥ 0`. -/
private lemma young_ineq (a b t : ℝ) (ht : 0 < t) :
    |a| * |b| ≤ t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  -- (t|a| - |b|)² ≥ 0 gives: 2t|a||b| ≤ t²a² + b²
  have key : 2 * t * (|a| * |b|) ≤ t ^ 2 * a ^ 2 + b ^ 2 := by
    have h1 := sq_nonneg (t * |a| - |b|)
    have h2 : |a| ^ 2 = a ^ 2 := sq_abs a
    have h3 : |b| ^ 2 = b ^ 2 := sq_abs b
    nlinarith
  -- RHS * 2t = t²a² + b²
  have identity : 2 * t * (t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2) =
      t ^ 2 * a ^ 2 + b ^ 2 := by field_simp
  -- Conclude by dividing the scaled inequality by 2t
  by_contra h_neg
  push_neg at h_neg
  have scaled := mul_lt_mul_of_pos_left h_neg h2t
  rw [identity] at scaled
  linarith

/-! ## L² norm convergence from L² convergence -/

/-- If `∫(f_n - f)² → 0` then `∫ f_n² → ∫ f²`.

    Proof uses Young's inequality with parameter:
    `|ab| ≤ t/2·a² + 1/(2t)·b²` for t > 0.
    This gives `|∫(F_n-f)·f| ≤ t/2·∫(F_n-f)² + 1/(2t)·∫f²`.
    Since the first term → 0 for fixed t and the second → 0 as t → ∞,
    we conclude `∫(F_n-f)·f → 0`, hence `∫F_n² → ∫f²`. -/
theorem sq_integral_tendsto_of_L2_tendsto [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hf_sq : Integrable (fun ω => f ω ^ 2) μ)
    (hFf_sq : ∀ n, Integrable (fun ω => (F n ω - f ω) ^ 2) μ)
    (hFf_prod : ∀ n, Integrable (fun ω => (F n ω - f ω) * f ω) μ)
    (hL2 : Filter.Tendsto (fun n => ∫ ω, (F n ω - f ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ ω, F n ω ^ 2 ∂μ)
      Filter.atTop (nhds (∫ ω, f ω ^ 2 ∂μ)) := by
  -- Expand: F_n² = (F_n-f)² + 2(F_n-f)·f + f²
  -- So ∫F_n² - ∫f² = ∫(F_n-f)² + 2∫(F_n-f)·f
  -- Suffices to show ∫(F_n-f)² → 0 and ∫(F_n-f)·f → 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hL2
  set C := ∫ ω, f ω ^ 2 ∂μ
  have hC_nn : 0 ≤ C := integral_nonneg (fun ω => sq_nonneg _)
  -- Young's parameter: choose t > 0 so that C/t < ε/4
  set t := 4 * C / ε + 1 with ht_def
  have ht_pos : 0 < t := by positivity
  have hCt : C / t < ε / 4 := by
    rw [div_lt_div_iff₀ ht_pos (by positivity : (0 : ℝ) < 4)]
    have : ε * t = 4 * C + ε := by
      rw [ht_def]; field_simp
    linarith
  -- Choose N so that (1 + t)·∫(F_n-f)² < ε/2 for n ≥ N
  obtain ⟨N, hN⟩ := hL2 (ε / (2 * (1 + t))) (by positivity)
  use N
  intro n hn
  rw [Real.dist_eq]
  -- Expand: ∫F_n² - ∫f² = ∫(F_n-f)² + 2∫(F_n-f)·f
  have hfun : ∀ ω, F n ω ^ 2 - f ω ^ 2 =
      (F n ω - f ω) ^ 2 + 2 * ((F n ω - f ω) * f ω) := by
    intro ω; ring
  have hFn_sq : Integrable (fun ω => F n ω ^ 2) μ := by
    have heq : (fun ω => F n ω ^ 2) =
        fun ω => (F n ω - f ω) ^ 2 + 2 * ((F n ω - f ω) * f ω) + f ω ^ 2 := by
      ext ω; ring
    rw [heq]
    exact ((hFf_sq n).add ((hFf_prod n).const_mul 2)).add hf_sq
  have hdiff : ∫ ω, F n ω ^ 2 ∂μ - ∫ ω, f ω ^ 2 ∂μ =
      ∫ ω, (F n ω - f ω) ^ 2 ∂μ + 2 * ∫ ω, (F n ω - f ω) * f ω ∂μ := by
    calc ∫ ω, F n ω ^ 2 ∂μ - ∫ ω, f ω ^ 2 ∂μ
        = ∫ ω, (F n ω ^ 2 - f ω ^ 2) ∂μ := (integral_sub hFn_sq hf_sq).symm
      _ = ∫ ω, ((F n ω - f ω) ^ 2 + 2 * ((F n ω - f ω) * f ω)) ∂μ := by
          congr 1; ext ω; exact hfun ω
      _ = ∫ ω, (F n ω - f ω) ^ 2 ∂μ + ∫ ω, 2 * ((F n ω - f ω) * f ω) ∂μ :=
          integral_add (hFf_sq n) ((hFf_prod n).const_mul 2)
      _ = ∫ ω, (F n ω - f ω) ^ 2 ∂μ + 2 * ∫ ω, (F n ω - f ω) * f ω ∂μ := by
          rw [integral_const_mul]
  -- Get L² bound for this n
  have hL2n := hN n hn
  rw [Real.dist_eq, sub_zero] at hL2n
  have hL2_nn : 0 ≤ ∫ ω, (F n ω - f ω) ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hL2_val : ∫ ω, (F n ω - f ω) ^ 2 ∂μ < ε / (2 * (1 + t)) := by
    rwa [abs_of_nonneg hL2_nn] at hL2n
  -- Young's inequality pointwise: |(a-b)·b| ≤ t/2·(a-b)² + 1/(2t)·b²
  have hyoung : |∫ ω, (F n ω - f ω) * f ω ∂μ| ≤
      t / 2 * ∫ ω, (F n ω - f ω) ^ 2 ∂μ + 1 / (2 * t) * C := by
    calc |∫ ω, (F n ω - f ω) * f ω ∂μ|
        ≤ ∫ ω, |(F n ω - f ω) * f ω| ∂μ := by
          rw [show |∫ ω, (F n ω - f ω) * f ω ∂μ| =
            ‖∫ ω, (F n ω - f ω) * f ω ∂μ‖ from (Real.norm_eq_abs _).symm]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (t / 2 * (F n ω - f ω) ^ 2 + 1 / (2 * t) * f ω ^ 2) ∂μ := by
          apply integral_mono_ae (hFf_prod n).abs
            ((hFf_sq n).const_mul _ |>.add (hf_sq.const_mul _))
          filter_upwards with ω
          simp only [Pi.add_apply]
          rw [abs_mul]
          exact young_ineq _ _ t ht_pos
      _ = t / 2 * ∫ ω, (F n ω - f ω) ^ 2 ∂μ + 1 / (2 * t) * C := by
          rw [integral_add ((hFf_sq n).const_mul _) (hf_sq.const_mul _),
              integral_const_mul, integral_const_mul]
  -- Combine bounds
  calc |∫ ω, F n ω ^ 2 ∂μ - ∫ ω, f ω ^ 2 ∂μ|
      = |∫ ω, (F n ω - f ω) ^ 2 ∂μ + 2 * ∫ ω, (F n ω - f ω) * f ω ∂μ| := by
        rw [hdiff]
    _ ≤ ∫ ω, (F n ω - f ω) ^ 2 ∂μ + 2 * |∫ ω, (F n ω - f ω) * f ω ∂μ| := by
        calc |∫ ω, (F n ω - f ω) ^ 2 ∂μ + 2 * ∫ ω, (F n ω - f ω) * f ω ∂μ|
            ≤ |∫ ω, (F n ω - f ω) ^ 2 ∂μ| + |2 * ∫ ω, (F n ω - f ω) * f ω ∂μ| :=
              abs_add_le _ _
          _ = ∫ ω, (F n ω - f ω) ^ 2 ∂μ + 2 * |∫ ω, (F n ω - f ω) * f ω ∂μ| := by
              rw [abs_of_nonneg hL2_nn, abs_mul, abs_of_pos (by positivity : (2 : ℝ) > 0)]
    _ ≤ ∫ ω, (F n ω - f ω) ^ 2 ∂μ + 2 * (t / 2 * ∫ ω, (F n ω - f ω) ^ 2 ∂μ +
        1 / (2 * t) * C) := by linarith [hyoung]
    _ = (1 + t) * ∫ ω, (F n ω - f ω) ^ 2 ∂μ + C / t := by
        have hne : t ≠ 0 := ne_of_gt ht_pos
        field_simp
        ring
    _ < (1 + t) * (ε / (2 * (1 + t))) + ε / 4 := by
        have h1 : (1 + t) * ∫ ω, (F n ω - f ω) ^ 2 ∂μ <
            (1 + t) * (ε / (2 * (1 + t))) :=
          mul_lt_mul_of_pos_left hL2_val (by linarith)
        linarith
    _ = ε / 2 + ε / 4 := by field_simp
    _ < ε := by linarith

end SPDE
