/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.KolmogorovChentsov.ContinuousModification
import StochasticPDE.ItoCalculus.QuarticBound
import StochasticPDE.ItoCalculus.AdaptedLimit

/-!
# Stochastic Integral Continuity

Under bounded diffusion, the stochastic integral `SI_t = ∫₀ᵗ σ dW` has a continuous
modification on any compact interval `[0, T]`.

## Strategy

1. From `stoch_integral_increment_L4_bound_proof`: `E[(SI_t - SI_s)⁴] ≤ 3Mσ⁴(t-s)²`
2. Bridge to KC format: `E[|SI_t - SI_s|⁴] ≤ 3Mσ⁴|t-s|²` (even power, absolute values)
3. Apply Kolmogorov-Chentsov with p=4, q=2, geometric threshold δ(n) = (9/10)ⁿ
4. Under usual conditions, the modification inherits adaptedness

## Main Results

* `stoch_integral_continuous_modification` — SI has a continuous modification on [0,T]
* `stoch_integral_continuous_adapted_modification` — with adaptedness under usual conditions

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Theorem 2.2.8
-/

namespace SPDE

open MeasureTheory Filter Set KolmogorovChentsov

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Bridge lemmas: even powers and absolute values -/

/-- For fourth powers, |a|⁴ = a⁴. -/
private lemma abs_pow_four (a : ℝ) : |a| ^ 4 = a ^ 4 := by
  calc |a| ^ 4 = (|a| ^ 2) ^ 2 := by ring
    _ = (a ^ 2) ^ 2 := by rw [sq_abs]
    _ = a ^ 4 := by ring

/-! ## Symmetric L4 bounds -/

/-- Symmetric L⁴ bound for stochastic integral increments in absolute-value form.
    Converts the ordered bound from QuarticBound.lean to the KC format. -/
theorem stoch_integral_increment_L4_bound_abs {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ ω, |X.stoch_integral t ω - X.stoch_integral s ω| ^ 4 ∂μ) ≤
    3 * Mσ ^ 4 * |t - s| ^ 2 := by
  simp_rw [abs_pow_four]
  by_cases hst : s ≤ t
  · rw [sq_abs]
    exact stoch_integral_increment_L4_bound_proof X hMσ s t hs hst
  · push_neg at hst
    have h_swap : ∀ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4 =
        (X.stoch_integral s ω - X.stoch_integral t ω) ^ 4 := fun ω => by ring
    simp_rw [h_swap]
    rw [show |t - s| ^ 2 = (s - t) ^ 2 from by
      rw [show t - s = -(s - t) from by ring, abs_neg, sq_abs]]
    exact stoch_integral_increment_L4_bound_proof X hMσ t s ht (le_of_lt hst)

/-- Symmetric L⁴ integrability for stochastic integral increments. -/
theorem stoch_integral_increment_L4_integrable_abs {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (fun ω => |X.stoch_integral t ω - X.stoch_integral s ω| ^ 4) μ := by
  simp_rw [abs_pow_four]
  by_cases hst : s ≤ t
  · exact stoch_integral_increment_L4_integrable_proof X hMσ s t hs hst
  · push_neg at hst
    have h_swap : ∀ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4 =
        (X.stoch_integral s ω - X.stoch_integral t ω) ^ 4 := fun ω => by ring
    simp_rw [h_swap]
    exact stoch_integral_increment_L4_integrable_proof X hMσ t s ht (le_of_lt hst)

/-! ## Algebraic helper for Borel-Cantelli term -/

set_option maxHeartbeats 400000 in
/-- Algebraic simplification of the Borel-Cantelli term for geometric threshold.
    2ⁿ * (M * (T/2ⁿ)² / ((rⁿ)⁴)) = M * T² / (2 * r⁴)ⁿ -/
lemma bc_term_geometric_eq {M T r : ℝ} (hr : 0 < r) (n : ℕ) :
    (2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ 2 / ((r ^ n) ^ 4)) =
    M * T ^ 2 / (2 * r ^ 4) ^ n := by
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n two_ne_zero
  have hrn : r ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hr)
  have _hr4n : (r ^ n) ^ 4 ≠ 0 := pow_ne_zero 4 hrn
  have _h2r4n : (2 * r ^ 4) ^ n ≠ 0 := pow_ne_zero n (by positivity)
  field_simp
  ring

/-! ## Main theorem -/

set_option maxHeartbeats 400000 in
/-- Under bounded diffusion, the stochastic integral has a continuous modification
    on [0, T]. Applied via Kolmogorov-Chentsov with p=4, q=2, δ(n)=(9/10)ⁿ.

    The quartic moment bound E[(SI_t - SI_s)⁴] ≤ 3Mσ⁴(t-s)² from QuarticBound.lean
    provides the Kolmogorov condition with q=2 > 1. -/
theorem stoch_integral_continuous_modification {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T : ℝ) (hT : 0 < T) :
    ∃ SI' : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => SI' t ω) (Icc 0 T)) ∧
      (∀ t, t ∈ Icc 0 T → ∀ᵐ ω ∂μ, SI' t ω = X.stoch_integral t ω) := by
  -- Nonempty Ω (from probability measure)
  haveI : Nonempty Ω := by
    by_contra h; rw [not_nonempty_iff] at h
    have := @IsProbabilityMeasure.measure_univ _ _ μ _
    rw [univ_eq_empty_iff.mpr h, measure_empty] at this; exact zero_ne_one this
  -- Mσ ≥ 0 from the absolute value bound
  have hMσ_nn : 0 ≤ Mσ := le_trans (abs_nonneg _) (hMσ 0 (Classical.arbitrary Ω))
  -- KC parameters: p = 4, q = 2, M = 3Mσ⁴
  -- Geometric threshold: r = 9/10, δ(n) = r^n
  set r : ℝ := 9 / 10 with hr_def
  -- Integrability hypothesis for KC
  have hint : ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T →
      Integrable (fun ω => |X.stoch_integral t ω - X.stoch_integral s ω| ^ (4 : ℕ)) μ :=
    fun s t hs ht => stoch_integral_increment_L4_integrable_abs X hMσ s t hs.1 ht.1
  -- Moment bound hypothesis for KC
  have hbound : ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T →
      (∫ ω, |X.stoch_integral t ω - X.stoch_integral s ω| ^ (4 : ℕ) ∂μ) ≤
      (3 * Mσ ^ 4) * |t - s| ^ (2 : ℕ) :=
    fun s t hs ht => stoch_integral_increment_L4_bound_abs X hMσ s t hs.1 ht.1
  -- δ(n) = r^n is positive and summable
  have hr_pos : (0 : ℝ) < r := by norm_num [hr_def]
  have hδ_pos : ∀ n, 0 < r ^ n := fun n => pow_pos hr_pos n
  have hδ_sum : Summable (fun n => r ^ n) :=
    summable_geometric_of_lt_one (by norm_num [hr_def]) (by norm_num [hr_def])
  -- BC term nonnegativity
  have hterms_nn : ∀ n, 0 ≤ (2 : ℝ) ^ n *
      ((3 * Mσ ^ 4) * (T / 2 ^ n) ^ (2 : ℕ) / (r ^ n) ^ (4 : ℕ)) := by
    intro n
    apply mul_nonneg (pow_nonneg (by norm_num) n)
    apply div_nonneg
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact pow_nonneg (pow_pos hr_pos n).le 4
  -- BC sum summability: each term = (3Mσ⁴T²) * s^n where s = (2r⁴)⁻¹ < 1
  have hBC_sum : Summable (fun n => (2 : ℝ) ^ n *
      ((3 * Mσ ^ 4) * (T / 2 ^ n) ^ (2 : ℕ) / (r ^ n) ^ (4 : ℕ))) := by
    -- Define geometric ratio s = (2*r⁴)⁻¹
    have h2r4_pos : (0 : ℝ) < 2 * r ^ 4 := by positivity
    set s := (2 * r ^ 4)⁻¹ with hs_def
    have hs_nn : (0 : ℝ) ≤ s := by positivity
    have hs_lt : s < 1 := by
      rw [hs_def, inv_eq_one_div, div_lt_one h2r4_pos]
      norm_num [hr_def]
    -- Show each BC term equals (3*Mσ⁴*T²) * s^n
    have h_eq : ∀ n, (2 : ℝ) ^ n *
        ((3 * Mσ ^ 4) * (T / 2 ^ n) ^ 2 / (r ^ n) ^ 4) =
        (3 * Mσ ^ 4 * T ^ 2) * s ^ n := by
      intro n
      rw [bc_term_geometric_eq hr_pos, div_eq_mul_inv, ← inv_pow]
    simp_rw [h_eq]
    exact (summable_geometric_of_lt_one hs_nn hs_lt).const_smul (3 * Mσ ^ 4 * T ^ 2)
  -- Apply Kolmogorov-Chentsov theorem
  exact kolmogorov_chentsov (X := X.stoch_integral) (p := 4) (q := 2)
    (M := 3 * Mσ ^ 4) (δ := fun n => r ^ n)
    hT (by norm_num) hint hbound hδ_pos hδ_sum hterms_nn hBC_sum

/-- Under bounded diffusion and usual conditions, the stochastic integral has a
    continuous modification on [0, T] that is adapted to the filtration.
    The adaptedness follows from the modification property SI'(t) =ᵐ SI(t)
    and the completeness of the filtration under usual conditions. -/
theorem stoch_integral_continuous_adapted_modification {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (huc : F.usualConditions μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T : ℝ) (hT : 0 < T) :
    ∃ SI' : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => SI' t ω) (Icc 0 T)) ∧
      (∀ t, t ∈ Icc 0 T → SI' t =ᵐ[μ] X.stoch_integral t) ∧
      (∀ t, t ∈ Icc 0 T → @Measurable Ω ℝ (F.σ_algebra t) _ (SI' t)) := by
  obtain ⟨SI', hcont, hmod⟩ := stoch_integral_continuous_modification X hMσ T hT
  exact ⟨SI', hcont, fun t ht => hmod t ht,
    fun t ht => Filtration.measurable_of_ae_eq huc (X.stoch_integral_adapted t ht.1) (hmod t ht)⟩

end SPDE
