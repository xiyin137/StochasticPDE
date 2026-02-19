/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Helpers.SimpleProcessDef
import StochasticPDE.Helpers.SetIntegralHelpers

/-!
# Simple Stochastic Integral Martingale Property

This file proves that the time-parameterized simple stochastic integral
`stochasticIntegral_at` is a martingale: for 0 ≤ s ≤ t and A ∈ F_s,
  ∫_A stochasticIntegral_at(H, W, t) dμ = ∫_A stochasticIntegral_at(H, W, s) dμ

## Main Results

* `setIntegral_adapted_mul_increment_zero` - For A ∈ F_r, g F_r-measurable
  and bounded, 0 ≤ r ≤ u: ∫_A g·(W_u - W_r) dμ = 0

* `setIntegral_summand_zero_of_future` - For A ∈ F_{t_j} and j ≤ i:
  ∫_A Hᵢ·ΔWᵢ dμ = 0

* `stochasticIntegral_at_martingale` - The full martingale property

## Application

These lemmas are the key step toward proving that the Itô integral
(L² limit of simple integrals) is a martingale.

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-! ## Key helper: adapted × future BM increment has zero set integral -/

/-- For A ∈ F_r, g F_r-measurable and bounded, 0 ≤ r ≤ u:
    ∫_A g·(W_u - W_r) dμ = 0.

    This is the fundamental building block for the martingale property.
    It combines filtration measurability, BM independence, and zero mean. -/
theorem setIntegral_adapted_mul_increment_zero
    (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    {g : Ω → ℝ} {r u : ℝ}
    (hg_meas : @Measurable Ω ℝ (W.F.σ_algebra r) _ g)
    (hg_int : Integrable g μ)
    (hr : 0 ≤ r) (hru : r ≤ u)
    (A : Set Ω) (hA : @MeasurableSet Ω (W.F.σ_algebra r) A) :
    ∫ ω in A, g ω * (W.toAdapted.process u ω - W.toAdapted.process r ω) ∂μ = 0 :=
  Probability.setIntegral_mul_zero_of_adapted_and_indep_zero_mean
    (W.F.le_ambient r) hg_meas hA hg_int.integrableOn
    (W.increment_integrable r u hr hru)
    (W.independent_increments r u hr hru)
    (W.increment_mean_zero r u hr hru)

/-! ## Integrability helpers -/

/-- A bounded adapted process value is integrable on a probability space. -/
theorem values_integrable (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (i : Fin H.n) :
    Integrable (H.values i) μ := by
  obtain ⟨Ci, hCi⟩ := hH_bdd i
  exact Integrable.of_bound
    ((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).aestronglyMeasurable
    Ci
    (ae_of_all μ (fun ω => by simp only [Real.norm_eq_abs]; exact hCi ω))

/-- H_i * (W_v - W_u) is integrable on any set, when H_i is bounded and 0 ≤ u ≤ v. -/
private theorem integrableOn_values_mul_increment
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (i : Fin H.n) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (A : Set Ω) :
    IntegrableOn (fun ω => H.values i ω *
      (W.toAdapted.process v ω - W.toAdapted.process u ω)) A μ := by
  apply Integrable.integrableOn
  obtain ⟨Ci, hCi⟩ := hH_bdd i
  exact Integrable.bdd_mul (c := Ci) (W.increment_integrable u v hu huv)
    ((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).aestronglyMeasurable
    (ae_of_all μ (fun ω => by simp only [Real.norm_eq_abs]; exact hCi ω))

/-! ## Future summand vanishing at partition times -/

/-- Individual future summand has zero set integral at partition times.
    For j ≤ i and A ∈ F_{t_j}: ∫_A Hᵢ·ΔWᵢ dμ = 0. -/
theorem setIntegral_summand_zero_of_future
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (j i : Fin H.n) (hi : (i : ℕ) + 1 < H.n)
    (hij : (j : ℕ) ≤ (i : ℕ))
    (A : Set Ω) (hA : @MeasurableSet Ω (W.F.σ_algebra (H.times j)) A) :
    ∫ ω in A, H.values i ω *
      (W.toAdapted.process (H.times ⟨i + 1, hi⟩) ω -
       W.toAdapted.process (H.times i) ω) ∂μ = 0 := by
  -- Lift A from F_{t_j} to F_{t_i}
  have hA_i : @MeasurableSet Ω (W.F.σ_algebra (H.times i)) A := by
    rcases Nat.eq_or_lt_of_le hij with h_eq | hlt
    · have hji : j = i := Fin.ext h_eq
      rw [← hji]; exact hA
    · exact (W.F.mono _ _ (le_of_lt (H.increasing j i (Fin.lt_def.mpr hlt)))) A hA
  -- Apply the key helper with r = t_i
  exact setIntegral_adapted_mul_increment_zero W (hH_adapted_all i)
    (values_integrable H W hH_adapted_all hH_bdd i)
    (hH_times_nn i)
    (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])))
    A hA_i

/-! ## Stochastic integral at time-parameterized martingale property -/

/-- The time-parameterized simple stochastic integral is a martingale:
    for 0 ≤ s ≤ t and A ∈ F_s,
    ∫_A stochasticIntegral_at(H, W, t) dμ = ∫_A stochasticIntegral_at(H, W, s) dμ.

    **Proof strategy**: Decompose into summands. For each summand, the difference
    between times t and s is either 0 or Hᵢ·(W_u - W_v) where v ≥ s. In the latter
    case, the set integral over A ∈ F_s ⊆ F_v vanishes by independence and zero mean.

    The hypotheses are the standard ones for simple process computations:
    - adapted: Hᵢ is F_{tᵢ}-measurable
    - bounded: each Hᵢ is uniformly bounded
    - nonneg times: all partition times are ≥ 0
    - s_nn: 0 ≤ s (needed for BM increment properties) -/
theorem stochasticIntegral_at_martingale
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (W.F.σ_algebra s) A) :
    ∫ ω in A, H.stochasticIntegral_at W t ω ∂μ =
    ∫ ω in A, H.stochasticIntegral_at W s ω ∂μ := by
  -- Unfold stochasticIntegral_at as a Finset sum
  simp only [stochasticIntegral_at, BrownianMotion.process]
  -- Define summand function for readability
  set f : Fin H.n → ℝ → Ω → ℝ := fun i τ ω =>
    if h : (i : ℕ) + 1 < H.n then
      if H.times ⟨i + 1, h⟩ ≤ τ then
        H.values i ω * (W.toAdapted.process (H.times ⟨i + 1, h⟩) ω -
          W.toAdapted.process (H.times i) ω)
      else if H.times i ≤ τ then
        H.values i ω * (W.toAdapted.process τ ω - W.toAdapted.process (H.times i) ω)
      else 0
    else 0 with hf_def
  -- Each summand is integrable (bounded × BM increment)
  have hf_int : ∀ i τ, 0 ≤ τ → IntegrableOn (f i τ) A μ := by
    intro i τ hτ
    simp only [hf_def]
    split_ifs with h h1 h2
    · -- Full interval: H_i * ΔW_i
      exact integrableOn_values_mul_increment H W hH_adapted_all hH_bdd i _ _
        (hH_times_nn i)
        (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, h⟩ (by simp [Fin.lt_def]))) A
    · -- Partial interval: H_i * (W_τ - W_{t_i})
      exact integrableOn_values_mul_increment H W hH_adapted_all hH_bdd i _ _
        (hH_times_nn i) h2 A
    · exact integrableOn_zero
    · exact integrableOn_zero
  -- Suffices to show each summand has equal set integrals
  suffices h_summand : ∀ i : Fin H.n,
      ∫ ω in A, f i t ω ∂μ = ∫ ω in A, f i s ω ∂μ by
    -- Pull integral through the Finset.sum
    have hint_t : ∀ i : Fin H.n, IntegrableOn (f i t) A μ := fun i => hf_int i t (le_trans hs hst)
    have hint_s : ∀ i : Fin H.n, IntegrableOn (f i s) A μ := fun i => hf_int i s hs
    rw [show (fun ω => ∑ i : Fin H.n, f i t ω) = (fun ω => ∑ i, f i t ω) from rfl,
        show (fun ω => ∑ i : Fin H.n, f i s ω) = (fun ω => ∑ i, f i s ω) from rfl]
    simp_rw [integral_finset_sum _ (fun i _ => hint_t i),
             integral_finset_sum _ (fun i _ => hint_s i)]
    exact Finset.sum_congr rfl (fun i _ => h_summand i)
  -- Prove each summand has equal set integrals
  intro i
  simp only [hf_def]
  -- Case split on whether i+1 < n
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    -- Case split on the relationship between s, t and partition times
    by_cases h_full_s : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ s
    · -- Case: t_{i+1} ≤ s ≤ t. Both sides are the full interval integral.
      simp only [if_pos h_full_s, if_pos (le_trans h_full_s hst)]
    · -- s < t_{i+1}
      push_neg at h_full_s
      by_cases h_start_s : H.times i ≤ s
      · -- Case: t_i ≤ s < t_{i+1}
        simp only [if_neg (not_le.mpr h_full_s), if_pos h_start_s]
        by_cases h_full_t : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ t
        · -- Subcase: t_i ≤ s < t_{i+1} ≤ t
          -- LHS = ∫_A H_i · (W_{t_{i+1}} - W_{t_i}) dμ
          -- RHS = ∫_A H_i · (W_s - W_{t_i}) dμ
          -- Diff = ∫_A H_i · (W_{t_{i+1}} - W_s) dμ = 0
          simp only [if_pos h_full_t]
          -- Rewrite as: RHS + ∫_A H_i·(W_{t_{i+1}} - W_s) = RHS
          suffices hdiff : ∫ ω in A, H.values i ω *
              (W.toAdapted.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
               W.toAdapted.process (H.times i) ω) ∂μ -
              ∫ ω in A, H.values i ω *
              (W.toAdapted.process s ω - W.toAdapted.process (H.times i) ω) ∂μ = 0 by
            linarith
          -- Combine into single integral
          rw [← integral_sub
            (integrableOn_values_mul_increment H W hH_adapted_all hH_bdd i _ _
              (hH_times_nn i)
              (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def]))) A)
            (integrableOn_values_mul_increment H W hH_adapted_all hH_bdd i _ _
              (hH_times_nn i) h_start_s A)]
          -- Simplify: H_i * (W_{t_{i+1}} - W_{t_i}) - H_i * (W_s - W_{t_i})
          --         = H_i * (W_{t_{i+1}} - W_s)
          simp_rw [show ∀ ω, H.values i ω *
              (W.toAdapted.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
               W.toAdapted.process (H.times i) ω) -
              H.values i ω *
              (W.toAdapted.process s ω - W.toAdapted.process (H.times i) ω) =
              H.values i ω *
              (W.toAdapted.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
               W.toAdapted.process s ω)
            from fun ω => by ring]
          -- Apply key helper with r = s
          have hHi_s_meas : @Measurable Ω ℝ (W.F.σ_algebra s) _ (H.values i) :=
            (hH_adapted_all i).mono (W.F.mono _ _ h_start_s) le_rfl
          exact setIntegral_adapted_mul_increment_zero W hHi_s_meas
            (values_integrable H W hH_adapted_all hH_bdd i)
            hs (le_of_lt h_full_s) A hA
        · -- Subcase: t_i ≤ s < t_{i+1} and t < t_{i+1}
          push_neg at h_full_t
          -- Both sides have partial intervals
          have h_start_t : H.times i ≤ t := le_trans h_start_s hst
          simp only [if_neg (not_le.mpr h_full_t), if_pos h_start_t]
          -- LHS = ∫_A H_i · (W_t - W_{t_i}) dμ
          -- RHS = ∫_A H_i · (W_s - W_{t_i}) dμ
          -- Diff = ∫_A H_i · (W_t - W_s) dμ = 0
          suffices hdiff : ∫ ω in A, H.values i ω *
              (W.toAdapted.process t ω - W.toAdapted.process (H.times i) ω) ∂μ -
              ∫ ω in A, H.values i ω *
              (W.toAdapted.process s ω - W.toAdapted.process (H.times i) ω) ∂μ = 0 by
            linarith
          rw [← integral_sub
            (integrableOn_values_mul_increment H W hH_adapted_all hH_bdd i _ _
              (hH_times_nn i) h_start_t A)
            (integrableOn_values_mul_increment H W hH_adapted_all hH_bdd i _ _
              (hH_times_nn i) h_start_s A)]
          simp_rw [show ∀ ω, H.values i ω *
              (W.toAdapted.process t ω - W.toAdapted.process (H.times i) ω) -
              H.values i ω *
              (W.toAdapted.process s ω - W.toAdapted.process (H.times i) ω) =
              H.values i ω * (W.toAdapted.process t ω - W.toAdapted.process s ω)
            from fun ω => by ring]
          have hHi_s_meas : @Measurable Ω ℝ (W.F.σ_algebra s) _ (H.values i) :=
            (hH_adapted_all i).mono (W.F.mono _ _ h_start_s) le_rfl
          exact setIntegral_adapted_mul_increment_zero W hHi_s_meas
            (values_integrable H W hH_adapted_all hH_bdd i) hs hst A hA
      · -- Case: s < t_i
        push_neg at h_start_s
        -- s-side: both outer and inner ifs are false, so f i s = 0
        simp only [if_neg (not_le.mpr h_full_s), if_neg (not_le.mpr h_start_s)]
        -- RHS = ∫_A 0 dμ = 0, so suffices to show LHS = 0
        have hA_i : @MeasurableSet Ω (W.F.σ_algebra (H.times i)) A :=
          (W.F.mono _ _ (le_of_lt h_start_s)) A hA
        have hrhs_zero : ∫ ω in A, (0 : ℝ) ∂μ = 0 := by
          rw [setIntegral_const, smul_zero]
        by_cases h_full_t : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ t
        · -- Subcase: s < t_i < t_{i+1} ≤ t (full interval at t, 0 at s)
          simp only [if_pos h_full_t]
          rw [hrhs_zero]
          exact setIntegral_adapted_mul_increment_zero W (hH_adapted_all i)
            (values_integrable H W hH_adapted_all hH_bdd i)
            (hH_times_nn i)
            (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])))
            A hA_i
        · push_neg at h_full_t
          by_cases h_start_t : H.times i ≤ t
          · -- Subcase: s < t_i ≤ t < t_{i+1} (partial at t, 0 at s)
            simp only [if_neg (not_le.mpr h_full_t), if_pos h_start_t]
            rw [hrhs_zero]
            exact setIntegral_adapted_mul_increment_zero W (hH_adapted_all i)
              (values_integrable H W hH_adapted_all hH_bdd i)
              (hH_times_nn i) h_start_t A hA_i
          · -- Subcase: s < t < t_i (both 0)
            simp only [if_neg (not_le.mpr h_full_t), if_neg h_start_t]
  · -- i+1 ≥ n: both sides are 0
    simp [dif_neg hi]

end SimpleProcess

end SPDE
