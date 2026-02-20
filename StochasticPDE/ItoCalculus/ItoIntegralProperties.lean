/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.SimpleIntegralMartingale
import StochasticPDE.ItoCalculus.L2LimitInfrastructure

/-!
Note: `ItoIntegral.is_martingale_proof` and `ItoIntegral.ito_isometry_proof` were
formerly in this file but have been moved to `StochasticIntegration.lean` to avoid
import cycles (these reference `ItoIntegral` which is defined there).
-/

/-!
# Itô Integral Properties

This file proves that the Itô integral is a martingale by combining:
- Phase 3: Simple stochastic integrals are martingales (`stochasticIntegral_at_martingale`)
- Phase 4: L² limits preserve the martingale set-integral property
  (`martingale_setIntegral_eq_of_L2_limit`)

## Main Results

* `stochasticIntegral_at_integrable` — Simple stochastic integrals of bounded
  adapted processes are integrable
* `ito_integral_martingale_setIntegral` — The Itô integral satisfies the
  martingale set-integral property

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-! ## Integrability of simple stochastic integrals -/

/-- A simple stochastic integral at time t is integrable when the process
    is bounded and adapted to the BM filtration, on a probability space.

    Proof: The integral is a finite sum of terms H_i * ΔW_i where H_i is bounded
    and ΔW_i is integrable (Gaussian). Each term is integrable by `Integrable.bdd_mul`,
    and the sum is integrable by `integrable_finset_sum`. -/
theorem stochasticIntegral_at_integrable
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (_ht : 0 ≤ t) :
    Integrable (H.stochasticIntegral_at W t) μ := by
  -- The integral is a finite sum; show each summand is integrable.
  unfold stochasticIntegral_at
  simp only [BrownianMotion.process]
  apply integrable_finset_sum
  intro i _
  -- Case split on whether i+1 < n (the dite condition)
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    -- Case split on t_{i+1} ≤ t
    by_cases h_full : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ t
    · -- Full interval: H_i(ω) * (W_{t_{i+1}} - W_{t_i})(ω)
      simp only [if_pos h_full]
      obtain ⟨Ci, hCi⟩ := hH_bdd i
      exact Integrable.bdd_mul (c := Ci)
        (W.increment_integrable (H.times i) (H.times ⟨(i : ℕ) + 1, hi⟩)
          (hH_times_nn i)
          (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def]))))
        ((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).aestronglyMeasurable
        (ae_of_all μ (fun ω => by simp only [Real.norm_eq_abs]; exact hCi ω))
    · simp only [if_neg h_full]
      -- Case split on t_i ≤ t
      by_cases h_start : H.times i ≤ t
      · -- Partial interval: H_i(ω) * (W_t - W_{t_i})(ω)
        simp only [if_pos h_start]
        obtain ⟨Ci, hCi⟩ := hH_bdd i
        exact Integrable.bdd_mul (c := Ci)
          (W.increment_integrable (H.times i) t (hH_times_nn i) h_start)
          ((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).aestronglyMeasurable
          (ae_of_all μ (fun ω => by simp only [Real.norm_eq_abs]; exact hCi ω))
      · -- Both partition times past t: summand is 0
        simp only [if_neg h_start]
        exact integrable_zero _ _ _
  · -- i+1 ≥ n: summand is 0
    simp only [dif_neg hi]
    exact integrable_zero _ _ _

/-- Square-integrability of the difference between a simple integral and a limit function. -/
theorem stochasticIntegral_at_sub_sq_integrable
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (f : Ω → ℝ) (hf_int : Integrable f μ)
    (hf_sq_int : Integrable (fun ω => (f ω)^2) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (H.stochasticIntegral_at W t ω - f ω) ^ 2) μ := by
  -- Strategy: show S_t - f ∈ L²(μ), then convert to integrability of square.
  -- S_t ∈ L² (finite sum of L² functions), f ∈ L² (given).
  have hS_int := stochasticIntegral_at_integrable H W hH_adapted_all hH_bdd hH_times_nn t ht
  have hSf_asm : AEStronglyMeasurable (fun ω => H.stochasticIntegral_at W t ω - f ω) μ :=
    hS_int.aestronglyMeasurable.sub hf_int.aestronglyMeasurable
  rw [← memLp_two_iff_integrable_sq hSf_asm]
  -- f ∈ L²
  have hf_memLp : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hf_int.aestronglyMeasurable).mpr hf_sq_int
  -- Suffices to show S_t ∈ L²
  suffices hS_memLp : MemLp (H.stochasticIntegral_at W t) 2 μ from hS_memLp.sub hf_memLp
  -- Show S_t ∈ L² via finite sum: S_t = Σᵢ aᵢ, each aᵢ ∈ L²
  unfold stochasticIntegral_at
  simp only [BrownianMotion.process]
  apply memLp_finset_sum
  intro i _
  -- Helper: bounded H_i × BM increment ∈ L²
  have h_mul_memLp : ∀ (s₁ s₂ : ℝ), 0 ≤ s₁ → s₁ ≤ s₂ →
      MemLp (fun ω => H.values i ω *
        (W.toAdapted.process s₂ ω - W.toAdapted.process s₁ ω)) 2 μ := by
    intro s₁ s₂ hs₁ hs₁₂
    have h_asm : AEStronglyMeasurable (fun ω => H.values i ω *
        (W.toAdapted.process s₂ ω - W.toAdapted.process s₁ ω)) μ :=
      ((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).mul
        (((W.toAdapted.adapted s₂).mono (W.F.le_ambient _) le_rfl).sub
          ((W.toAdapted.adapted s₁).mono (W.F.le_ambient _) le_rfl))
        |>.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq h_asm]
    -- (H_i · ΔW)² = H_i² · ΔW², bounded × integrable
    have hsq : (fun ω => (H.values i ω *
        (W.toAdapted.process s₂ ω - W.toAdapted.process s₁ ω)) ^ 2) =
      (fun ω => (H.values i ω) ^ 2 *
        (W.toAdapted.process s₂ ω - W.toAdapted.process s₁ ω) ^ 2) := by
      ext ω; ring
    rw [hsq]
    obtain ⟨C, hC⟩ := hH_bdd i
    exact Integrable.bdd_mul (c := C ^ 2)
      (W.increment_sq_integrable s₁ s₂ hs₁ hs₁₂)
      (((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).pow_const 2).aestronglyMeasurable
      (ae_of_all μ (fun ω => by
        simp only [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) 2))
  -- Case split on the dite/ite conditions
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    by_cases h_full : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ t
    · simp only [if_pos h_full]
      exact h_mul_memLp (H.times i) (H.times ⟨(i : ℕ) + 1, hi⟩)
        (hH_times_nn i)
        (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])))
    · simp only [if_neg h_full]
      by_cases h_start : H.times i ≤ t
      · simp only [if_pos h_start]
        exact h_mul_memLp (H.times i) t (hH_times_nn i) h_start
      · simp only [if_neg h_start]
        exact memLp_const (0 : ℝ)
  · simp only [dif_neg hi]
    exact memLp_const (0 : ℝ)

end SimpleProcess

/-! ## Itô integral martingale property -/

/-- The Itô integral satisfies the martingale set-integral property:
    for 0 ≤ s ≤ t ≤ T and A ∈ F_s, ∫_A I(t) dμ = ∫_A I(s) dμ.

    This is the core theorem connecting:
    - Phase 3: Simple process integrals are martingales
    - Phase 4: L² limits preserve the martingale property

    The proof structure:
    1. Extract the approximating simple processes from the L² limit
    2. Each simple integral S_n is a martingale (by `stochasticIntegral_at_martingale`)
    3. S_n → I in L² (by hypothesis)
    4. By `martingale_setIntegral_eq_of_L2_limit`, the limit I also satisfies
       the set-integral property -/
theorem ito_integral_martingale_setIntegral
    {F : Filtration Ω ℝ} {T : ℝ}
    (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (integral : ℝ → Ω → ℝ)
    -- Approximating simple processes with standard properties
    (approx : ℕ → SimpleProcess F)
    (hH_adapted : ∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (W.F.σ_algebra ((approx n).times i)) _ ((approx n).values i))
    (hH_bdd : ∀ n, ∀ i : Fin (approx n).n,
      ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C)
    (hH_times_nn : ∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i)
    -- L² convergence
    (hL2 : ∀ t : ℝ, 0 ≤ t → t ≤ T →
      Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) W t ω -
                                       integral t ω)^2 ∂μ)
        Filter.atTop (nhds 0))
    -- Integrability of the limit
    (hI_int : ∀ t, 0 ≤ t → t ≤ T → Integrable (integral t) μ)
    -- Square-integrability of the limit (for the sq_int condition)
    (hI_sq_int : ∀ t, 0 ≤ t → t ≤ T → Integrable (fun ω => (integral t ω) ^ 2) μ)
    -- The set-integral equality
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[W.F.σ_algebra s] A) :
    ∫ ω in A, integral t ω ∂μ = ∫ ω in A, integral s ω ∂μ := by
  -- Apply the L² limit infrastructure directly
  exact martingale_setIntegral_eq_of_L2_limit
    -- hM_int_s: limit is integrable at s
    (hI_int s hs (le_trans hst ht))
    -- hM_int_t: limit is integrable at t
    (hI_int t (le_trans hs hst) ht)
    -- hMn_int_s: each approximant is integrable at s
    (fun n => SimpleProcess.stochasticIntegral_at_integrable (approx n) W
      (hH_adapted n) (hH_bdd n) (hH_times_nn n) s hs)
    -- hMn_int_t: each approximant is integrable at t
    (fun n => SimpleProcess.stochasticIntegral_at_integrable (approx n) W
      (hH_adapted n) (hH_bdd n) (hH_times_nn n) t (le_trans hs hst))
    -- hMn_sq_int_s: square-integrability of differences at s
    (fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) W
      (hH_adapted n) (hH_bdd n) (hH_times_nn n)
      (integral s) (hI_int s hs (le_trans hst ht))
      (hI_sq_int s hs (le_trans hst ht)) s hs)
    -- hMn_sq_int_t: square-integrability of differences at t
    (fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) W
      (hH_adapted n) (hH_bdd n) (hH_times_nn n)
      (integral t) (hI_int t (le_trans hs hst) ht)
      (hI_sq_int t (le_trans hs hst) ht) t (le_trans hs hst))
    -- hL2_s: L² convergence at time s
    (hL2 s hs (le_trans hst ht))
    -- hL2_t: L² convergence at time t
    (hL2 t (le_trans hs hst) ht)
    -- hA: A is ambient-measurable
    (W.F.le_ambient s A hA)
    -- h_mart: each approximant satisfies the martingale set-integral property
    (fun n => SimpleProcess.stochasticIntegral_at_martingale (approx n) W
      (hH_adapted n) (hH_bdd n) (hH_times_nn n) s t hs hst A hA)

end SPDE
