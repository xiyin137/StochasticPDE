/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Helpers.CommonRefinement
import StochasticPDE.Helpers.SimpleProcessLinear
import StochasticPDE.Helpers.MergedValueAtTime
import StochasticPDE.Helpers.ItoIntegralProperties
import StochasticPDE.Probability.IndependenceHelpers
import StochasticPDE.Probability.Pythagoras

/-!
# Simple Process Isometry at Time t

This file proves the time-parameterized Itô isometry for simple processes:

  E[(∫₀ᵗ H dW)²] = E[∫₀ᵗ H(s)² ds]

where the LHS uses `stochasticIntegral_at` and the RHS uses `valueAtTime`.

## Main Results

* `SimpleProcess.isometry_at` — The quadratic isometry at time t
* `SimpleProcess.bilinear_isometry_at` — The bilinear isometry at time t

## Strategy

The proof uses the min-capped reformulation `stochasticIntegral_at_eq_min`:
  S(t) = Σᵢ Hᵢ · (W(min(tᵢ₊₁,t)) - W(min(tᵢ,t)))

Then:
1. Pythagoras: E[(Σaᵢ)²] = Σ E[aᵢ²] (cross terms vanish)
2. Diagonal: E[aᵢ²] = E[Hᵢ²] · (min(tᵢ₊₁,t) - min(tᵢ,t))
3. Connection: Σ E[Hᵢ²] · Δtᵢ_capped = E[∫₀ᵗ val² ds]

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-! ## Cross-term vanishing for min-capped increments -/

/-- Cross-term vanishing for min-capped increments: for i < j,
    E[Hᵢ·ΔWᵢ_cap · Hⱼ·ΔWⱼ_cap] = 0.

    The min-capped increment at j is either 0 (if tⱼ ≥ t) or
    starts at tⱼ > tᵢ₊₁, giving independence with the i-factor. -/
theorem cross_term_zero_at (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (_ht : 0 ≤ t)
    (i j : Fin H.n)
    (hi : (i : ℕ) + 1 < H.n) (hj : (j : ℕ) + 1 < H.n)
    (hij : (i : ℕ) < (j : ℕ)) :
    ∫ ω, (H.values i ω *
           (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
            W.process (min (H.times i) t) ω)) *
          (H.values j ω *
           (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
            W.process (min (H.times j) t) ω)) ∂μ = 0 := by
  -- Successor comparison helpers
  have hj_succ : j < (⟨(j : ℕ) + 1, hj⟩ : Fin H.n) := by
    show (j : ℕ) < (j : ℕ) + 1; omega
  have hi_succ : i < (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) := by
    show (i : ℕ) < (i : ℕ) + 1; omega
  -- If the j-increment is trivial (both endpoints capped to t), it's 0
  by_cases hjt : H.times j ≥ t
  · -- min(t_j, t) = min(t_{j+1}, t) = t, so ΔW_j_cap = 0
    have h1 : min (H.times j) t = t := min_eq_right hjt
    have h2 : min (H.times ⟨j + 1, hj⟩) t = t :=
      min_eq_right (le_trans hjt (le_of_lt (H.increasing j ⟨j + 1, hj⟩ hj_succ)))
    simp only [h1, h2, sub_self, mul_zero, MeasureTheory.integral_zero]
  · push_neg at hjt
    -- min(t_j, t) = t_j since t_j < t
    have hj_min : min (H.times j) t = H.times j := min_eq_left (le_of_lt hjt)
    -- Regroup: (Hᵢ·ΔWᵢ_cap) · (Hⱼ·ΔWⱼ_cap) = (Hᵢ·ΔWᵢ_cap·Hⱼ) · ΔWⱼ_cap
    have hregroup : ∀ ω,
        (H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω)) *
        (H.values j ω *
          (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
           W.process (min (H.times j) t) ω)) =
        (H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) *
        (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
         W.process (min (H.times j) t) ω) := by
      intro ω; ring
    simp_rw [hregroup, hj_min]
    -- Ordering helpers
    have htj_nn := hH_times_nn j
    have hjj1 : H.times j < min (H.times ⟨j + 1, hj⟩) t :=
      lt_min (H.increasing j ⟨j + 1, hj⟩ hj_succ) hjt
    have hij_fin : i < j := Fin.lt_def.mpr hij
    have hi_le_j : H.times i ≤ H.times j :=
      le_of_lt (H.increasing i j hij_fin)
    have hi1_le_j : H.times ⟨i + 1, hi⟩ ≤ H.times j := by
      by_cases h : (i : ℕ) + 1 = (j : ℕ)
      · have : (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) = j := by ext; exact h
        rw [this]
      · exact le_of_lt (H.increasing ⟨(i : ℕ) + 1, hi⟩ j (by show (i : ℕ) + 1 < (j : ℕ); omega))
    -- The product factor (Hᵢ·ΔWᵢ_cap·Hⱼ) is F_{t_j}-measurable
    have hX_meas : @Measurable Ω ℝ (W.F.σ_algebra (H.times j)) _
        (fun ω => H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) := by
      exact ((hH_adapted i).mono (W.F.mono _ _ hi_le_j) le_rfl |>.mul
        (((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_of_left_le hi1_le_j)) le_rfl).sub
         ((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_of_left_le hi_le_j)) le_rfl))).mul
        ((hH_adapted j).mono le_rfl le_rfl)
    -- The product factor is integrable (bounded × integrable pattern)
    have hX_int : Integrable
        (fun ω => H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) μ := by
      -- Regroup as (Hi * Hj) * ΔWi_cap
      have hregroup' : (fun ω => H.values i ω *
          (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
         H.values j ω) =
          (fun ω => (H.values i ω * H.values j ω) *
            (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
             W.process (min (H.times i) t) ω)) := by
        ext ω; ring
      rw [hregroup']
      -- ΔWi_cap is integrable (L² hence L¹)
      have hΔWi_int := W.increment_integrable _ _
        (le_min (hH_times_nn i) _ht)
        (min_le_min_right t (le_of_lt (H.increasing i ⟨i + 1, hi⟩ hi_succ)))
      -- Hi * Hj is bounded
      obtain ⟨Ci, hCi⟩ := hH_bdd i
      obtain ⟨Cj, hCj⟩ := hH_bdd j
      apply Integrable.bdd_mul hΔWi_int
      · exact (((hH_adapted i).mono (W.F.le_ambient _) le_rfl).mul
          ((hH_adapted j).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCi ω) (hCj ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hCi ω))
    -- ΔW_j_cap is integrable
    have hY_int : Integrable
        (fun ω => W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
         W.process (H.times j) ω) μ :=
      W.increment_integrable _ _ htj_nn (le_of_lt hjj1)
    -- ΔW_j_cap has mean 0
    have hY_mean : ∫ ω, (W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
        W.process (H.times j) ω) ∂μ = 0 :=
      W.increment_mean_zero _ _ htj_nn (le_of_lt hjj1)
    -- Independence: ΔW_j_cap is independent of F_{t_j}
    have hindep : Indep (W.F.σ_algebra (H.times j))
      (MeasurableSpace.comap (fun ω => W.process (min (H.times ⟨j + 1, hj⟩) t) ω -
        W.process (H.times j) ω) inferInstance) μ :=
      W.independent_increments _ _ htj_nn (le_of_lt hjj1)
    -- Apply the key lemma: E[X·Y] = 0
    exact SPDE.Probability.integral_mul_zero_of_indep_zero_mean
      (W.F.le_ambient _) hX_meas hX_int hY_int hindep hY_mean

/-! ## The isometry at time t -/

/-- The isometry for simple processes at time t:
    E[(∫₀ᵗ H dW)²] = E[∫₀ᵗ H(s)² ds].

    Uses the min-capped reformulation of `stochasticIntegral_at`,
    Pythagoras (cross terms vanish), and diagonal computation. -/
theorem isometry_at (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, (H.stochasticIntegral_at W t ω) ^ 2 ∂μ =
    ∫ ω, (∫ s in Set.Icc 0 t, (H.valueAtTime s ω) ^ 2 ∂volume) ∂μ := by
  -- Derived: square integrability from boundedness
  have hH_sq_int : ∀ k : Fin H.n, Integrable (fun ω => (H.values k ω) ^ 2) μ := by
    intro k; obtain ⟨Ck, hCk⟩ := hH_bdd k
    exact Integrable.of_bound
      (((hH_adapted k).mono (W.F.le_ambient _) le_rfl).pow_const 2).aestronglyMeasurable
      (Ck ^ 2) (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        calc |H.values k ω ^ 2| = |H.values k ω| ^ 2 := by rw [abs_pow]
          _ ≤ Ck ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hCk ω) 2)
  -- Define the min-capped summands a_i(ω) = dite(i+1<n, H_i·ΔW_cap_i, 0)
  set a : Fin H.n → Ω → ℝ := fun i ω =>
    if h : (i : ℕ) + 1 < H.n then
      H.values i ω * (W.process (min (H.times ⟨i + 1, h⟩) t) ω -
                       W.process (min (H.times i) t) ω)
    else 0 with ha_def
  -- Step 1: Rewrite LHS as E[(Σ aᵢ)²]
  have hI : ∀ ω, H.stochasticIntegral_at W t ω = ∑ i, a i ω := by
    intro ω; simp [stochasticIntegral_at_eq_min, a]
  simp_rw [hI]
  -- Step 2: Rewrite RHS using step function integral
  simp_rw [valueAtTime_sq_integral_eq_sum H hH_times_nn t ht]
  -- Step 3: Cross-product integrability
  have h_cross_int : ∀ i j : Fin H.n,
      Integrable (fun ω => a i ω * a j ω) μ := by
    intro i j; simp only [ha_def]
    split_ifs with hi hj hj
    · obtain ⟨Ci, hCi⟩ := hH_bdd i; obtain ⟨Cj, hCj⟩ := hH_bdd j
      have hregroup_ij : (fun ω =>
          (H.values i ω * (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
            W.process (min (H.times i) t) ω)) *
          (H.values j ω * (W.process (min (H.times ⟨↑j + 1, hj⟩) t) ω -
            W.process (min (H.times j) t) ω))) =
          (fun ω => (H.values i ω * H.values j ω) *
            ((W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
              W.process (min (H.times i) t) ω) *
             (W.process (min (H.times ⟨↑j + 1, hj⟩) t) ω -
              W.process (min (H.times j) t) ω))) := by ext ω; ring
      rw [hregroup_ij]
      have hi_succ : i < (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) := by simp [Fin.lt_def]
      have hj_succ : j < (⟨(j : ℕ) + 1, hj⟩ : Fin H.n) := by simp [Fin.lt_def]
      have hΔWi_sq := W.increment_sq_integrable _ _
        (le_min (hH_times_nn i) ht)
        (min_le_min_right t (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ hi_succ)))
      have hΔWj_sq := W.increment_sq_integrable _ _
        (le_min (hH_times_nn j) ht)
        (min_le_min_right t (le_of_lt (H.increasing j ⟨(j : ℕ) + 1, hj⟩ hj_succ)))
      have hΔW_prod_int : Integrable (fun ω =>
          (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
           W.process (min (H.times i) t) ω) *
          (W.process (min (H.times ⟨↑j + 1, hj⟩) t) ω -
           W.process (min (H.times j) t) ω)) μ := by
        apply Integrable.mono' (hΔWi_sq.add hΔWj_sq)
        · exact (((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl).sub
            ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl)).mul
            (((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl).sub
            ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl))
            |>.aestronglyMeasurable
        · filter_upwards with ω
          simp only [Real.norm_eq_abs, BrownianMotion.process, Pi.add_apply]
          set u := W.toAdapted.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
            W.toAdapted.process (min (H.times i) t) ω
          set v := W.toAdapted.process (min (H.times ⟨↑j + 1, hj⟩) t) ω -
            W.toAdapted.process (min (H.times j) t) ω
          rw [abs_mul]
          nlinarith [sq_abs u, sq_abs v, sq_nonneg (|u| - |v|),
            mul_nonneg (abs_nonneg u) (abs_nonneg v)]
      apply Integrable.bdd_mul hΔW_prod_int
      · exact (((hH_adapted i).mono (W.F.le_ambient _) le_rfl).mul
          ((hH_adapted j).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCi ω) (hCj ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hCi ω))
    all_goals simp [integrable_zero _ _ μ]
  -- Step 4: Orthogonality (cross terms vanish)
  have h_orthog : ∀ i j : Fin H.n, i ≠ j →
      ∫ ω, a i ω * a j ω ∂μ = 0 := by
    intro i j hij; simp only [ha_def]
    split_ifs with hi hj hj
    · rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact cross_term_zero_at H W hH_adapted hH_bdd hH_times_nn t ht i j hi hj h
      · simp_rw [show ∀ ω, (H.values i ω *
            (W.process (min (H.times ⟨(i : ℕ) + 1, hi⟩) t) ω -
             W.process (min (H.times i) t) ω)) *
            (H.values j ω *
            (W.process (min (H.times ⟨(j : ℕ) + 1, hj⟩) t) ω -
             W.process (min (H.times j) t) ω)) =
            (H.values j ω *
            (W.process (min (H.times ⟨(j : ℕ) + 1, hj⟩) t) ω -
             W.process (min (H.times j) t) ω)) *
            (H.values i ω *
            (W.process (min (H.times ⟨(i : ℕ) + 1, hi⟩) t) ω -
             W.process (min (H.times i) t) ω))
          from fun ω => by ring]
        exact cross_term_zero_at H W hH_adapted hH_bdd hH_times_nn t ht j i hj hi h
    all_goals simp
  -- Step 5: Apply Pythagoras: E[(Σ aᵢ)²] = Σ E[aᵢ²]
  rw [SPDE.Probability.sum_sq_integral_eq_sum_integral_sq a h_cross_int h_orthog]
  -- Step 6: Push integral inside RHS sum
  rw [integral_finset_sum _ (fun i _ => by
    by_cases hi : (i : ℕ) + 1 < H.n
    · simp only [dif_pos hi]; exact (hH_sq_int i).mul_const _
    · simp only [dif_neg hi]; exact integrable_zero _ _ _)]
  -- Step 7: Match term by term (diagonal factorization)
  congr 1; ext i; simp only [ha_def]
  split_ifs with hi
  · -- Non-trivial: E[(Hi·ΔW_cap)²] = ∫ Hi²·Δt_cap ∂μ
    have hsq : ∀ ω, (H.values i ω * (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
        W.process (min (H.times i) t) ω)) ^ 2 =
        (H.values i ω) ^ 2 * (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
        W.process (min (H.times i) t) ω) ^ 2 := fun ω => by ring
    simp_rw [hsq]
    have hi_succ : i < (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) := by simp [Fin.lt_def]
    -- Case split: t_i ≥ t vs t_i < t
    by_cases hit : H.times i ≥ t
    · -- t_i ≥ t: both sides are 0
      have h1 : min (H.times i) t = t := min_eq_right hit
      have h2 : min (H.times ⟨↑i + 1, hi⟩) t = t :=
        min_eq_right (le_trans hit (le_of_lt (H.increasing i ⟨↑i + 1, hi⟩ hi_succ)))
      simp [h1, h2, sub_self]
    · push_neg at hit -- hit : H.times i < t
      have h_min_i : min (H.times i) t = H.times i := min_eq_left (le_of_lt hit)
      have h_min_le : H.times i ≤ min (H.times ⟨↑i + 1, hi⟩) t :=
        le_min (le_of_lt (H.increasing i ⟨↑i + 1, hi⟩ hi_succ)) (le_of_lt hit)
      rw [h_min_i]
      -- Factor E[Hi²·ΔW²] = E[Hi²]·E[ΔW²] using independence
      set Δt_cap := min (H.times ⟨↑i + 1, hi⟩) t - H.times i
      -- Hi² is F_{t_i}-measurable
      have hHsq_meas : @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _
          (fun ω => (H.values i ω) ^ 2) :=
        (hH_adapted i).pow_const 2
      -- ΔW² is integrable
      have hΔW_sq_int : Integrable (fun ω =>
          (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
           W.process (H.times i) ω) ^ 2) μ :=
        W.increment_sq_integrable _ _ (hH_times_nn i) h_min_le
      -- Independence: ΔW is independent of F_{t_i}
      have hindep : Indep (W.F.σ_algebra (H.times i))
          (MeasurableSpace.comap (fun ω =>
            W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
            W.process (H.times i) ω) inferInstance) μ :=
        W.independent_increments _ _ (hH_times_nn i) h_min_le
      -- Derive independence for squared increment
      have hindep_sq : Indep (W.F.σ_algebra (H.times i))
          (MeasurableSpace.comap (fun ω =>
            (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
             W.process (H.times i) ω) ^ 2) inferInstance) μ := by
        apply indep_of_indep_of_le_right hindep
        intro s hs; obtain ⟨u, hu, rfl⟩ := hs
        exact ⟨(fun x => x ^ 2) ⁻¹' u, (measurable_id.pow_const 2) hu, rfl⟩
      -- Factor: E[Hi²·ΔW²] = E[Hi²]·E[ΔW²]
      have hfact : ∫ ω, (H.values i ω) ^ 2 *
          (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
           W.process (H.times i) ω) ^ 2 ∂μ =
          (∫ ω, (H.values i ω) ^ 2 ∂μ) *
          (∫ ω, (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
                 W.process (H.times i) ω) ^ 2 ∂μ) :=
        SPDE.Probability.integral_mul_of_indep_sigma_algebra
          (W.F.le_ambient _) hHsq_meas (hH_sq_int i) hΔW_sq_int hindep_sq
      -- Variance: E[ΔW²] = Δt_cap
      have hvar : ∫ ω, (W.process (min (H.times ⟨↑i + 1, hi⟩) t) ω -
          W.process (H.times i) ω) ^ 2 ∂μ = Δt_cap :=
        W.increment_variance _ _ (hH_times_nn i) h_min_le
      -- Pull constant from RHS: ∫ Hi²·Δt_cap = Δt_cap · ∫ Hi²
      have hpull : ∫ ω, (H.values i ω) ^ 2 * Δt_cap ∂μ =
          (∫ ω, (H.values i ω) ^ 2 ∂μ) * Δt_cap :=
        integral_mul_const Δt_cap _
      rw [hfact, hvar, hpull]
  · -- Invalid index: both sides 0
    simp [sq]

/-- Bilinear isometry at time t: E[S₁(t)·S₂(t)] = E[∫₀ᵗ val₁·val₂ ds].

    Proved by polarization from `isometry_at` combined with
    `exists_linear_simple_integral` for the common refinement. -/
theorem bilinear_isometry_at (H₁ H₂ : SimpleProcess F)
    (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH₁_adapted : ∀ i : Fin H₁.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H₁.times i)) _ (H₁.values i))
    (hH₂_adapted : ∀ i : Fin H₂.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H₂.times i)) _ (H₂.values i))
    (hH₁_bdd : ∀ i : Fin H₁.n, ∃ C : ℝ, ∀ ω, |H₁.values i ω| ≤ C)
    (hH₂_bdd : ∀ i : Fin H₂.n, ∃ C : ℝ, ∀ ω, |H₂.values i ω| ≤ C)
    (hH₁_nn : ∀ i : Fin H₁.n, 0 ≤ H₁.times i)
    (hH₂_nn : ∀ i : Fin H₂.n, 0 ≤ H₂.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, H₁.stochasticIntegral_at W t ω * H₂.stochasticIntegral_at W t ω ∂μ =
    ∫ ω, (∫ s in Set.Icc 0 t,
      H₁.valueAtTime s ω * H₂.valueAtTime s ω ∂volume) ∂μ := by
  -- Polarization: 2*E[S₁·S₂] = E[(S₁+S₂)²] - E[S₁²] - E[S₂²]
  -- and similarly for RHS. Both sides match via isometry_at.
  -- Step 1: Merged process M with M.S(t) = S₁(t) + S₂(t)
  set M := mergedProcess H₁ H₂ 1 1
  have hM_adapted : ∀ i : Fin M.n,
      @Measurable Ω ℝ (W.F.σ_algebra (M.times i)) _ (M.values i) := by
    intro i
    exact (measurable_const.mul (valueAtTime_measurable_filtration H₁ _ hH₁_adapted)).add
      (measurable_const.mul (valueAtTime_measurable_filtration H₂ _ hH₂_adapted))
  have hM_bdd : ∀ i : Fin M.n, ∃ C : ℝ, ∀ ω, |M.values i ω| ≤ C := by
    intro i
    obtain ⟨C₁, hC₁⟩ := valueAtTime_bounded H₁ _ hH₁_bdd
    obtain ⟨C₂, hC₂⟩ := valueAtTime_bounded H₂ _ hH₂_bdd
    exact ⟨|1| * C₁ + |1| * C₂, fun ω => by
      calc |(mergedProcess H₁ H₂ 1 1).values i ω|
          = |1 * H₁.valueAtTime _ ω + 1 * H₂.valueAtTime _ ω| := rfl
        _ ≤ |1 * H₁.valueAtTime _ ω| + |1 * H₂.valueAtTime _ ω| := abs_add_le _ _
        _ = |1| * |H₁.valueAtTime _ ω| + |1| * |H₂.valueAtTime _ ω| := by
            rw [abs_mul, abs_mul]
        _ ≤ |1| * C₁ + |1| * C₂ := add_le_add
            (mul_le_mul_of_nonneg_left (hC₁ ω) (abs_nonneg 1))
            (mul_le_mul_of_nonneg_left (hC₂ ω) (abs_nonneg 1))⟩
  have hM_nn : ∀ i : Fin M.n, 0 ≤ M.times i := by
    intro i
    have hmem := mergedProcess_times_mem H₁ H₂ 1 1 i
    simp only [mergedFinset, Finset.mem_union, partitionFinset, Finset.mem_image,
      Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [← hj]; exact hH₁_nn j
    · rw [← hj]; exact hH₂_nn j
  -- Step 2: Three isometry results
  have hisoM := isometry_at M W hM_adapted hM_bdd hM_nn t ht
  have hiso₁ := isometry_at H₁ W hH₁_adapted hH₁_bdd hH₁_nn t ht
  have hiso₂ := isometry_at H₂ W hH₂_adapted hH₂_bdd hH₂_nn t ht
  -- Step 3: Rewrite hisoM using merged process identities
  have hM_int : ∀ ω, M.stochasticIntegral_at W t ω =
      H₁.stochasticIntegral_at W t ω + H₂.stochasticIntegral_at W t ω := by
    intro ω; have := mergedProcess_integral_eq H₁ H₂ W 1 1 t ω; linarith
  have hM_val : ∀ s ω, M.valueAtTime s ω =
      H₁.valueAtTime s ω + H₂.valueAtTime s ω := by
    intro s ω; have := mergedProcess_valueAtTime_linear H₁ H₂ 1 1 s ω; linarith
  -- Rewrite LHS of hisoM: M.S² → (S₁+S₂)² → S₁² + 2*S₁*S₂ + S₂²
  simp_rw [hM_int, show ∀ (a b : ℝ), (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2
    from fun a b => by ring] at hisoM
  -- Rewrite RHS of hisoM: M.val² → (v₁+v₂)² → v₁² + 2*v₁*v₂ + v₂²
  simp_rw [hM_val, show ∀ (a b : ℝ), (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2
    from fun a b => by ring] at hisoM
  -- Step 4: Integrability conditions for integral splitting
  -- L² integrability of stochastic integrals (from sub_sq with f=0)
  have hS₁_sq_int : Integrable (fun ω => (H₁.stochasticIntegral_at W t ω) ^ 2) μ := by
    have h := stochasticIntegral_at_sub_sq_integrable H₁ W hH₁_adapted hH₁_bdd hH₁_nn
      (fun _ => 0) (integrable_const 0) (by simp) t ht
    simp only [sub_zero] at h; exact h
  have hS₂_sq_int : Integrable (fun ω => (H₂.stochasticIntegral_at W t ω) ^ 2) μ := by
    have h := stochasticIntegral_at_sub_sq_integrable H₂ W hH₂_adapted hH₂_bdd hH₂_nn
      (fun _ => 0) (integrable_const 0) (by simp) t ht
    simp only [sub_zero] at h; exact h
  -- S₁*S₂ integrable by AM-GM: |S₁*S₂| ≤ (S₁²+S₂²)
  have hS₁₂_int : Integrable (fun ω =>
      H₁.stochasticIntegral_at W t ω * H₂.stochasticIntegral_at W t ω) μ := by
    apply Integrable.mono' (hS₁_sq_int.add hS₂_sq_int)
    · exact (Integrable.aestronglyMeasurable
          (stochasticIntegral_at_integrable H₁ W hH₁_adapted hH₁_bdd hH₁_nn t ht)).mul
        (Integrable.aestronglyMeasurable
          (stochasticIntegral_at_integrable H₂ W hH₂_adapted hH₂_bdd hH₂_nn t ht))
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_mul]; nlinarith [sq_abs (H₁.stochasticIntegral_at W t ω),
        sq_abs (H₂.stochasticIntegral_at W t ω),
        sq_nonneg (|H₁.stochasticIntegral_at W t ω| - |H₂.stochasticIntegral_at W t ω|)]
  -- Uniform bounds on valueAtTime for IntegrableOn conditions
  obtain ⟨C₁, _, hC₁⟩ := valueAtTime_uniform_bounded H₁ hH₁_bdd
  obtain ⟨C₂, _, hC₂⟩ := valueAtTime_uniform_bounded H₂ hH₂_bdd
  -- Joint measurability for section measurability
  have hjm₁ := valueAtTime_jointly_measurable H₁
  have hjm₂ := valueAtTime_jointly_measurable H₂
  -- Section measurability helper
  have hmeas_s₁ : ∀ ω, Measurable (fun s => H₁.valueAtTime s ω) :=
    fun ω => hjm₁.comp (measurable_id.prodMk measurable_const)
  have hmeas_s₂ : ∀ ω, Measurable (fun s => H₂.valueAtTime s ω) :=
    fun ω => hjm₂.comp (measurable_id.prodMk measurable_const)
  -- IntegrableOn conditions (bounded measurable on finite measure interval)
  haveI : Fact (volume (Set.Icc 0 t) < ⊤) := ⟨measure_Icc_lt_top⟩
  have hion_sq₁ : ∀ ω, IntegrableOn (fun s => (H₁.valueAtTime s ω) ^ 2)
      (Set.Icc 0 t) volume := fun ω =>
    Integrable.of_bound
      ((hmeas_s₁ ω).pow_const 2).aestronglyMeasurable
      (C₁ ^ 2) (ae_of_all _ fun s => by
        simp only [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC₁ s ω) 2)
  have hion_sq₂ : ∀ ω, IntegrableOn (fun s => (H₂.valueAtTime s ω) ^ 2)
      (Set.Icc 0 t) volume := fun ω =>
    Integrable.of_bound
      ((hmeas_s₂ ω).pow_const 2).aestronglyMeasurable
      (C₂ ^ 2) (ae_of_all _ fun s => by
        simp only [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC₂ s ω) 2)
  have hion_prod : ∀ ω, IntegrableOn (fun s => H₁.valueAtTime s ω * H₂.valueAtTime s ω)
      (Set.Icc 0 t) volume := fun ω =>
    Integrable.of_bound
      ((hmeas_s₁ ω).mul (hmeas_s₂ ω)).aestronglyMeasurable
      (C₁ * C₂) (ae_of_all _ fun s => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hC₁ s ω) (hC₂ s ω) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hC₁ s ω)))
  -- Split inner integrals (for ALL ω)
  have h_inner_split : ∀ ω,
      ∫ s in Set.Icc 0 t, ((H₁.valueAtTime s ω) ^ 2 +
        2 * (H₁.valueAtTime s ω * H₂.valueAtTime s ω) +
        (H₂.valueAtTime s ω) ^ 2) ∂volume =
      (∫ s in Set.Icc 0 t, (H₁.valueAtTime s ω) ^ 2 ∂volume) +
      2 * (∫ s in Set.Icc 0 t, H₁.valueAtTime s ω * H₂.valueAtTime s ω ∂volume) +
      (∫ s in Set.Icc 0 t, (H₂.valueAtTime s ω) ^ 2 ∂volume) := by
    intro ω
    -- Reassociate goal LHS from (a+b)+c to a+(b+c) to match integral_add
    simp_rw [show ∀ s, H₁.valueAtTime s ω ^ 2 +
        2 * (H₁.valueAtTime s ω * H₂.valueAtTime s ω) +
        H₂.valueAtTime s ω ^ 2 =
        H₁.valueAtTime s ω ^ 2 +
        (2 * (H₁.valueAtTime s ω * H₂.valueAtTime s ω) +
        H₂.valueAtTime s ω ^ 2) from fun s => by ring]
    have h1 := integral_add (hion_sq₁ ω) (((hion_prod ω).const_mul 2).add (hion_sq₂ ω))
    simp only [Pi.add_apply] at h1
    have h2 := integral_add ((hion_prod ω).const_mul 2) (hion_sq₂ ω)
    have h3 := integral_const_mul (μ := volume.restrict (Set.Icc 0 t)) (2 : ℝ)
      (fun s => H₁.valueAtTime s ω * H₂.valueAtTime s ω)
    linarith
  simp_rw [h_inner_split] at hisoM
  -- Outer integrability for inner integral functions
  -- Helper: v^2 ≤ C^2 from uniform bound
  have h_sq_le₁ : ∀ s ω, H₁.valueAtTime s ω ^ 2 ≤ C₁ ^ 2 := fun s ω => by
    have := pow_le_pow_left₀ (abs_nonneg _) (hC₁ s ω) 2; rwa [sq_abs] at this
  have h_sq_le₂ : ∀ s ω, H₂.valueAtTime s ω ^ 2 ≤ C₂ ^ 2 := fun s ω => by
    have := pow_le_pow_left₀ (abs_nonneg _) (hC₂ s ω) 2; rwa [sq_abs] at this
  have hR₁_int : Integrable (fun ω =>
      ∫ s in Set.Icc 0 t, (H₁.valueAtTime s ω) ^ 2 ∂volume) μ := by
    apply Integrable.of_bound
      (hjm₁.pow_const 2 |>.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Icc 0 t))).aestronglyMeasurable
      (C₁ ^ 2 * t)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    calc ∫ s in Set.Icc 0 t, (H₁.valueAtTime s ω) ^ 2 ∂volume
        ≤ ∫ _ in Set.Icc 0 t, C₁ ^ 2 ∂volume :=
          integral_mono (hion_sq₁ ω) (integrable_const (C₁ ^ 2))
            (fun s => h_sq_le₁ s ω)
      _ = C₁ ^ 2 * t := by
          rw [integral_const, smul_eq_mul, mul_comm]; congr 1
          simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t - 0)]; ring
  have hR₂_int : Integrable (fun ω =>
      ∫ s in Set.Icc 0 t, (H₂.valueAtTime s ω) ^ 2 ∂volume) μ := by
    apply Integrable.of_bound
      (hjm₂.pow_const 2 |>.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Icc 0 t))).aestronglyMeasurable
      (C₂ ^ 2 * t)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    calc ∫ s in Set.Icc 0 t, (H₂.valueAtTime s ω) ^ 2 ∂volume
        ≤ ∫ _ in Set.Icc 0 t, C₂ ^ 2 ∂volume :=
          integral_mono (hion_sq₂ ω) (integrable_const (C₂ ^ 2))
            (fun s => h_sq_le₂ s ω)
      _ = C₂ ^ 2 * t := by
          rw [integral_const, smul_eq_mul, mul_comm]; congr 1
          simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t - 0)]; ring
  have hR₁₂_int : Integrable (fun ω =>
      ∫ s in Set.Icc 0 t, H₁.valueAtTime s ω * H₂.valueAtTime s ω ∂volume) μ := by
    apply Integrable.mono' (hR₁_int.add hR₂_int)
    · exact ((hjm₁.mul hjm₂).stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Icc 0 t))).aestronglyMeasurable
    · have h_bound : ∀ s ω, |H₁.valueAtTime s ω * H₂.valueAtTime s ω| ≤
          (H₁.valueAtTime s ω) ^ 2 + (H₂.valueAtTime s ω) ^ 2 := by
        intro s ω; rw [abs_mul]
        nlinarith [sq_abs (H₁.valueAtTime s ω), sq_abs (H₂.valueAtTime s ω),
          sq_nonneg (|H₁.valueAtTime s ω| - |H₂.valueAtTime s ω|)]
      filter_upwards with ω
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs]
      calc |∫ s in Set.Icc 0 t, H₁.valueAtTime s ω * H₂.valueAtTime s ω ∂volume|
          ≤ ∫ s in Set.Icc 0 t, |H₁.valueAtTime s ω * H₂.valueAtTime s ω| ∂volume := by
            rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
        _ ≤ ∫ s in Set.Icc 0 t, ((H₁.valueAtTime s ω) ^ 2 +
            (H₂.valueAtTime s ω) ^ 2) ∂volume := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
              ((hion_sq₁ ω).add (hion_sq₂ ω))
            exact ae_of_all _ fun s => h_bound s ω
        _ = _ := integral_add (hion_sq₁ ω) (hion_sq₂ ω)
  -- Step 5: Split outer integrals and conclude by linarith
  -- Split LHS of hisoM: ∫(S₁²+2S₁S₂+S₂²) = ∫S₁² + 2∫S₁S₂ + ∫S₂²
  have hL1 := integral_add (hS₁_sq_int.add (hS₁₂_int.const_mul 2)) hS₂_sq_int
  simp only [Pi.add_apply] at hL1
  have hL2 := integral_add hS₁_sq_int (hS₁₂_int.const_mul 2)
  have hL3 := integral_const_mul (μ := μ) (2 : ℝ)
    (fun ω => H₁.stochasticIntegral_at W t ω * H₂.stochasticIntegral_at W t ω)
  -- Split RHS of hisoM: ∫(R₁+2R₁₂+R₂) = ∫R₁ + 2∫R₁₂ + ∫R₂
  have hR1 := integral_add (hR₁_int.add (hR₁₂_int.const_mul 2)) hR₂_int
  simp only [Pi.add_apply] at hR1
  have hR2 := integral_add hR₁_int (hR₁₂_int.const_mul 2)
  have hR3 := integral_const_mul (μ := μ) (2 : ℝ)
    (fun ω => ∫ s in Set.Icc 0 t, H₁.valueAtTime s ω * H₂.valueAtTime s ω ∂volume)
  linarith

end SimpleProcess

end SPDE
