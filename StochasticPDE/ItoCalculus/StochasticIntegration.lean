/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.ItoIntegralProperties
import StochasticPDE.ItoCalculus.AdaptedLimit
import StochasticPDE.ItoCalculus.SimpleProcessLinear
import StochasticPDE.ItoCalculus.MergedValueAtTime
import StochasticPDE.ItoCalculus.IsometryAt
import StochasticPDE.ItoCalculus.GronwallForSDE
import StochasticPDE.ItoCalculus.ProductL2Convergence
import StochasticPDE.ItoCalculus.IteratedProductConvergence
import StochasticPDE.ItoCalculus.Probability.IndependenceHelpers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Stochastic Integration (Itô Calculus)

This file develops stochastic integration with respect to Brownian motion
and more general semimartingales.

## Main Definitions

* `StochasticIntegral` - The Itô integral ∫₀ᵗ H_s dW_s
* `ItoProcess` - Processes of the form dX = μ dt + σ dW
* `ItoFormula` - Itô's formula for C² functions

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus"
* Revuz, Yor, "Continuous Martingales and Brownian Motion"
-/

namespace SPDE

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Simple Processes

The `SimpleProcess` structure, `stochasticIntegral`, and `stochasticIntegral_at` are
defined in `Helpers/SimpleProcessDef.lean` to avoid import cycles with helper files.
The isometry proof and other theorems are proved here. -/

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-! ### Helper lemmas for the Itô isometry -/

/-- Helper: for i-1 < j in a simple process, times (i-1) < times j -/
private theorem times_pred_lt_times (H : SimpleProcess F) {i j : Fin H.n}
    (hi0 : (i : ℕ) > 0) (hij : (i : ℕ) ≤ (j : ℕ)) :
    H.times ⟨(i : ℕ) - 1, by omega⟩ < H.times j := by
  apply H.increasing ⟨(i : ℕ) - 1, by omega⟩ j
  simp only [Fin.lt_def]; omega

/-- Cross-term vanishing: for i < j, E[Hᵢ·ΔWᵢ · Hⱼ·ΔWⱼ] = 0.

    Proof: regroup as E[(Hᵢ·ΔWᵢ·Hⱼ) · ΔWⱼ], show the first factor is
    F_{tⱼ}-measurable, ΔWⱼ is independent of F_{tⱼ} with zero mean,
    then apply integral factorization. -/
theorem cross_term_zero (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (i j : Fin H.n)
    (hi : (i : ℕ) + 1 < H.n) (hj : (j : ℕ) + 1 < H.n)
    (hij : (i : ℕ) < (j : ℕ)) :
    ∫ ω, (H.values i ω * (W.process (H.times ⟨i + 1, hi⟩) ω - W.process (H.times i) ω)) *
         (H.values j ω * (W.process (H.times ⟨j + 1, hj⟩) ω - W.process (H.times j) ω)) ∂μ = 0 := by
  -- Regroup: (Hᵢ·ΔWᵢ) · (Hⱼ·ΔWⱼ) = (Hᵢ·ΔWᵢ·Hⱼ) · ΔWⱼ
  have hregroup : ∀ ω,
      (H.values i ω * (W.process (H.times ⟨i + 1, hi⟩) ω - W.process (H.times i) ω)) *
      (H.values j ω * (W.process (H.times ⟨j + 1, hj⟩) ω - W.process (H.times j) ω)) =
      (H.values i ω * (W.process (H.times ⟨i + 1, hi⟩) ω - W.process (H.times i) ω) * H.values j ω) *
      (W.process (H.times ⟨j + 1, hj⟩) ω - W.process (H.times j) ω) := by
    intro ω; ring
  simp_rw [hregroup]
  -- Ordering helper
  have hjj1 : H.times j < H.times ⟨(j : ℕ) + 1, hj⟩ :=
    H.increasing j ⟨(j : ℕ) + 1, hj⟩ (by simp [Fin.lt_def])
  have hii1 : H.times i < H.times ⟨(i : ℕ) + 1, hi⟩ :=
    H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])
  have hij_times : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ H.times j := by
    by_cases h : (i : ℕ) + 1 = (j : ℕ)
    · have : (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) = j := by ext; exact h
      rw [this]
    · exact le_of_lt (H.increasing ⟨(i : ℕ) + 1, hi⟩ j (by
        simp only [Fin.lt_def]; omega))
  -- ΔWⱼ has zero mean
  have hΔW_mean : ∫ ω, (W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω -
      W.process (H.times j) ω) ∂μ = 0 :=
    W.increment_mean_zero _ _ (hH_times_nn j) (le_of_lt hjj1)
  -- ΔWⱼ is integrable
  have hΔW_int : Integrable (fun ω => W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω -
      W.process (H.times j) ω) μ :=
    W.increment_integrable _ _ (hH_times_nn j) (le_of_lt hjj1)
  -- Independence: ΔWⱼ is independent of F_{tⱼ}
  have hindep : Indep (W.F.σ_algebra (H.times j))
    (MeasurableSpace.comap (fun ω => W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω -
      W.process (H.times j) ω) inferInstance) μ :=
    W.independent_increments _ _ (hH_times_nn j) (le_of_lt hjj1)
  -- Show (Hᵢ·ΔWᵢ·Hⱼ) is F_{tⱼ}-measurable
  have hX_meas : @Measurable Ω ℝ (W.F.σ_algebra (H.times j)) _
      (fun ω => H.values i ω *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) *
        H.values j ω) := by
    apply Measurable.mul
    apply Measurable.mul
    · -- Hᵢ is F_{tᵢ}-measurable ≤ F_{tⱼ}
      have hij_fin : i < j := Fin.lt_def.mpr hij
      exact (hH_adapted_all i).mono (W.F.mono _ _ (le_of_lt (H.increasing i j hij_fin))) le_rfl
    · -- ΔWᵢ is F_{tⱼ}-measurable
      have hij_fin : i < j := Fin.lt_def.mpr hij
      apply Measurable.sub
      · exact (W.toAdapted.adapted _).mono (W.F.mono _ _ hij_times) le_rfl
      · exact (W.toAdapted.adapted _).mono (W.F.mono _ _ (le_of_lt
          (H.increasing i j hij_fin))) le_rfl
    · -- Hⱼ is F_{tⱼ}-measurable
      exact hH_adapted_all j
  -- X is integrable (bounded × integrable = integrable)
  have hX_int : Integrable (fun ω => H.values i ω *
      (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) *
      H.values j ω) μ := by
    -- Regroup as (Hi * Hj) * ΔWi
    have hregroup' : (fun ω => H.values i ω *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) *
        H.values j ω) =
        (fun ω => (H.values i ω * H.values j ω) *
          (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)) := by
      ext ω; ring
    rw [hregroup']
    -- ΔWi is integrable
    have hΔWi_int := W.increment_integrable _ _ (hH_times_nn i) (le_of_lt hii1)
    -- Hi * Hj is bounded and AEStronglyMeasurable
    obtain ⟨Ci, hCi⟩ := hH_bdd i
    obtain ⟨Cj, hCj⟩ := hH_bdd j
    apply Integrable.bdd_mul hΔWi_int
    · exact (((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).mul
        ((hH_adapted_all j).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hCi ω) (hCj ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hCi ω))
  -- Apply the key lemma
  exact SPDE.Probability.integral_mul_zero_of_indep_zero_mean
    (W.F.le_ambient _) hX_meas hX_int hΔW_int hindep hΔW_mean

/-- Diagonal term: E[Hᵢ²·(ΔWᵢ)²] = E[Hᵢ²]·Δtᵢ.

    Proof: Hᵢ² is F_{tᵢ}-measurable and ΔWᵢ is independent of F_{tᵢ},
    so E[Hᵢ²·(ΔWᵢ)²] = E[Hᵢ²]·E[(ΔWᵢ)²] = E[Hᵢ²]·Δtᵢ. -/
theorem diagonal_term (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_sq_int : ∀ i : Fin H.n, Integrable (fun ω => (H.values i ω)^2) μ)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (i : Fin H.n) (hi : (i : ℕ) + 1 < H.n) :
    ∫ ω, (H.values i ω)^2 * (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω)^2 ∂μ =
    (∫ ω, (H.values i ω)^2 ∂μ) * (H.times ⟨(i : ℕ) + 1, hi⟩ - H.times i) := by
  -- Ordering
  have hii1 : H.times i < H.times ⟨(i : ℕ) + 1, hi⟩ :=
    H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])
  -- Hᵢ² is F_{tᵢ}-measurable
  have hHsq_meas : @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _
      (fun ω => (H.values i ω)^2) := by
    have hm := hH_adapted_all i
    have : (fun ω => (H.values i ω)^2) = (fun ω => H.values i ω * H.values i ω) := by
      ext ω; ring
    rw [this]; exact hm.mul hm
  -- Independence: ΔWᵢ is independent of F_{tᵢ}
  have hindep : Indep (W.F.σ_algebra (H.times i))
    (MeasurableSpace.comap (fun ω => W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω) inferInstance) μ :=
    W.independent_increments _ _ (hH_times_nn i) (le_of_lt hii1)
  -- Integrability
  have hHsq_int := hH_sq_int i
  have hDWsq_int : Integrable (fun ω => (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω)^2) μ :=
    W.increment_sq_integrable _ _ (hH_times_nn i) (le_of_lt hii1)
  -- Build IndepFun for Hᵢ² and (ΔWᵢ)²
  have hIndepFun : IndepFun (fun ω => (H.values i ω)^2)
      (fun ω => (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)^2) μ := by
    rw [IndepFun_iff_Indep]
    -- comap(Hᵢ²) ≤ F_{tᵢ}
    have hle1 : MeasurableSpace.comap (fun ω => (H.values i ω)^2) inferInstance ≤
        W.F.σ_algebra (H.times i) :=
      MeasurableSpace.comap_le_iff_le_map.mpr (fun _ hs => hHsq_meas hs)
    -- comap((ΔWᵢ)²) ≤ comap(ΔWᵢ)
    have hle2 : MeasurableSpace.comap
        (fun ω => (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)^2)
        inferInstance ≤
        MeasurableSpace.comap (fun ω => W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
          W.process (H.times i) ω) inferInstance := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := hs
      exact ⟨(fun x => x ^ 2) ⁻¹' t, (measurable_id.pow_const 2) ht, rfl⟩
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hindep hle2) hle1
  -- Factor: E[Hᵢ²·(ΔWᵢ)²] = E[Hᵢ²]·E[(ΔWᵢ)²]
  have hfactor := hIndepFun.integral_mul_eq_mul_integral
    hHsq_int.aestronglyMeasurable hDWsq_int.aestronglyMeasurable
  -- Use E[(ΔWᵢ)²] = Δtᵢ
  have hvar : ∫ ω, (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω -
      W.process (H.times i) ω)^2 ∂μ = H.times ⟨(i : ℕ) + 1, hi⟩ - H.times i :=
    W.increment_variance _ _ (hH_times_nn i) (le_of_lt hii1)
  -- Combine: rewrite integral using factorization then variance
  rw [show (fun ω => (H.values i ω) ^ 2 *
      (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) ^ 2) =
      (fun ω => (H.values i ω) ^ 2) * (fun ω =>
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) ^ 2)
    from funext (fun ω => by simp [Pi.mul_apply])]
  rw [hfactor, hvar]

omit [MeasurableSpace Ω] in
/-- Pythagoras for orthogonal sums: if E[aᵢ·aⱼ] = 0 for i ≠ j, then
    E[(Σ aᵢ)²] = Σ E[aᵢ²].

    This is the L² Pythagorean theorem, the algebraic core of the Itô isometry. -/
private theorem sum_sq_integral_eq_sum_integral_sq {n : ℕ}
    (a : Fin n → Ω → ℝ)
    (h_cross_int : ∀ i j : Fin n, Integrable (fun ω => a i ω * a j ω) μ)
    (h_orthog : ∀ i j : Fin n, i ≠ j → ∫ ω, a i ω * a j ω ∂μ = 0) :
    ∫ ω, (∑ i : Fin n, a i ω) ^ 2 ∂μ =
    ∑ i : Fin n, ∫ ω, (a i ω) ^ 2 ∂μ := by
  -- Step 1: (Σ aᵢ)² = Σᵢ Σⱼ aᵢ·aⱼ
  have hexpand : ∀ ω, (∑ i : Fin n, a i ω) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, a i ω * a j ω := by
    intro ω; simp [sq, Finset.sum_mul_sum]
  simp_rw [hexpand]
  -- Step 2: Pull integral inside the double sum
  have h_inner_int : ∀ i : Fin n,
      Integrable (fun ω => ∑ j : Fin n, a i ω * a j ω) μ :=
    fun i => integrable_finset_sum _ (fun j _ => h_cross_int i j)
  rw [integral_finset_sum _ (fun i _ => h_inner_int i)]
  simp_rw [integral_finset_sum _ (fun j _ => h_cross_int _ j)]
  -- Step 3: Extract diagonal, zero out cross terms
  -- Now goal: Σᵢ Σⱼ ∫ aᵢ·aⱼ = Σᵢ ∫ aᵢ²
  congr 1; ext i
  -- Split: Σⱼ ∫ aᵢ·aⱼ = ∫ aᵢ·aᵢ + Σⱼ≠ᵢ ∫ aᵢ·aⱼ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  -- Off-diagonal terms vanish
  have hoff : ∑ j ∈ Finset.univ.erase i, ∫ ω, a i ω * a j ω ∂μ = 0 :=
    Finset.sum_eq_zero (fun j hj => h_orthog i j (Finset.ne_of_mem_erase hj).symm)
  rw [hoff, add_zero]
  -- aᵢ · aᵢ = aᵢ²
  congr 1; ext ω; ring

/-- The Itô isometry for simple processes:

    E[(∫H dW)²] = Σᵢ E[Hᵢ²] * (tᵢ₊₁ - tᵢ)

    Proved using:
    1. Pythagoras (cross terms vanish by `cross_term_zero`)
    2. Diagonal factorization by `diagonal_term` -/
theorem isometry (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted_all : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i) :
    ∫ ω, (H.stochasticIntegral W ω)^2 ∂μ =
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      (∫ ω, (H.values i ω)^2 ∂μ) * (H.times ⟨i + 1, h⟩ - H.times i)
    else 0 := by
  -- Define the summand a_i(ω) = dite(i+1 < n, H_i · ΔW_i, 0)
  set a : Fin H.n → Ω → ℝ := fun i ω =>
    if h : (i : ℕ) + 1 < H.n then
      H.values i ω * (W.process (H.times ⟨i + 1, h⟩) ω - W.process (H.times i) ω)
    else 0 with ha_def
  -- The stochastic integral is Σ a_i
  have hI : ∀ ω, H.stochasticIntegral W ω = ∑ i, a i ω := by
    intro ω; simp [stochasticIntegral, a]
  simp_rw [hI]
  -- Apply Pythagoras: E[(Σ aᵢ)²] = Σ E[aᵢ²]
  -- Need: cross-product integrability and orthogonality
  have h_cross_int : ∀ i j : Fin H.n,
      Integrable (fun ω => a i ω * a j ω) μ := by
    intro i j
    simp only [ha_def]
    split_ifs with hi hj hj
    · -- Both valid: bounded × integrable products
      obtain ⟨Ci, hCi⟩ := hH_bdd i
      obtain ⟨Cj, hCj⟩ := hH_bdd j
      -- Regroup as (Hi * Hj) * (ΔWi * ΔWj)
      have hregroup_ij : (fun ω =>
          (H.values i ω * (W.process (H.times ⟨↑i + 1, hi⟩) ω - W.process (H.times i) ω)) *
          (H.values j ω * (W.process (H.times ⟨↑j + 1, hj⟩) ω - W.process (H.times j) ω))) =
          (fun ω => (H.values i ω * H.values j ω) *
            ((W.process (H.times ⟨↑i + 1, hi⟩) ω - W.process (H.times i) ω) *
             (W.process (H.times ⟨↑j + 1, hj⟩) ω - W.process (H.times j) ω))) := by
        ext ω; ring
      rw [hregroup_ij]
      -- Increments are square-integrable
      have hΔWi_sq := W.increment_sq_integrable _ _ (hH_times_nn i)
        (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def])))
      have hΔWj_sq := W.increment_sq_integrable _ _ (hH_times_nn j)
        (le_of_lt (H.increasing j ⟨(j : ℕ) + 1, hj⟩ (by simp [Fin.lt_def])))
      -- Product of increments is integrable by AM-GM: |a*b| ≤ a² + b²
      have hΔW_prod_int : Integrable (fun ω =>
          (W.process (H.times ⟨↑i + 1, hi⟩) ω - W.process (H.times i) ω) *
          (W.process (H.times ⟨↑j + 1, hj⟩) ω - W.process (H.times j) ω)) μ := by
        apply Integrable.mono' (hΔWi_sq.add hΔWj_sq)
        · exact (((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl).sub
            ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl)).mul
            (((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl).sub
            ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl))
            |>.aestronglyMeasurable
        · filter_upwards with ω
          simp only [Real.norm_eq_abs, BrownianMotion.process, Pi.add_apply]
          -- |a*b| ≤ a² + b² by AM-GM: (|a| - |b|)² ≥ 0
          set u := W.toAdapted.process (H.times ⟨↑i + 1, hi⟩) ω -
            W.toAdapted.process (H.times i) ω
          set v := W.toAdapted.process (H.times ⟨↑j + 1, hj⟩) ω -
            W.toAdapted.process (H.times j) ω
          rw [abs_mul]
          nlinarith [sq_abs u, sq_abs v, sq_nonneg (|u| - |v|),
            mul_nonneg (abs_nonneg u) (abs_nonneg v)]
      -- Bounded × integrable = integrable
      apply Integrable.bdd_mul hΔW_prod_int
      · exact (((hH_adapted_all i).mono (W.F.le_ambient _) le_rfl).mul
          ((hH_adapted_all j).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hCi ω) (hCj ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hCi ω))
    all_goals simp [integrable_zero _ _ μ]
  have h_orthog : ∀ i j : Fin H.n, i ≠ j →
      ∫ ω, a i ω * a j ω ∂μ = 0 := by
    intro i j hij
    simp only [ha_def]
    split_ifs with hi hj hj
    · -- Both valid indices, i ≠ j. Use cross_term_zero.
      -- Need i < j or j < i
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact cross_term_zero H W hH_adapted_all hH_bdd hH_times_nn i j hi hj h
      · -- j < i: swap and use commutativity
        have hcomm : ∀ ω, a i ω * a j ω = a j ω * a i ω := fun ω => mul_comm _ _
        simp_rw [ha_def, dif_pos hi, dif_pos hj] at hcomm ⊢
        simp_rw [show ∀ ω, (H.values i ω *
            (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)) *
            (H.values j ω *
            (W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω - W.process (H.times j) ω)) =
            (H.values j ω *
            (W.process (H.times ⟨(j : ℕ) + 1, hj⟩) ω - W.process (H.times j) ω)) *
            (H.values i ω *
            (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω))
          from fun ω => by ring]
        exact cross_term_zero H W hH_adapted_all hH_bdd hH_times_nn j i hj hi h
    all_goals simp
  -- Apply Pythagoras
  rw [sum_sq_integral_eq_sum_integral_sq a h_cross_int h_orthog]
  -- Now: Σᵢ ∫ (a_i)² = Σᵢ dite(...)
  congr 1; ext i
  simp only [ha_def]
  split_ifs with hi
  · -- Valid index: ∫ (H_i · ΔW_i)² = E[H_i²] · Δt_i
    have hsq : ∀ ω, (H.values i ω *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω)) ^ 2 =
        (H.values i ω) ^ 2 *
        (W.process (H.times ⟨(i : ℕ) + 1, hi⟩) ω - W.process (H.times i) ω) ^ 2 := by
      intro ω; ring
    simp_rw [hsq]
    -- Helper: derive square-integrability from boundedness
    have hH_sq_int_of_bdd : ∀ k : Fin H.n,
        Integrable (fun ω => (H.values k ω) ^ 2) μ := by
      intro k
      obtain ⟨Ck, hCk⟩ := hH_bdd k
      exact Integrable.of_bound
        (((hH_adapted_all k).mono (W.F.le_ambient _) le_rfl).pow_const 2).aestronglyMeasurable
        (Ck ^ 2)
        (ae_of_all μ (fun ω => by
          simp only [Real.norm_eq_abs]
          calc |H.values k ω ^ 2| = |H.values k ω| ^ 2 := by rw [abs_pow]
            _ ≤ Ck ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hCk ω) 2))
    exact diagonal_term H W hH_adapted_all hH_sq_int_of_bdd hH_times_nn i hi
  · -- Invalid index: both sides are 0
    simp [sq]

end SimpleProcess

/-! ## Itô Integral -/

/-- The space of Itô integrable processes.
    H is integrable if E[∫₀ᵀ H²_s ds] < ∞.

    The process is assumed to be jointly measurable (measurable as a function
    (t, ω) ↦ H(t, ω) on the product space ℝ × Ω). This is standard: in classical
    stochastic analysis, Itô integrands are assumed progressively measurable,
    which implies joint measurability. Joint measurability is needed for
    Fubini/Tonelli arguments (e.g., showing ω ↦ ∫₀ᵗ H²(s,ω) ds is measurable). -/
structure ItoIntegrableProcess (F : Filtration Ω ℝ) (μ : Measure Ω) (T : ℝ) where
  /-- The process -/
  process : ℝ → Ω → ℝ
  /-- Adapted to F -/
  adapted : ∀ t : ℝ, t ≤ T → @Measurable Ω ℝ (F.σ_algebra t) _ (process t)
  /-- Jointly measurable: (t, ω) ↦ H(t, ω) is measurable on ℝ × Ω.
      This is the standard condition for Itô integrands (implied by progressive
      measurability). Needed for Fubini/Tonelli arguments. -/
  jointly_measurable : Measurable (Function.uncurry process)
  /-- Square-integrable condition: (s, ω) ↦ H(s, ω)² is integrable on [0,T] × Ω.
      This is the product-space formulation of E[∫₀ᵀ H²_s ds] < ∞.
      Using product integrability rather than iterated Bochner integrals avoids
      the issue that the Bochner integral returns 0 for non-integrable functions.
      From this, Fubini gives:
      - a.e. IntegrableOn of H² on [0,T] (via `Integrable.prod_left_ae`)
      - Bochner integrability of ω ↦ ∫₀ᵀ H²(s,ω) ds (via `Integrable.integral_prod_right`) -/
  square_integrable : Integrable
    (fun p : ℝ × Ω => (process p.1 p.2) ^ 2)
    ((volume.restrict (Set.Icc 0 T)).prod μ)

namespace ItoIntegrableProcess

variable {F : Filtration Ω ℝ} {μ : Measure Ω} {T : ℝ}

/-- Product integrability on sub-intervals [0,t] ⊆ [0,T].
    Via prod_restrict: convert to IntegrableOn on the product, use mono_set, convert back. -/
theorem square_integrable_sub [SFinite μ] (H : ItoIntegrableProcess F μ T)
    {t : ℝ} (_ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun p : ℝ × Ω => (H.process p.1 p.2) ^ 2)
      ((volume.restrict (Set.Icc 0 t)).prod μ) := by
  -- Separate f from H to avoid dependent type issues in measure rewriting
  set f : ℝ × Ω → ℝ := fun p => (H.process p.1 p.2) ^ 2
  have hsq : Integrable f ((volume.restrict (Set.Icc 0 T)).prod μ) := H.square_integrable
  -- Convert product measures to restrictions of vol.prod μ via prod_restrict
  -- (vol.restrict s).prod μ = (vol.prod μ).restrict (s ×ˢ univ)
  have hconv : ∀ (s : Set ℝ), (volume.restrict s).prod μ =
      (volume.prod μ).restrict (s ×ˢ Set.univ) := fun s => by
    conv_lhs => rw [show μ = μ.restrict Set.univ from Measure.restrict_univ.symm]
    exact Measure.prod_restrict s Set.univ
  rw [hconv] at hsq ⊢
  exact hsq.mono_measure (Measure.restrict_mono
    (Set.prod_mono (Set.Icc_subset_Icc_right htT) le_rfl) le_rfl)

/-- The inner square integral is well-defined (IntegrableOn) for a.e. ω on [0,T].
    From product integrability via Fubini (`Integrable.prod_left_ae`). -/
theorem integrableOn_sq_ae [SFinite μ] (H : ItoIntegrableProcess F μ T) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun s => (H.process s ω) ^ 2) (Set.Icc 0 T) volume :=
  H.square_integrable.prod_left_ae

/-- The Bochner integral E[∫₀ᵀ H²] is well-defined and integrable.
    From product integrability via Fubini (`Integrable.integral_prod_right`). -/
theorem bochner_square_integrable [SFinite μ] (H : ItoIntegrableProcess F μ T) :
    Integrable (fun ω => ∫ s in Set.Icc 0 T, (H.process s ω) ^ 2 ∂volume) μ :=
  H.square_integrable.integral_prod_right

/-- Bochner integrability of ω ↦ ∫₀ᵗ H²(s,ω) ds for sub-intervals t ≤ T. -/
theorem bochner_square_integrable_sub [SFinite μ] (H : ItoIntegrableProcess F μ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun ω => ∫ s in Set.Icc 0 t, (H.process s ω) ^ 2 ∂volume) μ :=
  (H.square_integrable_sub ht0 htT).integral_prod_right

/-- The inner square integral is well-defined on sub-intervals [0,t] for a.e. ω. -/
theorem integrableOn_sq_sub_ae [SFinite μ] (H : ItoIntegrableProcess F μ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun s => (H.process s ω) ^ 2) (Set.Icc 0 t) volume :=
  (H.square_integrable_sub ht0 htT).prod_left_ae

/-- Product integrability of H₁·H₂ on [0,t]×Ω from individual square integrability.
    Uses AM-GM: |H₁·H₂| ≤ (H₁² + H₂²)/2 on the product space. -/
theorem product_integrable_sub [SFinite μ] (H₁ H₂ : ItoIntegrableProcess F μ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun p : ℝ × Ω => H₁.process p.1 p.2 * H₂.process p.1 p.2)
      ((volume.restrict (Set.Icc 0 t)).prod μ) := by
  have h1 := H₁.square_integrable_sub ht0 htT
  have h2 := H₂.square_integrable_sub ht0 htT
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × Ω => H₁.process p.1 p.2 * H₂.process p.1 p.2)
      ((volume.restrict (Set.Icc 0 t)).prod μ) :=
    (H₁.jointly_measurable.mul H₂.jointly_measurable).aestronglyMeasurable
  exact (h1.add h2).mono' hmeas (Filter.Eventually.of_forall fun p => by
    simp only [Real.norm_eq_abs, Pi.add_apply, abs_mul]
    nlinarith [sq_nonneg (|H₁.process p.1 p.2| - |H₂.process p.1 p.2|),
      sq_abs (H₁.process p.1 p.2), sq_abs (H₂.process p.1 p.2)])

/-- Bochner integrability of ω ↦ ∫₀ᵗ H₁·H₂ from individual square integrability. -/
theorem bochner_product_integrable_sub [SFinite μ] (H₁ H₂ : ItoIntegrableProcess F μ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (fun ω => ∫ s in Set.Icc 0 t,
      H₁.process s ω * H₂.process s ω ∂volume) μ :=
  (product_integrable_sub H₁ H₂ ht0 htT).integral_prod_right

end ItoIntegrableProcess

/-- The Itô integral ∫₀ᵗ H_s dW_s, defined as the L² limit of simple process integrals.

    This structure carries the data of the integral process. The key properties
    (martingale, isometry) are proved as theorems, NOT bundled as fields. -/
structure ItoIntegral (F : Filtration Ω ℝ) (μ : Measure Ω) (T : ℝ) where
  /-- The integrand -/
  integrand : ItoIntegrableProcess F μ T
  /-- The driving Brownian motion -/
  BM : BrownianMotion Ω μ
  /-- The resulting process -/
  integral : ℝ → Ω → ℝ
  /-- The integral is adapted to F -/
  adapted : ∀ t : ℝ, t ≤ T → @Measurable Ω ℝ (F.σ_algebra t) _ (integral t)
  /-- The integral at time 0 is 0 -/
  initial : ∀ᵐ ω ∂μ, integral 0 ω = 0
  /-- The integral is the L² limit of simple process integrals:
      there exist simple processes Hₙ → H in L² such that
      ∫₀ᵗ Hₙ dW → ∫₀ᵗ H dW in L² for all t ∈ [0, T].
      This is the defining property (not isometry, which is proved from this).
      The time-parameterized version is needed for the martingale property.

      The approximating processes are adapted to the BM filtration, bounded,
      and have nonnegative partition times — these are standard properties
      guaranteed by the construction of the Itô integral. -/
  is_L2_limit : ∃ (approx : ℕ → SimpleProcess F),
    -- Adapted to BM filtration at partition times
    (∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i)) ∧
    -- Each value function is bounded
    (∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C) ∧
    -- Partition times are nonnegative
    (∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i) ∧
    -- L² convergence at each time
    (∀ t : ℝ, 0 ≤ t → t ≤ T →
    Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) BM t ω -
                                     integral t ω)^2 ∂μ)
      Filter.atTop (nhds 0)) ∧
    -- Isometry convergence: the L² norms of simple integrals converge to the integrand L² norm.
    -- This is structural data from the Itô integral construction: the simple processes
    -- approximate the integrand in L²(Ω × [0,T]), and the isometry for simple processes
    -- transfers this to convergence of the integral L² norms.
    (∀ t : ℝ, 0 ≤ t → t ≤ T →
    Filter.Tendsto
      (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) BM t ω)^2 ∂μ)
      Filter.atTop
      (nhds (∫ ω, (∫ (s : ℝ) in Set.Icc 0 t, (integrand.process s ω)^2 ∂volume) ∂μ))) ∧
    -- Integrand L² convergence: the piecewise-constant value functions of the approximating
    -- simple processes converge to the integrand in L²([0,t] × Ω). This is the standard
    -- construction property: E[∫₀ᵗ |Hₙ - H|² ds] → 0.
    (∀ t : ℝ, 0 ≤ t → t ≤ T →
    Filter.Tendsto
      (fun n => ∫ ω, (∫ s in Set.Icc 0 t,
        (SimpleProcess.valueAtTime (approx n) s ω - integrand.process s ω) ^ 2 ∂volume) ∂μ)
      Filter.atTop (nhds 0))
  /-- The integral is square-integrable at each time in [0, T].
      This is part of the L² limit definition: the limit of an L² Cauchy sequence
      is in L². Without this, `is_L2_limit` would be vacuously true for non-L² functions
      due to Bochner integral conventions (∫ of non-integrable function = 0). -/
  sq_integrable_limit : ∀ t : ℝ, 0 ≤ t → t ≤ T →
    Integrable (fun ω => (integral t ω) ^ 2) μ

namespace ItoIntegral

variable {F : Filtration Ω ℝ} {μ : Measure Ω} {T : ℝ}

/-- The Itô integral is integrable at each time in [0, T].
    On a probability space, follows from `sq_integrable_limit`: L² ⊂ L¹
    on finite measure spaces (Cauchy-Schwarz). -/
theorem integrable_limit (I : ItoIntegral F μ T) [IsProbabilityMeasure μ]
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Integrable (I.integral t) μ := by
  -- L² ⊂ L¹ on probability spaces: |f(ω)| ≤ f(ω)² + 1
  have hsq := I.sq_integrable_limit t ht0 htT
  have hasm : AEStronglyMeasurable (I.integral t) μ :=
    ((I.adapted t htT).mono (F.le_ambient t) le_rfl).aestronglyMeasurable
  refine (hsq.add (integrable_const 1)).mono' hasm ?_
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (|I.integral t ω| - 1), sq_abs (I.integral t ω),
    abs_nonneg (I.integral t ω)]

/-- Itô isometry: E[(∫₀ᵗ H dW)²] = E[∫₀ᵗ H² ds].

    Proof: By `is_L2_limit`, simple integrals S_n converge to I in L².
    - `sq_integral_tendsto_of_L2_tendsto` gives `∫ S_n² → ∫ I²`
    - Isometry convergence field gives `∫ S_n² → ∫∫ H²`
    - By uniqueness of limits: `∫ I² = ∫∫ H²` -/
theorem ito_isometry (I : ItoIntegral F μ T) [IsProbabilityMeasure μ]
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ T) :
    ∫ ω, (I.integral t ω)^2 ∂μ =
    ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t, (I.integrand.process s ω)^2 ∂volume) ∂μ := by
  obtain ⟨approx, hadapted, hbdd, hnn, hL2, hiso, _⟩ := I.is_L2_limit
  have h_sq_conv : Filter.Tendsto
      (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) I.BM t ω)^2 ∂μ)
      Filter.atTop (nhds (∫ ω, (I.integral t ω) ^ 2 ∂μ)) := by
    have hI_int := I.integrable_limit t ht0 ht
    have hI_sq := I.sq_integrable_limit t ht0 ht
    have hSn_int : ∀ n, Integrable (SimpleProcess.stochasticIntegral_at (approx n) I.BM t) μ :=
      fun n => SimpleProcess.stochasticIntegral_at_integrable (approx n) I.BM
        (hadapted n) (hbdd n) (hnn n) t ht0
    have hSub_sq : ∀ n, Integrable (fun ω =>
        (SimpleProcess.stochasticIntegral_at (approx n) I.BM t ω - I.integral t ω) ^ 2) μ :=
      fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) I.BM
        (hadapted n) (hbdd n) (hnn n) (I.integral t) hI_int hI_sq t ht0
    exact sq_integral_tendsto_of_L2_tendsto hI_sq hSub_sq
      (fun n => by
        -- Cross-term integrability: |(g-f)*f| ≤ (g-f)² + f² by AM-GM
        refine ((hSub_sq n).add hI_sq).mono'
          (((hSn_int n).sub hI_int).aestronglyMeasurable.mul
            hI_int.aestronglyMeasurable) ?_
        filter_upwards with ω
        simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|SimpleProcess.stochasticIntegral_at (approx n) I.BM t ω -
            I.integral t ω| - |I.integral t ω|),
          sq_abs (SimpleProcess.stochasticIntegral_at (approx n) I.BM t ω - I.integral t ω),
          sq_abs (I.integral t ω)])
      (hL2 t ht0 ht)
  exact tendsto_nhds_unique h_sq_conv (hiso t ht0 ht)

/-- Bilinear Itô isometry: E[I₁(t)·I₂(t)] = E[∫₀ᵗ H₁(s)·H₂(s) ds].

    Proof strategy:
    1. For simple processes on the same partition: direct computation using
       independence of increments and E[(ΔWᵢ)²] = Δtᵢ.
    2. Approximate both integrands by simple processes and take L² limits. -/
theorem bilinear_ito_isometry (I₁ I₂ : ItoIntegral F μ T) [IsProbabilityMeasure μ]
    (h : I₁.BM = I₂.BM) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ T) :
    ∫ ω, I₁.integral t ω * I₂.integral t ω ∂μ =
    ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t,
      I₁.integrand.process s ω * I₂.integrand.process s ω ∂volume) ∂μ := by
  -- Extract approximating sequences with all 6 components
  obtain ⟨approx₁, hadapt₁, hbdd₁, hnn₁, hL2₁, hiso₁, hint₁⟩ := I₁.is_L2_limit
  obtain ⟨approx₂, hadapt₂, hbdd₂, hnn₂, hL2₂, hiso₂, hint₂⟩ := I₂.is_L2_limit
  -- Transport approx₂ to use I₁.BM (since I₁.BM = I₂.BM)
  have hadapt₂' : ∀ (n : ℕ) (i : Fin (approx₂ n).n),
      @Measurable Ω ℝ (I₁.BM.F.σ_algebra ((approx₂ n).times i)) _
        ((approx₂ n).values i) := by
    intro n i; rw [h]; exact hadapt₂ n i
  have hL2₂' : ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ ≤ T →
      Filter.Tendsto (fun n => ∫ ω,
        (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t₀ ω -
          I₂.integral t₀ ω)^2 ∂μ) Filter.atTop (nhds 0) := by
    intro t₀ ht₀0 ht₀T
    rw [show I₁.BM = I₂.BM from h]; exact hL2₂ t₀ ht₀0 ht₀T
  -- Abbreviations for stochastic integrals
  let S₁ := fun n ω => SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω
  let S₂ := fun n ω => SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω
  -- Step 1: E[S₁ₙ·S₂ₙ] → E[I₁·I₂] (product L² convergence)
  -- From L² convergence: S₁ₙ → I₁ and S₂ₙ → I₂, so product converges.
  have h_prod_conv : Filter.Tendsto
      (fun n => ∫ ω, S₁ n ω * S₂ n ω ∂μ)
      Filter.atTop (nhds (∫ ω, I₁.integral t ω * I₂.integral t ω ∂μ)) := by
    -- Basic integrability facts
    have hI₁_sq := I₁.sq_integrable_limit t ht0 ht
    have hI₂_sq := I₂.sq_integrable_limit t ht0 ht
    have hI₁_int := I₁.integrable_limit t ht0 ht
    have hI₂_int := I₂.integrable_limit t ht0 ht
    have hS₁_int : ∀ n, Integrable (S₁ n) μ :=
      fun n => SimpleProcess.stochasticIntegral_at_integrable (approx₁ n) I₁.BM
        (hadapt₁ n) (hbdd₁ n) (hnn₁ n) t ht0
    have hS₂_int : ∀ n, Integrable (S₂ n) μ :=
      fun n => SimpleProcess.stochasticIntegral_at_integrable (approx₂ n) I₁.BM
        (hadapt₂' n) (hbdd₂ n) (hnn₂ n) t ht0
    -- Square-integrability of differences
    have hSub₁_sq : ∀ n, Integrable (fun ω => (S₁ n ω - I₁.integral t ω) ^ 2) μ :=
      fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx₁ n) I₁.BM
        (hadapt₁ n) (hbdd₁ n) (hnn₁ n) _ hI₁_int hI₁_sq t ht0
    have hSub₂_sq : ∀ n, Integrable (fun ω => (S₂ n ω - I₂.integral t ω) ^ 2) μ := by
      intro n
      -- Unfold S₂ to expose I₁.BM, then rewrite to I₂.BM
      change Integrable (fun ω =>
        (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
          I₂.integral t ω) ^ 2) μ
      rw [show I₁.BM = I₂.BM from h]
      exact SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx₂ n) I₂.BM
        (hadapt₂ n) (hbdd₂ n) (hnn₂ n) _ hI₂_int hI₂_sq t ht0
    -- Product integrabilities via AM-GM: |ab| ≤ (a²+b²)/2 ≤ a²+b²
    have hfg_int : Integrable (fun ω => I₁.integral t ω * I₂.integral t ω) μ := by
      refine (hI₁_sq.add hI₂_sq).mono'
        (hI₁_int.aestronglyMeasurable.mul hI₂_int.aestronglyMeasurable) ?_
      filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|I₁.integral t ω| - |I₂.integral t ω|),
        sq_abs (I₁.integral t ω), sq_abs (I₂.integral t ω)]
    have hFG_int : ∀ n, Integrable (fun ω => S₁ n ω * S₂ n ω) μ := by
      intro n
      -- |S₁·S₂| ≤ (S₁-I₁)²+I₁²+(S₂-I₂)²+I₂² via AM-GM + (a-2b)²≥0
      refine (((hSub₁_sq n).add hI₁_sq).add ((hSub₂_sq n).add hI₂_sq)).mono'
        ((hS₁_int n).aestronglyMeasurable.mul (hS₂_int n).aestronglyMeasurable) ?_
      filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|S₁ n ω| - |S₂ n ω|),
        sq_abs (S₁ n ω), sq_abs (S₂ n ω),
        sq_nonneg (S₁ n ω - 2 * I₁.integral t ω),
        sq_nonneg (S₂ n ω - 2 * I₂.integral t ω)]
    -- Cross-product integrabilities for integral splitting
    have hcross : ∀ n, Integrable (fun ω =>
        (S₁ n ω - I₁.integral t ω) * (S₂ n ω - I₂.integral t ω)) μ := by
      intro n
      refine ((hSub₁_sq n).add (hSub₂_sq n)).mono'
        (((hS₁_int n).sub hI₁_int).aestronglyMeasurable.mul
          ((hS₂_int n).sub hI₂_int).aestronglyMeasurable) ?_
      filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|S₁ n ω - I₁.integral t ω| - |S₂ n ω - I₂.integral t ω|),
        sq_abs (S₁ n ω - I₁.integral t ω), sq_abs (S₂ n ω - I₂.integral t ω)]
    have hFg : ∀ n, Integrable (fun ω =>
        (S₁ n ω - I₁.integral t ω) * I₂.integral t ω) μ := by
      intro n
      refine ((hSub₁_sq n).add hI₂_sq).mono'
        (((hS₁_int n).sub hI₁_int).aestronglyMeasurable.mul
          hI₂_int.aestronglyMeasurable) ?_
      filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|S₁ n ω - I₁.integral t ω| - |I₂.integral t ω|),
        sq_abs (S₁ n ω - I₁.integral t ω), sq_abs (I₂.integral t ω)]
    have hfG : ∀ n, Integrable (fun ω =>
        I₁.integral t ω * (S₂ n ω - I₂.integral t ω)) μ := by
      intro n
      refine (hI₁_sq.add (hSub₂_sq n)).mono'
        (hI₁_int.aestronglyMeasurable.mul
          ((hS₂_int n).sub hI₂_int).aestronglyMeasurable) ?_
      filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|I₁.integral t ω| - |S₂ n ω - I₂.integral t ω|),
        sq_abs (I₁.integral t ω), sq_abs (S₂ n ω - I₂.integral t ω)]
    exact product_integral_tendsto_of_L2_tendsto
      hI₁_sq hI₂_sq hFG_int hfg_int hSub₁_sq hSub₂_sq
      hcross hFg hfG (hL2₁ t ht0 ht) (hL2₂' t ht0 ht)
  -- Step 2: E[S₁ₙ·S₂ₙ] = E[∫val₁ₙ·val₂ₙ] (bilinear isometry at simple process level)
  have h_bilinear : ∀ n,
      ∫ ω, S₁ n ω * S₂ n ω ∂μ =
      ∫ ω, (∫ s in Set.Icc 0 t,
        SimpleProcess.valueAtTime (approx₁ n) s ω *
        SimpleProcess.valueAtTime (approx₂ n) s ω ∂volume) ∂μ := by
    intro n
    exact SimpleProcess.bilinear_isometry_at (approx₁ n) (approx₂ n) I₁.BM
      (hadapt₁ n) (hadapt₂' n) (hbdd₁ n) (hbdd₂ n) (hnn₁ n) (hnn₂ n) t ht0
  -- Step 3: E[∫val₁ₙ·val₂ₙ] → E[∫h₁·h₂] (from integrand L² convergence)
  have h_integrand_conv : Filter.Tendsto
      (fun n => ∫ ω, (∫ s in Set.Icc 0 t,
        SimpleProcess.valueAtTime (approx₁ n) s ω *
        SimpleProcess.valueAtTime (approx₂ n) s ω ∂volume) ∂μ)
      Filter.atTop
      (nhds (∫ ω, (∫ s in Set.Icc 0 t,
        I₁.integrand.process s ω * I₂.integrand.process s ω ∂volume) ∂μ)) := by
    exact iterated_product_integral_tendsto
      (f := I₁.integrand.process) (g := I₂.integrand.process)
      (F := fun n => SimpleProcess.valueAtTime (approx₁ n))
      (G := fun n => SimpleProcess.valueAtTime (approx₂ n))
      ht0
      I₁.integrand.jointly_measurable
      I₂.integrand.jointly_measurable
      (fun n => SimpleProcess.valueAtTime_jointly_measurable (approx₁ n))
      (fun n => SimpleProcess.valueAtTime_jointly_measurable (approx₂ n))
      (I₁.integrand.square_integrable_sub ht0 ht)
      (I₂.integrand.square_integrable_sub ht0 ht)
      (fun n => (SimpleProcess.valueAtTime_uniform_bounded
        (approx₁ n) (hbdd₁ n)).imp fun _ h => h.2)
      (fun n => (SimpleProcess.valueAtTime_uniform_bounded
        (approx₂ n) (hbdd₂ n)).imp fun _ h => h.2)
      (hint₁ t ht0 ht)
      (hint₂ t ht0 ht)
  -- Step 4: Combine via uniqueness of limits
  -- Rewrite h_prod_conv using h_bilinear to get the same sequence as h_integrand_conv
  have h_prod_rewrite : Filter.Tendsto
      (fun n => ∫ ω, (∫ s in Set.Icc 0 t,
        SimpleProcess.valueAtTime (approx₁ n) s ω *
        SimpleProcess.valueAtTime (approx₂ n) s ω ∂volume) ∂μ)
      Filter.atTop (nhds (∫ ω, I₁.integral t ω * I₂.integral t ω ∂μ)) := by
    have : (fun n => ∫ ω, (∫ s in Set.Icc 0 t,
        SimpleProcess.valueAtTime (approx₁ n) s ω *
        SimpleProcess.valueAtTime (approx₂ n) s ω ∂volume) ∂μ) =
        (fun n => ∫ ω, S₁ n ω * S₂ n ω ∂μ) :=
      funext (fun n => (h_bilinear n).symm)
    rw [this]; exact h_prod_conv
  exact tendsto_nhds_unique h_prod_rewrite h_integrand_conv

/-- Combined Itô isometry: E[(aI₁(t) + bI₂(t))²] = E[∫₀ᵗ (aH₁ + bH₂)² ds].

    Proof: Expand both sides as quadratic forms in a, b, then apply `ito_isometry`
    for the diagonal terms and `bilinear_ito_isometry` for the cross term. -/
theorem combined_sq_integral_eq (I₁ I₂ : ItoIntegral F μ T) [IsProbabilityMeasure μ]
    (h : I₁.BM = I₂.BM) (a b : ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ T) :
    ∫ ω, (a * I₁.integral t ω + b * I₂.integral t ω) ^ 2 ∂μ =
    ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t,
      (a * I₁.integrand.process s ω + b * I₂.integrand.process s ω) ^ 2 ∂volume) ∂μ := by
  -- Integrability of I₁², I₂², I₁*I₂
  have hI₁_sq := I₁.sq_integrable_limit t ht0 ht
  have hI₂_sq := I₂.sq_integrable_limit t ht0 ht
  have hprod_int : Integrable (fun ω => I₁.integral t ω * I₂.integral t ω) μ := by
    refine (hI₁_sq.add hI₂_sq).mono'
      ((I₁.integrable_limit t ht0 ht).aestronglyMeasurable.mul
        (I₂.integrable_limit t ht0 ht).aestronglyMeasurable) ?_
    filter_upwards with ω
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    nlinarith [sq_nonneg (|I₁.integral t ω| - |I₂.integral t ω|),
      sq_abs (I₁.integral t ω), sq_abs (I₂.integral t ω)]
  -- Expand LHS: ∫(aI₁+bI₂)² = a²∫I₁² + 2ab∫I₁I₂ + b²∫I₂²
  have hLHS : ∫ ω, (a * I₁.integral t ω + b * I₂.integral t ω) ^ 2 ∂μ =
      a ^ 2 * ∫ ω, (I₁.integral t ω) ^ 2 ∂μ +
      2 * a * b * ∫ ω, I₁.integral t ω * I₂.integral t ω ∂μ +
      b ^ 2 * ∫ ω, (I₂.integral t ω) ^ 2 ∂μ := by
    -- Expand the square, keeping lambda form
    have h_eq : (fun ω => (a * I₁.integral t ω + b * I₂.integral t ω) ^ 2) =
        (fun ω => a ^ 2 * I₁.integral t ω ^ 2 +
          2 * a * b * (I₁.integral t ω * I₂.integral t ω) +
          b ^ 2 * I₂.integral t ω ^ 2) := by ext ω; ring
    rw [h_eq]
    -- Construct integrability proofs with explicit types matching goal form
    have hab_int : Integrable (fun ω => a ^ 2 * I₁.integral t ω ^ 2 +
        2 * a * b * (I₁.integral t ω * I₂.integral t ω)) μ :=
      (hI₁_sq.const_mul _).add (hprod_int.const_mul _)
    have hc_int : Integrable (fun ω => b ^ 2 * I₂.integral t ω ^ 2) μ :=
      hI₂_sq.const_mul _
    rw [integral_add hab_int hc_int]
    have ha_int : Integrable (fun ω => a ^ 2 * I₁.integral t ω ^ 2) μ :=
      hI₁_sq.const_mul _
    have hb_int : Integrable (fun ω =>
        2 * a * b * (I₁.integral t ω * I₂.integral t ω)) μ :=
      hprod_int.const_mul _
    rw [integral_add ha_int hb_int, integral_const_mul, integral_const_mul,
      integral_const_mul]
  -- Expand RHS: ∫∫(aH₁+bH₂)² = a²∫∫H₁² + 2ab∫∫H₁H₂ + b²∫∫H₂²
  -- Outer integrability of inner integrals (from square_integrable)
  -- Outer integrability of inner integrals (from square_integrable of I₁, I₂)
  -- These follow from: E[∫₀ᵀ Hᵢ²] < ∞ ⟹ E[∫₀ᵗ Hᵢ²] < ∞ (since [0,t] ⊆ [0,T], Hᵢ² ≥ 0)
  -- and |H₁H₂| ≤ (H₁² + H₂²)/2 for the product term
  have hI₁_inner_int : Integrable (fun ω => ∫ (s : ℝ) in Set.Icc 0 t,
      I₁.integrand.process s ω ^ 2 ∂volume) μ :=
    I₁.integrand.bochner_square_integrable_sub ht0 ht
  have hI₂_inner_int : Integrable (fun ω => ∫ (s : ℝ) in Set.Icc 0 t,
      I₂.integrand.process s ω ^ 2 ∂volume) μ :=
    I₂.integrand.bochner_square_integrable_sub ht0 ht
  have hprod_inner_int : Integrable (fun ω => ∫ (s : ℝ) in Set.Icc 0 t,
      I₁.integrand.process s ω * I₂.integrand.process s ω ∂volume) μ :=
    ItoIntegrableProcess.bochner_product_integrable_sub I₁.integrand I₂.integrand ht0 ht
  have hRHS : ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t,
      (a * I₁.integrand.process s ω + b * I₂.integrand.process s ω) ^ 2 ∂volume) ∂μ =
      a ^ 2 * ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t,
        (I₁.integrand.process s ω) ^ 2 ∂volume) ∂μ +
      2 * a * b * ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t,
        I₁.integrand.process s ω * I₂.integrand.process s ω ∂volume) ∂μ +
      b ^ 2 * ∫ ω, (∫ (s : ℝ) in Set.Icc 0 t,
        (I₂.integrand.process s ω) ^ 2 ∂volume) ∂μ := by
    -- Step 1: Expand the square inside inner integral
    have h_ring : ∀ s ω,
        (a * I₁.integrand.process s ω + b * I₂.integrand.process s ω) ^ 2 =
        a ^ 2 * I₁.integrand.process s ω ^ 2 +
        2 * a * b * (I₁.integrand.process s ω * I₂.integrand.process s ω) +
        b ^ 2 * I₂.integrand.process s ω ^ 2 := fun s ω => by ring
    simp_rw [h_ring]
    -- Step 2: Split inner integral (a.e. in ω)
    have h_inner : ∀ᵐ ω ∂μ,
        ∫ (s : ℝ) in Set.Icc 0 t,
          (a ^ 2 * I₁.integrand.process s ω ^ 2 +
           2 * a * b * (I₁.integrand.process s ω * I₂.integrand.process s ω) +
           b ^ 2 * I₂.integrand.process s ω ^ 2) ∂volume =
        a ^ 2 * ∫ (s : ℝ) in Set.Icc 0 t, I₁.integrand.process s ω ^ 2 ∂volume +
        2 * a * b * ∫ (s : ℝ) in Set.Icc 0 t,
          I₁.integrand.process s ω * I₂.integrand.process s ω ∂volume +
        b ^ 2 * ∫ (s : ℝ) in Set.Icc 0 t, I₂.integrand.process s ω ^ 2 ∂volume := by
      -- For a.e. ω, H₁(·,ω)² and H₂(·,ω)² are IntegrableOn [0,t]
      -- from product integrability via Fubini
      have hion_f := I₁.integrand.integrableOn_sq_sub_ae ht0 ht
      have hion_g := I₂.integrand.integrableOn_sq_sub_ae ht0 ht
      have hion_fg : ∀ᵐ ω ∂μ, IntegrableOn (fun s => I₁.integrand.process s ω *
          I₂.integrand.process s ω) (Set.Icc 0 t) volume :=
        (ItoIntegrableProcess.product_integrable_sub I₁.integrand I₂.integrand ht0 ht).prod_left_ae
      filter_upwards [hion_f, hion_g, hion_fg] with ω hf_sq hg_sq hfg
      -- Now split the integral using integrability of each term
      have h1 : IntegrableOn (fun s => a ^ 2 * (I₁.integrand.process s ω) ^ 2)
          (Set.Icc 0 t) volume := hf_sq.const_mul _
      have h2 : IntegrableOn (fun s => 2 * a * b *
          (I₁.integrand.process s ω * I₂.integrand.process s ω))
          (Set.Icc 0 t) volume := hfg.const_mul _
      have h3 : IntegrableOn (fun s => b ^ 2 * (I₂.integrand.process s ω) ^ 2)
          (Set.Icc 0 t) volume := hg_sq.const_mul _
      -- Split the integral step by step using integral_add with explicit types
      have h_split1 : ∫ (s : ℝ) in Set.Icc 0 t,
          (a ^ 2 * (I₁.integrand.process s ω) ^ 2 +
           2 * a * b * (I₁.integrand.process s ω * I₂.integrand.process s ω) +
           b ^ 2 * (I₂.integrand.process s ω) ^ 2) ∂volume =
        ∫ (s : ℝ) in Set.Icc 0 t,
          (a ^ 2 * (I₁.integrand.process s ω) ^ 2 +
           2 * a * b * (I₁.integrand.process s ω * I₂.integrand.process s ω)) ∂volume +
        ∫ (s : ℝ) in Set.Icc 0 t,
          b ^ 2 * (I₂.integrand.process s ω) ^ 2 ∂volume :=
        integral_add (h1.add h2) h3
      have h_split2 : ∫ (s : ℝ) in Set.Icc 0 t,
          (a ^ 2 * (I₁.integrand.process s ω) ^ 2 +
           2 * a * b * (I₁.integrand.process s ω * I₂.integrand.process s ω)) ∂volume =
        ∫ (s : ℝ) in Set.Icc 0 t,
          a ^ 2 * (I₁.integrand.process s ω) ^ 2 ∂volume +
        ∫ (s : ℝ) in Set.Icc 0 t,
          2 * a * b * (I₁.integrand.process s ω * I₂.integrand.process s ω) ∂volume :=
        integral_add h1 h2
      rw [h_split1, h_split2, integral_const_mul, integral_const_mul, integral_const_mul]
    rw [integral_congr_ae h_inner]
    -- Step 3: Split outer integral (same technique as hLHS)
    have hab_int : Integrable (fun ω =>
        a ^ 2 * ∫ (s : ℝ) in Set.Icc 0 t, I₁.integrand.process s ω ^ 2 ∂volume +
        2 * a * b * ∫ (s : ℝ) in Set.Icc 0 t,
          I₁.integrand.process s ω * I₂.integrand.process s ω ∂volume) μ :=
      (hI₁_inner_int.const_mul _).add (hprod_inner_int.const_mul _)
    have hc_int : Integrable (fun ω =>
        b ^ 2 * ∫ (s : ℝ) in Set.Icc 0 t,
          I₂.integrand.process s ω ^ 2 ∂volume) μ :=
      hI₂_inner_int.const_mul _
    rw [integral_add hab_int hc_int]
    have ha_int : Integrable (fun ω =>
        a ^ 2 * ∫ (s : ℝ) in Set.Icc 0 t,
          I₁.integrand.process s ω ^ 2 ∂volume) μ :=
      hI₁_inner_int.const_mul _
    have hb_int : Integrable (fun ω =>
        2 * a * b * ∫ (s : ℝ) in Set.Icc 0 t,
          I₁.integrand.process s ω * I₂.integrand.process s ω ∂volume) μ :=
      hprod_inner_int.const_mul _
    rw [integral_add ha_int hb_int, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hLHS, ito_isometry I₁ t ht0 ht, ito_isometry I₂ t ht0 ht,
    bilinear_ito_isometry I₁ I₂ h t ht0 ht, ← hRHS]

/-- Linearity of Itô integral in the integrand -/
theorem linear (I₁ I₂ : ItoIntegral F μ T) [IsProbabilityMeasure μ]
    (_h : I₁.BM = I₂.BM) (a b : ℝ) :
    ∃ I : ItoIntegral F μ T,
      I.BM = I₁.BM ∧
      ∀ t : ℝ, ∀ᵐ ω ∂μ, I.integral t ω = a * I₁.integral t ω + b * I₂.integral t ω := by
  -- Get approximating sequences for both integrals
  obtain ⟨approx₁, hadapt₁, hbdd₁, hnn₁, hL2₁, hiso₁, hint₁⟩ := I₁.is_L2_limit
  obtain ⟨approx₂, hadapt₂, hbdd₂, hnn₂, hL2₂, hiso₂, hint₂⟩ := I₂.is_L2_limit
  -- Convert I₂.BM references to I₁.BM using _h
  have hadapt₂' : ∀ (n : ℕ), ∀ i : Fin (approx₂ n).n,
      @Measurable Ω ℝ (I₁.BM.F.σ_algebra ((approx₂ n).times i)) _ ((approx₂ n).values i) := by
    intro n i; rw [_h]; exact hadapt₂ n i
  -- Construct combined process directly as mergedProcess
  let combined : ℕ → SimpleProcess F :=
    fun n => SimpleProcess.mergedProcess (approx₁ n) (approx₂ n) a b
  -- Stochastic integral linearity
  have hcomb_int : ∀ n t ω, (combined n).stochasticIntegral_at I₁.BM t ω =
      a * (approx₁ n).stochasticIntegral_at I₁.BM t ω +
      b * (approx₂ n).stochasticIntegral_at I₁.BM t ω :=
    fun n t ω => SimpleProcess.mergedProcess_integral_eq _ _ I₁.BM a b t ω
  -- valueAtTime linearity
  have hcomb_val : ∀ n s ω, (combined n).valueAtTime s ω =
      a * (approx₁ n).valueAtTime s ω + b * (approx₂ n).valueAtTime s ω :=
    fun n => SimpleProcess.mergedProcess_valueAtTime_linear _ _ a b
  -- Adaptedness
  have hcomb_adapt' : ∀ (n : ℕ), ∀ i : Fin (combined n).n,
      @Measurable Ω ℝ (I₁.BM.F.σ_algebra ((combined n).times i)) _ ((combined n).values i) :=
    fun n i => (measurable_const.mul
      (SimpleProcess.valueAtTime_measurable_filtration (approx₁ n) _ (hadapt₁ n))).add
      (measurable_const.mul
      (SimpleProcess.valueAtTime_measurable_filtration (approx₂ n) _ (hadapt₂' n)))
  -- Boundedness
  have hcomb_bdd' : ∀ (n : ℕ), ∀ i : Fin (combined n).n,
      ∃ C : ℝ, ∀ ω, |(combined n).values i ω| ≤ C := by
    intro n i
    obtain ⟨C₁, hC₁⟩ := SimpleProcess.valueAtTime_bounded (approx₁ n) _ (hbdd₁ n)
    obtain ⟨C₂, hC₂⟩ := SimpleProcess.valueAtTime_bounded (approx₂ n) _ (hbdd₂ n)
    exact ⟨|a| * C₁ + |b| * C₂, fun ω => by
      calc |(combined n).values i ω|
          = |a * (approx₁ n).valueAtTime _ ω + b * (approx₂ n).valueAtTime _ ω| := rfl
        _ ≤ |a * (approx₁ n).valueAtTime _ ω| + |b * (approx₂ n).valueAtTime _ ω| :=
            abs_add_le _ _
        _ = |a| * |(approx₁ n).valueAtTime _ ω| + |b| * |(approx₂ n).valueAtTime _ ω| := by
            rw [abs_mul, abs_mul]
        _ ≤ |a| * C₁ + |b| * C₂ := add_le_add
            (mul_le_mul_of_nonneg_left (hC₁ ω) (abs_nonneg a))
            (mul_le_mul_of_nonneg_left (hC₂ ω) (abs_nonneg b))⟩
  -- Nonneg times
  have hcomb_nn' : ∀ (n : ℕ), ∀ i : Fin (combined n).n, 0 ≤ (combined n).times i := by
    intro n i
    have hmem := SimpleProcess.mergedProcess_times_mem (approx₁ n) (approx₂ n) a b i
    simp only [SimpleProcess.mergedFinset, Finset.mem_union, SimpleProcess.partitionFinset,
      Finset.mem_image, Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [← hj]; exact hnn₁ n j
    · rw [← hj]; exact hnn₂ n j
  -- The combined integral function
  let I_integral : ℝ → Ω → ℝ := fun t ω => a * I₁.integral t ω + b * I₂.integral t ω
  -- L² convergence (factored out for use in isometry convergence)
  have hL2_combined : ∀ (t : ℝ), 0 ≤ t → t ≤ T →
      Filter.Tendsto
        (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (combined n) I₁.BM t ω -
          I_integral t ω)^2 ∂μ)
        Filter.atTop (nhds 0) := by
    intro t ht0 htT
    have hL2₂' : Filter.Tendsto
        (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
          I₂.integral t ω)^2 ∂μ) Filter.atTop (nhds 0) := by
      rw [show I₁.BM = I₂.BM from _h]; exact hL2₂ t ht0 htT
    have hI₁_int := I₁.integrable_limit t ht0 htT
    have hI₁_sq := I₁.sq_integrable_limit t ht0 htT
    have hI₂_int := I₂.integrable_limit t ht0 htT
    have hI₂_sq := I₂.sq_integrable_limit t ht0 htT
    have hd1_sq : ∀ n, Integrable (fun ω =>
        (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
          I₁.integral t ω) ^ 2) μ :=
      fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx₁ n) I₁.BM
        (hadapt₁ n) (hbdd₁ n) (hnn₁ n) _ hI₁_int hI₁_sq t ht0
    have hd2_sq : ∀ n, Integrable (fun ω =>
        (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
          I₂.integral t ω) ^ 2) μ := by
      intro n; rw [show I₁.BM = I₂.BM from _h]
      exact SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx₂ n) I₂.BM
        (hadapt₂ n) (hbdd₂ n) (hnn₂ n) _ hI₂_int hI₂_sq t ht0
    have hupper : Filter.Tendsto (fun n =>
        2 * a ^ 2 * ∫ ω, (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
          I₁.integral t ω) ^ 2 ∂μ +
        2 * b ^ 2 * ∫ ω, (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
          I₂.integral t ω) ^ 2 ∂μ) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => 2 * a ^ 2 * ∫ ω,
          (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
            I₁.integral t ω) ^ 2 ∂μ) Filter.atTop (nhds 0) := by
        simpa [mul_zero] using tendsto_const_nhds.mul (hL2₁ t ht0 htT)
      have h2 : Filter.Tendsto (fun n => 2 * b ^ 2 * ∫ ω,
          (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
            I₂.integral t ω) ^ 2 ∂μ) Filter.atTop (nhds 0) := by
        simpa [mul_zero] using tendsto_const_nhds.mul hL2₂'
      simpa [add_zero] using h1.add h2
    refine squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) ?_ hupper
    intro n
    have hrewrite : ∀ ω,
        (combined n).stochasticIntegral_at I₁.BM t ω - I_integral t ω =
        a * (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
          I₁.integral t ω) +
        b * (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
          I₂.integral t ω) := by
      intro ω; simp only [I_integral]; rw [hcomb_int n t ω]; ring
    simp_rw [hrewrite]
    have hbd_int : Integrable (fun ω =>
        2 * a ^ 2 * (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
          I₁.integral t ω) ^ 2 +
        2 * b ^ 2 * (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
          I₂.integral t ω) ^ 2) μ :=
      ((hd1_sq n).const_mul _).add ((hd2_sq n).const_mul _)
    have hpw_bound : ∀ ω : Ω,
        (a * (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
            I₁.integral t ω) +
         b * (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
            I₂.integral t ω)) ^ 2 ≤
        2 * a ^ 2 * (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
            I₁.integral t ω) ^ 2 +
        2 * b ^ 2 * (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
            I₂.integral t ω) ^ 2 := by
      intro ω
      set X := SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω - I₁.integral t ω
      set Y := SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω - I₂.integral t ω
      have h1 : 0 ≤ (a * X - b * Y) ^ 2 := sq_nonneg _
      have h2 : (a * X + b * Y) ^ 2 + (a * X - b * Y) ^ 2 =
        2 * a ^ 2 * X ^ 2 + 2 * b ^ 2 * Y ^ 2 := by ring
      linarith
    have h_le := integral_mono_of_nonneg
      (ae_of_all μ fun ω => sq_nonneg
        (a * (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
            I₁.integral t ω) +
         b * (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
            I₂.integral t ω)))
      hbd_int (ae_of_all μ hpw_bound)
    calc ∫ ω, (a * (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
              I₁.integral t ω) +
            b * (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
              I₂.integral t ω)) ^ 2 ∂μ
        ≤ ∫ ω, (2 * a ^ 2 * (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
              I₁.integral t ω) ^ 2 +
            2 * b ^ 2 * (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
              I₂.integral t ω) ^ 2) ∂μ := h_le
      _ = 2 * a ^ 2 * ∫ ω, (SimpleProcess.stochasticIntegral_at (approx₁ n) I₁.BM t ω -
              I₁.integral t ω) ^ 2 ∂μ +
          2 * b ^ 2 * ∫ ω, (SimpleProcess.stochasticIntegral_at (approx₂ n) I₁.BM t ω -
              I₂.integral t ω) ^ 2 ∂μ := by
        rw [integral_add ((hd1_sq n).const_mul _) ((hd2_sq n).const_mul _),
          integral_const_mul, integral_const_mul]
  -- Construct the ItoIntegral
  refine ⟨{
    integrand := {
      process := fun t ω => a * I₁.integrand.process t ω + b * I₂.integrand.process t ω
      adapted := fun t ht =>
        (measurable_const.mul (I₁.integrand.adapted t ht)).add
          (measurable_const.mul (I₂.integrand.adapted t ht))
      jointly_measurable := by
        show Measurable (fun p : ℝ × Ω =>
          a * I₁.integrand.process p.1 p.2 + b * I₂.integrand.process p.1 p.2)
        exact (measurable_const.mul I₁.integrand.jointly_measurable).add
          (measurable_const.mul I₂.integrand.jointly_measurable)
      square_integrable := by
        -- (aH₁+bH₂)² ≤ 2(a²H₁² + b²H₂²) pointwise
        -- Product integrability from I₁ and I₂
        show Integrable (fun p : ℝ × Ω =>
          (a * I₁.integrand.process p.1 p.2 + b * I₂.integrand.process p.1 p.2) ^ 2)
          ((volume.restrict (Set.Icc 0 T)).prod μ)
        have h1 := I₁.integrand.square_integrable
        have h2 := I₂.integrand.square_integrable
        have hmeas : AEStronglyMeasurable (fun p : ℝ × Ω =>
            (a * I₁.integrand.process p.1 p.2 + b * I₂.integrand.process p.1 p.2) ^ 2)
            ((volume.restrict (Set.Icc 0 T)).prod μ) :=
          (((measurable_const.mul I₁.integrand.jointly_measurable).add
            (measurable_const.mul I₂.integrand.jointly_measurable)).pow_const 2).aestronglyMeasurable
        exact ((h1.const_mul (2 * a ^ 2)).add (h2.const_mul (2 * b ^ 2))).mono' hmeas
          (Filter.Eventually.of_forall fun p => by
            simp only [Real.norm_eq_abs, Pi.add_apply]
            rw [abs_of_nonneg (sq_nonneg _)]
            nlinarith [sq_nonneg (a * I₁.integrand.process p.1 p.2 -
              b * I₂.integrand.process p.1 p.2)])
    }
    BM := I₁.BM
    integral := I_integral
    adapted := fun t ht =>
      (measurable_const.mul (I₁.adapted t ht)).add
        (measurable_const.mul (I₂.adapted t ht))
    initial := by
      filter_upwards [I₁.initial, I₂.initial] with ω h₁ h₂
      show a * I₁.integral 0 ω + b * I₂.integral 0 ω = 0
      rw [h₁, h₂, mul_zero, mul_zero, add_zero]
    is_L2_limit := ⟨combined, hcomb_adapt', hcomb_bdd', hcomb_nn', hL2_combined, ?_, ?_⟩
    sq_integrable_limit := fun t ht0 htT => by
      -- Use L² approach: aI₁ + bI₂ ∈ L² → (aI₁ + bI₂)² ∈ L¹
      have hmeas : AEStronglyMeasurable
          (fun ω => a * I₁.integral t ω + b * I₂.integral t ω) μ := by
        apply Measurable.aestronglyMeasurable
        exact (measurable_const.mul ((I₁.adapted t htT).mono (F.le_ambient t) le_rfl)).add
          (measurable_const.mul ((I₂.adapted t htT).mono (F.le_ambient t) le_rfl))
      rw [← memLp_two_iff_integrable_sq hmeas]
      have hI₁_L2 : MemLp (I₁.integral t) 2 μ :=
        (memLp_two_iff_integrable_sq
          (I₁.integrable_limit t ht0 htT).aestronglyMeasurable).mpr
          (I₁.sq_integrable_limit t ht0 htT)
      have hI₂_L2 : MemLp (I₂.integral t) 2 μ :=
        (memLp_two_iff_integrable_sq
          (I₂.integrable_limit t ht0 htT).aestronglyMeasurable).mpr
          (I₂.sq_integrable_limit t ht0 htT)
      exact (hI₁_L2.const_smul a).add (hI₂_L2.const_smul b)
  }, rfl, fun t => Filter.Eventually.of_forall fun ω => rfl⟩
  · -- Isometry convergence: ∫ (combined_n stoch)² → ∫∫ (aH₁+bH₂)²
    -- Strategy: sq_integral_tendsto_of_L2_tendsto gives ∫(S_n)² → ∫(aI₁+bI₂)²,
    -- then combined_sq_integral_eq shows ∫(aI₁+bI₂)² = ∫∫(aH₁+bH₂)².
    intro t ht0 htT
    -- Rewrite target using combined_sq_integral_eq
    rw [(combined_sq_integral_eq I₁ I₂ _h a b t ht0 htT).symm]
    -- Integrability of (aI₁+bI₂)²
    have hI_int : Integrable (fun ω => a * I₁.integral t ω + b * I₂.integral t ω) μ :=
      ((I₁.integrable_limit t ht0 htT).const_mul a).add
        ((I₂.integrable_limit t ht0 htT).const_mul b)
    have hI_sq : Integrable (fun ω => (a * I₁.integral t ω + b * I₂.integral t ω) ^ 2) μ := by
      have hmeas : AEStronglyMeasurable
          (fun ω => a * I₁.integral t ω + b * I₂.integral t ω) μ :=
        hI_int.aestronglyMeasurable
      rw [← memLp_two_iff_integrable_sq hmeas]
      exact ((memLp_two_iff_integrable_sq
          (I₁.integrable_limit t ht0 htT).aestronglyMeasurable).mpr
          (I₁.sq_integrable_limit t ht0 htT)).const_smul a |>.add
        (((memLp_two_iff_integrable_sq
          (I₂.integrable_limit t ht0 htT).aestronglyMeasurable).mpr
          (I₂.sq_integrable_limit t ht0 htT)).const_smul b)
    -- Integrability of (S_n - (aI₁+bI₂))²
    have hSub_sq : ∀ n, Integrable (fun ω =>
        (SimpleProcess.stochasticIntegral_at (combined n) I₁.BM t ω -
          (a * I₁.integral t ω + b * I₂.integral t ω)) ^ 2) μ :=
      fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (combined n) I₁.BM
        (hcomb_adapt' n) (hcomb_bdd' n) (hcomb_nn' n) _ hI_int hI_sq t ht0
    -- Cross-term integrability: |(g-f)*f| ≤ (g-f)² + f²
    have hFf_prod : ∀ n, Integrable (fun ω =>
        (SimpleProcess.stochasticIntegral_at (combined n) I₁.BM t ω -
          (a * I₁.integral t ω + b * I₂.integral t ω)) *
          (a * I₁.integral t ω + b * I₂.integral t ω)) μ := by
      intro n
      have hSn_int := SimpleProcess.stochasticIntegral_at_integrable (combined n) I₁.BM
        (hcomb_adapt' n) (hcomb_bdd' n) (hcomb_nn' n) t ht0
      refine ((hSub_sq n).add hI_sq).mono'
        ((hSn_int.sub hI_int).aestronglyMeasurable.mul
          hI_int.aestronglyMeasurable) ?_
      filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
      nlinarith [sq_nonneg (|SimpleProcess.stochasticIntegral_at (combined n) I₁.BM t ω -
          (a * I₁.integral t ω + b * I₂.integral t ω)| -
          |a * I₁.integral t ω + b * I₂.integral t ω|),
        sq_abs (SimpleProcess.stochasticIntegral_at (combined n) I₁.BM t ω -
          (a * I₁.integral t ω + b * I₂.integral t ω)),
        sq_abs (a * I₁.integral t ω + b * I₂.integral t ω)]
    exact sq_integral_tendsto_of_L2_tendsto hI_sq hSub_sq hFf_prod (hL2_combined t ht0 htT)
  · -- Integrand L² convergence: E[∫₀ᵗ |combined_val - (aH₁+bH₂)|² ds] → 0
    -- Strategy: (a(val₁-H₁) + b(val₂-H₂))² ≤ 2a²(val₁-H₁)² + 2b²(val₂-H₂)²
    intro t ht0 htT
    -- Upper bound → 0 from integrand convergences of I₁ and I₂
    have hupper : Filter.Tendsto (fun n =>
        2 * a ^ 2 * ∫ ω, ∫ s in Set.Icc 0 t,
          ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 ∂volume ∂μ +
        2 * b ^ 2 * ∫ ω, ∫ s in Set.Icc 0 t,
          ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2 ∂volume ∂μ)
        Filter.atTop (nhds 0) := by
      simpa [add_zero, mul_zero] using
        (tendsto_const_nhds.mul (hint₁ t ht0 htT)).add
        (tendsto_const_nhds.mul (hint₂ t ht0 htT))
    refine squeeze_zero
      (fun n => integral_nonneg fun ω => integral_nonneg fun s => sq_nonneg _)
      (fun n => ?_) hupper
    -- Rewrite using valueAtTime linearity
    have hrew : ∀ s ω,
        (combined n).valueAtTime s ω -
          (a * I₁.integrand.process s ω + b * I₂.integrand.process s ω) =
        a * ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) +
        b * ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) := by
      intro s ω; rw [hcomb_val]; ring
    simp_rw [hrew]
    -- Pointwise bound: (aX+bY)² ≤ 2a²X² + 2b²Y²
    have hpw : ∀ s ω,
        (a * ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) +
         b * ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω)) ^ 2 ≤
        2 * a ^ 2 * ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 +
        2 * b ^ 2 * ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2 := by
      intro s ω
      nlinarith [sq_nonneg (a * ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) -
        b * ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω))]
    -- Product integrability of (val - H)² on [0,t] × Ω (via domination)
    haveI h_fin_vol : IsFiniteMeasure (volume.restrict (Set.Icc 0 t)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have h_prod₁ : Integrable (fun p : ℝ × Ω =>
        ((approx₁ n).valueAtTime p.1 p.2 - I₁.integrand.process p.1 p.2) ^ 2)
        ((volume.restrict (Set.Icc 0 t)).prod μ) := by
      obtain ⟨C, _, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded _ (hbdd₁ n)
      have hH := I₁.integrand.square_integrable_sub ht0 htT
      have h_const_int : Integrable (fun _ : ℝ × Ω => (2 * C ^ 2 : ℝ))
          ((volume.restrict (Set.Icc 0 t)).prod μ) := integrable_const _
      apply Integrable.mono' (h_const_int.add (hH.const_mul 2))
      · exact ((SimpleProcess.valueAtTime_jointly_measurable _).sub
            I₁.integrand.jointly_measurable).pow_const 2 |>.aestronglyMeasurable
      · filter_upwards with p
        simp only [Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (sq_nonneg _)]
        have hle := abs_le.mp (hC p.1 p.2)
        have hv_sq : ((approx₁ n).valueAtTime p.1 p.2) ^ 2 ≤ C ^ 2 :=
          sq_le_sq' hle.1 hle.2
        nlinarith [sq_nonneg ((approx₁ n).valueAtTime p.1 p.2 +
          I₁.integrand.process p.1 p.2)]
    have h_prod₂ : Integrable (fun p : ℝ × Ω =>
        ((approx₂ n).valueAtTime p.1 p.2 - I₂.integrand.process p.1 p.2) ^ 2)
        ((volume.restrict (Set.Icc 0 t)).prod μ) := by
      obtain ⟨C, _, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded _ (hbdd₂ n)
      have hH := I₂.integrand.square_integrable_sub ht0 htT
      have h_const_int : Integrable (fun _ : ℝ × Ω => (2 * C ^ 2 : ℝ))
          ((volume.restrict (Set.Icc 0 t)).prod μ) := integrable_const _
      apply Integrable.mono' (h_const_int.add (hH.const_mul 2))
      · exact ((SimpleProcess.valueAtTime_jointly_measurable _).sub
            I₂.integrand.jointly_measurable).pow_const 2 |>.aestronglyMeasurable
      · filter_upwards with p
        simp only [Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (sq_nonneg _)]
        have hle := abs_le.mp (hC p.1 p.2)
        have hv_sq : ((approx₂ n).valueAtTime p.1 p.2) ^ 2 ≤ C ^ 2 :=
          sq_le_sq' hle.1 hle.2
        nlinarith [sq_nonneg ((approx₂ n).valueAtTime p.1 p.2 +
          I₂.integrand.process p.1 p.2)]
    -- Derive via Fubini: outer integrability and a.e. inner integrability
    have hd1_outer_int : Integrable (fun ω =>
        ∫ s in Set.Icc 0 t,
          ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 ∂volume) μ :=
      h_prod₁.integral_prod_right
    have hd2_outer_int : Integrable (fun ω =>
        ∫ s in Set.Icc 0 t,
          ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2 ∂volume) μ :=
      h_prod₂.integral_prod_right
    have h_ae_sq₁ : ∀ᵐ ω ∂μ, IntegrableOn (fun s =>
        ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2)
        (Set.Icc 0 t) volume :=
      h_prod₁.prod_left_ae
    have h_ae_sq₂ : ∀ᵐ ω ∂μ, IntegrableOn (fun s =>
        ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2)
        (Set.Icc 0 t) volume :=
      h_prod₂.prod_left_ae
    -- Inner integral bound (a.e.)
    have hinner_ae : ∀ᵐ ω ∂μ,
        ∫ s in Set.Icc 0 t,
          (a * ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) +
           b * ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω)) ^ 2 ∂volume ≤
        2 * a ^ 2 * ∫ s in Set.Icc 0 t,
          ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 ∂volume +
        2 * b ^ 2 * ∫ s in Set.Icc 0 t,
          ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2 ∂volume := by
      filter_upwards [h_ae_sq₁, h_ae_sq₂] with ω hω₁ hω₂
      have hbnd_int := (hω₁.const_mul (2 * a ^ 2)).add (hω₂.const_mul (2 * b ^ 2))
      calc ∫ s in Set.Icc 0 t, _ ^ 2 ∂volume
          ≤ ∫ s in Set.Icc 0 t,
              (2 * a ^ 2 * ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 +
               2 * b ^ 2 * ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2)
              ∂volume := by
            apply MeasureTheory.integral_mono_of_nonneg
              (ae_of_all _ fun s => sq_nonneg _) hbnd_int
              (ae_of_all _ fun s => hpw s ω)
        _ = 2 * a ^ 2 * ∫ s in Set.Icc 0 t,
              ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 ∂volume +
            2 * b ^ 2 * ∫ s in Set.Icc 0 t,
              ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2 ∂volume := by
          rw [MeasureTheory.integral_add (hω₁.const_mul _) (hω₂.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    -- Outer integral bound
    calc ∫ ω, _ ∂μ
        ≤ ∫ ω,
            (2 * a ^ 2 * ∫ s in Set.Icc 0 t,
              ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 ∂volume +
            2 * b ^ 2 * ∫ s in Set.Icc 0 t,
              ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2 ∂volume) ∂μ :=
          MeasureTheory.integral_mono_of_nonneg
            (ae_of_all _ fun ω => integral_nonneg fun s => sq_nonneg _)
            ((hd1_outer_int.const_mul _).add (hd2_outer_int.const_mul _))
            hinner_ae
      _ = 2 * a ^ 2 * ∫ ω, (∫ s in Set.Icc 0 t,
              ((approx₁ n).valueAtTime s ω - I₁.integrand.process s ω) ^ 2 ∂volume) ∂μ +
          2 * b ^ 2 * ∫ ω, (∫ s in Set.Icc 0 t,
              ((approx₂ n).valueAtTime s ω - I₂.integrand.process s ω) ^ 2 ∂volume) ∂μ := by
        rw [MeasureTheory.integral_add (hd1_outer_int.const_mul _) (hd2_outer_int.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- The Itô integral satisfies the martingale set-integral property on [0, T]:
    for 0 ≤ s ≤ t ≤ T and A ∈ F_s, ∫_A I(t) dμ = ∫_A I(s) dμ.

    This is the mathematical content of "the Itô integral is a martingale".
    Proof combines Phase 3 (simple integrals are martingales) and Phase 4
    (L² limits preserve the martingale property). -/
theorem is_martingale (I : ItoIntegral F μ T) [IsProbabilityMeasure μ]
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {A : Set Ω} (hA : MeasurableSet[I.BM.F.σ_algebra s] A) :
    ∫ ω in A, I.integral t ω ∂μ = ∫ ω in A, I.integral s ω ∂μ := by
  obtain ⟨approx, hadapted, hbdd, hnn, hL2, _, _⟩ := I.is_L2_limit
  exact ito_integral_martingale_setIntegral I.BM I.integral approx
    hadapted hbdd hnn hL2 I.integrable_limit I.sq_integrable_limit hs hst ht hA

end ItoIntegral

/-! ## Itô Processes -/

/-- An Itô process: dX_t = μ_t dt + σ_t dW_t

    The stochastic integral ∫₀ᵗ σ_s dW_s is represented as a process field,
    characterized as an L² limit of simple process integrals. -/
structure ItoProcess (F : Filtration Ω ℝ) (μ : Measure Ω) where
  /-- The process X -/
  process : ℝ → Ω → ℝ
  /-- The drift coefficient μ -/
  drift : ℝ → Ω → ℝ
  /-- The diffusion coefficient σ -/
  diffusion : ℝ → Ω → ℝ
  /-- The driving Brownian motion -/
  BM : BrownianMotion Ω μ
  /-- The stochastic integral process ∫₀ᵗ σ_s dW_s -/
  stoch_integral : ℝ → Ω → ℝ
  /-- The stochastic integral is the L² limit of simple process approximations
      of the diffusion coefficient. This connects `stoch_integral` to `diffusion` and `BM`.
      Convergence holds at all times t ≥ 0.

      The approximating processes are adapted, bounded, with nonneg partition times.

      Includes isometry convergence, integrand L² convergence, and a.e. pointwise
      convergence — these are construction data from the Itô integral construction,
      describing properties of the approximating sequence (not theorems about the result).

      The a.e. convergence is achieved by choosing approximants with fast L² convergence
      (‖SI_n - SI‖_{L²} < 2^{-n}), so Borel-Cantelli gives a.e. convergence of the
      full sequence. This breaks the Bochner integral circularity: `stoch_integral_measurable`
      and `stoch_integral_sq_integrable` are derived as theorems (not assumed as fields). -/
  stoch_integral_is_L2_limit : ∃ (approx : ℕ → SimpleProcess F),
    (∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (F.σ_algebra ((approx n).times i)) _ ((approx n).values i)) ∧
    (∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C) ∧
    (∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) BM t ω -
                                     stoch_integral t ω)^2 ∂μ)
      Filter.atTop (nhds 0)) ∧
    -- Isometry convergence: ∫ SI_n(t)² → ∫∫ σ²(s,ω) (construction data)
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto
      (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) BM t ω)^2 ∂μ)
      Filter.atTop
      (nhds (∫ ω, (∫ (s : ℝ) in Set.Icc 0 t, (diffusion s ω)^2 ∂volume) ∂μ))) ∧
    -- Integrand L² convergence: E[∫₀ᵗ |H_n - σ|² ds] → 0 (construction data)
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto
      (fun n => ∫ ω, (∫ s in Set.Icc 0 t,
        (SimpleProcess.valueAtTime (approx n) s ω - diffusion s ω) ^ 2 ∂volume) ∂μ)
      Filter.atTop (nhds 0)) ∧
    -- A.e. pointwise convergence: the approximants converge to SI pointwise a.e.
    -- Construction data from the Itô integral construction: by choosing
    -- approximants with fast L² convergence (‖SI_n - SI‖_{L²} < 2^{-n}),
    -- Borel-Cantelli gives a.e. convergence of the full sequence.
    (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n =>
        SimpleProcess.stochasticIntegral_at (approx n) BM t ω)
        Filter.atTop (nhds (stoch_integral t ω)))
  /-- Integral form: X_t = X_0 + ∫₀ᵗ μ_s ds + ∫₀ᵗ σ_s dW_s -/
  integral_form : ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
    process t ω = process 0 ω +
      (∫ (s : ℝ) in Set.Icc 0 t, drift s ω ∂volume) +
      stoch_integral t ω
  /-- The process X is adapted to F -/
  process_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (process t)
  /-- The drift is integrable in time for each ω.
      This ensures the drift integral ∫₀ᵗ μ_s ω ds is meaningful and can be
      manipulated (split, bounded, etc.) via standard measure theory.

      Without this, `integral_form` uses a possibly-zero integral (by Bochner
      convention for non-integrable functions), making the drift contribution vacuous. -/
  drift_time_integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntegrableOn (fun s => drift s ω) (Set.Icc 0 t) volume
  /-- The drift coefficient is adapted to the filtration F:
      μ(t, ·) is F_t-measurable for each t. This is a standard requirement —
      the drift must use only information available at time t.
      Parallel to `diffusion_adapted` for the diffusion coefficient. -/
  drift_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (drift t)
  /-- The drift coefficient is jointly measurable in (t, ω).
      Together with adaptedness, this gives progressive measurability,
      needed for parametric integral measurability via Fubini arguments.
      Parallel to `diffusion_jointly_measurable` for the diffusion coefficient. -/
  drift_jointly_measurable : Measurable (Function.uncurry drift)
  /-- The diffusion coefficient is adapted to the filtration F:
      σ(t, ·) is F_t-measurable for each t. This is a standard requirement in
      stochastic analysis — the diffusion coefficient must use only information
      available at time t. Together with joint measurability, this gives progressive
      measurability. Adaptedness is essential for the conditional isometry
      E[Z₁·Z₂] = 0 on disjoint intervals (needed for QV convergence and Itô's formula). -/
  diffusion_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (diffusion t)
  /-- The diffusion coefficient is jointly measurable in (t, ω).
      This is a standard requirement in stochastic analysis: σ(t, ω) must be
      progressively measurable (adapted + jointly measurable). Joint measurability
      is needed for Fubini/Tonelli arguments and for inner integral measurability. -/
  diffusion_jointly_measurable : Measurable (Function.uncurry diffusion)
  /-- The squared diffusion is integrable in time for each ω.
      This is a pathwise regularity condition for the diffusion coefficient:
      σ(·, ω) is locally L² in time, which is necessary for the stochastic
      integral ∫₀ᵗ σ(s, ω) dW(s) to exist and for the isometry
      E[(∫σ dW)²] = E[∫σ²] to have a well-defined inner integral. -/
  diffusion_sq_time_integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntegrableOn (fun s => (diffusion s ω)^2) (Set.Icc 0 t) volume
  /-- The function ω ↦ ∫₀ᵗ σ(s,ω)² ds is integrable over Ω.
      This ensures the isometry E[(∫σ dW)²] = E[∫σ² ds] has well-defined
      integrals on both sides and allows manipulation of the outer integral
      (splitting, bounding, Fubini). Analogous to the standard requirement
      σ ∈ L²([0,t] × Ω) for the Itô integral theory. -/
  diffusion_sq_integral_integrable : ∀ (t : ℝ), 0 ≤ t →
    Integrable (fun ω => ∫ s in Set.Icc 0 t, (diffusion s ω)^2 ∂volume) μ
  /-- The working filtration F is a sub-filtration of the BM's natural filtration.
      This is a compatibility condition: if A ∈ F_s then A ∈ BM.F_s, which allows
      the martingale property (proved w.r.t. BM.F) to imply the F-martingale property.
      In the standard setup where F = BM.F, this is just `le_refl`. -/
  F_le_BM_F : ∀ t, F.σ_algebra t ≤ BM.F.σ_algebra t
  /-- The Brownian motion is adapted to the working filtration F.
      Standard assumption in Itô calculus: the working filtration F contains
      BM's natural filtration (Karatzas-Shreve §2.7). Combined with `F_le_BM_F`,
      this means F and BM.F agree at each time. In the standard setup where
      F = BM.F, this is `BM.toAdapted.adapted t`.
      Needed for the stochastic integral to be F-adapted: the L² limit of
      F-adapted simple process integrals inherits F-adaptedness. -/
  BM_adapted_to_F : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (BM.process t)
  /-- The filtration satisfies usual conditions (right-continuous + complete).
      Standard assumption in Itô calculus (Karatzas-Shreve §2.7). Needed to
      upgrade AEMeasurable to Measurable when deriving `stoch_integral_adapted`
      from the L² limit of adapted simple process integrals.
      Definition at `ItoCalculus/Basic.lean`. -/
  usual_conditions : F.usualConditions μ
  /-- The process has continuous sample paths a.s.
      This is a fundamental property of Itô processes: X_t = X_0 + ∫μ ds + ∫σ dW
      is a.s. continuous when the drift integral is continuous in t (from integrability
      of μ) and the stochastic integral has a continuous modification (standard result
      for L² martingales with continuous quadratic variation). -/
  process_continuous : ∀ᵐ ω ∂μ, Continuous (fun t => process t ω)

namespace ItoProcess

variable {F : Filtration Ω ℝ} {μ : Measure Ω}

/-- Helper: the stochastic integral of a simple process at time t is F_t-measurable,
    when values are F-adapted and BM is F-adapted. Uses the min-capped reformulation
    so that all BM values and partition times in non-zero summands are ≤ t. -/
private theorem stochasticIntegral_at_Ft_measurable
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (hBM_F : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (W.process t))
    (h_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (F.σ_algebra (H.times i)) _ (H.values i))
    (t : ℝ) :
    @Measurable Ω ℝ (F.σ_algebra t) _ (H.stochasticIntegral_at W t) := by
  -- Rewrite as min-capped form: all BM values at times ≤ t
  have heq : H.stochasticIntegral_at W t = fun ω =>
      ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
        H.values i ω * (W.process (min (H.times ⟨i + 1, h⟩) t) ω -
                         W.process (min (H.times i) t) ω)
      else 0 := by
    ext ω; exact H.stochasticIntegral_at_eq_min W t ω
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    by_cases hts : H.times i ≤ t
    · -- t_i ≤ t: H_i is F_{t_i}-meas ≤ F_t, BM values at times ≤ t are F_t-meas
      exact ((h_adapted i).mono (F.mono _ t hts) le_rfl).mul
        (((hBM_F _).mono (F.mono _ t (min_le_right _ _)) le_rfl).sub
         ((hBM_F _).mono (F.mono _ t (min_le_right _ _)) le_rfl))
    · -- t_i > t: both min = t, so increment = W(t)-W(t) = 0, product = 0
      push_neg at hts
      have h1 : min (H.times i) t = t := min_eq_right (le_of_lt hts)
      have h2 : min (H.times ⟨i + 1, hi⟩) t = t :=
        min_eq_right (le_trans (le_of_lt hts)
          (le_of_lt (H.increasing i ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))))
      have : (fun ω => H.values i ω * (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
                         W.process (min (H.times i) t) ω)) = fun _ => 0 := by
        ext ω; rw [h1, h2, sub_self, mul_zero]
      rw [this]; exact measurable_const
  · simp only [dif_neg hi]; exact measurable_const

/-- The stochastic integral is AEStronglyMeasurable at each t ≥ 0.
    Derived from a.e. convergence of the approximating sequence: each SI_n(t) is
    measurable (hence ASM), and SI_n(t) → SI(t) a.e., so SI(t) is ASM by
    `aestronglyMeasurable_of_tendsto_ae`. -/
theorem stoch_integral_aestronglyMeasurable (X : ItoProcess F μ)
    (t : ℝ) (ht : 0 ≤ t) :
    AEStronglyMeasurable (X.stoch_integral t) μ := by
  obtain ⟨approx, h_adapted, _, _, _, _, _, hae⟩ := X.stoch_integral_is_L2_limit
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n => ((stochasticIntegral_at_Ft_measurable (approx n) X.BM
      X.BM_adapted_to_F (h_adapted n) t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable)
    (hae t ht)

/-- The stochastic integral is square-integrable at each t ≥ 0.
    Derived from a.e. convergence + Fatou's lemma: SI_n → SI a.e. implies
    ∫⁻ SI² ≤ liminf ∫⁻ SI_n², and the RHS is finite by isometry convergence.

    Key steps:
    1. Each SI_n² is integrable (stochasticIntegral_at_sub_sq_integrable with f = 0)
    2. SI_n → SI a.e. ⟹ ofReal(SI_n²) → ofReal(SI²) a.e. (continuous composition)
    3. Fatou: ∫⁻ ofReal(SI²) ≤ liminf ∫⁻ ofReal(SI_n²)
    4. ∫⁻ ofReal(SI_n²) = ofReal(∫ SI_n²) (Bochner = lintegral for nonneg integrable)
    5. liminf ofReal(∫ SI_n²) = ofReal(L) (Tendsto.liminf_eq from isometry convergence)
    6. ofReal(L) < ⊤ -/
theorem stoch_integral_sq_integrable (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : t ≥ 0) :
    Integrable (fun ω => (X.stoch_integral t ω) ^ 2) μ := by
  obtain ⟨approx, h_adapted, h_bounded, h_nonneg, _, hiso, _, hae⟩ :=
    X.stoch_integral_is_L2_limit
  have hSI_asm := X.stoch_integral_aestronglyMeasurable t ht
  -- Each SI_n(t) is measurable
  have hSI_n_meas : ∀ n, Measurable
      (fun ω => SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) :=
    fun n => (stochasticIntegral_at_Ft_measurable (approx n) X.BM
      X.BM_adapted_to_F (h_adapted n) t).mono (F.le_ambient t) le_rfl
  -- Each SI_n(t)² is integrable (from sub_sq_integrable with f = 0)
  have hSI_n_sq_int : ∀ n, Integrable
      (fun ω => (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2) μ := by
    intro n
    have h := SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (fun i => (h_adapted n i).mono (X.F_le_BM_F _) le_rfl) (h_bounded n) (h_nonneg n)
      0 (integrable_const 0) (by simp [integrable_const]) t ht
    simp [sub_zero] at h; exact h
  -- Integrable = ASM + HasFiniteIntegral
  refine ⟨hSI_asm.pow _, ?_⟩
  -- HasFiniteIntegral: ∫⁻ ‖SI²‖ₑ < ⊤
  show ∫⁻ ω, ‖(X.stoch_integral t ω) ^ 2‖ₑ ∂μ < ⊤
  -- Convert enorm to ofReal for nonneg values: ‖x²‖ₑ = ofReal(x²)
  have h_enorm_sq : ∀ (x : ℝ), ‖x ^ 2‖ₑ = ENNReal.ofReal (x ^ 2) :=
    fun x => Real.enorm_eq_ofReal (sq_nonneg x)
  simp_rw [h_enorm_sq]
  -- Goal: ∫⁻ ω, ofReal((SI t ω)²) ∂μ < ⊤
  -- A.e. convergence of ofReal(SI_n²) → ofReal(SI²)
  have hae_sq : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => ENNReal.ofReal
        ((SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal ((X.stoch_integral t ω) ^ 2))) := by
    filter_upwards [hae t ht] with ω hω
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_pow 2).tendsto _).comp hω)
  -- Fatou chain: ∫⁻ ofReal(SI²) ≤ liminf ∫⁻ ofReal(SI_n²) = ofReal(L) < ⊤
  calc ∫⁻ ω, ENNReal.ofReal ((X.stoch_integral t ω) ^ 2) ∂μ
      ≤ ∫⁻ ω, Filter.atTop.liminf
          (fun n => ENNReal.ofReal
            ((SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hae_sq] with ω hω
        exact le_of_eq hω.liminf_eq.symm
    _ ≤ Filter.atTop.liminf
          (fun n => ∫⁻ ω, ENNReal.ofReal
            ((SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2) ∂μ) :=
        lintegral_liminf_le
          (fun n => ENNReal.measurable_ofReal.comp
            ((continuous_pow 2).measurable.comp (hSI_n_meas n)))
    _ = Filter.atTop.liminf
          (fun n => ENNReal.ofReal (∫ ω,
            (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2 ∂μ)) := by
        congr 1; ext n
        exact (ofReal_integral_eq_lintegral_ofReal (hSI_n_sq_int n)
          (ae_of_all _ fun ω => sq_nonneg _)).symm
    _ = ENNReal.ofReal (∫ ω, (∫ s in Set.Icc 0 t,
          (X.diffusion s ω) ^ 2 ∂volume) ∂μ) :=
        ((ENNReal.continuous_ofReal.tendsto _).comp (hiso t ht)).liminf_eq
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The stochastic integral is integrable at each t ≥ 0.
    On a probability space, follows from `stoch_integral_sq_integrable`:
    L² ⊂ L¹ on finite measure spaces (Cauchy-Schwarz). -/
theorem stoch_integral_integrable (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : t ≥ 0) :
    Integrable (X.stoch_integral t) μ := by
  -- L² ⊂ L¹ on probability spaces: |f(ω)| ≤ f(ω)² + 1
  have hsq := X.stoch_integral_sq_integrable t ht
  have hasm := X.stoch_integral_aestronglyMeasurable t ht
  refine (hsq.add (integrable_const 1)).mono' hasm ?_
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (|X.stoch_integral t ω| - 1), sq_abs (X.stoch_integral t ω),
    abs_nonneg (X.stoch_integral t ω)]

/-- The stochastic integral is adapted to F (F_t-measurable at each t ≥ 0).
    This is DERIVED from the L² limit characterization, not assumed as a structure field.

    Proof outline (simplified using a.e. convergence from construction data):
    1. Each SI_n(t) is F_t-measurable (from `stochasticIntegral_at_Ft_measurable`)
    2. SI_n(t) → SI(t) a.e. (from construction data)
    3. Indicator trick: multiply by 1_A (convergence set) for pointwise everywhere convergence
    4. `measurable_of_tendsto_metrizable` with F.σ_algebra t gives F_t-measurable limit
    5. `Filtration.measurable_of_ae_eq` under usual conditions transfers to SI(t)

    Uses: `BM_adapted_to_F` (BM is F-adapted), `usual_conditions` (completeness). -/
theorem stoch_integral_adapted [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (t : ℝ) (ht : 0 ≤ t) :
    @Measurable Ω ℝ (F.σ_algebra t) _ (X.stoch_integral t) := by
  -- Step 1: Get F-adapted approximants with a.e. convergence
  obtain ⟨approx, h_adapted, _, _, _, _, _, hae⟩ := X.stoch_integral_is_L2_limit
  -- Each SI_n(t) is F_t-measurable
  have hSI_Ft : ∀ n, @Measurable Ω ℝ (F.σ_algebra t) _
      (SimpleProcess.stochasticIntegral_at (approx n) X.BM t) :=
    fun n => stochasticIntegral_at_Ft_measurable (approx n) X.BM
      X.BM_adapted_to_F (h_adapted n) t
  -- Step 2: Use a.e. convergence directly (from construction data)
  have hae_t := hae t ht
  -- Step 3: Indicator trick for sub-σ-algebra measurability
  set A : Set Ω := {ω | Filter.Tendsto
    (fun n => SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω)
    Filter.atTop (nhds (X.stoch_integral t ω))} with hA_def
  have hA_compl_null : μ Aᶜ = 0 := by rwa [ae_iff] at hae_t
  have hAc_meas : @MeasurableSet Ω (F.σ_algebra t) Aᶜ :=
    X.usual_conditions.2 t Aᶜ hA_compl_null
  have hA_meas : @MeasurableSet Ω (F.σ_algebra t) A := compl_compl A ▸ hAc_meas.compl
  -- g_n = SI_n(t) · 1_A converges pointwise everywhere to h = SI(t) · 1_A
  set g : ℕ → Ω → ℝ := fun n => A.indicator
    (SimpleProcess.stochasticIntegral_at (approx n) X.BM t)
  set h : Ω → ℝ := A.indicator (X.stoch_integral t)
  have hg_Ft : ∀ n, @Measurable Ω ℝ (F.σ_algebra t) _ (g n) :=
    fun n => (hSI_Ft n).indicator hA_meas
  have hg_tendsto : ∀ ω, Filter.Tendsto (fun n => g n ω) Filter.atTop (nhds (h ω)) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [g, h, Set.indicator_of_mem hω]; exact hω
    · simp only [g, h, Set.indicator_of_notMem hω]; exact tendsto_const_nhds
  have hh_Ft : @Measurable Ω ℝ (F.σ_algebra t) _ h :=
    @measurable_of_tendsto_metrizable Ω ℝ (F.σ_algebra t) _ _ _ _
      g h hg_Ft (tendsto_pi_nhds.mpr hg_tendsto)
  have hh_ae : X.stoch_integral t =ᵐ[μ] h := by
    have hA_ae : A ∈ ae μ := compl_compl A ▸ compl_mem_ae_iff.mpr hA_compl_null
    filter_upwards [hA_ae] with ω hω
    exact (Set.indicator_of_mem hω _).symm
  exact Filtration.measurable_of_ae_eq X.usual_conditions hh_Ft hh_ae

/-- The stochastic integral is measurable (in the ambient σ-algebra) at each t ≥ 0.
    Follows from F_t-measurability (stoch_integral_adapted) since F_t ≤ ambient. -/
theorem stoch_integral_measurable (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) :
    Measurable (X.stoch_integral t) :=
  (X.stoch_integral_adapted t ht).mono (F.le_ambient t) le_rfl

/-- The stochastic integral at time 0 is 0 a.s.
    Follows from L² convergence: simple process integrals at time 0 are all 0,
    so the L² limit is 0. Proved in Helpers/ from `stoch_integral_is_L2_limit`. -/
theorem stoch_integral_initial (X : ItoProcess F μ) :
    ∀ᵐ ω ∂μ, X.stoch_integral 0 ω = 0 := by
  obtain ⟨approx, _, _, hnn, _, _, _, hae⟩ := X.stoch_integral_is_L2_limit
  -- Step 1: Simple process integrals at t=0 are all 0.
  -- At t=0, no partition intervals are completed, and the partial interval (if any)
  -- contributes H_0 * (W(0) - W(0)) = 0.
  have hSn_zero : ∀ n ω,
      SimpleProcess.stochasticIntegral_at (approx n) X.BM 0 ω = 0 := by
    intro n ω
    unfold SimpleProcess.stochasticIntegral_at
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : (i : ℕ) + 1 < (approx n).n
    · simp only [dif_pos h]
      -- times ⟨i+1, h⟩ > 0 (partition is nonneg + strictly increasing)
      have hpos : ¬ (approx n).times ⟨(i : ℕ) + 1, h⟩ ≤ 0 := by
        push_neg
        calc 0 ≤ (approx n).times ⟨0, by omega⟩ := hnn n ⟨0, by omega⟩
          _ < (approx n).times ⟨(i : ℕ) + 1, h⟩ :=
            (approx n).increasing ⟨0, by omega⟩ ⟨(i : ℕ) + 1, h⟩
              (by simp [Fin.lt_def])
      simp only [if_neg hpos]
      by_cases hi0 : (approx n).times i ≤ 0
      · -- times i = 0 (nonneg + ≤ 0), so W(0) - W(0) = 0
        simp only [if_pos hi0]
        have : (approx n).times i = 0 := le_antisymm hi0 (hnn n i)
        rw [this, sub_self, mul_zero]
      · simp only [if_neg hi0]
    · simp only [dif_neg h]
  -- Step 2: SI_n(0) → SI(0) a.e. with SI_n(0) = 0, so SI(0) = 0 a.e.
  filter_upwards [hae 0 le_rfl] with ω hω
  have : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
      (nhds (X.stoch_integral 0 ω)) := by
    have h_eq : (fun n => SimpleProcess.stochasticIntegral_at (approx n) X.BM 0 ω) =
        fun _ => 0 := funext (fun n => hSn_zero n ω)
    rwa [h_eq] at hω
  exact tendsto_nhds_unique this tendsto_const_nhds

/-- The stochastic integral satisfies the martingale set-integral property:
    for 0 ≤ s ≤ t and A ∈ F_s, ∫_A M(t) dμ = ∫_A M(s) dμ.
    Proof: simple process integrals are martingales (Phase 3), L² limits preserve
    the martingale set-integral property (Phase 4), and F ≤ BM.F lets us
    upgrade F-measurability of A to BM.F-measurability. -/
theorem stoch_integral_martingale (X : ItoProcess F μ) [IsProbabilityMeasure μ] (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s) A) :
    ∫ ω in A, X.stoch_integral t ω ∂μ = ∫ ω in A, X.stoch_integral s ω ∂μ := by
  -- Convert F-measurability to BM.F-measurability
  have hA' : MeasurableSet[X.BM.F.σ_algebra s] A := X.F_le_BM_F s A hA
  -- Extract approximating sequence
  obtain ⟨approx, hadapted, hbdd, hnn, hL2, _, _, _⟩ := X.stoch_integral_is_L2_limit
  -- Apply ito_integral_martingale_setIntegral with T = t
  exact ito_integral_martingale_setIntegral (T := t) X.BM X.stoch_integral approx
    (fun n i => (hadapted n i).mono (X.F_le_BM_F _) le_rfl) hbdd hnn
    (fun u hu _ => hL2 u hu)
    (fun u hu _ => X.stoch_integral_integrable u hu)
    (fun u hu _ => X.stoch_integral_sq_integrable u hu)
    hs hst le_rfl hA'

/-- The quadratic variation of an Itô process is ∫₀ᵗ σ²_s ds -/
theorem quadratic_variation (X : ItoProcess F μ) :
    ∃ qv : QuadraticVariation F,
      qv.process = X.process ∧
      (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
        qv.variation t ω = ∫ (s : ℝ) in Set.Icc 0 t, (X.diffusion s ω)^2 ∂volume) := by
  sorry

/-- Itô processes are semimartingales.

    The decomposition is:
    - M_t = stoch_integral_t (for t ≥ 0), M_t = 0 (for t < 0)
    - A_t = X_0 + ∫₀ᵗ drift ds (for t ≥ 0), A_t = X.process t (for t < 0)
    Then X_t = M_t + A_t. -/
theorem is_semimartingale (X : ItoProcess F μ) [IsProbabilityMeasure μ] :
    ∃ (M : LocalMartingale F μ ℝ) (A : ℝ → Ω → ℝ),
      ∀ t : ℝ, ∀ᵐ ω ∂μ, X.process t ω = M.process t ω + A t ω := by
  -- Define M_t = stoch_integral_t for t ≥ 0, 0 for t < 0
  -- Define A_t = X₀ + ∫₀ᵗ drift ds for t ≥ 0, X_t for t < 0
  -- Helper: the stopped-process integrability
  have int_helper : ∀ (n : ℕ) (t : ℝ),
      Integrable (fun ω => if min t (n : ℝ) ≥ 0 then
        X.stoch_integral (min t (n : ℝ)) ω else 0) μ := by
    intro n t
    split_ifs with ht
    · exact X.stoch_integral_integrable _ ht
    · exact integrable_const 0
  -- Helper: the stopped-process martingale property
  have mart_helper : ∀ (n : ℕ) (s t : ℝ), s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
      ∫ ω in A, (if min t (n : ℝ) ≥ 0 then
        X.stoch_integral (min t (n : ℝ)) ω else 0) ∂μ =
      ∫ ω in A, (if min s (n : ℝ) ≥ 0 then
        X.stoch_integral (min s (n : ℝ)) ω else 0) ∂μ := by
    intro n s t hst A hA
    by_cases hs : min s (n : ℝ) ≥ 0
    · -- Case: min(s, n) ≥ 0, so also min(t, n) ≥ 0
      have ht : min t (n : ℝ) ≥ 0 :=
        le_trans hs (min_le_min_right (n : ℝ) hst)
      simp only [if_pos ht, if_pos hs]
      by_cases hsn : s ≤ (n : ℝ)
      · -- Case: s ≤ n, so min(s, n) = s
        have hmin_s : min s (n : ℝ) = s := min_eq_left hsn
        simp only [hmin_s]
        have hs' : 0 ≤ s := hmin_s ▸ hs
        have hst' : s ≤ min t (n : ℝ) := le_min hst hsn
        exact X.stoch_integral_martingale s (min t (n : ℝ)) hs' hst' A hA
      · -- Case: s > n, so min(s, n) = n and min(t, n) = n
        push_neg at hsn
        simp only [min_eq_right (le_of_lt hsn), min_eq_right (le_trans (le_of_lt hsn) hst)]
    · -- Case: min(s, n) < 0
      push_neg at hs
      have hs_neg : s < 0 := by
        by_contra h; push_neg at h
        exact absurd (le_min h (Nat.cast_nonneg n)) (not_le.mpr hs)
      simp only [if_neg (not_le.mpr hs)]
      by_cases ht : min t (n : ℝ) ≥ 0
      · -- min(t, n) ≥ 0 but min(s, n) < 0
        simp only [if_pos ht]
        rw [integral_zero]
        have hA0 : @MeasurableSet Ω (F.σ_algebra 0) A :=
          (F.mono s 0 (le_of_lt hs_neg)) _ hA
        have hmartingale := X.stoch_integral_martingale 0 (min t (n : ℝ))
          (le_refl 0) ht A hA0
        rw [hmartingale]
        calc ∫ ω in A, X.stoch_integral 0 ω ∂μ
            = ∫ ω in A, (0 : ℝ) ∂μ := by
              apply setIntegral_congr_ae (F.le_ambient 0 _ hA0)
              filter_upwards [X.stoch_integral_initial] with ω h0 _
              exact h0
          _ = 0 := by simp
      · -- Both min(s,n) < 0 and min(t,n) < 0: both sides are ∫_A 0
        simp only [if_neg ht]
  -- Construct the LocalMartingale and FV part
  refine ⟨{
    process := fun t ω => if t ≥ 0 then X.stoch_integral t ω else 0
    adapted := fun t => by
      split_ifs with ht
      · exact X.stoch_integral_adapted t ht
      · exact measurable_const
    localizing_seq := fun n => StoppingTime.const F (n : ℝ)
    localizing_increasing := fun n ω => by
      simp only [StoppingTime.const]
      exact_mod_cast Nat.le_succ n
    localizing_to_infty := fun ω => by
      simp only [StoppingTime.const]
      exact tendsto_natCast_atTop_atTop
    stopped_is_martingale := fun n => by
      refine ⟨?_, ?_⟩
      · -- Integrability
        intro t
        have : stoppedProcess (fun t ω => if t ≥ 0 then X.stoch_integral t ω else 0)
            (StoppingTime.const F (n : ℝ)) t =
            fun ω => if min t (n : ℝ) ≥ 0 then X.stoch_integral (min t (n : ℝ)) ω else 0 := by
          ext ω; simp only [stoppedProcess, StoppingTime.const]
        rw [this]
        exact int_helper n t
      · -- Martingale property
        intro s t hst A hA
        have heqt : stoppedProcess (fun t ω => if t ≥ 0 then X.stoch_integral t ω else 0)
            (StoppingTime.const F (n : ℝ)) t =
            fun ω => if min t (n : ℝ) ≥ 0 then X.stoch_integral (min t (n : ℝ)) ω else 0 := by
          ext ω; simp only [stoppedProcess, StoppingTime.const]
        have heqs : stoppedProcess (fun t ω => if t ≥ 0 then X.stoch_integral t ω else 0)
            (StoppingTime.const F (n : ℝ)) s =
            fun ω => if min s (n : ℝ) ≥ 0 then X.stoch_integral (min s (n : ℝ)) ω else 0 := by
          ext ω; simp only [stoppedProcess, StoppingTime.const]
        rw [heqt, heqs]
        exact mart_helper n s t hst A hA
  }, fun t ω => if t ≥ 0 then
      X.process 0 ω + ∫ (s : ℝ) in Set.Icc 0 t, X.drift s ω ∂volume
    else X.process t ω, ?_⟩
  -- Show X_t = M_t + A_t
  intro t
  by_cases ht : t ≥ 0
  · simp only [if_pos ht]
    filter_upwards [X.integral_form t ht] with ω hω
    linarith
  · simp only [if_neg ht]
    filter_upwards with ω
    simp [zero_add]

end ItoProcess

/-! ## Itô's Formula

The Itô formula is proved in `Helpers/ItoFormulaProof.lean` as `SPDE.ito_formula`.
It lives there because the proof depends on infrastructure (ItoFormulaDecomposition,
ItoFormulaProof, etc.) that imports this file, making circular import impossible. -/

/-! ## Stochastic Differential Equations -/

/-- An SDE: dX_t = b(t, X_t) dt + σ(t, X_t) dW_t -/
structure SDE (F : Filtration Ω ℝ) (μ : Measure Ω) where
  /-- Drift coefficient b(t, x) -/
  drift : ℝ → ℝ → ℝ
  /-- Diffusion coefficient σ(t, x) -/
  diffusion : ℝ → ℝ → ℝ
  /-- Lipschitz condition in x -/
  lipschitz : ∃ K : ℝ, K > 0 ∧ ∀ t x y : ℝ,
    |drift t x - drift t y| + |diffusion t x - diffusion t y| ≤ K * |x - y|
  /-- Linear growth condition -/
  linear_growth : ∃ K : ℝ, K > 0 ∧ ∀ t x : ℝ,
    |drift t x|^2 + |diffusion t x|^2 ≤ K^2 * (1 + |x|^2)

/-- A strong solution to an SDE -/
structure SDESolution (F : Filtration Ω ℝ) (μ : Measure Ω) (sde : SDE F μ) where
  /-- The solution process -/
  solution : ItoProcess F μ
  /-- Initial condition -/
  initial : Ω → ℝ
  /-- Initial value matches -/
  initial_matches : ∀ᵐ ω ∂μ, solution.process 0 ω = initial ω
  /-- The drift matches -/
  drift_matches : ∀ t : ℝ, ∀ᵐ ω ∂μ,
    solution.drift t ω = sde.drift t (solution.process t ω)
  /-- The diffusion matches -/
  diffusion_matches : ∀ t : ℝ, ∀ᵐ ω ∂μ,
    solution.diffusion t ω = sde.diffusion t (solution.process t ω)

/-- Existence and uniqueness theorem for SDEs (Picard-Lindelöf) -/
theorem sde_existence_uniqueness {F : Filtration Ω ℝ} {μ : Measure Ω}
    (sde : SDE F μ) (W : BrownianMotion Ω μ) (initial : Ω → ℝ)
    (h_initial : Integrable (fun ω => (initial ω)^2) μ) :
    ∃ sol : SDESolution F μ sde, sol.initial = initial ∧ sol.solution.BM = W := by
  sorry

/-- Pathwise uniqueness for SDE solutions.

    If two strong solutions to the same SDE, driven by the same Brownian motion,
    start from the same initial condition a.s., then they agree a.s. at all times.

    The proof uses Grönwall's inequality: define φ(t) = E[|X₁(t) - X₂(t)|²],
    show φ(0) = 0 and φ(t) ≤ C ∫₀ᵗ φ(s) ds via Lipschitz + Itô isometry,
    then apply `integral_gronwall_zero` to get φ ≡ 0. -/
theorem sde_uniqueness_law {F : Filtration Ω ℝ} {μ : Measure Ω}
    (sde : SDE F μ) (sol₁ sol₂ : SDESolution F μ sde)
    (h_bm : sol₁.solution.BM = sol₂.solution.BM)
    (h : ∀ᵐ ω ∂μ, sol₁.initial ω = sol₂.initial ω) :
    ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ, sol₁.solution.process t ω = sol₂.solution.process t ω := by
  -- Step 1: Get the Lipschitz constant
  obtain ⟨K, hK_pos, hK_lip⟩ := sde.lipschitz
  -- Step 2: Define the difference and its L² norm
  set Z : ℝ → Ω → ℝ := fun t ω =>
    sol₁.solution.process t ω - sol₂.solution.process t ω with hZ_def
  set φ : ℝ → ℝ := fun t => ∫ ω, (Z t ω) ^ 2 ∂μ with hφ_def
  -- Step 3: φ(0) = 0 from equal initial conditions
  have hφ0 : φ 0 = 0 := by
    have h_ae : ∀ᵐ ω ∂μ, (Z 0 ω) ^ 2 = 0 := by
      filter_upwards [sol₁.initial_matches, sol₂.initial_matches, h] with ω h1 h2 h3
      simp only [hZ_def, h1, h3, ← h2, sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true]
    calc φ 0 = ∫ ω, (0 : ℝ) ∂μ := integral_congr_ae h_ae
      _ = 0 := by simp
  -- Step 4: Main argument via Grönwall
  -- The full Grönwall argument requires:
  -- (a) φ is continuous on [0, T] for each T (L² continuity of Itô processes)
  -- (b) φ(t) ≤ C ∫₀ᵗ φ(s) ds (from integral_form + Lipschitz + Itô isometry)
  -- (c) integral_gronwall_zero gives φ ≡ 0
  -- (d) ae_eq_zero_of_integral_sq_zero gives Z = 0 a.e.
  -- The main estimate (b) uses:
  --   Z_t = Z_0 + ∫₀ᵗ [b(s,X₁)-b(s,X₂)] ds + [M₁(t)-M₂(t)]  (integral form)
  --   E[Z_t²] ≤ 3E[Z_0²] + 3t·K²·∫₀ᵗ E[Z_s²]ds + 3K²·∫₀ᵗ E[Z_s²]ds  (Lipschitz+isometry)
  --          = C ∫₀ᵗ φ(s) ds   (since E[Z_0²] = 0)
  sorry

/-! ## Stratonovich Integral -/

/-- The Stratonovich integral ∫₀ᵗ H_s ∘ dW_s.
    Related to Itô by: ∫ H ∘ dW = ∫ H dW + (1/2)⟨H, W⟩_t

    The correction term (1/2)⟨H, W⟩_t is a deterministic integral when H is
    a smooth function of W. -/
structure StratonovichIntegral (F : Filtration Ω ℝ) (μ : Measure Ω) (T : ℝ) where
  /-- The integrand -/
  integrand : ItoIntegrableProcess F μ T
  /-- The driving Brownian motion -/
  BM : BrownianMotion Ω μ
  /-- The corresponding Itô integral -/
  ito_integral : ItoIntegral F μ T
  /-- The Itô-Stratonovich correction process (1/2)⟨H, W⟩_t -/
  correction : ℝ → Ω → ℝ
  /-- The correction is adapted -/
  correction_adapted : ∀ t : ℝ, t ≤ T →
    @Measurable Ω ℝ (F.σ_algebra t) _ (correction t)
  /-- The result: Stratonovich integral = Itô integral + correction -/
  integral : ℝ → Ω → ℝ
  /-- Relation to Itô integral with correction term -/
  ito_correction : ∀ t : ℝ, t ≤ T → ∀ᵐ ω ∂μ,
    integral t ω = ito_integral.integral t ω + correction t ω

/-- Stratonovich calculus follows the ordinary chain rule -/
theorem stratonovich_chain_rule {F : Filtration Ω ℝ} {μ : Measure Ω} {T : ℝ}
    (I : StratonovichIntegral F μ T)
    (f : ℝ → ℝ)
    (_hf : ContDiff ℝ 1 f) :
    ∀ t : ℝ, t ≤ T → ∀ᵐ ω ∂μ,
      f (I.integral t ω) = f (I.integral 0 ω) +
        ∫ (s : ℝ) in Set.Icc 0 t, deriv f (I.integral s ω) * I.integrand.process s ω ∂volume := by
  sorry

/-! ## Finite Variation Processes -/

/-- A partition of [0, T] is an increasing list of times.
    We represent this as a list with the property that consecutive elements are ordered. -/
structure Partition (T : ℝ) where
  /-- The partition points -/
  points : List ℝ
  /-- Non-empty with 0 at start -/
  starts_zero : points.head? = some 0
  /-- Ends at T -/
  ends_T : points.getLast? = some T
  /-- Strictly increasing -/
  increasing : points.IsChain (· < ·)

/-- The total variation of a function over a partition -/
noncomputable def totalVariationOver (A : ℝ → ℝ) (π : Partition T) : ℝ :=
  (π.points.zip π.points.tail).foldl
    (fun acc (pair : ℝ × ℝ) => acc + |A pair.2 - A pair.1|) 0

/-- A function A : ℝ → ℝ has finite variation on [0, T] if the total variation
    over all partitions is bounded. -/
def HasFiniteVariation (A : ℝ → ℝ) (T : ℝ) : Prop :=
  ∃ V : ℝ, V ≥ 0 ∧ ∀ π : Partition T, totalVariationOver A π ≤ V

/-- The total variation of A on [0, T] (as a sup over partitions) -/
noncomputable def totalVariation (A : ℝ → ℝ) (T : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ π : Partition T, v = totalVariationOver A π}

/-! ## Semimartingales -/

/-- A semimartingale is X = M + A where M is a local martingale and A has finite variation.

    This is the fundamental decomposition for stochastic calculus.
    Key examples:
    - Brownian motion: M = W, A = 0
    - Itô process: M = ∫σ dW, A = ∫μ dt -/
structure Semimartingale (F : Filtration Ω ℝ) (μ : Measure Ω) where
  /-- The local martingale part M -/
  martingale_part : LocalMartingale F μ ℝ
  /-- The finite variation part A -/
  finite_variation_part : ℝ → Ω → ℝ
  /-- A has finite variation on [0, T] for each ω and T ≥ 0.
      CORRECT DEFINITION: The variation is computed as the supremum of
      Σᵢ |A(tᵢ₊₁, ω) - A(tᵢ, ω)| over all partitions {t₀ < t₁ < ... < tₙ} of [0, T]. -/
  finite_variation : ∀ ω : Ω, ∀ T : ℝ, T ≥ 0 →
    HasFiniteVariation (fun t => finite_variation_part t ω) T
  /-- A(0) = 0 (canonical starting point) -/
  fv_initial : ∀ ω : Ω, finite_variation_part 0 ω = 0
  /-- A is right-continuous (càdlàg) -/
  fv_right_continuous : ∀ ω : Ω, ∀ t : ℝ,
    Filter.Tendsto (fun s => finite_variation_part s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (finite_variation_part t ω))
  /-- The process X = M + A -/
  process : ℝ → Ω → ℝ
  /-- Decomposition X = M + A -/
  decomposition : ∀ t : ℝ, ∀ ω : Ω,
    process t ω = martingale_part.process t ω + finite_variation_part t ω

namespace Semimartingale

variable {F : Filtration Ω ℝ} {μ : Measure Ω}

/-- The variation process: V_t(ω) = total variation of A on [0, t] -/
noncomputable def variation_process (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω => if t ≥ 0 then totalVariation (fun s => X.finite_variation_part s ω) t else 0

/-- Decomposition of A into increasing parts: A = A⁺ - A⁻ (Jordan decomposition) -/
noncomputable def positive_variation (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω => (X.variation_process t ω + X.finite_variation_part t ω) / 2

noncomputable def negative_variation (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω => (X.variation_process t ω - X.finite_variation_part t ω) / 2

end Semimartingale

/-- Lebesgue-Stieltjes integral ∫₀ᵗ H dA for finite variation A.

    This is defined via the associated measure: the increment A(b) - A(a)
    determines a signed measure, and we integrate H against it.

    For continuous H and A, this equals lim_{‖π‖→0} Σᵢ H(tᵢ)(A(tᵢ₊₁) - A(tᵢ)). -/
structure LebesgueStieltjesIntegral {F : Filtration Ω ℝ}
    (H : PredictableProcess F ℝ) (A : ℝ → Ω → ℝ) (T : ℝ) where
  /-- The integral process -/
  integral : Ω → ℝ
  /-- A has finite variation -/
  fv : ∀ ω : Ω, HasFiniteVariation (fun t => A t ω) T
  /-- The integral is the limit of Riemann-Stieltjes sums:
      lim Σᵢ H(tᵢ, ω)(A(tᵢ₊₁, ω) - A(tᵢ, ω)) as mesh → 0 -/
  is_limit : ∀ ω : Ω, ∀ ε > 0, ∃ δ > 0,
    ∀ π : Partition T,
    (∀ i : Fin (π.points.length - 1),
      π.points.get ⟨i.val + 1, by omega⟩ - π.points.get ⟨i.val, by omega⟩ < δ) →
    |integral ω - (π.points.zip π.points.tail).foldl
      (fun acc (pair : ℝ × ℝ) => acc + H.process pair.1 ω * (A pair.2 ω - A pair.1 ω)) 0| < ε

/-- Stochastic integral w.r.t. semimartingale: ∫₀ᵗ H dX = ∫₀ᵗ H dM + ∫₀ᵗ H dA

    The first term is the Itô integral (against local martingale).
    The second term is the Lebesgue-Stieltjes integral (against finite variation).

    **Mathematical Definition**:
    For a predictable process H and semimartingale X = M + A:
    - The Itô integral ∫₀ᵗ H dM is defined as the L²-limit of simple process integrals
    - The LS integral ∫₀ᵗ H dA is defined via the associated Lebesgue-Stieltjes measure

    **Structure**:
    This structure witnesses the existence of the integral and provides the result.
    The existence requires:
    1. H is predictable (F_{t-}-measurable)
    2. H satisfies integrability: E[∫₀ᵀ H² d⟨M⟩] < ∞ for the martingale part
    3. H is integrable w.r.t. |dA| for the finite variation part -/
structure SemimartingaleIntegral
    {F : Filtration Ω ℝ} {μ : Measure Ω}
    (H : PredictableProcess F ℝ)
    (X : Semimartingale F μ)
    (T : ℝ) where
  /-- The resulting integral process -/
  integral : ℝ → Ω → ℝ
  /-- The martingale part of the integral: ∫₀ᵗ H dM -/
  martingale_integral : ℝ → Ω → ℝ
  /-- The Lebesgue-Stieltjes part of the integral: ∫₀ᵗ H dA -/
  ls_integral : ℝ → Ω → ℝ
  /-- The integral at time 0 is 0 -/
  initial : ∀ ω, integral 0 ω = 0
  /-- The integral is adapted to F -/
  adapted : ∀ t : ℝ, t ≤ T → @Measurable Ω ℝ (F.σ_algebra t) _ (integral t)
  /-- The integral decomposes as martingale + LS integral.
      ∫₀ᵗ H dX = ∫₀ᵗ H dM + ∫₀ᵗ H dA for each ω and t. -/
  decomposition : ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ᵐ ω ∂μ,
    integral t ω = martingale_integral t ω + ls_integral t ω
  /-- The martingale part is a local martingale -/
  martingale_integral_is_local_martingale :
    ∃ M : LocalMartingale F μ ℝ, M.process = martingale_integral
  /-- The LS part has finite variation -/
  ls_integral_finite_variation : ∀ ω : Ω,
    HasFiniteVariation (fun t => ls_integral t ω) T

/-- Existence of semimartingale integral for bounded predictable processes.
    For H bounded and X a semimartingale, ∫ H dX exists. -/
theorem semimartingale_integral_exists
    {F : Filtration Ω ℝ} {μ : Measure Ω}
    (H : PredictableProcess F ℝ)
    (X : Semimartingale F μ)
    (T : ℝ) (hT : T ≥ 0)
    (hH_bounded : ∃ C : ℝ, ∀ t : ℝ, ∀ ω : Ω, |H.process t ω| ≤ C) :
    ∃ I : SemimartingaleIntegral H X T, True := by
  sorry  -- Requires full construction of stochastic integral

/-- For simple predictable processes, the semimartingale integral
    is the Riemann sum Σᵢ Hᵢ (X_{tᵢ₊₁} - X_{tᵢ}). -/
noncomputable def semimartingale_integral_simple
    {F : Filtration Ω ℝ} {μ : Measure Ω}
    (H : SimpleProcess F)
    (X : Semimartingale F μ) : ℝ → Ω → ℝ :=
  fun t ω =>
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      if H.times ⟨i + 1, h⟩ ≤ t then
        H.values i ω * (X.process (H.times ⟨i + 1, h⟩) ω - X.process (H.times i) ω)
      else if H.times i ≤ t then
        H.values i ω * (X.process t ω - X.process (H.times i) ω)
      else 0
    else 0

/-! ## Girsanov's Theorem -/

/-- Girsanov's theorem: under change of measure, BM becomes BM with drift.
    If dQ/dP = exp(∫θ dW - (1/2)∫θ² dt), then W̃_t = W_t - ∫₀ᵗ θ_s ds is Q-BM. -/
theorem girsanov {F : Filtration Ω ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : BrownianMotion Ω μ)
    (θ : ℝ → Ω → ℝ)
    (T : ℝ)
    (_novikov : ∃ (bound : ℝ),
      ∫ ω, Real.exp ((1/2) * ∫ (t : ℝ) in Set.Icc 0 T, (θ t ω)^2 ∂volume) ∂μ ≤ bound) :
    ∃ (ν : Measure Ω) (W' : BrownianMotion Ω ν),
      ∀ t : ℝ, ∀ᵐ ω ∂μ,
        W'.process t ω = W.process t ω - ∫ (s : ℝ) in Set.Icc 0 t, θ s ω ∂volume := by
  sorry

/-! ## Martingale Representation Theorem -/

/-- Every square-integrable martingale adapted to the Brownian filtration
    can be represented as a stochastic integral:
    M_t = M_0 + ∫₀ᵗ H_s dW_s

    The integrand H is predictable and the stochastic integral is the L² limit
    of simple process approximations. -/
theorem martingale_representation {F : Filtration Ω ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (W : BrownianMotion Ω μ)
    (M : Martingale F μ ℝ)
    (hM : ∀ t : ℝ, Integrable (fun ω => (M.process t ω)^2) μ) :
    ∃ (H : ℝ → Ω → ℝ) (stoch_int : ℝ → Ω → ℝ),
      -- H is adapted (predictable)
      (∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (H t)) ∧
      -- stoch_int is the L² limit of simple process integrals of H w.r.t. W
      (∃ (approx : ℕ → SimpleProcess F),
        ∀ t : ℝ, t ≥ 0 →
        Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) W t ω -
                                         stoch_int t ω)^2 ∂μ)
          Filter.atTop (nhds 0)) ∧
      -- M = M_0 + stochastic integral
      (∀ t : ℝ, ∀ᵐ ω ∂μ, M.process t ω = M.process 0 ω + stoch_int t ω) := by
  sorry

end SPDE
