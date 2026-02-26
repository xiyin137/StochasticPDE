/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.QVConvergence

/-!
# Weighted QV Discrepancy L² Bound

Proves the weighted version of the QV discrepancy L² bound needed for the Itô formula:
E[(Σ wᵢ(QVᵢ - (ΔXᵢ)²))²] ≤ C · T/(n+1) for adapted bounded weights wᵢ.

## Main results

* `ItoProcess.weighted_compensated_orthogonal` - Weighted compensated squared SI increments
  on disjoint intervals are orthogonal: E[(φ₁·Z₁)(φ₂·Z₂)] = 0
* `weighted_compensated_orthogonal_partition` - Partition-level specialization
* `weighted_capped_qv_L2_bound` - The full weighted bound

## Proof strategy

For the orthogonality, decompose E[(φ₁Z₁φ₂)·Z₂] where Z₁ = ΔSI₁² - QV₁:
- E[(φ₁·ΔSI₁²·φ₂)·Z₂] = 0: product is F_{s₂}-measurable, conditional isometry for Z₂
- E[(φ₁·QV₁·φ₂)·Z₂] = 0: Fubini swaps ∫_ω and ∫_u, pointwise zero by same argument
-/

namespace SPDE

open Set MeasureTheory MeasureTheory.Measure Filter Finset

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Weighted compensated orthogonality -/

set_option maxHeartbeats 800000 in
/-- Weighted compensated squared SI increments on disjoint intervals are orthogonal:
    E[(φ₁·Z₁)(φ₂·Z₂)] = 0 for F_{s₂}-measurable bounded φ₁, φ₂ and t₁ ≤ s₂. -/
theorem ItoProcess.weighted_compensated_orthogonal {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₁ t₁ s₂ t₂ : ℝ) (hs₁ : 0 ≤ s₁) (hst₁ : s₁ ≤ t₁) (ht₁s₂ : t₁ ≤ s₂) (hst₂ : s₂ ≤ t₂)
    (φ₁ φ₂ : Ω → ℝ) {C₁ C₂ : ℝ}
    (hφ₁_meas : @Measurable Ω ℝ (F.σ_algebra s₂) _ φ₁)
    (hφ₂_meas : @Measurable Ω ℝ (F.σ_algebra s₂) _ φ₂)
    (hφ₁_bdd : ∀ ω, |φ₁ ω| ≤ C₁) (hφ₂_bdd : ∀ ω, |φ₂ ω| ≤ C₂) :
    ∫ ω, (φ₁ ω * ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
                    ∫ r in Icc s₁ t₁, (X.diffusion r ω) ^ 2 ∂volume)) *
          (φ₂ ω * ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
                    ∫ r in Icc s₂ t₂, (X.diffusion r ω) ^ 2 ∂volume)) ∂μ = 0 := by
  -- Abbreviations
  set Z₂ := fun ω => (X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
    ∫ r in Icc s₂ t₂, (X.diffusion r ω) ^ 2 ∂volume
  -- Basic facts
  have hs₂ : 0 ≤ s₂ := le_trans (le_trans hs₁ hst₁) ht₁s₂
  -- Integrability infrastructure
  have hΔ₁_sq_int := si_increment_sq_integrable' X s₁ t₁ hs₁ hst₁
  have hQ₁_int := diffusion_sq_interval_integrable X s₁ t₁ hs₁ hst₁
  have hZ₂_int := compensated_sq_integrable' X s₂ t₂ hs₂ hst₂
  have hZ₂_sq_int := compensated_sq_sq_integrable' X hMσ s₂ t₂ hs₂ hst₂
  have hΔ₁_L4 := stoch_integral_increment_L4_integrable_proof X hMσ s₁ t₁ hs₁ hst₁
  have hQ₁_bdd := diffusion_sq_integral_bound X hMσ s₁ t₁ hst₁
  -- φ₁, φ₂ are ambient-measurable
  have hφ₁_m := hφ₁_meas.mono (F.le_ambient s₂) le_rfl
  have hφ₂_m := hφ₂_meas.mono (F.le_ambient s₂) le_rfl
  -- (φ₁·ΔSI₁²·φ₂) · Z₂ integrable
  have hdom : Integrable (fun ω =>
      C₁ * C₂ * ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 + Z₂ ω ^ 2)) μ :=
    (hΔ₁_L4.add hZ₂_sq_int).const_mul (C₁ * C₂)
  have h_term1_int : Integrable (fun ω =>
      (φ₁ ω * (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * φ₂ ω) * Z₂ ω) μ :=
    hdom.mono'
      (((hφ₁_m.aestronglyMeasurable.mul
        hΔ₁_sq_int.aestronglyMeasurable).mul
        hφ₂_m.aestronglyMeasurable).mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
        simp only [abs_of_nonneg (sq_nonneg (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω))]
        have hC₁ : 0 ≤ C₁ := le_trans (abs_nonneg _) (hφ₁_bdd ω)
        have hC₂ : 0 ≤ C₂ := le_trans (abs_nonneg _) (hφ₂_bdd ω)
        have hΔ := sq_nonneg (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω)
        have hφ₁φ₂ := mul_le_mul (hφ₁_bdd ω) (hφ₂_bdd ω) (abs_nonneg _) hC₁
        have h_amgm : (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * |Z₂ ω| ≤
            (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 + Z₂ ω ^ 2 := by
          nlinarith [sq_nonneg ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 - |Z₂ ω|),
                     sq_abs (Z₂ ω), mul_nonneg hΔ (abs_nonneg (Z₂ ω))]
        calc |φ₁ ω| * (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 *
              |φ₂ ω| * |Z₂ ω|
            = (|φ₁ ω| * |φ₂ ω|) *
              ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * |Z₂ ω|) := by ring
          _ ≤ (C₁ * C₂) *
              ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * |Z₂ ω|) :=
            mul_le_mul_of_nonneg_right hφ₁φ₂ (mul_nonneg hΔ (abs_nonneg _))
          _ ≤ (C₁ * C₂) *
              ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 + Z₂ ω ^ 2) :=
            mul_le_mul_of_nonneg_left h_amgm (mul_nonneg hC₁ hC₂)
          _ = C₁ * C₂ *
              ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 + Z₂ ω ^ 2) := by ring)
  -- (φ₁·QV₁·φ₂) · Z₂ integrable (QV₁ bounded by Mσ²(t₁-s₁))
  have h_term2_int : Integrable (fun ω =>
      (φ₁ ω * (∫ r in Icc s₁ t₁, (X.diffusion r ω) ^ 2 ∂volume) * φ₂ ω) * Z₂ ω) μ :=
    (hZ₂_int.norm.const_mul (C₁ * C₂ * (Mσ ^ 2 * (t₁ - s₁)))).mono'
      (((hφ₁_m.aestronglyMeasurable.mul
        hQ₁_int.aestronglyMeasurable).mul
        hφ₂_m.aestronglyMeasurable).mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_mul, abs_mul, abs_mul]
        have hab := mul_le_mul (hφ₁_bdd ω) (hQ₁_bdd ω) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hφ₁_bdd ω))
        have habc := mul_le_mul hab (hφ₂_bdd ω) (abs_nonneg _)
          (mul_nonneg (le_trans (abs_nonneg _) (hφ₁_bdd ω))
            (le_trans (abs_nonneg _) (hQ₁_bdd ω)))
        calc |φ₁ ω| * |∫ r in Icc s₁ t₁, (X.diffusion r ω) ^ 2 ∂volume| *
              |φ₂ ω| * |Z₂ ω|
            ≤ C₁ * (Mσ ^ 2 * (t₁ - s₁)) * C₂ * |Z₂ ω| :=
          mul_le_mul_of_nonneg_right habc (abs_nonneg _)
          _ = C₁ * C₂ * (Mσ ^ 2 * (t₁ - s₁)) * |Z₂ ω| := by ring)
  -- Rewrite: (φ₁Z₁)(φ₂Z₂) = (φ₁·ΔSI₁²·φ₂)·Z₂ - (φ₁·QV₁·φ₂)·Z₂
  have h_rw : (fun ω => (φ₁ ω * ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
      ∫ r in Icc s₁ t₁, (X.diffusion r ω) ^ 2 ∂volume)) *
      (φ₂ ω * Z₂ ω)) =
    fun ω => (φ₁ ω * (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * φ₂ ω) *
      Z₂ ω - (φ₁ ω * (∫ r in Icc s₁ t₁, (X.diffusion r ω) ^ 2 ∂volume) * φ₂ ω) *
      Z₂ ω := by ext ω; ring
  rw [h_rw, integral_sub h_term1_int h_term2_int]
  -- Part 1: E[(φ₁·ΔSI₁²·φ₂)·Z₂] = 0
  have h_part1 : ∫ ω, (φ₁ ω * (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 *
      φ₂ ω) * Z₂ ω ∂μ = 0 :=
    integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s₂)
      ((hφ₁_meas.mul
        (((X.stoch_integral_adapted t₁ (le_trans hs₁ hst₁)).sub
          ((X.stoch_integral_adapted s₁ hs₁).mono (F.mono s₁ t₁ hst₁) le_rfl)).pow_const 2
          |>.mono (F.mono t₁ s₂ ht₁s₂) le_rfl)).mul hφ₂_meas)
      hZ₂_int h_term1_int
      (X.compensated_sq_setIntegral_zero hMσ s₂ t₂ hs₂ hst₂)
  -- Part 2: E[(φ₁·QV₁·φ₂)·Z₂] = 0 by Fubini
  have h_part2 : ∫ ω, (φ₁ ω * (∫ r in Icc s₁ t₁, (X.diffusion r ω) ^ 2 ∂volume) *
      φ₂ ω) * Z₂ ω ∂μ = 0 := by
    -- σ²(r,·) is F_{s₂}-measurable for r ∈ [s₁,t₁]
    have h_diff_Fs₂ : ∀ r, r ∈ Icc s₁ t₁ →
        @Measurable Ω ℝ (F.σ_algebra s₂) _ (fun ω => (X.diffusion r ω) ^ 2) := by
      intro r ⟨_, hrt⟩
      exact ((X.diffusion_adapted r).mono (F.mono r s₂ (le_trans hrt ht₁s₂)) le_rfl).pow_const 2
    -- For each r, E[φ₁·φ₂·σ²(r)·Z₂] = 0
    have h_inner_zero : ∀ r, r ∈ Icc s₁ t₁ →
        ∫ ω, (φ₁ ω * (X.diffusion r ω) ^ 2 * φ₂ ω) * Z₂ ω ∂μ = 0 := by
      intro r hr
      apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s₂)
      · exact hφ₁_meas.mul (h_diff_Fs₂ r hr) |>.mul hφ₂_meas
      · exact hZ₂_int
      · -- φ₁σ²φ₂·Z₂ integrable: bounded by C₁C₂Mσ²·|Z₂|
        exact (hZ₂_int.norm.const_mul (C₁ * C₂ * Mσ ^ 2)).mono'
          (((hφ₁_m.aestronglyMeasurable.mul
            (h_diff_Fs₂ r hr |>.mono (F.le_ambient s₂) le_rfl).aestronglyMeasurable).mul
            hφ₂_m.aestronglyMeasurable).mul hZ₂_int.aestronglyMeasurable)
          (ae_of_all _ fun ω => by
            simp only [Real.norm_eq_abs]
            rw [abs_mul, abs_mul, abs_mul]
            simp only [abs_of_nonneg (sq_nonneg (X.diffusion r ω))]
            have hσ_sq : (X.diffusion r ω) ^ 2 ≤ Mσ ^ 2 :=
              (sq_abs (X.diffusion r ω)).symm ▸
                pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω) 2
            have := mul_le_mul (mul_le_mul (hφ₁_bdd ω) hσ_sq (sq_nonneg _)
                (le_trans (abs_nonneg _) (hφ₁_bdd ω)))
              (hφ₂_bdd ω) (abs_nonneg _)
              (mul_nonneg (le_trans (abs_nonneg _) (hφ₁_bdd ω)) (sq_nonneg _))
            calc |φ₁ ω| * (X.diffusion r ω) ^ 2 * |φ₂ ω| * |Z₂ ω|
                ≤ C₁ * Mσ ^ 2 * C₂ * |Z₂ ω| :=
              mul_le_mul_of_nonneg_right this (abs_nonneg _)
              _ = C₁ * C₂ * Mσ ^ 2 * |Z₂ ω| := by ring)
      · exact X.compensated_sq_setIntegral_zero hMσ s₂ t₂ hs₂ hst₂
    -- Pull φ₁φ₂Z₂ inside: (φ₁·(∫σ²)·φ₂)·Z₂ = ∫(φ₁·σ²·φ₂·Z₂)
    have h_pull : ∀ ω, (φ₁ ω * (∫ r in Icc s₁ t₁, (X.diffusion r ω) ^ 2 ∂volume) *
        φ₂ ω) * Z₂ ω =
      ∫ r in Icc s₁ t₁, (φ₁ ω * (X.diffusion r ω) ^ 2 * φ₂ ω) * Z₂ ω ∂volume := fun ω => by
      conv_rhs => arg 2; ext r
                  rw [show (φ₁ ω * (X.diffusion r ω) ^ 2 * φ₂ ω) * Z₂ ω =
                    (X.diffusion r ω) ^ 2 * (φ₁ ω * φ₂ ω * Z₂ ω) from by ring]
      rw [integral_mul_const]; ring
    simp_rw [h_pull]
    -- Swap integrals by Fubini
    set ν := volume.restrict (Icc s₁ t₁)
    have hν_finite : IsFiniteMeasure ν :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    -- Product integrability
    have h_meas_σ_sq : Measurable (fun p : Ω × ℝ => (X.diffusion p.2 p.1) ^ 2) :=
      (X.diffusion_jointly_measurable.comp measurable_swap).pow_const 2
    have h_meas_uncurry : AEStronglyMeasurable
        (Function.uncurry (fun ω r => (φ₁ ω * (X.diffusion r ω) ^ 2 * φ₂ ω) * Z₂ ω))
        (μ.prod ν) :=
      (((hφ₁_m.aestronglyMeasurable.comp_fst (ν := ν)).mul
        h_meas_σ_sq.aestronglyMeasurable).mul
        (hφ₂_m.aestronglyMeasurable.comp_fst (ν := ν))).mul
        (hZ₂_int.aestronglyMeasurable.comp_fst (ν := ν))
    have h_product_int : Integrable
        (Function.uncurry (fun ω r => (φ₁ ω * (X.diffusion r ω) ^ 2 * φ₂ ω) * Z₂ ω))
        (μ.prod ν) :=
      ((hZ₂_int.norm.const_mul (C₁ * C₂ * Mσ ^ 2)).comp_fst (ν := ν)).mono'
        h_meas_uncurry
        (ae_of_all _ fun ⟨ω, r⟩ => by
          simp only [Function.uncurry, Real.norm_eq_abs]
          rw [abs_mul, abs_mul, abs_mul]
          simp only [abs_of_nonneg (sq_nonneg (X.diffusion r ω))]
          have hσ_sq : (X.diffusion r ω) ^ 2 ≤ Mσ ^ 2 :=
            (sq_abs (X.diffusion r ω)).symm ▸
              pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω) 2
          have := mul_le_mul (mul_le_mul (hφ₁_bdd ω) hσ_sq (sq_nonneg _)
              (le_trans (abs_nonneg _) (hφ₁_bdd ω)))
            (hφ₂_bdd ω) (abs_nonneg _)
            (mul_nonneg (le_trans (abs_nonneg _) (hφ₁_bdd ω)) (sq_nonneg _))
          calc |φ₁ ω| * (X.diffusion r ω) ^ 2 * |φ₂ ω| * |Z₂ ω|
              ≤ C₁ * Mσ ^ 2 * C₂ * |Z₂ ω| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg _)
            _ = C₁ * C₂ * Mσ ^ 2 * |Z₂ ω| := by ring)
    rw [integral_integral_swap h_product_int]
    -- Each inner integral is 0
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact h_inner_zero r hr
  linarith

/-! ## Weighted compensated partition orthogonality -/

/-- Weighted compensated orthogonality on a capped partition:
    E[(wᵢZᵢ)(wⱼZⱼ)] = 0 for i < j, with capped partition times
    τᵢ = min(i·T/(n+1), u). -/
theorem weighted_compensated_orthogonal_partition {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 ≤ T) (hu : 0 ≤ u) (_huT : u ≤ T) (n : ℕ)
    (w : Fin (n+1) → Ω → ℝ) {C_w : ℝ}
    (hw_bdd : ∀ (i : Fin (n+1)) (ω : Ω), |w i ω| ≤ C_w)
    (hw_meas : ∀ i : Fin (n+1),
      @Measurable Ω ℝ (F.σ_algebra (min (↑(i : ℕ) * T / ↑(n + 1)) u)) _ (w i))
    (i j : Fin (n + 1)) (hij : (i : ℕ) < (j : ℕ)) :
    ∫ ω,
      (w i ω * ((X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
        X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
       ∫ r in Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
           (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
         (X.diffusion r ω) ^ 2 ∂volume)) *
      (w j ω * ((X.stoch_integral (min ((↑(j : ℕ) + 1) * T / ↑(n + 1)) u) ω -
        X.stoch_integral (min (↑(j : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
       ∫ r in Icc (min (↑(j : ℕ) * T / ↑(n + 1)) u)
           (min ((↑(j : ℕ) + 1) * T / ↑(n + 1)) u),
         (X.diffusion r ω) ^ 2 ∂volume)) ∂μ = 0 := by
  -- Capped partition time properties
  have hs₁_nn : 0 ≤ min (↑(i : ℕ) * T / ↑(n + 1)) u := le_min (by positivity) hu
  have hst₁ : min (↑(i : ℕ) * T / ↑(n + 1)) u ≤ min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u :=
    min_le_min_right u (div_le_div_of_nonneg_right (by nlinarith [hT])
      (by positivity : (0 : ℝ) < ↑(n + 1)).le)
  have ht₁s₂ : min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u ≤ min (↑(j : ℕ) * T / ↑(n + 1)) u :=
    min_le_min_right u (partition_time_disjoint T hT n i j hij)
  have hst₂ : min (↑(j : ℕ) * T / ↑(n + 1)) u ≤ min ((↑(j : ℕ) + 1) * T / ↑(n + 1)) u :=
    min_le_min_right u (div_le_div_of_nonneg_right (by nlinarith [hT])
      (by positivity : (0 : ℝ) < ↑(n + 1)).le)
  exact X.weighted_compensated_orthogonal hMσ _ _ _ _ hs₁_nn hst₁ ht₁s₂ hst₂ _ _
    ((hw_meas i).mono (F.mono _ _ (le_trans hst₁ ht₁s₂)) le_rfl)
    (hw_meas j) (hw_bdd i) (hw_bdd j)

/-! ## Main weighted QV discrepancy L² bound -/

set_option maxHeartbeats 4000000 in
/-- Weighted QV discrepancy L2 bound for capped partitions. -/
theorem weighted_capped_qv_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) (n : ℕ)
    (w : Fin (n+1) → Ω → ℝ) {C_w : ℝ} (hCw : 0 ≤ C_w)
    (hw_bdd : ∀ (i : Fin (n+1)) (ω : Ω), |w i ω| ≤ C_w)
    (hw_meas : ∀ i : Fin (n+1),
      @Measurable Ω ℝ (F.σ_algebra (min (↑(i : ℕ) * T / ↑(n + 1)) u)) _ (w i)) :
    ∫ ω, (∑ i : Fin (n + 1),
        w i ω *
        ((∫ s in Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          (X.diffusion s ω) ^ 2 ∂volume) -
         (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
          X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) ^ 2 ∂μ ≤
    3 * (C_w ^ 2 * 8 * Mσ ^ 4 * u +
      4 * C_w ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T +
      C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T) * T / ↑(n + 1) := by
  -- === SETUP ===
  have hn_pos : (0 : ℝ) < ↑(n + 1) := by positivity
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hMμ_nn : 0 ≤ Mμ := le_trans (abs_nonneg _) (hMμ 0 (Classical.arbitrary Ω))
  have hMσ_nn : 0 ≤ Mσ := le_trans (abs_nonneg _) (hMσ 0 (Classical.arbitrary Ω))
  set sc : ℕ → ℝ := fun i => min (↑i * T / ↑(n + 1)) u
  have hsc_succ : ∀ k : ℕ, sc (k + 1) = min ((↑k + 1) * T / ↑(n + 1)) u := by
    intro k; simp only [sc, Nat.cast_succ]
  simp_rw [← hsc_succ]
  -- Mesh bound
  have hΔ_le : ∀ i : ℕ, sc (i + 1) - sc i ≤ T / ↑(n + 1) := by
    intro i; show min _ _ - min _ _ ≤ _
    have ha : ↑i * T / ↑(n + 1) ≤ ↑(i + 1) * T / ↑(n + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.le_succ i) hT.le) (by positivity : (0 : ℝ) < ↑(n + 1)).le
    have hd : ↑(i + 1) * T / ↑(n + 1) - ↑i * T / ↑(n + 1) = T / ↑(n + 1) := by
      rw [Nat.cast_succ]; ring
    show min _ _ - min _ _ ≤ _
    simp only [min_def]; split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · linarith [div_nonneg hT.le hn_pos.le]
  -- Capped time properties
  have hsc_nn : ∀ i : ℕ, 0 ≤ sc i := fun i => le_min (by positivity) hu
  have hsc_mono : ∀ i : ℕ, sc i ≤ sc (i + 1) := fun i =>
    min_le_min_right u (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hT.le)
      (by positivity : (0 : ℝ) < ↑(n + 1)).le)
  -- Sum of interval lengths ≤ u
  have hΔ_sum : ∑ i : Fin (n + 1), (sc ((i : ℕ) + 1) - sc (i : ℕ)) ≤ u := by
    rw [Fin.sum_univ_eq_sum_range (fun i => sc (i + 1) - sc i) (n + 1),
        Finset.sum_range_sub sc]
    have h0 : sc 0 = 0 := by simp [sc, min_eq_left hu]
    rw [h0, sub_zero]
    exact min_le_right _ _
  -- Sum of squared intervals ≤ T/(n+1) * u
  have hΔ_sq_sum : ∑ i : Fin (n + 1), (sc ((i : ℕ) + 1) - sc (i : ℕ)) ^ 2 ≤
      T / ↑(n + 1) * u := by
    calc ∑ i : Fin (n + 1), (sc ((i : ℕ) + 1) - sc (i : ℕ)) ^ 2
        ≤ ∑ i : Fin (n + 1), T / ↑(n + 1) * (sc ((i : ℕ) + 1) - sc (i : ℕ)) := by
          apply Finset.sum_le_sum; intro i _
          rw [sq]; exact mul_le_mul_of_nonneg_right (hΔ_le _)
            (sub_nonneg.mpr (hsc_mono _))
      _ = T / ↑(n + 1) * ∑ i : Fin (n + 1), (sc ((i : ℕ) + 1) - sc (i : ℕ)) := by
          rw [← Finset.mul_sum]
      _ ≤ T / ↑(n + 1) * u := by
          exact mul_le_mul_of_nonneg_left hΔ_sum (div_nonneg hT.le hn_pos.le)
  -- === DECOMPOSITION ===
  set ΔD : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)), X.drift s ω ∂volume
  set ΔSI : Fin (n + 1) → Ω → ℝ := fun i ω =>
    X.stoch_integral (sc ((i : ℕ) + 1)) ω - X.stoch_integral (sc (i : ℕ)) ω
  have h_decomp : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process (sc ((i : ℕ) + 1)) ω - X.process (sc (i : ℕ)) ω =
      ΔD i ω + ΔSI i ω := by
    -- Use integral_form at each time point, then subtract + split integral
    have h_all : ∀ᵐ ω ∂μ, ∀ k : Fin (n + 2),
        X.process (sc (k : ℕ)) ω = X.process 0 ω +
          (∫ s in Icc 0 (sc (k : ℕ)), X.drift s ω ∂volume) +
          X.stoch_integral (sc (k : ℕ)) ω := by
      rw [ae_all_iff]; intro k
      exact X.integral_form (sc (k : ℕ)) (hsc_nn _)
    filter_upwards [h_all] with ω hω
    intro i
    have hi := hω ⟨(i : ℕ), by omega⟩
    have hi1 := hω ⟨(i : ℕ) + 1, by omega⟩
    simp only [] at hi hi1
    have h_int := X.drift_time_integrable ω _ (le_trans (hsc_nn _) (hsc_mono ↑i))
    have hsplit := setIntegral_Icc_split (hsc_nn ↑i) (hsc_mono ↑i) h_int
    simp only [ΔD, ΔSI]; linarith
  set Z : Fin (n + 1) → Ω → ℝ := fun i ω =>
    (ΔSI i ω) ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
      (X.diffusion s ω) ^ 2 ∂volume
  -- === THREE-WAY DECOMPOSITION: goal = -(B₁ + 2B₂ + B₃) ===
  set B₁ : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), w i ω * Z i ω
  set B₂ : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), w i ω * ΔSI i ω * ΔD i ω
  set B₃ : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), w i ω * (ΔD i ω) ^ 2
  -- A.e. Young bound
  have h_young : ∀ a b c : ℝ, (a + 2 * b + c) ^ 2 ≤
      3 * a ^ 2 + 12 * b ^ 2 + 3 * c ^ 2 := by
    intro a b c
    nlinarith [sq_nonneg (a - c), sq_nonneg (a - 2 * b), sq_nonneg (c - 2 * b)]
  have h_ae_bound : ∀ᵐ ω ∂μ,
      (∑ i : Fin (n + 1), w i ω *
        ((∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume) -
        (X.process (sc ((i : ℕ) + 1)) ω -
          X.process (sc (i : ℕ)) ω) ^ 2)) ^ 2 ≤
      3 * (B₁ ω) ^ 2 + 12 * (B₂ ω) ^ 2 + 3 * (B₃ ω) ^ 2 := by
    filter_upwards [h_decomp] with ω hω
    have h_eq : (∑ i : Fin (n + 1), w i ω *
        ((∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume) -
        (X.process (sc ((i : ℕ) + 1)) ω -
          X.process (sc (i : ℕ)) ω) ^ 2)) =
      -(B₁ ω + 2 * B₂ ω + B₃ ω) := by
      have h_term : ∀ i : Fin (n + 1),
          w i ω * ((∫ s in Icc (sc ↑i) (sc (↑i + 1)),
            (X.diffusion s ω) ^ 2 ∂volume) -
          (X.process (sc (↑i + 1)) ω - X.process (sc ↑i) ω) ^ 2) =
        -(w i ω * Z i ω + 2 * (w i ω * ΔSI i ω * ΔD i ω) +
          w i ω * (ΔD i ω) ^ 2) := fun i => by
        simp only [Z, ΔSI]; rw [hω i]; ring
      simp_rw [h_term, Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [B₁, B₂, B₃, ← Finset.mul_sum]
    rw [h_eq, neg_sq]; exact h_young _ _ _
  -- === INTEGRABILITY ===
  have hΔSI_sq_int : ∀ i : Fin (n + 1),
      Integrable (fun ω => (ΔSI i ω) ^ 2) μ := by
    intro i; simp only [ΔSI]
    exact si_increment_sq_integrable' X _ _ (hsc_nn _) (hsc_mono _)
  have hZ_int : ∀ i : Fin (n + 1), Integrable (Z i) μ := by
    intro i; simp only [Z, ΔSI]
    exact compensated_sq_integrable' X _ _ (hsc_nn _) (hsc_mono _)
  have hZ_sq_int : ∀ i : Fin (n + 1), Integrable (fun ω => (Z i ω) ^ 2) μ := by
    intro i; simp only [Z, ΔSI]
    exact compensated_sq_sq_integrable' X hMσ _ _ (hsc_nn _) (hsc_mono _)
  -- === HELPER: Drift increment bound ===
  have h_drift_bdd : ∀ (i : Fin (n + 1)) (ω : Ω),
      |ΔD i ω| ≤ Mμ * (sc (↑i + 1) - sc ↑i) := by
    intro i ω; simp only [ΔD]
    exact drift_increment_bound X hMμ _ _ (hsc_mono _) ω
  -- === HELPER: Ambient measurability ===
  have hw_m : ∀ i : Fin (n + 1), Measurable (w i) :=
    fun i => (hw_meas i).mono (F.le_ambient _) le_rfl
  have hΔSI_m : ∀ i : Fin (n + 1), Measurable (ΔSI i) := by
    intro i; simp only [ΔSI]
    exact (X.stoch_integral_measurable _ (hsc_nn _)).sub
      (X.stoch_integral_measurable _ (hsc_nn _))
  have hZ_m : ∀ i : Fin (n + 1), AEStronglyMeasurable (Z i) μ :=
    fun i => (hZ_int i).aestronglyMeasurable
  -- === INTEGRABILITY: wᵢZᵢ products (for orthogonality) ===
  have hwZ_sq_int : ∀ i : Fin (n + 1),
      Integrable (fun ω => (w i ω * Z i ω) ^ 2) μ := by
    intro i
    have : ∀ ω, (w i ω * Z i ω) ^ 2 ≤ C_w ^ 2 * (Z i ω) ^ 2 := by
      intro ω; rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (sq_le_sq' (abs_le.mp (hw_bdd i ω)).1 (abs_le.mp (hw_bdd i ω)).2) (sq_nonneg _)
    exact ((hZ_sq_int i).const_mul (C_w ^ 2)).mono'
      (let h := (hw_m i).aestronglyMeasurable.mul (hZ_m i)
       (h.mul h).congr (ae_of_all _ fun ω => (sq (w i ω * Z i ω)).symm))
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact this ω)
  have hwZ_cross_int : ∀ i j : Fin (n + 1),
      Integrable (fun ω => (w i ω * Z i ω) * (w j ω * Z j ω)) μ := by
    intro i j
    -- |(wᵢZᵢ)(wⱼZⱼ)| ≤ ½((wᵢZᵢ)² + (wⱼZⱼ)²)
    exact ((hwZ_sq_int i).add (hwZ_sq_int j)).mono'
      ((hw_m i).aestronglyMeasurable.mul (hZ_m i) |>.mul
        ((hw_m j).aestronglyMeasurable.mul (hZ_m j)))
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        calc |w i ω * Z i ω * (w j ω * Z j ω)|
            = |w i ω * Z i ω| * |w j ω * Z j ω| := abs_mul _ _
          _ ≤ (w i ω * Z i ω) ^ 2 + (w j ω * Z j ω) ^ 2 := by
              nlinarith [sq_abs (w i ω * Z i ω), sq_abs (w j ω * Z j ω),
                         sq_nonneg (|w i ω * Z i ω| - |w j ω * Z j ω|),
                         abs_nonneg (w i ω * Z i ω), abs_nonneg (w j ω * Z j ω)])
  -- === ORTHOGONALITY: E[(wᵢZᵢ)(wⱼZⱼ)] = 0 for i ≠ j ===
  have hwZ_orth : ∀ i j : Fin (n + 1), i ≠ j →
      ∫ ω, (w i ω * Z i ω) * (w j ω * Z j ω) ∂μ = 0 := by
    intro i j hij
    -- WLOG i < j (by symmetry of the integral)
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · -- i < j: direct from weighted_compensated_orthogonal_partition
      have h_eq : (fun ω => (w i ω * Z i ω) * (w j ω * Z j ω)) =
          fun ω => (w i ω * ((X.stoch_integral (sc (↑i + 1)) ω -
            X.stoch_integral (sc ↑i) ω) ^ 2 -
           ∫ r in Icc (sc ↑i) (sc (↑i + 1)), (X.diffusion r ω) ^ 2 ∂volume)) *
          (w j ω * ((X.stoch_integral (sc (↑j + 1)) ω -
            X.stoch_integral (sc ↑j) ω) ^ 2 -
           ∫ r in Icc (sc ↑j) (sc (↑j + 1)), (X.diffusion r ω) ^ 2 ∂volume)) := by
        ext ω; simp only [Z, ΔSI]
      rw [h_eq]; simp only [hsc_succ]
      exact weighted_compensated_orthogonal_partition X hMσ T u hT.le hu huT n
        w hw_bdd hw_meas i j h
    · -- j < i: swap and use symmetry
      have h_eq : (fun ω => (w i ω * Z i ω) * (w j ω * Z j ω)) =
          fun ω => (w j ω * Z j ω) * (w i ω * Z i ω) := by
        ext ω; ring
      rw [h_eq]
      have h_eq2 : (fun ω => (w j ω * Z j ω) * (w i ω * Z i ω)) =
          fun ω => (w j ω * ((X.stoch_integral (sc (↑j + 1)) ω -
            X.stoch_integral (sc ↑j) ω) ^ 2 -
           ∫ r in Icc (sc ↑j) (sc (↑j + 1)), (X.diffusion r ω) ^ 2 ∂volume)) *
          (w i ω * ((X.stoch_integral (sc (↑i + 1)) ω -
            X.stoch_integral (sc ↑i) ω) ^ 2 -
           ∫ r in Icc (sc ↑i) (sc (↑i + 1)), (X.diffusion r ω) ^ 2 ∂volume)) := by
        ext ω; simp only [Z, ΔSI]
      rw [h_eq2]; simp only [hsc_succ]
      exact weighted_compensated_orthogonal_partition X hMσ T u hT.le hu huT n
        w hw_bdd hw_meas j i h
  -- === MEASURABILITY of B₁ ===
  have hB₁_m : AEStronglyMeasurable B₁ μ :=
    (aestronglyMeasurable_sum (μ := μ) Finset.univ
      (f := fun (i : Fin (n + 1)) (ω : Ω) => w i ω * Z i ω)
      (fun i _ => (hw_m i).aestronglyMeasurable.mul (hZ_m i))).congr
      (ae_of_all _ fun ω => Finset.sum_apply ω Finset.univ _)
  -- === MEASURABILITY of ΔD (via decomposition) ===
  have hΔD_aesm : ∀ i : Fin (n + 1), AEStronglyMeasurable (ΔD i) μ := by
    intro i
    have h_eq : ΔD i =ᵐ[μ] fun ω =>
        (X.process (sc (↑i + 1)) ω - X.process (sc ↑i) ω) - ΔSI i ω := by
      filter_upwards [h_decomp] with ω hω
      have hi := hω i; simp only [ΔD, ΔSI] at hi ⊢; linarith
    have h1 : Measurable (X.process (sc (↑i + 1))) :=
      (X.process_adapted (sc (↑i + 1))).mono (F.le_ambient _) le_rfl
    have h2 : Measurable (X.process (sc ↑i)) :=
      (X.process_adapted (sc ↑i)).mono (F.le_ambient _) le_rfl
    exact (h1.aestronglyMeasurable.sub h2.aestronglyMeasurable |>.sub
      (hΔSI_m i).aestronglyMeasurable).congr h_eq.symm
  -- === MEASURABILITY of B₂ and B₃ ===
  have hB₂_m : AEStronglyMeasurable B₂ μ :=
    (aestronglyMeasurable_sum (μ := μ) Finset.univ
      (f := fun (i : Fin (n + 1)) (ω : Ω) => w i ω * ΔSI i ω * ΔD i ω)
      (fun i _ => ((hw_m i).aestronglyMeasurable.mul
        (hΔSI_m i).aestronglyMeasurable).mul (hΔD_aesm i))).congr
      (ae_of_all _ fun ω => Finset.sum_apply ω Finset.univ _)
  have hB₃_m : AEStronglyMeasurable B₃ μ :=
    (aestronglyMeasurable_sum (μ := μ) Finset.univ
      (f := fun (i : Fin (n + 1)) (ω : Ω) => w i ω * (ΔD i ω) ^ 2)
      (fun i _ => (hw_m i).aestronglyMeasurable.mul ((hΔD_aesm i).pow 2))).congr
      (ae_of_all _ fun ω => Finset.sum_apply ω Finset.univ _)
  -- === POINTWISE BOUNDS ===
  have h_dd_sq : ∀ (i : Fin (n + 1)) (ω : Ω),
      (ΔD i ω) ^ 2 ≤ Mμ ^ 2 * (sc (↑i + 1) - sc ↑i) ^ 2 := fun i ω =>
    (sq_abs (ΔD i ω)).symm ▸ (mul_pow Mμ _ 2).symm ▸
      pow_le_pow_left₀ (abs_nonneg _) (h_drift_bdd i ω) 2
  have hB₃_bdd : ∀ ω, |B₃ ω| ≤ C_w * Mμ ^ 2 * (T / ↑(n + 1) * u) := by
    intro ω; simp only [B₃]
    calc |∑ i : Fin (n + 1), w i ω * (ΔD i ω) ^ 2|
        ≤ ∑ i : Fin (n + 1), |w i ω * (ΔD i ω) ^ 2| := by
          simp only [← Real.norm_eq_abs]; exact norm_sum_le _ _
      _ ≤ ∑ i : Fin (n + 1), C_w * (Mμ ^ 2 * (sc (↑i + 1) - sc ↑i) ^ 2) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul, abs_of_nonneg (sq_nonneg (ΔD i ω))]
          exact mul_le_mul (hw_bdd i ω) (h_dd_sq i ω) (sq_nonneg _) hCw
      _ = C_w * Mμ ^ 2 * ∑ i : Fin (n + 1), (sc (↑i + 1) - sc ↑i) ^ 2 := by
          simp_rw [← Finset.mul_sum]; ring
      _ ≤ C_w * Mμ ^ 2 * (T / ↑(n + 1) * u) := by gcongr
  -- === INTEGRABILITY of B₁², B₂², B₃² ===
  have hB₁_int : Integrable (fun ω => (B₁ ω) ^ 2) μ := by
    have h_sum_int : Integrable (fun ω => ∑ i : Fin (n + 1), (w i ω * Z i ω) ^ 2) μ :=
      integrable_finset_sum _ fun i _ => hwZ_sq_int i
    exact (h_sum_int.const_mul ↑(n + 1)).mono'
      ((hB₁_m.mul hB₁_m).congr (ae_of_all _ fun ω => (sq (B₁ ω)).symm))
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        simp only [B₁]
        calc (∑ i, w i ω * Z i ω) ^ 2
            ≤ ↑(Finset.univ.card) * ∑ i, (w i ω * Z i ω) ^ 2 :=
              sq_sum_le_card_mul_sum_sq
          _ = ↑(n + 1) * ∑ i, (w i ω * Z i ω) ^ 2 := by
              rw [Finset.card_fin])
  -- B₂² pointwise bound: B₂² ≤ C_w²Mμ²T²/(n+1) · ∑(ΔSIᵢ)²
  have hB₂_pw : ∀ ω, (B₂ ω) ^ 2 ≤
      C_w ^ 2 * Mμ ^ 2 * T ^ 2 / ↑(n + 1) *
        ∑ i : Fin (n + 1), (ΔSI i ω) ^ 2 := by
    intro ω; simp only [B₂]
    have h_cs := @sq_sum_le_card_mul_sum_sq (Fin (n + 1)) ℝ _ _ _ _
      Finset.univ (fun i => w i ω * ΔSI i ω * ΔD i ω)
    rw [Finset.card_fin] at h_cs
    calc (∑ i, w i ω * ΔSI i ω * ΔD i ω) ^ 2
        ≤ ↑(n + 1) * ∑ i, (w i ω * ΔSI i ω * ΔD i ω) ^ 2 := h_cs
      _ ≤ ↑(n + 1) * ∑ i, C_w ^ 2 * Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 *
            (ΔSI i ω) ^ 2 := by
          gcongr with i _
          calc (w i ω * ΔSI i ω * ΔD i ω) ^ 2
              = (w i ω) ^ 2 * (ΔD i ω) ^ 2 * (ΔSI i ω) ^ 2 := by ring
            _ ≤ C_w ^ 2 * (Mμ ^ 2 * (T / ↑(n + 1)) ^ 2) * (ΔSI i ω) ^ 2 := by
                apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                have hw_sq : (w i ω) ^ 2 ≤ C_w ^ 2 :=
                  sq_le_sq' (abs_le.mp (hw_bdd i ω)).1 (abs_le.mp (hw_bdd i ω)).2
                have hd_sq : (ΔD i ω) ^ 2 ≤ Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 :=
                  le_trans (h_dd_sq i ω)
                    (mul_le_mul_of_nonneg_left
                      (pow_le_pow_left₀ (sub_nonneg.mpr (hsc_mono ↑i)) (hΔ_le ↑i) 2)
                      (sq_nonneg Mμ))
                exact mul_le_mul hw_sq hd_sq (sq_nonneg _) (sq_nonneg _)
            _ = C_w ^ 2 * Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * (ΔSI i ω) ^ 2 := by ring
      _ = C_w ^ 2 * Mμ ^ 2 * T ^ 2 / ↑(n + 1) * ∑ i, (ΔSI i ω) ^ 2 := by
          rw [← Finset.mul_sum]
          have hn : (↑(n + 1) : ℝ) ≠ 0 := ne_of_gt hn_pos
          field_simp
  have hB₂_int : Integrable (fun ω => (B₂ ω) ^ 2) μ :=
    ((integrable_finset_sum _ fun i _ => hΔSI_sq_int i).const_mul
      (C_w ^ 2 * Mμ ^ 2 * T ^ 2 / ↑(n + 1))).mono'
      ((hB₂_m.mul hB₂_m).congr (ae_of_all _ fun ω => (sq (B₂ ω)).symm))
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hB₂_pw ω)
  have hB₃_int : Integrable (fun ω => (B₃ ω) ^ 2) μ :=
    (integrable_const ((C_w * Mμ ^ 2 * (T / ↑(n + 1) * u)) ^ 2)).mono'
      ((hB₃_m.mul hB₃_m).congr (ae_of_all _ fun ω => (sq (B₃ ω)).symm))
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact (sq_abs (B₃ ω)).symm ▸
          pow_le_pow_left₀ (abs_nonneg _) (hB₃_bdd ω) 2)
  have h_dom_int : Integrable (fun ω =>
      3 * (B₁ ω) ^ 2 + 12 * (B₂ ω) ^ 2 + 3 * (B₃ ω) ^ 2) μ :=
    ((hB₁_int.const_mul 3).add (hB₂_int.const_mul 12)).add (hB₃_int.const_mul 3)
  -- === BOUND E[B₁²] via weighted orthogonality ===
  have hB₁_bound : ∫ ω, (B₁ ω) ^ 2 ∂μ ≤
      C_w ^ 2 * 8 * Mσ ^ 4 * u * T / ↑(n + 1) := by
    -- By orthogonality: E[B₁²] = ∑ E[(wᵢZᵢ)²]
    have h_orth := integral_sq_sum_orthogonal (fun i => fun ω => w i ω * Z i ω)
      hwZ_cross_int hwZ_orth
    simp only [B₁] at h_orth ⊢
    rw [h_orth]
    -- Bound each E[(wᵢZᵢ)²] ≤ C_w² · E[Zᵢ²] ≤ C_w² · 8Mσ⁴ · Δᵢ²
    calc ∑ i : Fin (n + 1), ∫ ω, (w i ω * Z i ω) ^ 2 ∂μ
        ≤ ∑ i : Fin (n + 1), ∫ ω, C_w ^ 2 * (Z i ω) ^ 2 ∂μ := by
          apply Finset.sum_le_sum; intro i _
          apply integral_mono (hwZ_sq_int i) ((hZ_sq_int i).const_mul _)
          intro ω; dsimp only; rw [mul_pow]
          exact mul_le_mul_of_nonneg_right
            (sq_le_sq' (abs_le.mp (hw_bdd i ω)).1 (abs_le.mp (hw_bdd i ω)).2) (sq_nonneg _)
      _ = ∑ i : Fin (n + 1), C_w ^ 2 * ∫ ω, (Z i ω) ^ 2 ∂μ := by
          congr 1; ext i; exact integral_const_mul _ _
      _ ≤ ∑ i : Fin (n + 1), C_w ^ 2 * (8 * Mσ ^ 4 * (sc (↑i + 1) - sc ↑i) ^ 2) := by
          apply Finset.sum_le_sum; intro i _
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg C_w)
          simp only [Z, ΔSI]
          exact si_compensated_sq_L2_single X hMσ _ _ (hsc_nn _) (hsc_mono _)
      _ = C_w ^ 2 * 8 * Mσ ^ 4 * ∑ i : Fin (n + 1), (sc (↑i + 1) - sc ↑i) ^ 2 := by
          simp_rw [← Finset.mul_sum]; ring
      _ ≤ C_w ^ 2 * 8 * Mσ ^ 4 * (T / ↑(n + 1) * u) := by
          gcongr
      _ = C_w ^ 2 * 8 * Mσ ^ 4 * u * T / ↑(n + 1) := by ring
  -- === BOUND E[B₂²] via Cauchy-Schwarz ===
  have hB₂_bound : ∫ ω, (B₂ ω) ^ 2 ∂μ ≤
      C_w ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T ^ 2 / ↑(n + 1) := by
    -- Step 1: E[B₂²] ≤ C_B₂ · ∑ E[(ΔSIᵢ)²]
    calc ∫ ω, (B₂ ω) ^ 2 ∂μ
        ≤ ∫ ω, (C_w ^ 2 * Mμ ^ 2 * T ^ 2 / ↑(n + 1) *
            ∑ i : Fin (n + 1), (ΔSI i ω) ^ 2) ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
            (((integrable_finset_sum _ fun i _ => hΔSI_sq_int i).const_mul _))
            (ae_of_all _ hB₂_pw)
      _ = C_w ^ 2 * Mμ ^ 2 * T ^ 2 / ↑(n + 1) *
          ∑ i : Fin (n + 1), ∫ ω, (ΔSI i ω) ^ 2 ∂μ := by
          rw [integral_const_mul]
          congr 1; exact integral_finset_sum _ fun i _ => hΔSI_sq_int i
      -- Step 2: ∑ E[(ΔSIᵢ)²] ≤ Mσ² · u via isometry + diffusion bound
      _ ≤ C_w ^ 2 * Mμ ^ 2 * T ^ 2 / ↑(n + 1) * (Mσ ^ 2 * u) := by
          gcongr
          calc ∑ i : Fin (n + 1), ∫ ω, (ΔSI i ω) ^ 2 ∂μ
              = ∑ i : Fin (n + 1), ∫ ω, (∫ r in Icc (sc ↑i) (sc (↑i + 1)),
                  (X.diffusion r ω) ^ 2 ∂volume) ∂μ := by
                congr 1; ext i; simp only [ΔSI]
                exact X.stoch_integral_isometry _ _ (hsc_nn _) (hsc_mono _)
            _ ≤ ∑ i : Fin (n + 1), Mσ ^ 2 * (sc (↑i + 1) - sc ↑i) := by
                apply Finset.sum_le_sum; intro i _
                calc ∫ ω, (∫ r in Icc (sc ↑i) (sc (↑i + 1)),
                      (X.diffusion r ω) ^ 2 ∂volume) ∂μ
                    ≤ ∫ _, Mσ ^ 2 * (sc (↑i + 1) - sc ↑i) ∂μ := by
                      apply integral_mono
                        (diffusion_sq_interval_integrable X _ _ (hsc_nn _) (hsc_mono _))
                        (integrable_const _)
                      intro ω; dsimp only
                      exact le_trans (le_abs_self _)
                        (diffusion_sq_integral_bound X hMσ _ _ (hsc_mono _) ω)
                  _ = Mσ ^ 2 * (sc (↑i + 1) - sc ↑i) := by
                      rw [integral_const, smul_eq_mul,
                        show μ.real Set.univ = 1 from by
                          simp [Measure.real, measure_univ], one_mul]
            _ = Mσ ^ 2 * ∑ i : Fin (n + 1), (sc (↑i + 1) - sc ↑i) := by
                rw [← Finset.mul_sum]
            _ ≤ Mσ ^ 2 * u := by gcongr
      _ = C_w ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T ^ 2 / ↑(n + 1) := by ring
  -- === BOUND E[B₃²] (pointwise) ===
  have hB₃_bound : ∫ ω, (B₃ ω) ^ 2 ∂μ ≤
      C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1) ^ 2 := by
    calc ∫ ω, (B₃ ω) ^ 2 ∂μ
        ≤ ∫ _, (C_w * Mμ ^ 2 * (T / ↑(n + 1) * u)) ^ 2 ∂μ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
            (integrable_const _) (ae_of_all _ fun ω =>
              (sq_abs (B₃ ω)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hB₃_bdd ω) 2)
      _ = (C_w * Mμ ^ 2 * (T / ↑(n + 1) * u)) ^ 2 := by
          rw [integral_const, smul_eq_mul,
            show μ.real Set.univ = 1 from by simp [Measure.real, measure_univ], one_mul]
      _ = C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1) ^ 2 := by ring
  -- === ASSEMBLY ===
  calc ∫ ω, (∑ i : Fin (n + 1), w i ω *
        ((∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume) -
        (X.process (sc ((i : ℕ) + 1)) ω -
          X.process (sc (i : ℕ)) ω) ^ 2)) ^ 2 ∂μ
      ≤ ∫ ω, (3 * (B₁ ω) ^ 2 + 12 * (B₂ ω) ^ 2 + 3 * (B₃ ω) ^ 2) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) h_dom_int h_ae_bound
    _ = 3 * ∫ ω, (B₁ ω) ^ 2 ∂μ + 12 * ∫ ω, (B₂ ω) ^ 2 ∂μ +
        3 * ∫ ω, (B₃ ω) ^ 2 ∂μ := by
      have h1 := integral_add ((hB₁_int.const_mul 3).add (hB₂_int.const_mul 12))
        (hB₃_int.const_mul 3)
      simp only [Pi.add_apply] at h1
      have h2 := integral_add (hB₁_int.const_mul 3) (hB₂_int.const_mul 12)
      rw [h1, h2, integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ 3 * (C_w ^ 2 * 8 * Mσ ^ 4 * u * T / ↑(n + 1)) +
        12 * (C_w ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T ^ 2 / ↑(n + 1)) +
        3 * (C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1) ^ 2) := by
      gcongr
    _ ≤ 3 * (C_w ^ 2 * 8 * Mσ ^ 4 * u +
        4 * C_w ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T +
        C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T) * T / ↑(n + 1) := by
      have hn1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_pos n
      -- Key: the /(n+1)² term is ≤ the /(n+1) term
      suffices h3 : 3 * (C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1) ^ 2) ≤
          3 * (C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1)) by
        -- With the upgrade, the three terms factor as (...)·T/(n+1)
        have h_eq : 3 * (C_w ^ 2 * 8 * Mσ ^ 4 * u * T / ↑(n + 1)) +
            12 * (C_w ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T ^ 2 / ↑(n + 1)) +
            3 * (C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1)) =
          3 * (C_w ^ 2 * 8 * Mσ ^ 4 * u + 4 * C_w ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T +
            C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T) * T / ↑(n + 1) := by ring
        linarith
      have h_le : ↑(n + 1) ≤ (↑(n + 1) : ℝ) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_right hn_pos.le hn1
      have h_div : C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1) ^ 2 ≤
          C_w ^ 2 * Mμ ^ 4 * u ^ 2 * T ^ 2 / ↑(n + 1) :=
        div_le_div_of_nonneg_left (by positivity) hn_pos h_le
      linarith

end SPDE
