/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.IsometryTheorems

/-!
# Conditional Itô Isometry

This file proves the conditional (set-integral) version of the Itô isometry:
for A ∈ F_s with s ≤ s₂ ≤ t₂,

  ∫_A [(SI(t₂)-SI(s₂))² - ∫_{s₂}^{t₂} σ² du] dμ = 0

This is the key ingredient for proving orthogonality of compensated squared
stochastic integral increments on disjoint intervals.

## Strategy

The proof uses L² limits from simple process approximations:

1. For each simple approximation Hₙ, define M_n(t) = SI_n(t)² - ∫₀ᵗ Hₙ²
2. Show ∫_A [M_n(t₂) - M_n(s₂)] = 0 (simple process compensated square martingale)
3. Show M_n → M in L¹
4. Conclude ∫_A [M(t₂) - M(s₂)] = 0

Step 2 uses the cross-term vanishing from the simple process martingale property
(existing `stochasticIntegral_at_martingale`) combined with the BM compensated
square set-integral factorization (from `quadratic_variation_compensator`).

## Main Results

* `ItoProcess.compensated_sq_setIntegral_zero` — The conditional isometry
* `ItoProcess.stoch_integral_squared_orthogonal` — Orthogonality (replaces sorry)

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3, Theorem 3.2.1
-/

noncomputable section

open MeasureTheory Set Filter

variable {Ω : Type*} [instΩ : MeasurableSpace Ω] {μ : Measure Ω}

namespace SPDE

/-! ## Set-integral cross-term vanishing for stochastic integrals -/

/-- On a set A ∈ F_s, the cross-term SI(s)·(SI(t)-SI(s)) integrates to zero.
    This is the set-integral analogue of the cross-term in `stoch_integral_cross_term`. -/
theorem ItoProcess.setIntegral_cross_term_zero {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s) A) :
    ∫ ω in A, X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω) ∂μ = 0 := by
  -- Rewrite as full integral with indicator: ∫_A f·g = ∫ (1_A·f)·g
  rw [← integral_indicator (F.le_ambient s A hA)]
  simp_rw [indicator_mul_left]
  -- Apply orthogonality lemma with X = 1_A·SI(s), Y = SI(t)-SI(s)
  apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s)
  · -- 1_A·SI(s) is F_s-measurable
    exact (X.stoch_integral_adapted s hs).indicator hA
  · -- SI(t)-SI(s) is integrable
    exact (X.stoch_integral_integrable t (le_trans hs hst)).sub
      (X.stoch_integral_integrable s hs)
  · -- Product integrability: (1_A·SI(s))·(SI(t)-SI(s)) is integrable
    -- Use AM-GM: |ab| ≤ a²+b²
    have hSI_s_sq := X.stoch_integral_sq_integrable s hs
    have hSI_t_sq := X.stoch_integral_sq_integrable t (le_trans hs hst)
    apply Integrable.mono' ((hSI_s_sq.add hSI_t_sq).add hSI_s_sq)
    · exact ((X.stoch_integral_integrable s hs).indicator
        (F.le_ambient s A hA)).aestronglyMeasurable.mul
        ((X.stoch_integral_integrable t (le_trans hs hst)).sub
          (X.stoch_integral_integrable s hs)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs]
      by_cases hω : ω ∈ A
      · simp only [indicator_of_mem hω]
        rw [abs_mul]
        set a := |X.stoch_integral s ω|
        set b := |X.stoch_integral t ω - X.stoch_integral s ω|
        nlinarith [sq_nonneg (a - b), sq_abs (X.stoch_integral s ω),
          sq_abs (X.stoch_integral t ω - X.stoch_integral s ω),
          sq_abs (X.stoch_integral t ω)]
      · simp only [indicator_of_notMem hω, zero_mul, abs_zero]
        positivity
  · -- ∫_B (SI(t)-SI(s)) = 0 for B ∈ F_s (martingale property)
    intro B hB
    rw [integral_sub (X.stoch_integral_integrable t (le_trans hs hst)).integrableOn
        (X.stoch_integral_integrable s hs).integrableOn]
    exact sub_eq_zero.mpr (X.stoch_integral_martingale s t hs hst B hB)

/-- Set-integral squared increment decomposition:
    ∫_A (SI(t)-SI(s))² = ∫_A SI(t)² - ∫_A SI(s)²

    Follows from the set-integral cross-term vanishing. -/
theorem ItoProcess.setIntegral_sq_increment_eq_diff {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s) A) :
    ∫ ω in A, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
    ∫ ω in A, (X.stoch_integral t ω) ^ 2 ∂μ -
    ∫ ω in A, (X.stoch_integral s ω) ^ 2 ∂μ := by
  have hSI_s_sq := X.stoch_integral_sq_integrable s hs
  have hSI_t_sq := X.stoch_integral_sq_integrable t (le_trans hs hst)
  have hcross := X.setIntegral_cross_term_zero s t hs hst A hA
  -- Cross term integrability
  have hcross_int : Integrable
      (fun ω => X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω)) μ := by
    apply Integrable.mono' ((hSI_t_sq.add hSI_s_sq).add hSI_s_sq)
    · exact (X.stoch_integral_integrable s hs).aestronglyMeasurable.mul
        ((X.stoch_integral_integrable t (le_trans hs hst)).sub
          (X.stoch_integral_integrable s hs)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_mul]; nlinarith [sq_abs (X.stoch_integral s ω),
        sq_abs (X.stoch_integral t ω - X.stoch_integral s ω),
        sq_abs (X.stoch_integral t ω),
        sq_nonneg (|X.stoch_integral s ω| - |X.stoch_integral t ω - X.stoch_integral s ω|)]
  -- Suffices: ∫_A SI(t)² = ∫_A SI(s)² + ∫_A (SI(t)-SI(s))²
  -- Proof: SI(t)² = SI(s)² + 2·SI(s)·(SI(t)-SI(s)) + (SI(t)-SI(s))²
  -- and ∫_A [2·SI(s)·(SI(t)-SI(s))] = 0 by cross-term vanishing
  suffices h : ∫ ω in A, (X.stoch_integral t ω) ^ 2 ∂μ =
      ∫ ω in A, (X.stoch_integral s ω) ^ 2 ∂μ +
      ∫ ω in A, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ by linarith
  -- Split: ∫_A SI(t)² = ∫_A [SI(s)² + 2·cross + incr²]
  --                    = ∫_A SI(s)² + 2·∫_A cross + ∫_A incr²
  have h_step1 : ∫ ω in A, (X.stoch_integral t ω) ^ 2 ∂μ =
      ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
        2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω)) +
        (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) ∂μ := by
    congr 1; ext ω; ring
  have h_step2 : ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
      2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω)) +
      (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) ∂μ =
      ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
        2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω))) ∂μ +
      ∫ ω in A, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ :=
    integral_add (hSI_s_sq.integrableOn.add (hcross_int.const_mul 2).integrableOn)
      (si_increment_sq_integrable' X s t hs hst).integrableOn
  have h_step3 : ∫ ω in A, ((X.stoch_integral s ω) ^ 2 +
      2 * (X.stoch_integral s ω * (X.stoch_integral t ω - X.stoch_integral s ω))) ∂μ =
      ∫ ω in A, (X.stoch_integral s ω) ^ 2 ∂μ +
      ∫ ω in A, 2 * (X.stoch_integral s ω *
        (X.stoch_integral t ω - X.stoch_integral s ω)) ∂μ :=
    integral_add hSI_s_sq.integrableOn (hcross_int.const_mul 2).integrableOn
  have h_step4 : ∫ ω in A, 2 * (X.stoch_integral s ω *
      (X.stoch_integral t ω - X.stoch_integral s ω)) ∂μ = 0 := by
    rw [show (fun ω => 2 * (X.stoch_integral s ω *
        (X.stoch_integral t ω - X.stoch_integral s ω))) =
        (fun ω => (2 : ℝ) * (X.stoch_integral s ω *
          (X.stoch_integral t ω - X.stoch_integral s ω))) from rfl,
      integral_const_mul, hcross, mul_zero]
  linarith

/-! ## Compensated square L¹ convergence -/

/-- L¹ convergence of the compensated square:
    ∫ |SI_n(t)² - SI(t)²| → 0 from L² convergence SI_n → SI.
    Uses Cauchy-Schwarz: |a²-b²| = |a-b|·|a+b|. -/
private theorem sq_L1_tendsto_of_L2 {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (approx : ℕ → SimpleProcess F)
    (hadapted : ∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (X.BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i))
    (hbdd : ∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C)
    (hnn : ∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i)
    (t : ℝ) (ht : 0 ≤ t)
    (hL2 : Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
                                     X.stoch_integral t ω)^2 ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω,
      ‖(SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω)^2 -
       (X.stoch_integral t ω)^2‖ ∂μ)
      atTop (nhds 0) := by
  -- Abbreviations
  set a := fun n ω => SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω
  set b := fun ω => X.stoch_integral t ω
  set ε := fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂μ
  set C := ∫ ω, (b ω) ^ 2 ∂μ
  -- Integrability
  have hb_sq : Integrable (fun ω => (b ω) ^ 2) μ := X.stoch_integral_sq_integrable t ht
  have hb_int : Integrable b μ := X.stoch_integral_integrable t ht
  have ha_int : ∀ n, Integrable (a n) μ := fun n =>
    SimpleProcess.stochasticIntegral_at_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) t ht
  have hdiff_sq : ∀ n, Integrable (fun ω => (a n ω - b ω) ^ 2) μ := fun n =>
    SimpleProcess.stochasticIntegral_at_sub_sq_integrable _ X.BM
      (hadapted n) (hbdd n) (hnn n) b hb_int hb_sq t ht
  -- Pointwise bound: ‖a²-b²‖ ≤ (a-b)² + 2·|a-b|·|b|
  have h_pw : ∀ n ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ≤
      (a n ω - b ω) ^ 2 + 2 * (|a n ω - b ω| * |b ω|) := by
    intro n ω
    rw [Real.norm_eq_abs]
    have : (a n ω) ^ 2 - (b ω) ^ 2 = (a n ω - b ω) * (a n ω + b ω) := by ring
    rw [this, abs_mul]
    have h1 : |a n ω + b ω| ≤ |a n ω - b ω| + 2 * |b ω| := by
      calc |a n ω + b ω| = |(a n ω - b ω) + 2 * b ω| := by ring_nf
        _ ≤ |a n ω - b ω| + |2 * b ω| := abs_add_le _ _
        _ = |a n ω - b ω| + 2 * |b ω| := by rw [abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0)]
    calc |a n ω - b ω| * |a n ω + b ω|
        ≤ |a n ω - b ω| * (|a n ω - b ω| + 2 * |b ω|) := by gcongr
      _ = |a n ω - b ω| ^ 2 + 2 * (|a n ω - b ω| * |b ω|) := by
          rw [show |a n ω - b ω| ^ 2 = |a n ω - b ω| * |a n ω - b ω| from sq _]; ring
      _ = (a n ω - b ω) ^ 2 + 2 * (|a n ω - b ω| * |b ω|) := by rw [sq_abs]
  -- Upper bound: ∫ ‖a²-b²‖ ≤ ε(n) + 2·√(ε(n))·√C
  have h_upper : ∀ n, ∫ ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ∂μ ≤
      ε n + 2 * Real.sqrt (ε n) * Real.sqrt C := by
    intro n
    -- Integrability of |a-b|·|b| via AM-GM domination
    have h_abs_prod : Integrable (fun ω => |a n ω - b ω| * |b ω|) μ :=
      ((hdiff_sq n).add hb_sq).mono'
        (AEStronglyMeasurable.mul
          (((ha_int n).sub hb_int).aestronglyMeasurable.norm.congr
            (ae_of_all _ fun ω => Real.norm_eq_abs _))
          (hb_int.aestronglyMeasurable.norm.congr
            (ae_of_all _ fun ω => Real.norm_eq_abs _)))
        (ae_of_all _ fun ω => by
          simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_abs]
          nlinarith [sq_abs (a n ω - b ω), sq_abs (b ω),
            sq_nonneg (|a n ω - b ω| - |b ω|)])
    -- Step 1: ∫ ‖a²-b²‖ ≤ ∫ [(a-b)² + 2|a-b||b|] = ε(n) + 2·∫|a-b||b|
    have h_int_bound : ∫ ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ∂μ ≤
        ε n + 2 * ∫ ω, |a n ω - b ω| * |b ω| ∂μ := by
      calc ∫ ω, ‖(a n ω) ^ 2 - (b ω) ^ 2‖ ∂μ
          ≤ ∫ ω, ((a n ω - b ω) ^ 2 + 2 * (|a n ω - b ω| * |b ω|)) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _)
              ((hdiff_sq n).add (h_abs_prod.const_mul 2))
              (ae_of_all _ (h_pw n))
        _ = ε n + 2 * ∫ ω, |a n ω - b ω| * |b ω| ∂μ := by
            rw [integral_add (hdiff_sq n) (h_abs_prod.const_mul 2),
              integral_const_mul]
    -- Step 2: ∫|a-b||b| ≤ √(ε(n))·√C by Cauchy-Schwarz
    have h_cs : ∫ ω, |a n ω - b ω| * |b ω| ∂μ ≤
        Real.sqrt (ε n) * Real.sqrt C := by
      have h_nn : 0 ≤ ∫ ω, |a n ω - b ω| * |b ω| ∂μ :=
        integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      -- Reduce to (∫|f||g|)² ≤ ε·C by squaring both sides
      suffices hsq : (∫ ω, |a n ω - b ω| * |b ω| ∂μ) ^ 2 ≤ ε n * C by
        rw [← Real.sqrt_sq h_nn, ← Real.sqrt_mul (integral_nonneg fun ω => sq_nonneg _)]
        exact Real.sqrt_le_sqrt hsq
      -- Cauchy-Schwarz: (∫|f||g|)² ≤ (∫|f|²)(∫|g|²) = (∫(a-b)²)(∫b²) = ε·C
      have habs_sq : ∀ x : ℝ, |x| ^ 2 = x ^ 2 := fun x => sq_abs x
      calc (∫ ω, |a n ω - b ω| * |b ω| ∂μ) ^ 2
          ≤ (∫ ω, (|a n ω - b ω|) ^ 2 ∂μ) * (∫ ω, (|b ω|) ^ 2 ∂μ) :=
            integral_cauchy_schwarz_sq
              ((hdiff_sq n).congr (ae_of_all _ fun ω => (habs_sq _).symm))
              (hb_sq.congr (ae_of_all _ fun ω => (habs_sq _).symm))
              h_abs_prod
        _ = ε n * C := by
            congr 1 <;> exact integral_congr_ae (ae_of_all _ fun ω => habs_sq _)
    linarith
  -- Squeeze: 0 ≤ ∫‖a²-b²‖ ≤ ε(n) + 2√ε(n)√C → 0
  have h_upper_tends : Tendsto (fun n => ε n + 2 * Real.sqrt (ε n) * Real.sqrt C)
      atTop (nhds 0) := by
    have h_sqrt_ε : Tendsto (fun n => Real.sqrt (ε n)) atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hL2
      rwa [Function.comp_def, Real.sqrt_zero] at this
    have : (0 : ℝ) = 0 + 2 * 0 * Real.sqrt C := by ring
    rw [this]
    exact hL2.add ((h_sqrt_ε.const_mul 2).mul_const _)
  exact squeeze_zero
    (fun n => integral_nonneg fun ω => norm_nonneg _)
    h_upper
    h_upper_tends

/-- L¹ convergence of the diffusion integral:
    ∫ |∫₀ᵗ Hₙ² - ∫₀ᵗ σ²| → 0 from integrand L² convergence.

    Strategy: |∫ Hₙ² - ∫ σ²| ≤ ∫ |Hₙ²-σ²| ≤ ∫(Hₙ-σ)² + 2Mσ·∫|Hₙ-σ|
    ≤ δₙ(ω) + 2Mσ√t·√δₙ(ω) where δₙ = ∫(Hₙ-σ)².
    Then E[δₙ] → 0 and E[√δₙ] ≤ √E[δₙ] → 0 by Jensen. -/
private theorem diffusion_integral_L1_tendsto {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (approx : ℕ → SimpleProcess F)
    (hbdd : ∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 ≤ t)
    (hL2_int : Tendsto
      (fun n => ∫ ω, (∫ s in Icc 0 t,
        (SimpleProcess.valueAtTime (approx n) s ω - X.diffusion s ω) ^ 2 ∂volume) ∂μ)
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ ω,
      ‖(∫ s in Icc 0 t, (SimpleProcess.valueAtTime (approx n) s ω)^2 ∂volume) -
       (∫ s in Icc 0 t, (X.diffusion s ω)^2 ∂volume)‖ ∂μ)
      atTop (nhds 0) := by
  -- Abbreviations
  set H := fun n s ω => SimpleProcess.valueAtTime (approx n) s ω
  set σ := fun s ω => X.diffusion s ω
  set δ := fun n ω => ∫ s in Icc 0 t, (H n s ω - σ s ω) ^ 2 ∂volume
  set ε := fun n => ∫ ω, δ n ω ∂μ
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hMσ_nn : 0 ≤ Mσ := le_trans (abs_nonneg _) (hMσ 0 (Classical.arbitrary Ω))
  -- Pointwise bound: |∫ Hₙ²-σ²| ≤ δₙ(ω) + 2Mσ√t·√δₙ(ω)
  -- Uses |H²-σ²| = |H-σ||H+σ| ≤ |H-σ|(|H-σ|+2Mσ) = (H-σ)² + 2Mσ|H-σ|
  -- Then ∫₀ᵗ |H-σ| ≤ √t · √δ by Cauchy-Schwarz on time integral
  have h_pw : ∀ n ω,
      ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
       (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ≤
      δ n ω + 2 * Mσ * Real.sqrt t * Real.sqrt (δ n ω) := by
    intro n ω
    -- Measurability
    have hσ_meas : Measurable (fun s => σ s ω) :=
      X.diffusion_jointly_measurable.comp (measurable_id.prodMk measurable_const)
    have hH_meas : Measurable (fun s => H n s ω) :=
      (SimpleProcess.valueAtTime_jointly_measurable (approx n)).comp
        (measurable_id.prodMk measurable_const)
    haveI h_fin : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    -- ω-dependent bound on |H|: step function → finitely many values
    obtain ⟨MH, hMH_nn, hMH⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |H n s ω| ≤ M := by
      refine ⟨(∑ j : Fin (approx n).n, |(approx n).values j ω|) + 1,
        add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) one_pos.le, fun s => ?_⟩
      show |SimpleProcess.valueAtTime (approx n) s ω| ≤ _
      unfold SimpleProcess.valueAtTime; split
      · next h =>
        exact le_trans (Finset.single_le_sum (fun j _ => abs_nonneg ((approx n).values j ω))
          (Finset.mem_univ h.choose)) (le_add_of_nonneg_right one_pos.le)
      · simp; exact add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) one_pos.le
    -- Integrability on Icc 0 t (bounded measurable on finite measure set)
    have hH_sq_int : IntegrableOn (fun s => (H n s ω)^2) (Icc 0 t) volume :=
      (integrable_const (MH^2)).mono'
        ((hH_meas.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          calc (H n s ω)^2 = |H n s ω|^2 := (sq_abs _).symm
            _ ≤ MH^2 := pow_le_pow_left₀ (abs_nonneg _) (hMH s) 2)
    have hσ_sq_int : IntegrableOn (fun s => (σ s ω)^2) (Icc 0 t) volume :=
      X.diffusion_sq_time_integrable ω t ht
    have hd_sq_int : IntegrableOn (fun s => (H n s ω - σ s ω)^2) (Icc 0 t) volume :=
      (integrable_const ((MH + Mσ)^2)).mono'
        (((hH_meas.sub hσ_meas).pow_const 2).stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          calc (H n s ω - σ s ω)^2 = |H n s ω - σ s ω|^2 := (sq_abs _).symm
            _ ≤ (MH + Mσ)^2 := by
                apply pow_le_pow_left₀ (abs_nonneg _)
                calc |H n s ω - σ s ω|
                    ≤ |H n s ω| + |σ s ω| := by
                      rw [show H n s ω - σ s ω = H n s ω + (-(σ s ω)) from sub_eq_add_neg _ _]
                      exact (abs_add_le _ _).trans (by rw [abs_neg])
                  _ ≤ MH + Mσ := add_le_add (hMH s) (hMσ s ω))
    -- |H-σ| integrable on Icc 0 t (from (H-σ)² integrable + finite measure, by Cauchy-Schwarz)
    have hd_abs_int : IntegrableOn (fun s => |H n s ω - σ s ω|) (Icc 0 t) volume :=
      (integrable_const (MH + Mσ)).mono'
        ((hH_meas.sub hσ_meas).stronglyMeasurable.aestronglyMeasurable.norm)
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_abs]
          calc |H n s ω - σ s ω|
              ≤ |H n s ω| + |σ s ω| := by
                rw [show H n s ω - σ s ω = H n s ω + (-(σ s ω)) from sub_eq_add_neg _ _]
                exact (abs_add_le _ _).trans (by rw [abs_neg])
            _ ≤ MH + Mσ := add_le_add (hMH s) (hMσ s ω))
    -- Step 1: ‖∫H² - ∫σ²‖ = ‖∫(H²-σ²)‖ ≤ ∫‖H²-σ²‖
    have h_step1 : ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
        (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ≤
        ∫ s in Icc 0 t, ‖(H n s ω)^2 - (σ s ω)^2‖ ∂volume := by
      rw [← integral_sub hH_sq_int hσ_sq_int]
      exact norm_integral_le_integral_norm _
    -- Step 2: ∫‖H²-σ²‖ ≤ ∫(H-σ)² + 2Mσ∫|H-σ| = δ + 2Mσ∫|H-σ|
    have h_step2 : ∫ s in Icc 0 t, ‖(H n s ω)^2 - (σ s ω)^2‖ ∂volume ≤
        δ n ω + 2 * Mσ * ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume := by
      calc ∫ s in Icc 0 t, ‖(H n s ω)^2 - (σ s ω)^2‖ ∂volume
          ≤ ∫ s in Icc 0 t, ((H n s ω - σ s ω)^2 +
            2 * Mσ * |H n s ω - σ s ω|) ∂volume := by
              apply integral_mono_of_nonneg
                (ae_of_all _ fun s => norm_nonneg _)
                (hd_sq_int.add (hd_abs_int.const_mul (2 * Mσ)))
                (ae_of_all _ fun s => by
                  simp only [Pi.add_apply]
                  rw [Real.norm_eq_abs]
                  have h_factor : (H n s ω)^2 - (σ s ω)^2 =
                      (H n s ω - σ s ω) * (H n s ω + σ s ω) := by ring
                  rw [h_factor, abs_mul]
                  have h_bound_sum : |H n s ω + σ s ω| ≤
                      |H n s ω - σ s ω| + 2 * Mσ := by
                    calc |H n s ω + σ s ω|
                        = |(H n s ω - σ s ω) + 2 * σ s ω| := by ring_nf
                      _ ≤ |H n s ω - σ s ω| + |2 * σ s ω| := abs_add_le _ _
                      _ = |H n s ω - σ s ω| + 2 * |σ s ω| := by
                          rw [abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0)]
                      _ ≤ |H n s ω - σ s ω| + 2 * Mσ := by linarith [hMσ s ω]
                  calc |H n s ω - σ s ω| * |H n s ω + σ s ω|
                      ≤ |H n s ω - σ s ω| * (|H n s ω - σ s ω| + 2 * Mσ) :=
                        mul_le_mul_of_nonneg_left h_bound_sum (abs_nonneg _)
                    _ = |H n s ω - σ s ω| ^ 2 + 2 * Mσ * |H n s ω - σ s ω| := by ring
                    _ = (H n s ω - σ s ω) ^ 2 + 2 * Mσ * |H n s ω - σ s ω| := by
                        rw [sq_abs])
        _ = δ n ω + 2 * Mσ * ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume := by
            rw [integral_add hd_sq_int (hd_abs_int.const_mul _), integral_const_mul]
    -- Step 3: Cauchy-Schwarz on time integral: ∫|H-σ| ≤ √t · √δ
    have h_step3 : ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume ≤
        Real.sqrt t * Real.sqrt (δ n ω) := by
      have h_nn : 0 ≤ ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume :=
        integral_nonneg_of_ae (ae_of_all _ fun s => abs_nonneg _)
      suffices hsq : (∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume) ^ 2 ≤
          t * δ n ω by
        calc ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume
            = Real.sqrt ((∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume) ^ 2) :=
              (Real.sqrt_sq h_nn).symm
          _ ≤ Real.sqrt (t * δ n ω) := Real.sqrt_le_sqrt hsq
          _ = Real.sqrt t * Real.sqrt (δ n ω) := Real.sqrt_mul ht _
      -- CS: (∫|f|·1)² ≤ (∫|f|²)(∫1²) = (∫f²)(∫1) = δ·t
      have h_one_sq : ∫ s in Icc 0 t, (1:ℝ)^2 ∂volume = t := by
        simp [one_pow, integral_const]; linarith
      -- Apply CS with f = |H-σ|, g = 1
      have hcs := @integral_cauchy_schwarz_sq _ _ (volume.restrict (Icc (0:ℝ) t))
        (fun s => |H n s ω - σ s ω|) (fun _ => (1:ℝ))
        (hd_sq_int.congr (ae_of_all _ fun s => (sq_abs _).symm))
        (integrable_const _)
        (hd_abs_int.congr (ae_of_all _ fun s => (mul_one _).symm))
      -- hcs: (∫ |H-σ|·1)² ≤ (∫ |H-σ|²)(∫ 1²)
      -- Convert: |H-σ|·1 = |H-σ|, |H-σ|² = (H-σ)², 1² = t
      have hmul : ∫ s in Icc 0 t, |H n s ω - σ s ω| * (1:ℝ) ∂volume =
          ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume :=
        integral_congr_ae (ae_of_all _ fun s => mul_one _)
      have habs_sq : ∫ s in Icc 0 t, |H n s ω - σ s ω| ^ 2 ∂volume = δ n ω :=
        integral_congr_ae (ae_of_all _ fun s => sq_abs _)
      rw [hmul, habs_sq, h_one_sq] at hcs
      linarith
    have h_mul : 2 * Mσ * ∫ s in Icc 0 t, |H n s ω - σ s ω| ∂volume ≤
        2 * Mσ * (Real.sqrt t * Real.sqrt (δ n ω)) :=
      mul_le_mul_of_nonneg_left h_step3 (by positivity)
    linarith
  -- Upper bound: E[‖...‖] ≤ ε(n) + 2Mσ√t·√ε(n)
  -- Uses Jensen: E[√δ] ≤ √(E[δ]) = √ε for probability measure
  have h_upper : ∀ n, ∫ ω,
      ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
       (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ∂μ ≤
      ε n + 2 * Mσ * Real.sqrt t * Real.sqrt (ε n) := by
    intro n
    -- Uniform bound on H_n
    obtain ⟨CH, hCH_nn, hCH⟩ :=
      SimpleProcess.valueAtTime_uniform_bounded (approx n) (hbdd n)
    -- δ non-negative and bounded
    have hδ_nn : ∀ ω, 0 ≤ δ n ω := fun ω => integral_nonneg fun s => sq_nonneg _
    haveI h_fin_icc : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have hδ_bound : ∀ ω, δ n ω ≤ (CH + Mσ) ^ 2 * t := by
      intro ω
      calc δ n ω
          ≤ ∫ s in Icc 0 t, (CH + Mσ) ^ 2 ∂volume := by
            apply integral_mono_of_nonneg (ae_of_all _ fun s => sq_nonneg _)
              (integrable_const _)
              (ae_of_all _ fun s => by
                calc (H n s ω - σ s ω) ^ 2 = |H n s ω - σ s ω| ^ 2 := (sq_abs _).symm
                  _ ≤ (CH + Mσ) ^ 2 := by
                      apply pow_le_pow_left₀ (abs_nonneg _)
                      exact (abs_sub _ _).trans (add_le_add (hCH s ω) (hMσ s ω)))
        _ = (CH + Mσ) ^ 2 * t := by
            rw [integral_const, smul_eq_mul, mul_comm]
            congr 1
            rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
              ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ t - 0), sub_zero]
    -- δ strongly measurable (via parametric integral of jointly measurable function)
    have hd_sq_sm : StronglyMeasurable
        (fun p : Ω × ℝ => (H n p.2 p.1 - σ p.2 p.1) ^ 2) :=
      (((SimpleProcess.valueAtTime_jointly_measurable (approx n)).comp
          measurable_swap).sub
        (X.diffusion_jointly_measurable.comp measurable_swap)).pow_const 2
      |>.stronglyMeasurable
    have hδ_sm : StronglyMeasurable (δ n) :=
      hd_sq_sm.integral_prod_right' (ν := volume.restrict (Icc (0:ℝ) t))
    -- δ integrable (bounded on probability space)
    have hδ_int : Integrable (δ n) μ :=
      (integrable_const ((CH + Mσ) ^ 2 * t)).mono' hδ_sm.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hδ_nn ω)]; exact hδ_bound ω)
    -- √δ measurable and integrable
    have hsqrtδ_sm : StronglyMeasurable (fun ω => Real.sqrt (δ n ω)) :=
      Real.continuous_sqrt.comp_stronglyMeasurable hδ_sm
    have hsqrtδ_int : Integrable (fun ω => Real.sqrt (δ n ω)) μ :=
      (integrable_const ((CH + Mσ) * Real.sqrt t)).mono' hsqrtδ_sm.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          calc Real.sqrt (δ n ω) ≤ Real.sqrt ((CH + Mσ) ^ 2 * t) :=
                Real.sqrt_le_sqrt (hδ_bound ω)
            _ = (CH + Mσ) * Real.sqrt t := by
                rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)])
    -- Step 1: ∫‖...‖ ≤ E[δ] + 2Mσ√t·E[√δ]
    have h_int_bound : ∫ ω, ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
        (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ∂μ ≤
        ε n + 2 * Mσ * Real.sqrt t * ∫ ω, Real.sqrt (δ n ω) ∂μ := by
      calc ∫ ω, ‖(∫ s in Icc 0 t, (H n s ω)^2 ∂volume) -
              (∫ s in Icc 0 t, (σ s ω)^2 ∂volume)‖ ∂μ
          ≤ ∫ ω, (δ n ω + 2 * Mσ * Real.sqrt t * Real.sqrt (δ n ω)) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => norm_nonneg _)
              (hδ_int.add (hsqrtδ_int.const_mul (2 * Mσ * Real.sqrt t)))
              (ae_of_all _ fun ω => h_pw n ω)
        _ = ε n + 2 * Mσ * Real.sqrt t * ∫ ω, Real.sqrt (δ n ω) ∂μ := by
            rw [integral_add hδ_int (hsqrtδ_int.const_mul _), integral_const_mul]
    -- Step 2: E[√δ] ≤ √ε by Jensen (via CS: (∫√δ)² ≤ ∫δ = ε)
    have h_jensen : ∫ ω, Real.sqrt (δ n ω) ∂μ ≤ Real.sqrt (ε n) := by
      have h_nn_int : 0 ≤ ∫ ω, Real.sqrt (δ n ω) ∂μ :=
        integral_nonneg fun ω => Real.sqrt_nonneg _
      suffices hsq : (∫ ω, Real.sqrt (δ n ω) ∂μ) ^ 2 ≤ ε n by
        calc ∫ ω, Real.sqrt (δ n ω) ∂μ
            = Real.sqrt ((∫ ω, Real.sqrt (δ n ω) ∂μ) ^ 2) :=
              (Real.sqrt_sq h_nn_int).symm
          _ ≤ Real.sqrt (ε n) := Real.sqrt_le_sqrt hsq
      -- Use sq_integral_abs_le_integral_sq with g = √δ
      -- (∫|√δ|)² ≤ ∫(√δ)² = ∫δ = ε
      have h_sq_sqrt_eq : ∀ ω, Real.sqrt (δ n ω) ^ 2 = δ n ω :=
        fun ω => Real.sq_sqrt (hδ_nn ω)
      have hcs := sq_integral_abs_le_integral_sq hsqrtδ_int
        (hδ_int.congr (ae_of_all _ fun ω => (h_sq_sqrt_eq ω).symm))
      -- hcs: (∫|√δ|)² ≤ ∫(√δ)²
      -- Convert: |√δ| = √δ (non-negative), (√δ)² = δ
      have h_abs_sqrt : ∫ ω, |Real.sqrt (δ n ω)| ∂μ = ∫ ω, Real.sqrt (δ n ω) ∂μ :=
        integral_congr_ae (ae_of_all _ fun ω => abs_of_nonneg (Real.sqrt_nonneg _))
      have h_sq_eq : ∫ ω, Real.sqrt (δ n ω) ^ 2 ∂μ = ε n :=
        integral_congr_ae (ae_of_all _ fun ω => h_sq_sqrt_eq ω)
      rw [h_abs_sqrt, h_sq_eq] at hcs; exact hcs
    have h_mul : 2 * Mσ * Real.sqrt t * ∫ ω, Real.sqrt (δ n ω) ∂μ ≤
        2 * Mσ * Real.sqrt t * Real.sqrt (ε n) :=
      mul_le_mul_of_nonneg_left h_jensen (by positivity)
    linarith
  -- Squeeze to 0
  have h_upper_tends : Tendsto (fun n => ε n + 2 * Mσ * Real.sqrt t * Real.sqrt (ε n))
      atTop (nhds 0) := by
    have h_sqrt_ε : Tendsto (fun n => Real.sqrt (ε n)) atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hL2_int
      rwa [Function.comp_def, Real.sqrt_zero] at this
    have : (0 : ℝ) = 0 + 2 * Mσ * Real.sqrt t * 0 := by ring
    rw [this]
    exact hL2_int.add (h_sqrt_ε.const_mul _)
  exact squeeze_zero
    (fun n => integral_nonneg fun ω => norm_nonneg _)
    h_upper
    h_upper_tends

/-! ## Simple process integrability infrastructure -/

/-- The time integral of a simple process squared is integrable on [0,t].
    Uses the finite sum decomposition from `valueAtTime_sq_integral_eq_sum`. -/
private lemma simple_process_sq_integral_integrable {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => ∫ s in Set.Icc 0 t, (H.valueAtTime s ω) ^ 2 ∂volume) μ := by
  -- Rewrite using the finite sum decomposition
  have h_eq : (fun ω => ∫ s in Set.Icc 0 t, (H.valueAtTime s ω) ^ 2 ∂volume) =
      (fun ω => ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
        (H.values i ω) ^ 2 * (min (H.times ⟨i + 1, h⟩) t - min (H.times i) t)
      else 0) := by
    ext ω; exact SimpleProcess.valueAtTime_sq_integral_eq_sum H hH_times_nn t ht ω
  rw [h_eq]
  apply integrable_finset_sum _ fun i _ => ?_
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    have h_meas : Measurable (H.values i) :=
      (hH_adapted i).mono (W.F.le_ambient _) le_rfl
    obtain ⟨Ci, hCi⟩ := hH_bdd i
    exact ((integrable_const (Ci ^ 2 * |min (H.times ⟨i + 1, hi⟩) t - min (H.times i) t|)).mono'
      ((h_meas.pow_const 2).aestronglyMeasurable.mul_const _)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (by rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hCi ω) 2)
          (abs_nonneg _)))
  · simp only [dif_neg hi]; exact integrable_zero _ _ _

/-- The time integral of a simple process squared is integrable on [s,t]. -/
private lemma simple_process_sq_interval_integrable {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => ∫ u in Set.Icc s t,
      (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) μ := by
  have ht := le_trans hs hst
  -- Express ∫_{s}^{t} = ∫₀^{t} - ∫₀^{s} using setIntegral_Icc_split'
  have h_split : (fun ω => ∫ u in Set.Icc s t,
      (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) =
      (fun ω => ∫ u in Set.Icc 0 t,
        (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) -
      (fun ω => ∫ u in Set.Icc 0 s,
        (SimpleProcess.valueAtTime H u ω) ^ 2 ∂volume) := by
    ext ω; simp only [Pi.sub_apply]
    obtain ⟨C, hC_nn, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded H hH_bdd
    have h_time_int : IntegrableOn (fun u => (H.valueAtTime u ω) ^ 2)
        (Set.Icc 0 t) volume := by
      haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) t)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
      have h_val_meas : Measurable (fun u => H.valueAtTime u ω) :=
        (SimpleProcess.valueAtTime_jointly_measurable H).comp
          (measurable_id.prodMk measurable_const)
      exact (integrable_const (C ^ 2)).mono'
        ((h_val_meas.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun u => by
          have hnn : (0 : ℝ) ≤ (H.valueAtTime u ω) ^ 2 := sq_nonneg _
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          calc (H.valueAtTime u ω) ^ 2
              = |H.valueAtTime u ω| ^ 2 := (sq_abs _).symm
            _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC u ω) 2)
    linarith [setIntegral_Icc_split' hs hst h_time_int]
  rw [h_split]
  exact (simple_process_sq_integral_integrable H W hH_adapted hH_bdd hH_times_nn t ht).sub
    (simple_process_sq_integral_integrable H W hH_adapted hH_bdd hH_times_nn s hs)

/-- SI²(t) is integrable for simple processes. -/
private lemma simple_stochasticIntegral_at_sq_integrable {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (H.stochasticIntegral_at W t ω) ^ 2) μ := by
  have h := SimpleProcess.stochasticIntegral_at_sub_sq_integrable H W hH_adapted hH_bdd hH_times_nn
    (fun _ => 0) (integrable_const 0)
    ((integrable_zero _ _ _).congr (ae_of_all _ fun _ => (zero_pow two_ne_zero).symm)) t ht
  simp only [sub_zero] at h; exact h

/-! ## Simple process filtration measurability -/

/-- Simple stochastic integrals at time s are measurable w.r.t. the filtration at time s.
    This is a local copy of the proof from `ItoFormulaDecomposition.lean` to avoid circular imports. -/
private lemma si_at_filt_meas {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (_ : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s : ℝ) (_ : 0 ≤ s) :
    @Measurable Ω ℝ (W.F.σ_algebra s) _ (H.stochasticIntegral_at W s) := by
  have heq : H.stochasticIntegral_at W s = fun ω =>
      ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
        H.values i ω * (W.process (min (H.times ⟨i + 1, h⟩) s) ω -
                         W.process (min (H.times i) s) ω)
      else 0 := by
    ext ω; exact H.stochasticIntegral_at_eq_min W s ω
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    by_cases hts : H.times i ≤ s
    · exact ((hH_adapted i).mono (W.F.mono _ _ hts) le_rfl).mul
        (((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_right _ _)) le_rfl).sub
         ((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_right _ _)) le_rfl))
    · push_neg at hts
      have h1 : min (H.times i) s = s := min_eq_right (le_of_lt hts)
      have h2 : min (H.times ⟨i + 1, hi⟩) s = s :=
        min_eq_right (le_trans (le_of_lt hts)
          (le_of_lt (H.increasing i ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))))
      have : (fun ω => H.values i ω * (W.process (min (H.times ⟨i + 1, hi⟩) s) ω -
                         W.process (min (H.times i) s) ω)) = fun _ => 0 := by
        ext ω; rw [h1, h2, sub_self, mul_zero]
      rw [this]; exact measurable_const
  · simp only [dif_neg hi]; exact measurable_const

/-! ## Algebraic identity: 4-point → 2-point for clamped BM endpoints -/

/-- For s ≤ t, the 4-point BM expression W(min b t) - W(min a t) - W(min b s) + W(min a s)
    simplifies to W(min(max b s) t) - W(min(max a s) t), i.e., a 2-point expression with
    clamped endpoints. This is the key algebraic identity for the conditional Itô isometry. -/
private lemma four_point_to_two_point
    (f : ℝ → ℝ) (a b s t : ℝ) (hab : a ≤ b) (hst : s ≤ t) :
    (f (min b t) - f (min a t)) - (f (min b s) - f (min a s)) =
    f (min (max b s) t) - f (min (max a s) t) := by
  -- Case analysis on relative position of a, b vs s, t
  by_cases hbs : b ≤ s
  · -- Both a, b ≤ s: LHS = (f b - f a) - (f b - f a) = 0
    have has : a ≤ s := le_trans hab hbs
    rw [min_eq_left (le_trans hbs hst), min_eq_left (le_trans has hst),
        min_eq_left hbs, min_eq_left has,
        max_eq_right hbs, max_eq_right has, min_eq_left hst]
    ring
  · push_neg at hbs -- s < b
    by_cases has : a ≤ s
    · -- a ≤ s < b: "straddling" case
      rw [min_eq_left has, max_eq_right has, min_eq_left hst,
          min_eq_right (le_of_lt hbs), max_eq_left (le_of_lt hbs)]
      by_cases hbt : b ≤ t
      · rw [min_eq_left hbt, min_eq_left (le_trans has hst)]
        ring
      · push_neg at hbt
        rw [min_eq_right (le_of_lt hbt), min_eq_left (le_trans has hst)]
        ring
    · -- s < a ≤ b: both a, b > s
      push_neg at has
      rw [max_eq_left (le_of_lt has), max_eq_left (le_of_lt hbs),
          min_eq_right (le_of_lt has), min_eq_right (le_of_lt hbs)]
      ring

/-- The clamped lower endpoint is ≤ the clamped upper endpoint. -/
private lemma clamp_le_clamp (a b s t : ℝ) (hab : a ≤ b) (_ : s ≤ t) :
    min (max a s) t ≤ min (max b s) t :=
  min_le_min_right t (max_le_max_right s hab)

/-- The clamped endpoint is ≥ s. -/
private lemma clamp_ge_lo (a s t : ℝ) (hst : s ≤ t) :
    s ≤ min (max a s) t :=
  le_min (le_max_right a s) hst

/-- The clamped endpoint is ≤ t. -/
private lemma clamp_le_hi (a s t : ℝ) :
    min (max a s) t ≤ t :=
  min_le_right _ t

/-- When max(a, s) ≤ t, a ≤ clamp(a, s, t). -/
private lemma clamp_ge_arg (a s t : ℝ) (h : max a s ≤ t) :
    a ≤ min (max a s) t :=
  le_min (le_max_left a s) (le_trans (le_max_left a s) h)

/-- Clamped endpoints from consecutive partition points are ordered:
    for i < j, clamp(t_{i+1}, s, t) ≤ clamp(t_j, s, t). -/
private lemma clamp_partition_ordered {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (s t : ℝ)
    (i j : Fin H.n) (hi : (i : ℕ) + 1 < H.n) (hij : (i : ℕ) < (j : ℕ)) :
    min (max (H.times ⟨(i : ℕ) + 1, hi⟩) s) t ≤ min (max (H.times j) s) t := by
  apply min_le_min_right
  apply max_le_max_right
  have hij1 : (⟨(i : ℕ) + 1, hi⟩ : Fin H.n) ≤ j := by
    rw [Fin.le_def]; exact Nat.succ_le_of_lt hij
  rcases hij1.eq_or_lt with h | h
  · exact le_of_eq (congrArg H.times h)
  · exact le_of_lt (H.increasing ⟨(i : ℕ) + 1, hi⟩ j h)

/-! ## QV sum identity for intervals [s, t] -/

/-- The quadratic variation ∫_{[s,t]} H²(u,ω) du equals a sum of clamped interval contributions.
    Each term is H_i(ω)² × (clamp(t_{i+1},s,t) - clamp(t_i,s,t)). -/
private lemma simple_QV_eq_clamped_sum {F : Filtration Ω ℝ}
    (H : SimpleProcess F)
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |(H.values i ω)| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    ∫ u in Set.Icc s t, (H.valueAtTime u ω) ^ 2 ∂volume =
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      (H.values i ω) ^ 2 * (min (max (H.times ⟨(i : ℕ) + 1, h⟩) s) t -
                              min (max (H.times i) s) t)
    else 0 := by
  have ht : 0 ≤ t := le_trans hs hst
  -- Step 1: Integrability of valueAtTime² on [0,t]
  obtain ⟨C, _, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded H hH_bdd
  have hf_intOn : IntegrableOn (fun u => (H.valueAtTime u ω) ^ 2) (Set.Icc 0 t) volume := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have h_val_meas : Measurable (fun u => H.valueAtTime u ω) :=
      (SimpleProcess.valueAtTime_jointly_measurable H).comp
        (measurable_id.prodMk measurable_const)
    exact (integrable_const (C ^ 2)).mono'
      ((h_val_meas.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        calc (H.valueAtTime u ω) ^ 2
            = |H.valueAtTime u ω| ^ 2 := (sq_abs _).symm
          _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC u ω) 2)
  -- Step 2: Splitting ∫_{[0,t]} = ∫_{[0,s]} + ∫_{[s,t]}
  have hsplit := setIntegral_Icc_split' hs hst hf_intOn
  -- Step 3: Apply sum formula for [0,t] and [0,s]
  have h_t := SimpleProcess.valueAtTime_sq_integral_eq_sum H hH_times_nn t ht ω
  have h_s := SimpleProcess.valueAtTime_sq_integral_eq_sum H hH_times_nn s hs ω
  -- Step 4: QV = ∫_{[0,t]} - ∫_{[0,s]}
  have hQV_diff : ∫ u in Set.Icc s t, (H.valueAtTime u ω) ^ 2 ∂volume =
      ∫ u in Set.Icc 0 t, (H.valueAtTime u ω) ^ 2 ∂volume -
      ∫ u in Set.Icc 0 s, (H.valueAtTime u ω) ^ 2 ∂volume := by linarith
  rw [hQV_diff, h_t, h_s, ← Finset.sum_sub_distrib]
  congr 1; ext i
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi, ← mul_sub]
    congr 1
    -- Apply four_point_to_two_point with f = id
    have := four_point_to_two_point id (H.times i) (H.times ⟨(i : ℕ) + 1, hi⟩) s t
      (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by simp [Fin.lt_def]))) hst
    simp only [id] at this
    linarith
  · simp only [dif_neg hi, sub_self]

/-! ## Set-integral Pythagoras -/

/-- Set-integral Pythagoras: ∫_A (Σ aᵢ)² = Σ ∫_A aᵢ² when set-integral cross terms vanish.
    Proved via indicator trick reducing to the full-integral Pythagoras. -/
private theorem set_sum_sq_integral_eq {n : ℕ}
    (a : Fin n → Ω → ℝ) {A : Set Ω} (hA : MeasurableSet A)
    (h_cross_int_on : ∀ i j : Fin n, IntegrableOn (fun ω => a i ω * a j ω) A μ)
    (h_orthog : ∀ i j : Fin n, i ≠ j → ∫ ω in A, a i ω * a j ω ∂μ = 0) :
    ∫ ω in A, (∑ i : Fin n, a i ω) ^ 2 ∂μ =
    ∑ i : Fin n, ∫ ω in A, (a i ω) ^ 2 ∂μ := by
  -- Indicator trick: define a'_i = 1_A · a_i
  set a' : Fin n → Ω → ℝ := fun i => A.indicator (a i) with ha'_def
  -- Key pointwise identity: indicator product = indicator of product
  have h_ind_mul : ∀ i j, ∀ ω,
      a' i ω * a' j ω = A.indicator (fun ω => a i ω * a j ω) ω := by
    intro i j ω; simp only [ha'_def, Set.indicator]
    split_ifs <;> simp
  -- Cross-product integrability
  have h_cross_int : ∀ i j : Fin n, Integrable (fun ω => a' i ω * a' j ω) μ := by
    intro i j
    have hrw : (fun ω => a' i ω * a' j ω) = A.indicator (fun ω => a i ω * a j ω) := by
      ext ω; exact h_ind_mul i j ω
    rw [hrw, integrable_indicator_iff hA]; exact h_cross_int_on i j
  -- Cross-term vanishing
  have h_orthog' : ∀ i j : Fin n, i ≠ j → ∫ ω, a' i ω * a' j ω ∂μ = 0 := by
    intro i j hij; simp_rw [h_ind_mul i j, integral_indicator hA]
    exact h_orthog i j hij
  -- Apply full-integral Pythagoras
  have hpyth := SPDE.Probability.sum_sq_integral_eq_sum_integral_sq a' h_cross_int h_orthog'
  -- Convert LHS: ∫ (Σ a'_i)² = ∫_A (Σ a_i)²
  have h_sum_ind : ∀ ω, ∑ i, a' i ω = A.indicator (fun ω => ∑ i, a i ω) ω := by
    intro ω; simp only [ha'_def, Set.indicator]
    split_ifs <;> simp
  have h_sq_ind : ∀ ω, (A.indicator (fun ω => ∑ i, a i ω) ω) ^ 2 =
      A.indicator (fun ω => (∑ i, a i ω) ^ 2) ω := by
    intro ω; simp only [Set.indicator]; split_ifs <;> simp
  simp_rw [h_sum_ind, h_sq_ind, integral_indicator hA] at hpyth
  -- Convert RHS: Σ ∫ (a'_i)² = Σ ∫_A a_i²
  have h_sq_ind' : ∀ i, ∀ ω, (a' i ω) ^ 2 = A.indicator (fun ω => (a i ω) ^ 2) ω := by
    intro i ω; simp only [ha'_def, Set.indicator]; split_ifs <;> simp
  have hRHS : ∑ i : Fin n, ∫ ω, (a' i ω) ^ 2 ∂μ = ∑ i : Fin n, ∫ ω in A, (a i ω) ^ 2 ∂μ := by
    congr 1; ext i; simp_rw [h_sq_ind' i, integral_indicator hA]
  rw [hRHS] at hpyth; exact hpyth

/-! ## Helper lemmas for compensated square proof -/

/-- The compensated BM square increment has zero set-integral:
    ∫_B [(W_b - W_a)² - (b-a)] = 0 for B ∈ F_a.
    This follows from the variance factorization on sets. -/
private lemma setIntegral_bm_compensated_sq_zero (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (B : Set Ω) (hB : @MeasurableSet Ω (W.F.σ_algebra a) B) :
    ∫ ω in B, ((W.process b ω - W.process a ω) ^ 2 - (b - a)) ∂μ = 0 := by
  show ∫ ω in B, ((W.toAdapted.process b ω - W.toAdapted.process a ω) ^ 2 - (b - a)) ∂μ = 0
  have hincr_sq_int := W.increment_sq_integrable a b ha hab
  have hvar := W.increment_variance a b ha hab
  have hindep := W.independent_increments a b ha hab
  have hincr_meas : Measurable (fun ω => W.toAdapted.process b ω - W.toAdapted.process a ω) :=
    ((W.toAdapted.adapted b).mono (W.F.le_ambient b) le_rfl).sub
      ((W.toAdapted.adapted a).mono (W.F.le_ambient a) le_rfl)
  haveI : SigmaFinite (μ.trim (W.F.le_ambient a)) := inferInstance
  rw [integral_sub hincr_sq_int.integrableOn (integrable_const _).integrableOn,
      Probability.setIntegral_sq_of_indep_eq_measure_mul_integral
        (W.F.le_ambient a) hincr_meas hincr_sq_int hindep B hB,
      setIntegral_const, smul_eq_mul, hvar, Measure.real]
  ring

/-- Each summand of `stochasticIntegral_at` equals the min-capped form:
    H_i · (W(min(t_{i+1}, t)) - W(min(t_i, t))). -/
private lemma si_at_summand_eq_min {F : Filtration Ω ℝ} (H : SimpleProcess F)
    (W : BrownianMotion Ω μ) (t : ℝ) (i : Fin H.n) (h : (i : ℕ) + 1 < H.n) (ω : Ω) :
    (if H.times ⟨(i : ℕ) + 1, h⟩ ≤ t then
      H.values i ω * (W.process (H.times ⟨(i : ℕ) + 1, h⟩) ω - W.process (H.times i) ω)
    else if H.times i ≤ t then
      H.values i ω * (W.process t ω - W.process (H.times i) ω)
    else 0) =
    H.values i ω * (W.process (min (H.times ⟨(i : ℕ) + 1, h⟩) t) ω -
                     W.process (min (H.times i) t) ω) := by
  by_cases h1 : H.times ⟨(i : ℕ) + 1, h⟩ ≤ t
  · -- Case 1: t_{i+1} ≤ t (full interval)
    have h_i_lt : i < (⟨(i : ℕ) + 1, h⟩ : Fin H.n) := by
      show i.val < (⟨(i : ℕ) + 1, h⟩ : Fin H.n).val; simp
    have h2 : H.times i ≤ t := le_trans (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, h⟩
        h_i_lt)) h1
    rw [if_pos h1, min_eq_left h1, min_eq_left h2]
  · push_neg at h1
    by_cases h2 : H.times i ≤ t
    · -- Case 2: t_i ≤ t < t_{i+1} (partial interval)
      rw [if_neg (not_le.mpr h1), if_pos h2, min_eq_right (le_of_lt h1), min_eq_left h2]
    · -- Case 3: t < t_i (no contribution)
      push_neg at h2
      rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2),
          min_eq_right (le_of_lt h1), min_eq_right (le_of_lt h2)]
      simp

/-- The difference SI(t₂) - SI(s₂) equals a sum of clamped BM increment terms. -/
private lemma si_at_diff_eq_clamped_sum {F : Filtration Ω ℝ} (H : SimpleProcess F)
    (W : BrownianMotion Ω μ) (s t : ℝ) (hst : s ≤ t) (ω : Ω) :
    H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω =
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      H.values i ω * (W.process (min (max (H.times ⟨(i : ℕ) + 1, h⟩) s) t) ω -
                       W.process (min (max (H.times i) s) t) ω)
    else 0 := by
  simp only [SimpleProcess.stochasticIntegral_at, ← Finset.sum_sub_distrib]
  congr 1; ext i
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    rw [si_at_summand_eq_min H W t i hi ω, si_at_summand_eq_min H W s i hi ω, ← mul_sub]
    congr 1
    have h_ab : H.times i ≤ H.times ⟨(i : ℕ) + 1, hi⟩ :=
      le_of_lt (H.increasing i ⟨(i : ℕ) + 1, hi⟩ (by show i.val < _; simp))
    have := four_point_to_two_point (fun r => W.process r ω)
      (H.times i) (H.times ⟨(i : ℕ) + 1, hi⟩) s t h_ab hst
    linarith
  · simp [dif_neg hi]

/-! ## Simple process compensated square set-integral -/

/-- For a simple process H, the compensated square set-integral vanishes:
    ∫_A [SI_H(t₂)² - SI_H(s₂)² - ∫_{s₂}^{t₂} H²] = 0 for A ∈ F_{s₂}.

    This is the simple process version of the conditional Itô isometry.
    The proof uses:
    1. Cross-term vanishing: ∫_A SI(s₂)·(SI(t₂)-SI(s₂)) = 0
       (from `stochasticIntegral_at_martingale`)
    2. BM compensated square: ∫_A [(ΔW)²-Δτ] = 0
       (from independence of BM increments)
    3. Expansion of (SI(t₂)-SI(s₂))² into diagonal + cross terms -/
theorem simple_compensated_sq_setIntegral_zero {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |(H.values i ω)| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s₂ t₂ : ℝ) (hs₂ : 0 ≤ s₂) (hst₂ : s₂ ≤ t₂)
    (A : Set Ω) (hA : @MeasurableSet Ω (W.F.σ_algebra s₂) A) :
    ∫ ω in A, ((H.stochasticIntegral_at W t₂ ω)^2 -
               (H.stochasticIntegral_at W s₂ ω)^2 -
               ∫ u in Icc s₂ t₂, (H.valueAtTime u ω)^2 ∂volume) ∂μ = 0 := by
  -- Abbreviations
  set SI := H.stochasticIntegral_at W
  set QV : Ω → ℝ := fun ω => ∫ u in Icc s₂ t₂, (H.valueAtTime u ω)^2 ∂volume
  have ht₂ : 0 ≤ t₂ := le_trans hs₂ hst₂
  -- Filtration measurability
  have hSI_filt : ∀ τ, 0 ≤ τ → @Measurable Ω ℝ (W.F.σ_algebra τ) _ (SI τ) :=
    fun τ hτ => si_at_filt_meas H W hH_adapted hH_times_nn τ hτ
  -- Integrability of SI(t) for simple processes
  have hSI_sq_int : ∀ τ, 0 ≤ τ → Integrable (fun ω => (SI τ ω) ^ 2) μ := fun τ hτ =>
    simple_stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn τ hτ
  have hSI_int : ∀ τ, 0 ≤ τ → Integrable (SI τ) μ := by
    intro τ hτ
    have hasm : AEStronglyMeasurable (SI τ) μ :=
      ((hSI_filt τ hτ).mono (W.F.le_ambient τ) le_rfl).stronglyMeasurable.aestronglyMeasurable
    exact ((hSI_sq_int τ hτ).add (integrable_const 1)).mono' hasm
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs, Pi.add_apply]
        nlinarith [sq_abs (SI τ ω), abs_nonneg (SI τ ω)])
  have hQV_int : Integrable QV μ :=
    simple_process_sq_interval_integrable H W hH_adapted hH_bdd hH_times_nn s₂ t₂ hs₂ hst₂
  -- SI(s₂) is F_{s₂}-measurable
  have hSI_s₂_meas : @Measurable Ω ℝ (W.F.σ_algebra s₂) _ (SI s₂) := hSI_filt s₂ hs₂
  -- === PART A: Cross-term vanishing ===
  -- ∫_A SI(s₂)·(SI(t₂)-SI(s₂)) = 0
  have h_cross : ∫ ω in A, SI s₂ ω * (SI t₂ ω - SI s₂ ω) ∂μ = 0 := by
    -- Use indicator trick: ∫_A f·g = ∫ (1_A·f)·g
    rw [← integral_indicator (W.F.le_ambient s₂ A hA)]
    simp_rw [Set.indicator_mul_left]
    apply integral_mul_eq_zero_of_setIntegral_eq_zero' (W.F.le_ambient s₂)
    · -- 1_A · SI(s₂) is F_{s₂}-measurable
      exact hSI_s₂_meas.indicator hA
    · -- SI(t₂) - SI(s₂) is integrable
      exact (hSI_int t₂ ht₂).sub (hSI_int s₂ hs₂)
    · -- Product integrability: (1_A·SI(s₂))·(SI(t₂)-SI(s₂)) is integrable
      -- Use AM-GM: |ab| ≤ a²+b²
      apply Integrable.mono' ((hSI_sq_int s₂ hs₂).add
        ((hSI_sq_int t₂ ht₂).add (hSI_sq_int s₂ hs₂)))
      · exact ((hSI_int s₂ hs₂).indicator
          (W.F.le_ambient s₂ A hA)).aestronglyMeasurable.mul
          ((hSI_int t₂ ht₂).sub (hSI_int s₂ hs₂)).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Pi.add_apply, Real.norm_eq_abs]
        by_cases hω : ω ∈ A
        · simp only [Set.indicator_of_mem hω]
          rw [abs_mul]
          set a := |SI s₂ ω|
          set b := |SI t₂ ω - SI s₂ ω|
          nlinarith [sq_nonneg (a - b), sq_abs (SI s₂ ω),
            sq_abs (SI t₂ ω - SI s₂ ω), sq_abs (SI t₂ ω)]
        · simp only [Set.indicator_of_notMem hω, zero_mul, abs_zero]
          positivity
    · -- ∀ B ∈ F_{s₂}, ∫_B (SI(t₂)-SI(s₂)) = 0
      intro B hB
      have h_mart := SimpleProcess.stochasticIntegral_at_martingale H W hH_adapted hH_bdd
        hH_times_nn s₂ t₂ hs₂ hst₂ B hB
      have h_split : ∫ ω in B, (SI t₂ ω - SI s₂ ω) ∂μ =
          ∫ ω in B, SI t₂ ω ∂μ - ∫ ω in B, SI s₂ ω ∂μ :=
        integral_sub (hSI_int t₂ ht₂).integrableOn (hSI_int s₂ hs₂).integrableOn
      linarith
  -- === PART B: Set-integral isometry for increment ===
  -- ∫_A [(SI(t₂)-SI(s₂))² - QV] = 0
  -- This is the hard part: uses BM increment simplification, Pythagoras on sets,
  -- and set-integral compensated square computation.
  have h_iso : ∫ ω in A, ((SI t₂ ω - SI s₂ ω) ^ 2 - QV ω) ∂μ = 0 := by
    -- === Setup: clamped summands ===
    set τ : Fin H.n → ℝ := fun i => min (max (H.times i) s₂) t₂
    set d : Fin H.n → Ω → ℝ := fun i ω =>
      if h : (i : ℕ) + 1 < H.n then
        H.values i ω * (W.process (τ ⟨(i:ℕ)+1, h⟩) ω - W.process (τ i) ω)
      else 0
    -- Clamped time properties
    have hτ_ge_s₂ : ∀ i, s₂ ≤ τ i := fun i => clamp_ge_lo _ s₂ t₂ hst₂
    have hτ_nn : ∀ i, 0 ≤ τ i := fun i => le_trans hs₂ (hτ_ge_s₂ i)
    have hτ_mono : ∀ (i : Fin H.n) (h : (i:ℕ)+1 < H.n), τ i ≤ τ ⟨(i:ℕ)+1, h⟩ := fun i h =>
      clamp_le_clamp _ _ s₂ t₂
        (le_of_lt (H.increasing i ⟨(i:ℕ)+1, h⟩ (by show i.val < _; simp))) hst₂
    have hA_amb : MeasurableSet A := W.F.le_ambient s₂ A hA
    -- SI(t₂) - SI(s₂) = Σ d_i
    have h_diff : ∀ ω, SI t₂ ω - SI s₂ ω = ∑ i, d i ω :=
      fun ω => si_at_diff_eq_clamped_sum H W s₂ t₂ hst₂ ω
    -- BM increment integrability
    have hΔW_int : ∀ (i : Fin H.n) (hi : (i:ℕ)+1 < H.n),
        Integrable (fun ω => W.process (τ ⟨(i:ℕ)+1, hi⟩) ω - W.process (τ i) ω) μ :=
      fun i hi => W.increment_integrable (τ i) (τ ⟨(i:ℕ)+1, hi⟩) (hτ_nn i) (hτ_mono i hi)
    have hΔW_sq_int : ∀ (i : Fin H.n) (hi : (i:ℕ)+1 < H.n),
        Integrable (fun ω => (W.process (τ ⟨(i:ℕ)+1, hi⟩) ω - W.process (τ i) ω)^2) μ :=
      fun i hi => W.increment_sq_integrable (τ i) (τ ⟨(i:ℕ)+1, hi⟩) (hτ_nn i) (hτ_mono i hi)
    -- === Cross-term integrability ===
    have hd_cross_int : ∀ i j : Fin H.n,
        IntegrableOn (fun ω => d i ω * d j ω) A μ := by
      intro i j; apply Integrable.integrableOn
      simp only [d]
      by_cases hi : (i:ℕ)+1 < H.n <;> by_cases hj : (j:ℕ)+1 < H.n <;>
        simp only [dif_pos, *]
      · -- Both active: |H_i·ΔW_i·H_j·ΔW_j| ≤ Ci·Cj·(ΔW_i² + ΔW_j²) by AM-GM
        obtain ⟨Ci, hCi⟩ := hH_bdd i; obtain ⟨Cj, hCj⟩ := hH_bdd j
        apply (((hΔW_sq_int i hi).add (hΔW_sq_int j hj)).const_mul (Ci * Cj)).mono'
        · exact ((hH_adapted i).mono (W.F.le_ambient (H.times i)) le_rfl).aestronglyMeasurable.mul
            ((W.toAdapted.adapted (τ ⟨_,hi⟩)).mono (W.F.le_ambient _) le_rfl |>.sub
            ((W.toAdapted.adapted (τ i)).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable
            |>.mul
            (((hH_adapted j).mono (W.F.le_ambient _) le_rfl).aestronglyMeasurable.mul
            ((W.toAdapted.adapted (τ ⟨_,hj⟩)).mono (W.F.le_ambient _) le_rfl |>.sub
            ((W.toAdapted.adapted (τ j)).mono (W.F.le_ambient _) le_rfl)).aestronglyMeasurable)
        · filter_upwards with ω
          simp only [Pi.add_apply, Real.norm_eq_abs]
          rw [abs_mul, abs_mul, abs_mul,
              ← sq_abs (W.process (τ ⟨(i:ℕ)+1,hi⟩) ω - W.process (τ i) ω),
              ← sq_abs (W.process (τ ⟨(j:ℕ)+1,hj⟩) ω - W.process (τ j) ω)]
          set a := |W.process (τ ⟨(i:ℕ)+1,hi⟩) ω - W.process (τ i) ω|
          set b := |W.process (τ ⟨(j:ℕ)+1,hj⟩) ω - W.process (τ j) ω|
          have ha := abs_nonneg (W.process (τ ⟨(i:ℕ)+1,hi⟩) ω - W.process (τ i) ω)
          have hb := abs_nonneg (W.process (τ ⟨(j:ℕ)+1,hj⟩) ω - W.process (τ j) ω)
          have hCi_nn : 0 ≤ Ci := le_trans (abs_nonneg _) (hCi ω)
          have hCj_nn : 0 ≤ Cj := le_trans (abs_nonneg _) (hCj ω)
          calc |H.values i ω| * a * (|H.values j ω| * b)
              ≤ Ci * a * (Cj * b) :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hCi ω) ha)
                  (mul_le_mul_of_nonneg_right (hCj ω) hb)
                  (mul_nonneg (abs_nonneg _) hb) (mul_nonneg hCi_nn ha)
            _ = Ci * Cj * (a * b) := by ring
            _ ≤ Ci * Cj * (a ^ 2 + b ^ 2) := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCi_nn hCj_nn)
                nlinarith [sq_nonneg (a - b), mul_nonneg ha hb]
      all_goals (simp only [dite_false, mul_zero, zero_mul]; exact integrable_zero _ _ _)
    -- === Cross-term orthogonality ===
    have hd_orth : ∀ i j : Fin H.n, i ≠ j →
        ∫ ω in A, d i ω * d j ω ∂μ = 0 := by
      intro i j hij
      simp only [d]
      by_cases hi : (i:ℕ)+1 < H.n <;> by_cases hj : (j:ℕ)+1 < H.n <;>
        simp only [dif_pos, *]
      · -- Both active: use BM independence
        -- WLOG i.val < j.val
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
        · -- i < j: use ΔW_j as the independent BM increment
          -- Rearrange: (H_i·ΔW_i)·(H_j·ΔW_j) = (H_i·ΔW_i·H_j)·ΔW_j
          have hrw : ∀ ω, H.values i ω * (W.process (τ ⟨_,hi⟩) ω - W.process (τ i) ω) *
              (H.values j ω * (W.process (τ ⟨_,hj⟩) ω - W.process (τ j) ω)) =
              (H.values i ω * (W.process (τ ⟨_,hi⟩) ω - W.process (τ i) ω) * H.values j ω) *
              (W.process (τ ⟨_,hj⟩) ω - W.process (τ j) ω) := fun ω => by ring
          simp_rw [hrw]; clear hrw
          show ∫ ω in A, _ * (W.toAdapted.process (τ ⟨_,hj⟩) ω -
            W.toAdapted.process (τ j) ω) ∂μ = 0
          -- Case split: is the j-th partition interval degenerate?
          by_cases h_active_j : max (H.times j) s₂ ≤ t₂
          · -- Active case: H.times j ≤ τ_j
            have hHj_le_τj : H.times j ≤ τ j := clamp_ge_arg _ s₂ t₂ h_active_j
            have hHi_le_τj : H.times i ≤ τ j := le_trans
              (le_of_lt (H.increasing i j (by exact_mod_cast hlt))) hHj_le_τj
            have hτi1_le_τj : τ ⟨(i:ℕ)+1, hi⟩ ≤ τ j :=
              clamp_partition_ordered H s₂ t₂ i j hi hlt
            apply SimpleProcess.setIntegral_adapted_mul_increment_zero W
            · -- g = (H_i · ΔW_i) · H_j is F_{τ_j}-measurable
              exact (((hH_adapted i).mono (W.F.mono _ _ hHi_le_τj) le_rfl).mul
                (((W.toAdapted.adapted (τ ⟨_,hi⟩)).mono
                  (W.F.mono _ _ hτi1_le_τj) le_rfl).sub
                ((W.toAdapted.adapted (τ i)).mono
                  (W.F.mono _ _ ((hτ_mono i hi).trans hτi1_le_τj)) le_rfl))).mul
                ((hH_adapted j).mono (W.F.mono _ _ hHj_le_τj) le_rfl)
            · -- g = H_i * ΔW_i * H_j is integrable
              obtain ⟨Ci, hCi⟩ := hH_bdd i; obtain ⟨Cj, hCj⟩ := hH_bdd j
              exact ((hΔW_int i hi).mul_of_top_right
                (memLp_top_of_bound (hH_adapted i |>.mono (W.F.le_ambient _) le_rfl
                  |>.stronglyMeasurable.aestronglyMeasurable) Ci
                  (ae_of_all _ fun ω => hCi ω))).mul_of_top_left
                (memLp_top_of_bound (hH_adapted j |>.mono (W.F.le_ambient _) le_rfl
                  |>.stronglyMeasurable.aestronglyMeasurable) Cj
                  (ae_of_all _ fun ω => hCj ω))
            · exact hτ_nn j
            · exact hτ_mono j hj
            · exact by apply W.F.mono _ _ (hτ_ge_s₂ j); exact hA
          · -- Degenerate case: max(H.times j, s₂) > t₂, so τ_j = τ_{j+1} = t₂
            push_neg at h_active_j
            have h1 : τ j = t₂ := min_eq_right (le_of_lt h_active_j)
            have h2 : τ ⟨(j:ℕ)+1, hj⟩ = t₂ := min_eq_right (le_trans (le_of_lt h_active_j)
              (max_le_max_right s₂ (le_of_lt (H.increasing j ⟨(j:ℕ)+1, hj⟩
                (by show j.val < _; simp)))))
            simp only [h1, h2, sub_self, mul_zero, integral_zero]
        · -- j < i: symmetric, swap using mul_comm
          have hrw : ∀ ω, H.values i ω * (W.process (τ ⟨_,hi⟩) ω - W.process (τ i) ω) *
              (H.values j ω * (W.process (τ ⟨_,hj⟩) ω - W.process (τ j) ω)) =
              (H.values j ω * (W.process (τ ⟨_,hj⟩) ω - W.process (τ j) ω) * H.values i ω) *
              (W.process (τ ⟨_,hi⟩) ω - W.process (τ i) ω) := fun ω => by ring
          simp_rw [hrw]; clear hrw
          show ∫ ω in A, _ * (W.toAdapted.process (τ ⟨_,hi⟩) ω -
            W.toAdapted.process (τ i) ω) ∂μ = 0
          -- Case split: is the i-th partition interval degenerate?
          by_cases h_active_i : max (H.times i) s₂ ≤ t₂
          · -- Active case: H.times i ≤ τ_i
            have hHi_le_τi : H.times i ≤ τ i := clamp_ge_arg _ s₂ t₂ h_active_i
            have hHj_le_τi : H.times j ≤ τ i := le_trans
              (le_of_lt (H.increasing j i (by exact_mod_cast hgt))) hHi_le_τi
            have hτj1_le_τi : τ ⟨(j:ℕ)+1, hj⟩ ≤ τ i :=
              clamp_partition_ordered H s₂ t₂ j i hj hgt
            apply SimpleProcess.setIntegral_adapted_mul_increment_zero W
            · -- g = (H_j · ΔW_j) · H_i is F_{τ_i}-measurable
              exact (((hH_adapted j).mono (W.F.mono _ _ hHj_le_τi) le_rfl).mul
                (((W.toAdapted.adapted (τ ⟨_,hj⟩)).mono
                  (W.F.mono _ _ hτj1_le_τi) le_rfl).sub
                ((W.toAdapted.adapted (τ j)).mono
                  (W.F.mono _ _ ((hτ_mono j hj).trans hτj1_le_τi)) le_rfl))).mul
                ((hH_adapted i).mono (W.F.mono _ _ hHi_le_τi) le_rfl)
            · -- g = H_j * ΔW_j * H_i is integrable
              obtain ⟨Ci, hCi⟩ := hH_bdd i; obtain ⟨Cj, hCj⟩ := hH_bdd j
              exact ((hΔW_int j hj).mul_of_top_right
                (memLp_top_of_bound (hH_adapted j |>.mono (W.F.le_ambient _) le_rfl
                  |>.stronglyMeasurable.aestronglyMeasurable) Cj
                  (ae_of_all _ fun ω => hCj ω))).mul_of_top_left
                (memLp_top_of_bound (hH_adapted i |>.mono (W.F.le_ambient _) le_rfl
                  |>.stronglyMeasurable.aestronglyMeasurable) Ci
                  (ae_of_all _ fun ω => hCi ω))
            · exact hτ_nn i
            · exact hτ_mono i hi
            · exact by apply W.F.mono _ _ (hτ_ge_s₂ i); exact hA
          · -- Degenerate case: max(H.times i, s₂) > t₂, so τ_i = τ_{i+1} = t₂
            push_neg at h_active_i
            have h1 : τ i = t₂ := min_eq_right (le_of_lt h_active_i)
            have h2 : τ ⟨(i:ℕ)+1, hi⟩ = t₂ := min_eq_right (le_trans (le_of_lt h_active_i)
              (max_le_max_right s₂ (le_of_lt (H.increasing i ⟨(i:ℕ)+1, hi⟩
                (by show i.val < _; simp)))))
            simp only [h1, h2, sub_self, mul_zero, integral_zero]
      -- Degenerate cases: one or both d_i = 0
      all_goals (simp only [dite_false, zero_mul, mul_zero]; exact integral_zero _ _)
    -- === Apply Pythagoras: ∫_A (Σ d_i)² = Σ ∫_A d_i² ===
    have h_pyth := set_sum_sq_integral_eq d hA_amb hd_cross_int hd_orth
    -- H_i² is integrable (bounded on probability space)
    have hH_sq_int : ∀ i : Fin H.n, Integrable (fun ω => (H.values i ω) ^ 2) μ := by
      intro i; obtain ⟨C, hC⟩ := hH_bdd i
      exact (memLp_top_of_bound
        ((hH_adapted i).mono (W.F.le_ambient _) le_rfl |>.pow_const 2
          |>.stronglyMeasurable.aestronglyMeasurable) (C ^ 2)
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [hC ω, sq_abs (H.values i ω), abs_nonneg (H.values i ω)])).integrable le_top
    -- === Rewrite and conclude ===
    -- Rewrite: ∫_A [(Σ d_i)² - QV] via h_diff and h_QV_eq
    simp_rw [h_diff]
    rw [integral_sub
      (by simp_rw [← h_diff]
          exact ((((hSI_sq_int t₂ ht₂).add (hSI_sq_int s₂ hs₂)).add
            ((hSI_sq_int t₂ ht₂).add (hSI_sq_int s₂ hs₂))).mono'
            (((hSI_int t₂ ht₂).sub (hSI_int s₂ hs₂)).aestronglyMeasurable.pow 2)
            (ae_of_all _ fun ω => by
              simp only [Real.norm_eq_abs, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
              rw [abs_of_nonneg (sq_nonneg _)]
              nlinarith [sq_nonneg (SI t₂ ω + SI s₂ ω)])).integrableOn)
      hQV_int.integrableOn]
    -- ∫_A (Σ d_i)² = Σ ∫_A d_i²
    rw [h_pyth]
    -- QV = Σ H_i² * Δτ_i
    have h_QV_sum : ∀ ω, QV ω = ∑ i : Fin H.n, if h : (i:ℕ)+1 < H.n then
        (H.values i ω)^2 * (τ ⟨(i:ℕ)+1, h⟩ - τ i) else 0 :=
      fun ω => simple_QV_eq_clamped_sum H hH_bdd hH_times_nn s₂ t₂ hs₂ hst₂ ω
    simp_rw [h_QV_sum]
    rw [integral_finset_sum _ (fun i _ => by
      split_ifs with hi
      · exact ((hH_sq_int i).mul_const _).integrableOn
      · exact integrableOn_zero)]
    -- Match: ∫_A d_i² = ∫_A H_i² * Δτ_i for each i
    -- Equivalently: Σ ∫_A d_i² - Σ ∫_A (H_i² * Δτ_i) = 0
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro i _
    -- For each i: ∫_A d_i² - ∫_A (H_i² * Δτ_i) = ∫_A [d_i² - H_i² * Δτ_i] = 0
    simp only [d]
    by_cases hi : (i:ℕ)+1 < H.n
    · simp only [dif_pos hi]
      -- d_i² = H_i² * ΔW_i², so d_i² - H_i² * Δτ_i = H_i² * (ΔW_i² - Δτ_i)
      have hrw : ∀ ω, (H.values i ω * (W.process (τ ⟨(i:ℕ)+1,hi⟩) ω -
          W.process (τ i) ω))^2 -
          (H.values i ω)^2 * (τ ⟨(i:ℕ)+1,hi⟩ - τ i) =
          (H.values i ω)^2 * ((W.process (τ ⟨(i:ℕ)+1,hi⟩) ω -
          W.process (τ i) ω)^2 - (τ ⟨(i:ℕ)+1,hi⟩ - τ i)) := fun ω => by ring
      have h_sq_int : IntegrableOn (fun ω => (H.values i ω * (W.process (τ ⟨(i:ℕ)+1,hi⟩) ω -
          W.process (τ i) ω)) ^ 2) A μ := by
        have h := hd_cross_int i i; simp only [d, dif_pos hi] at h; simp_rw [sq]; exact h
      rw [← integral_sub h_sq_int ((hH_sq_int i).mul_const _ |>.integrableOn)]
      simp_rw [hrw]
      -- ∫_A H_i² * (ΔW_i² - Δτ_i) = 0 by compensator
      -- Case split: when τ_i = τ_{i+1}, integrand is 0
      by_cases hτ_eq : τ i = τ ⟨(i:ℕ)+1, hi⟩
      · -- Degenerate: τ_i = τ_{i+1}, so ΔW = 0 and Δτ = 0
        have : ∀ ω, (H.values i ω) ^ 2 * ((W.process (τ ⟨(i:ℕ)+1,hi⟩) ω -
            W.process (τ i) ω) ^ 2 - (τ ⟨(i:ℕ)+1,hi⟩ - τ i)) = 0 := fun ω => by
          rw [← hτ_eq]; ring
        simp_rw [this]; exact integral_zero _ _
      · -- τ_i < τ_{i+1}: use BM compensator
        have hτ_strict : τ i < τ ⟨(i:ℕ)+1, hi⟩ := lt_of_le_of_ne (hτ_mono i hi) hτ_eq
        -- When τ_i < τ_{i+1}, max(H.times i, s₂) ≤ t₂ (otherwise both clamp to t₂)
        have h_max_le : max (H.times i) s₂ ≤ t₂ := by
          by_contra h_abs; push_neg at h_abs
          have eq1 : τ i = t₂ := min_eq_right (le_of_lt h_abs)
          have h2 : max (H.times ⟨(i:ℕ)+1, hi⟩) s₂ ≥ max (H.times i) s₂ :=
            max_le_max_right s₂ (le_of_lt (H.increasing i ⟨_, hi⟩ (by show i.val < _; simp)))
          have eq2 : τ ⟨(i:ℕ)+1, hi⟩ = t₂ := min_eq_right (le_of_lt (lt_of_lt_of_le h_abs h2))
          linarith
        -- Hence H.times i ≤ τ_i = max(H.times i, s₂)
        have hHi_le_τ : H.times i ≤ τ i := by
          show H.times i ≤ min (max (H.times i) s₂) t₂
          rw [min_eq_left h_max_le]; exact le_max_left _ _
        -- Use indicator trick: ∫_A f = ∫ 1_A · f
        rw [← integral_indicator hA_amb]
        simp_rw [Set.indicator_mul_left]
        -- Apply integral_mul_eq_zero_of_setIntegral_eq_zero'
        -- X = 1_A · H_i², Y = ΔW_i² - Δτ_i, m = F_{τ_i}
        apply integral_mul_eq_zero_of_setIntegral_eq_zero' (W.F.le_ambient (τ i))
        · -- 1_A · H_i² is F_{τ_i}-measurable
          have hA_τi : @MeasurableSet Ω (W.F.σ_algebra (τ i)) A := by
            apply W.F.mono _ _ (hτ_ge_s₂ i)
            exact hA
          exact ((hH_adapted i).mono (W.F.mono _ _ hHi_le_τ) le_rfl).pow_const 2
            |>.indicator hA_τi
        · -- ΔW_i² - Δτ_i is integrable
          exact (hΔW_sq_int i hi).sub (integrable_const _)
        · -- (1_A · H_i²) · (ΔW_i² - Δτ_i) is integrable
          obtain ⟨C, hC⟩ := hH_bdd i
          apply (((hΔW_sq_int i hi).add
            (integrable_const (τ ⟨(i:ℕ)+1,hi⟩ - τ i))).const_mul (C ^ 2)).mono'
          · exact (((hH_adapted i).mono (W.F.le_ambient _) le_rfl).pow_const 2
              |>.indicator (hA_amb)).stronglyMeasurable.aestronglyMeasurable.mul
              ((hΔW_sq_int i hi).sub (integrable_const _)).aestronglyMeasurable
          · filter_upwards with ω
            simp only [Pi.add_apply, Real.norm_eq_abs, Set.indicator]
            split_ifs
            · rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
              have hC_nn : 0 ≤ C := le_trans (abs_nonneg _) (hC ω)
              have hHsq : (H.values i ω) ^ 2 ≤ C ^ 2 := by
                nlinarith [hC ω, sq_abs (H.values i ω), abs_nonneg (H.values i ω)]
              have habs : |(W.process (τ ⟨(i:ℕ)+1,hi⟩) ω - W.process (τ i) ω) ^ 2 -
                  (τ ⟨(i:ℕ)+1,hi⟩ - τ i)| ≤
                  (W.process (τ ⟨(i:ℕ)+1,hi⟩) ω - W.process (τ i) ω) ^ 2 +
                  (τ ⟨(i:ℕ)+1,hi⟩ - τ i) := by
                rw [abs_le]; constructor <;> nlinarith [sq_nonneg (W.process
                  (τ ⟨(i:ℕ)+1,hi⟩) ω - W.process (τ i) ω), hτ_mono i hi]
              nlinarith
            · simp only [zero_mul, abs_zero]
              exact mul_nonneg (sq_nonneg _)
                (add_nonneg (sq_nonneg _) (sub_nonneg.mpr (hτ_mono i hi)))
        · -- ∀ B ∈ F_{τ_i}, ∫_B (ΔW_i² - Δτ_i) = 0
          intro B hB
          exact setIntegral_bm_compensated_sq_zero W (τ i) (τ ⟨(i:ℕ)+1,hi⟩)
            (hτ_nn i) (hτ_mono i hi) B hB
    · simp [dif_neg hi, sub_self]
  -- === COMBINE ===
  -- SI(t₂)² - SI(s₂)² - QV = 2·SI(s₂)·(SI(t₂)-SI(s₂)) + ((SI(t₂)-SI(s₂))² - QV)
  -- Rewrite integrand via algebraic identity
  suffices hsuff : ∫ ω in A, (2 * (SI s₂ ω * (SI t₂ ω - SI s₂ ω)) +
      ((SI t₂ ω - SI s₂ ω) ^ 2 - QV ω)) ∂μ = 0 by
    have hrw : ∀ ω, SI t₂ ω ^ 2 - SI s₂ ω ^ 2 - QV ω =
        2 * (SI s₂ ω * (SI t₂ ω - SI s₂ ω)) +
        ((SI t₂ ω - SI s₂ ω) ^ 2 - QV ω) := fun ω => by ring
    show ∫ ω in A, (SI t₂ ω ^ 2 - SI s₂ ω ^ 2 - QV ω) ∂μ = 0
    simp_rw [hrw]; exact hsuff
  -- Now prove the decomposed form
  have h_prod_int : Integrable (fun ω => SI s₂ ω * (SI t₂ ω - SI s₂ ω)) μ := by
    apply Integrable.mono' (((hSI_sq_int s₂ hs₂).add (hSI_sq_int t₂ ht₂)).add (hSI_sq_int s₂ hs₂))
    · exact (hSI_int s₂ hs₂).aestronglyMeasurable.mul
        ((hSI_int t₂ ht₂).sub (hSI_int s₂ hs₂)).aestronglyMeasurable
    · filter_upwards with ω
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_mul]
      set a := |SI s₂ ω|
      set b := |SI t₂ ω - SI s₂ ω|
      nlinarith [sq_nonneg (a - b), sq_abs (SI s₂ ω),
        sq_abs (SI t₂ ω - SI s₂ ω), sq_abs (SI t₂ ω)]
  have h_int1 : IntegrableOn (fun ω => 2 * (SI s₂ ω * (SI t₂ ω - SI s₂ ω))) A μ :=
    (h_prod_int.const_mul 2).integrableOn
  have hΔSI_sq_int : Integrable (fun ω => (SI t₂ ω - SI s₂ ω) ^ 2) μ := by
    -- (x-y)² ≤ 2(x²+y²), so dominate by 2*(SI_t² + SI_s²)
    exact (((hSI_sq_int t₂ ht₂).add (hSI_sq_int s₂ hs₂)).add
      ((hSI_sq_int t₂ ht₂).add (hSI_sq_int s₂ hs₂))).mono'
      (((hSI_int t₂ ht₂).sub (hSI_int s₂ hs₂)).aestronglyMeasurable.pow 2)
      (ae_of_all _ fun ω => by
        simp only [Pi.add_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (SI t₂ ω + SI s₂ ω)])
  have h_int2 : IntegrableOn (fun ω => (SI t₂ ω - SI s₂ ω) ^ 2 - QV ω) A μ :=
    (hΔSI_sq_int.sub hQV_int).integrableOn
  rw [integral_add h_int1 h_int2]
  -- Factor out 2 and use h_cross
  have h_cross_A : ∫ ω in A, 2 * (SI s₂ ω * (SI t₂ ω - SI s₂ ω)) ∂μ =
      2 * ∫ ω in A, SI s₂ ω * (SI t₂ ω - SI s₂ ω) ∂μ := by
    rw [integral_const_mul]
  rw [h_cross_A, h_cross, mul_zero, zero_add]
  exact h_iso

/-- L¹ convergence implies set integral convergence:
    if ∫ ‖fₙ - g‖ → 0 then ∫_A fₙ → ∫_A g. -/
private lemma tendsto_setIntegral_of_L1 (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf_int : ∀ n, Integrable (f n) μ) (hg_int : Integrable g μ)
    (hL1 : Tendsto (fun n => ∫ ω, ‖f n ω - g ω‖ ∂μ) atTop (nhds 0))
    (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, f n ω ∂μ) atTop (nhds (∫ ω in A, g ω ∂μ)) := by
  suffices h : Tendsto (fun n => ∫ ω in A, f n ω ∂μ - ∫ ω in A, g ω ∂μ)
      atTop (nhds 0) by
    have h' := h.add (@tendsto_const_nhds _ _ _ (∫ ω in A, g ω ∂μ) _)
    rw [zero_add] at h'
    exact h'.congr fun _ => sub_add_cancel _ _
  apply squeeze_zero_norm (fun n => ?_) hL1
  calc ‖∫ ω in A, f n ω ∂μ - ∫ ω in A, g ω ∂μ‖
      = ‖∫ ω in A, (f n ω - g ω) ∂μ‖ := by
        congr 1; exact (integral_sub (hf_int n).integrableOn hg_int.integrableOn).symm
    _ ≤ ∫ ω in A, ‖f n ω - g ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖f n ω - g ω‖ ∂μ :=
        setIntegral_le_integral ((hf_int n).sub hg_int).norm
          (ae_of_all _ fun _ => norm_nonneg _)

/-! ## Main conditional isometry theorem -/

/-- **Conditional Itô isometry**: For A ∈ F_s with s ≤ s₂ ≤ t₂,
    ∫_A [(SI(t₂)-SI(s₂))² - ∫_{s₂}^{t₂} σ²] dμ = 0.

    Equivalently: ∫_A (SI(t₂)-SI(s₂))² = ∫_A ∫_{s₂}^{t₂} σ².

    **Proof**: L² limit from simple process approximations.
    For each approximation Hₙ, the simple process version holds by
    `simple_compensated_sq_setIntegral_zero`. The convergence uses
    L¹ convergence of the compensated square. -/
theorem ItoProcess.compensated_sq_setIntegral_zero {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₂ t₂ : ℝ) (hs₂ : 0 ≤ s₂) (hst₂ : s₂ ≤ t₂)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s₂) A) :
    ∫ ω in A, ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
               ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  -- Step 1: Decompose (SI(t₂)-SI(s₂))² = SI(t₂)² - SI(s₂)² on sets
  -- by the cross-term vanishing (already proved)
  have h_sq_diff := X.setIntegral_sq_increment_eq_diff s₂ t₂ hs₂ hst₂ A hA
  -- Rewrite: ∫_A [(SI(t₂)-SI(s₂))² - ∫σ²] = ∫_A SI(t₂)² - ∫_A SI(s₂)² - ∫_A ∫σ²
  have ht₂ := le_trans hs₂ hst₂
  have hSI_t₂_sq_int := X.stoch_integral_sq_integrable t₂ ht₂
  have hSI_s₂_sq_int := X.stoch_integral_sq_integrable s₂ hs₂
  have hQ_s₂t₂_int := diffusion_sq_interval_integrable X s₂ t₂ hs₂ hst₂
  suffices h : ∫ ω in A, (X.stoch_integral t₂ ω) ^ 2 ∂μ -
      ∫ ω in A, (X.stoch_integral s₂ ω) ^ 2 ∂μ =
      ∫ ω in A, (∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ by
    rw [integral_sub (si_increment_sq_integrable' X s₂ t₂ hs₂ hst₂).integrableOn
      hQ_s₂t₂_int.integrableOn, h_sq_diff]
    linarith
  -- Step 2: Get approximation sequence
  obtain ⟨approx, hadapted_F, hbdd, hnn, hL2, _, hL2_int, _⟩ := X.stoch_integral_is_L2_limit
  -- Convert F-adapted to BM.F-adapted for SimpleProcess integration lemmas
  have hadapted : ∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (X.BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i) :=
    fun n i => (hadapted_F n i).mono (X.F_le_BM_F _) le_rfl
  -- Step 3: For each n, simple_compensated_sq_setIntegral_zero gives the identity
  -- ∫_A SI_n(t₂)² - ∫_A SI_n(s₂)² = ∫_A ∫_{s₂}^{t₂} H_n²
  -- Bridge filtration: F ≤ BM.F
  have hA' : @MeasurableSet Ω (X.BM.F.σ_algebra s₂) A := X.F_le_BM_F s₂ A hA
  have h_simple_id : ∀ n,
      ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω) ^ 2 ∂μ -
      ∫ ω in A, ((approx n).stochasticIntegral_at X.BM s₂ ω) ^ 2 ∂μ =
      ∫ ω in A, (∫ u in Icc s₂ t₂,
        (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) ∂μ := by
    intro n
    have h0 := simple_compensated_sq_setIntegral_zero (approx n) X.BM
      (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂ A hA'
    -- h0: ∫_A [SI_n(t₂)² - SI_n(s₂)² - ∫H_n²] = 0
    -- Split via linearity: ∫_A (a-b-c) = ∫_A a - ∫_A b - ∫_A c = 0
    have hSIn_t₂_sq : Integrable (fun ω =>
        ((approx n).stochasticIntegral_at X.BM t₂ ω) ^ 2) μ :=
      simple_stochasticIntegral_at_sq_integrable _ X.BM
        (hadapted n) (hbdd n) (hnn n) t₂ ht₂
    have hSIn_s₂_sq : Integrable (fun ω =>
        ((approx n).stochasticIntegral_at X.BM s₂ ω) ^ 2) μ :=
      simple_stochasticIntegral_at_sq_integrable _ X.BM
        (hadapted n) (hbdd n) (hnn n) s₂ hs₂
    have hHn_int : Integrable (fun ω =>
        ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) μ :=
      simple_process_sq_interval_integrable _ X.BM
        (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂
    -- Split using integral_sub (forward, not rewrite)
    have h_split_ab : ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 -
        (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2) ∂μ =
        ∫ ω in A, (approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 ∂μ -
        ∫ ω in A, (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2 ∂μ :=
      integral_sub hSIn_t₂_sq.integrableOn hSIn_s₂_sq.integrableOn
    have h_split_abc : ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 -
        (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2 -
        ∫ u in Icc s₂ t₂, (approx n).valueAtTime u ω ^ 2 ∂volume) ∂μ =
        ∫ ω in A, ((approx n).stochasticIntegral_at X.BM t₂ ω ^ 2 -
          (approx n).stochasticIntegral_at X.BM s₂ ω ^ 2) ∂μ -
        ∫ ω in A, ∫ u in Icc s₂ t₂, (approx n).valueAtTime u ω ^ 2 ∂volume ∂μ :=
      integral_sub (hSIn_t₂_sq.sub hSIn_s₂_sq).integrableOn hHn_int.integrableOn
    linarith
  -- Step 4: Pass to limit using L¹ convergence
  -- 4a: L¹ convergences of SI_n(t)² → SI(t)²
  have hL1_t₂ := sq_L1_tendsto_of_L2 X approx hadapted hbdd hnn t₂ ht₂ (hL2 t₂ ht₂)
  have hL1_s₂ := sq_L1_tendsto_of_L2 X approx hadapted hbdd hnn s₂ hs₂ (hL2 s₂ hs₂)
  -- 4b: L¹ convergence of diffusion integral on Icc s₂ t₂
  -- via splitting: ∫_{s₂}^{t₂} = ∫₀^{t₂} - ∫₀^{s₂}
  have hL1_0t := diffusion_integral_L1_tendsto X approx hbdd hMσ t₂ ht₂ (hL2_int t₂ ht₂)
  have hL1_0s := diffusion_integral_L1_tendsto X approx hbdd hMσ s₂ hs₂ (hL2_int s₂ hs₂)
  have h_split_Hn : ∀ n ω,
      ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume =
      (∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
      (∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) := by
    intro n ω
    obtain ⟨C, hC_nn, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded (approx n) (hbdd n)
    have h_int : IntegrableOn (fun u => (SimpleProcess.valueAtTime (approx n) u ω) ^ 2)
        (Icc 0 t₂) volume := by
      haveI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) t₂)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
      exact (integrable_const (C ^ 2)).mono'
        (((SimpleProcess.valueAtTime_jointly_measurable (approx n)).comp
          (measurable_id.prodMk measurable_const)).pow_const 2
          |>.stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          calc (SimpleProcess.valueAtTime (approx n) u ω) ^ 2
              = |SimpleProcess.valueAtTime (approx n) u ω| ^ 2 := (sq_abs _).symm
            _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC u ω) 2)
    linarith [setIntegral_Icc_split' hs₂ hst₂ h_int]
  have h_split_σ : ∀ ω,
      ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume =
      (∫ u in Icc 0 t₂, (X.diffusion u ω) ^ 2 ∂volume) -
      (∫ u in Icc 0 s₂, (X.diffusion u ω) ^ 2 ∂volume) := by
    intro ω
    linarith [setIntegral_Icc_split' hs₂ hst₂ (X.diffusion_sq_time_integrable ω t₂ ht₂)]
  -- Combine L1 convergences using triangle inequality
  have hL1_diff : Tendsto (fun n => ∫ ω,
      ‖(∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
       (∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume)‖ ∂μ)
      atTop (nhds 0) := by
    have hL1_sum : Tendsto (fun n =>
        (∫ ω, ‖(∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 t₂, (X.diffusion u ω) ^ 2 ∂volume)‖ ∂μ) +
        (∫ ω, ‖(∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 s₂, (X.diffusion u ω) ^ 2 ∂volume)‖ ∂μ))
        atTop (nhds 0) := by
      have := hL1_0t.add hL1_0s; rwa [add_zero] at this
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hL1_sum
    -- Bound: ‖∫_{s,t} Hₙ² - ∫_{s,t} σ²‖ ≤ ‖∫₀ᵗ Hₙ² - ∫₀ᵗ σ²‖ + ‖∫₀ˢ Hₙ² - ∫₀ˢ σ²‖
    calc ∫ ω, ‖(∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
         (∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume)‖ ∂μ
        ≤ ∫ ω, (‖(∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 t₂, (X.diffusion u ω) ^ 2 ∂volume)‖ +
          ‖(∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 s₂, (X.diffusion u ω) ^ 2 ∂volume)‖) ∂μ := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
            · exact ((simple_process_sq_integral_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) t₂ ht₂).sub
                (X.diffusion_sq_integral_integrable t₂ ht₂)).norm.add
                ((simple_process_sq_integral_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) s₂ hs₂).sub
                  (X.diffusion_sq_integral_integrable s₂ hs₂)).norm
            · exact ae_of_all _ fun ω => by
                dsimp only
                rw [h_split_Hn n ω, h_split_σ ω]
                have : ∀ (a b c d : ℝ), (a - c) - (b - d) = (a - b) - (c - d) := fun _ _ _ _ => by ring
                rw [this]
                exact norm_sub_le _ _
      _ = (∫ ω, ‖(∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 t₂, (X.diffusion u ω) ^ 2 ∂volume)‖ ∂μ) +
          (∫ ω, ‖(∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 s₂, (X.diffusion u ω) ^ 2 ∂volume)‖ ∂μ) := by
            exact integral_add
              ((simple_process_sq_integral_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) t₂ ht₂).sub
                (X.diffusion_sq_integral_integrable t₂ ht₂)).norm
              ((simple_process_sq_integral_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) s₂ hs₂).sub
                (X.diffusion_sq_integral_integrable s₂ hs₂)).norm
  -- 4c: Convert L1 to set integral convergence via tendsto_setIntegral_of_L1
  have h_SI_n_t₂_int : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at X.BM t₂ ω) ^ 2) μ :=
    fun n => simple_stochasticIntegral_at_sq_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) t₂ ht₂
  have h_SI_n_s₂_int : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at X.BM s₂ ω) ^ 2) μ :=
    fun n => simple_stochasticIntegral_at_sq_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) s₂ hs₂
  have h_Hn_int : ∀ n, Integrable (fun ω =>
      ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) μ :=
    fun n => simple_process_sq_interval_integrable _ X.BM (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂
  have hA_t₂ := tendsto_setIntegral_of_L1
    (fun n ω => ((approx n).stochasticIntegral_at X.BM t₂ ω) ^ 2)
    (fun ω => (X.stoch_integral t₂ ω) ^ 2) h_SI_n_t₂_int hSI_t₂_sq_int hL1_t₂ A
  have hA_s₂ := tendsto_setIntegral_of_L1
    (fun n ω => ((approx n).stochasticIntegral_at X.BM s₂ ω) ^ 2)
    (fun ω => (X.stoch_integral s₂ ω) ^ 2) h_SI_n_s₂_int hSI_s₂_sq_int hL1_s₂ A
  have hA_diff := tendsto_setIntegral_of_L1
    (fun n ω => ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume)
    (fun ω => ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume)
    h_Hn_int hQ_s₂t₂_int hL1_diff A
  -- 4d: Combine: LHS_n → LHS and RHS_n → RHS, with LHS_n = RHS_n ⟹ LHS = RHS
  have hLHS_tendsto := hA_t₂.sub hA_s₂
  -- hLHS_tendsto : ∫_A SIₙ(t₂)² - ∫_A SIₙ(s₂)² → ∫_A SI(t₂)² - ∫_A SI(s₂)²
  -- h_simple_id n : ∫_A SIₙ(t₂)² - ∫_A SIₙ(s₂)² = ∫_A ∫ Hₙ²
  -- So ∫_A ∫ Hₙ² → ∫_A SI(t₂)² - ∫_A SI(s₂)²
  -- Tendsto.congr h ht : given h : ∀ x, f₁ x = f₂ x and ht : Tendsto f₁, get Tendsto f₂
  have hRHS_also := Tendsto.congr h_simple_id hLHS_tendsto
  -- hRHS_also : ∫_A ∫ Hₙ² → ∫_A SI(t₂)² - ∫_A SI(s₂)²
  -- hA_diff : ∫_A ∫ Hₙ² → ∫_A ∫ σ²
  -- By uniqueness of limits: ∫_A SI(t₂)² - ∫_A SI(s₂)² = ∫_A ∫ σ²
  exact tendsto_nhds_unique hRHS_also hA_diff

/-- Core adapter for conditional compensated-square set-integral zero. -/
theorem ItoProcessCore.compensated_sq_setIntegral_zero_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₂ t₂ : ℝ) (hs₂ : 0 ≤ s₂) (hst₂ : s₂ ≤ t₂)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s₂) A) :
    ∫ ω in A, ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
               ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  let R : ItoProcessRegularity X := ItoProcessRegularity.ofSplit C DR D FC
  let Xp : ItoProcess F μ := X.toItoProcess R
  have hMσp : ∀ t ω, |Xp.diffusion t ω| ≤ Mσ := by
    simpa [Xp] using hMσ
  change ∫ ω in A, ((Xp.stoch_integral t₂ ω - Xp.stoch_integral s₂ ω) ^ 2 -
               ∫ u in Icc s₂ t₂, (Xp.diffusion u ω) ^ 2 ∂volume) ∂μ = 0
  have h_sq_diff := Xp.setIntegral_sq_increment_eq_diff s₂ t₂ hs₂ hst₂ A hA
  have ht₂ := le_trans hs₂ hst₂
  have hSI_t₂_sq_int := Xp.stoch_integral_sq_integrable t₂ ht₂
  have hSI_s₂_sq_int := Xp.stoch_integral_sq_integrable s₂ hs₂
  have hQ_s₂t₂_int := diffusion_sq_interval_integrable Xp s₂ t₂ hs₂ hst₂
  suffices h : ∫ ω in A, (Xp.stoch_integral t₂ ω) ^ 2 ∂μ -
      ∫ ω in A, (Xp.stoch_integral s₂ ω) ^ 2 ∂μ =
      ∫ ω in A, (∫ u in Icc s₂ t₂, (Xp.diffusion u ω) ^ 2 ∂volume) ∂μ by
    rw [integral_sub (si_increment_sq_integrable' Xp s₂ t₂ hs₂ hst₂).integrableOn
      hQ_s₂t₂_int.integrableOn, h_sq_diff]
    linarith
  obtain ⟨approx, hadapted_F, hbdd, hnn, hL2, _, hL2_int, _⟩ := Xp.stoch_integral_is_L2_limit
  have hadapted : ∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (Xp.BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i) :=
    fun n i => (hadapted_F n i).mono (Xp.F_le_BM_F _) le_rfl
  have hA' : @MeasurableSet Ω (Xp.BM.F.σ_algebra s₂) A := Xp.F_le_BM_F s₂ A hA
  have h_simple_id : ∀ n,
      ∫ ω in A, ((approx n).stochasticIntegral_at Xp.BM t₂ ω) ^ 2 ∂μ -
      ∫ ω in A, ((approx n).stochasticIntegral_at Xp.BM s₂ ω) ^ 2 ∂μ =
      ∫ ω in A, (∫ u in Icc s₂ t₂,
        (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) ∂μ := by
    intro n
    have h0 := simple_compensated_sq_setIntegral_zero (approx n) Xp.BM
      (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂ A hA'
    have hSIn_t₂_sq : Integrable (fun ω =>
        ((approx n).stochasticIntegral_at Xp.BM t₂ ω) ^ 2) μ :=
      simple_stochasticIntegral_at_sq_integrable _ Xp.BM
        (hadapted n) (hbdd n) (hnn n) t₂ ht₂
    have hSIn_s₂_sq : Integrable (fun ω =>
        ((approx n).stochasticIntegral_at Xp.BM s₂ ω) ^ 2) μ :=
      simple_stochasticIntegral_at_sq_integrable _ Xp.BM
        (hadapted n) (hbdd n) (hnn n) s₂ hs₂
    have hHn_int : Integrable (fun ω =>
        ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) μ :=
      simple_process_sq_interval_integrable _ Xp.BM
        (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂
    have h_split_ab : ∫ ω in A, ((approx n).stochasticIntegral_at Xp.BM t₂ ω ^ 2 -
        (approx n).stochasticIntegral_at Xp.BM s₂ ω ^ 2) ∂μ =
        ∫ ω in A, (approx n).stochasticIntegral_at Xp.BM t₂ ω ^ 2 ∂μ -
        ∫ ω in A, (approx n).stochasticIntegral_at Xp.BM s₂ ω ^ 2 ∂μ :=
      integral_sub hSIn_t₂_sq.integrableOn hSIn_s₂_sq.integrableOn
    have h_split_abc : ∫ ω in A, ((approx n).stochasticIntegral_at Xp.BM t₂ ω ^ 2 -
        (approx n).stochasticIntegral_at Xp.BM s₂ ω ^ 2 -
        ∫ u in Icc s₂ t₂, (approx n).valueAtTime u ω ^ 2 ∂volume) ∂μ =
        ∫ ω in A, ((approx n).stochasticIntegral_at Xp.BM t₂ ω ^ 2 -
          (approx n).stochasticIntegral_at Xp.BM s₂ ω ^ 2) ∂μ -
        ∫ ω in A, ∫ u in Icc s₂ t₂, (approx n).valueAtTime u ω ^ 2 ∂volume ∂μ :=
      integral_sub (hSIn_t₂_sq.sub hSIn_s₂_sq).integrableOn hHn_int.integrableOn
    linarith
  have hL1_t₂ := sq_L1_tendsto_of_L2 Xp approx hadapted hbdd hnn t₂ ht₂ (hL2 t₂ ht₂)
  have hL1_s₂ := sq_L1_tendsto_of_L2 Xp approx hadapted hbdd hnn s₂ hs₂ (hL2 s₂ hs₂)
  have hL1_0t := diffusion_integral_L1_tendsto Xp approx hbdd hMσp t₂ ht₂ (hL2_int t₂ ht₂)
  have hL1_0s := diffusion_integral_L1_tendsto Xp approx hbdd hMσp s₂ hs₂ (hL2_int s₂ hs₂)
  have h_split_Hn : ∀ n ω,
      ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume =
      (∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
      (∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) := by
    intro n ω
    obtain ⟨C0, hC_nn, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded (approx n) (hbdd n)
    have h_int : IntegrableOn (fun u => (SimpleProcess.valueAtTime (approx n) u ω) ^ 2)
        (Icc 0 t₂) volume := by
      haveI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) t₂)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
      exact (integrable_const (C0 ^ 2)).mono'
        (((SimpleProcess.valueAtTime_jointly_measurable (approx n)).comp
          (measurable_id.prodMk measurable_const)).pow_const 2
          |>.stronglyMeasurable.aestronglyMeasurable)
        (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          calc (SimpleProcess.valueAtTime (approx n) u ω) ^ 2
              = |SimpleProcess.valueAtTime (approx n) u ω| ^ 2 := (sq_abs _).symm
            _ ≤ C0 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC u ω) 2)
    linarith [setIntegral_Icc_split' hs₂ hst₂ h_int]
  have h_split_σ : ∀ ω,
      ∫ u in Icc s₂ t₂, (Xp.diffusion u ω) ^ 2 ∂volume =
      (∫ u in Icc 0 t₂, (Xp.diffusion u ω) ^ 2 ∂volume) -
      (∫ u in Icc 0 s₂, (Xp.diffusion u ω) ^ 2 ∂volume) := by
    intro ω
    linarith [setIntegral_Icc_split' hs₂ hst₂ (Xp.diffusion_sq_time_integrable ω t₂ ht₂)]
  have hL1_diff : Tendsto (fun n => ∫ ω,
      ‖(∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
       (∫ u in Icc s₂ t₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖ ∂μ)
      atTop (nhds 0) := by
    have hL1_sum : Tendsto (fun n =>
        (∫ ω, ‖(∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 t₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖ ∂μ) +
        (∫ ω, ‖(∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 s₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖ ∂μ))
        atTop (nhds 0) := by
      have := hL1_0t.add hL1_0s; rwa [add_zero] at this
    apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hL1_sum
    calc ∫ ω, ‖(∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
         (∫ u in Icc s₂ t₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖ ∂μ
        ≤ ∫ ω, (‖(∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 t₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖ +
          ‖(∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 s₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖) ∂μ := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
            · exact ((simple_process_sq_integral_integrable _ Xp.BM (hadapted n) (hbdd n) (hnn n) t₂ ht₂).sub
                (Xp.diffusion_sq_integral_integrable t₂ ht₂)).norm.add
                ((simple_process_sq_integral_integrable _ Xp.BM (hadapted n) (hbdd n) (hnn n) s₂ hs₂).sub
                  (Xp.diffusion_sq_integral_integrable s₂ hs₂)).norm
            · exact ae_of_all _ fun ω => by
                dsimp only
                rw [h_split_Hn n ω, h_split_σ ω]
                have : ∀ (a b c d : ℝ), (a - c) - (b - d) = (a - b) - (c - d) := fun _ _ _ _ => by ring
                rw [this]
                exact norm_sub_le _ _
      _ = (∫ ω, ‖(∫ u in Icc 0 t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 t₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖ ∂μ) +
          (∫ ω, ‖(∫ u in Icc 0 s₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) -
           (∫ u in Icc 0 s₂, (Xp.diffusion u ω) ^ 2 ∂volume)‖ ∂μ) := by
            exact integral_add
              ((simple_process_sq_integral_integrable _ Xp.BM (hadapted n) (hbdd n) (hnn n) t₂ ht₂).sub
                (Xp.diffusion_sq_integral_integrable t₂ ht₂)).norm
              ((simple_process_sq_integral_integrable _ Xp.BM (hadapted n) (hbdd n) (hnn n) s₂ hs₂).sub
                (Xp.diffusion_sq_integral_integrable s₂ hs₂)).norm
  have h_SI_n_t₂_int : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at Xp.BM t₂ ω) ^ 2) μ :=
    fun n => simple_stochasticIntegral_at_sq_integrable _ Xp.BM (hadapted n) (hbdd n) (hnn n) t₂ ht₂
  have h_SI_n_s₂_int : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at Xp.BM s₂ ω) ^ 2) μ :=
    fun n => simple_stochasticIntegral_at_sq_integrable _ Xp.BM (hadapted n) (hbdd n) (hnn n) s₂ hs₂
  have h_Hn_int : ∀ n, Integrable (fun ω =>
      ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume) μ :=
    fun n => simple_process_sq_interval_integrable _ Xp.BM (hadapted n) (hbdd n) (hnn n) s₂ t₂ hs₂ hst₂
  have hA_t₂ := tendsto_setIntegral_of_L1
    (fun n ω => ((approx n).stochasticIntegral_at Xp.BM t₂ ω) ^ 2)
    (fun ω => (Xp.stoch_integral t₂ ω) ^ 2) h_SI_n_t₂_int hSI_t₂_sq_int hL1_t₂ A
  have hA_s₂ := tendsto_setIntegral_of_L1
    (fun n ω => ((approx n).stochasticIntegral_at Xp.BM s₂ ω) ^ 2)
    (fun ω => (Xp.stoch_integral s₂ ω) ^ 2) h_SI_n_s₂_int hSI_s₂_sq_int hL1_s₂ A
  have hA_diff := tendsto_setIntegral_of_L1
    (fun n ω => ∫ u in Icc s₂ t₂, (SimpleProcess.valueAtTime (approx n) u ω) ^ 2 ∂volume)
    (fun ω => ∫ u in Icc s₂ t₂, (Xp.diffusion u ω) ^ 2 ∂volume)
    h_Hn_int hQ_s₂t₂_int hL1_diff A
  have hLHS_tendsto := hA_t₂.sub hA_s₂
  have hRHS_also := Tendsto.congr h_simple_id hLHS_tendsto
  exact tendsto_nhds_unique hRHS_also hA_diff

/-! ## Squared Orthogonality -/

/-- Compensated squared SI increments on disjoint intervals are orthogonal:
    E[((SI(t₁)-SI(s₁))² - ∫σ²₁) · ((SI(t₂)-SI(s₂))² - ∫σ²₂)] = 0
    for t₁ ≤ s₂.

    **Proof**: Decompose E[Z₁·Z₂] = E[Δ₁²·Z₂] - E[Q₁·Z₂].
    - E[Δ₁²·Z₂] = 0: Δ₁² is F_{s₂}-measurable, conditional isometry gives ∫_A Z₂ = 0.
    - E[Q₁·Z₂] = 0: Approximate Q₁ by F_{s₂}-measurable Q₁ₙ from simple processes. -/
theorem ItoProcess.stoch_integral_squared_orthogonal {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₁ t₁ s₂ t₂ : ℝ)
    (hs₁ : 0 ≤ s₁) (hst₁ : s₁ ≤ t₁) (ht₁s₂ : t₁ ≤ s₂) (hst₂ : s₂ ≤ t₂) :
    ∫ ω, ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
           ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) *
          ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
           ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  -- Convenience abbreviations and basic facts
  set Z₂ := fun ω => (X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
    ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume
  have hs₂ : 0 ≤ s₂ := le_trans (le_trans hs₁ hst₁) ht₁s₂
  have ht₁ : 0 ≤ t₁ := le_trans hs₁ hst₁
  -- Integrability
  have hΔ₁_sq_int := si_increment_sq_integrable' X s₁ t₁ hs₁ hst₁
  have hQ₁_int := diffusion_sq_interval_integrable X s₁ t₁ hs₁ hst₁
  have hZ₂_int := compensated_sq_integrable' X s₂ t₂ hs₂ hst₂
  have hZ₂_sq_int := compensated_sq_sq_integrable' X hMσ s₂ t₂ hs₂ hst₂
  have hΔ₁_L4 := stoch_integral_increment_L4_integrable_proof X hMσ s₁ t₁ hs₁ hst₁
  have hQ₁_bdd := diffusion_sq_integral_bound X hMσ s₁ t₁ hs₁ hst₁
  -- Δ₁²·Z₂ integrable (AM-GM: |ab| ≤ a² + b², Δ₁⁴ and Z₂² integrable)
  have hΔ₁_sq_Z₂_int : Integrable (fun ω =>
      (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω) μ := by
    have hdom : Integrable (fun ω =>
        (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 + Z₂ ω ^ 2) μ :=
      hΔ₁_L4.add hZ₂_sq_int
    exact hdom.mono'
      (hΔ₁_sq_int.aestronglyMeasurable.mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω))]
        have h4eq : (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 =
            ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2) ^ 2 := by ring
        rw [h4eq]
        nlinarith [sq_nonneg ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 - |Z₂ ω|),
          sq_abs (Z₂ ω)])
  -- Q₁·Z₂ integrable (Q₁ bounded, Z₂ integrable)
  have hQ₁_Z₂_int : Integrable (fun ω =>
      (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω) μ := by
    set C₁ := Mσ ^ 2 * (t₁ - s₁)
    -- Dominate by C₁ * ‖Z₂‖
    exact (hZ₂_int.norm.const_mul C₁).mono'
      (hQ₁_int.aestronglyMeasurable.mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hQ₁_bdd ω) (abs_nonneg _))
  -- Step 1: Decompose ∫ (Δ₁²-Q₁)·Z₂ = ∫ Δ₁²·Z₂ - ∫ Q₁·Z₂
  have hdecomp : (fun ω => ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
      ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) *
      ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
       ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume)) =
      (fun ω => (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω -
        (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω) := by
    ext ω; ring
  rw [hdecomp, integral_sub hΔ₁_sq_Z₂_int hQ₁_Z₂_int]
  -- Step 2: E[Δ₁²·Z₂] = 0 by martingale orthogonality + conditional isometry
  have h_part1 : ∫ ω, (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω ∂μ = 0 := by
    apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s₂)
    · -- Δ₁² is F_{s₂}-measurable: SI(t₁), SI(s₁) are F_{t₁}-meas, t₁ ≤ s₂
      exact ((X.stoch_integral_adapted t₁ ht₁).sub
        ((X.stoch_integral_adapted s₁ hs₁).mono (F.mono s₁ t₁ hst₁) le_rfl)).pow_const 2
        |>.mono (F.mono t₁ s₂ ht₁s₂) le_rfl
    · exact hZ₂_int
    · exact hΔ₁_sq_Z₂_int
    · -- Conditional isometry: ∫_A Z₂ = 0 for A ∈ F_{s₂}
      exact X.compensated_sq_setIntegral_zero hMσ s₂ t₂ hs₂ hst₂
  -- Step 3: E[Q₁·Z₂] = 0 by Fubini + pointwise orthogonality
  -- Strategy: (∫_u σ² du) * Z₂(ω) = ∫_u (σ² * Z₂) du, then swap ∫_ω ∫_u to ∫_u ∫_ω.
  -- For each u ∈ [s₁,t₁]: σ²(u,·) is F_{s₂}-measurable (by diffusion_adapted + u ≤ t₁ ≤ s₂),
  -- and ∫_A Z₂ = 0 for A ∈ F_{s₂} (conditional isometry), so E[σ²(u,·)·Z₂] = 0.
  have h_part2 : ∫ ω, (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω ∂μ = 0 := by
    -- Sub-step 3a: σ²(u,·) is F_{s₂}-measurable for u ∈ [s₁,t₁]
    have h_diff_Fs₂ : ∀ u, u ∈ Set.Icc s₁ t₁ →
        @Measurable Ω ℝ (F.σ_algebra s₂) _ (fun ω => (X.diffusion u ω) ^ 2) := by
      intro u ⟨_, hut⟩
      exact ((X.diffusion_adapted u).mono (F.mono u s₂ (le_trans hut ht₁s₂)) le_rfl).pow_const 2
    -- Sub-step 3b: For each u ∈ [s₁,t₁], E[σ²(u,·) · Z₂] = 0
    have h_inner_zero : ∀ u, u ∈ Set.Icc s₁ t₁ →
        ∫ ω, (X.diffusion u ω) ^ 2 * Z₂ ω ∂μ = 0 := by
      intro u hu
      apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s₂)
      · exact h_diff_Fs₂ u hu
      · exact hZ₂_int
      · -- σ²(u,·) * Z₂ integrable: |σ²| ≤ Mσ², so dominated by Mσ² * |Z₂|
        exact (hZ₂_int.norm.const_mul (Mσ ^ 2)).mono'
          ((h_diff_Fs₂ u hu |>.mono (F.le_ambient s₂) le_rfl
            |>.aestronglyMeasurable).mul hZ₂_int.aestronglyMeasurable)
          (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
            exact mul_le_mul_of_nonneg_right
              (by calc (X.diffusion u ω) ^ 2 = |X.diffusion u ω| ^ 2 := (sq_abs _).symm
                  _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ u ω) 2)
              (abs_nonneg _))
      · exact X.compensated_sq_setIntegral_zero hMσ s₂ t₂ hs₂ hst₂
    -- Sub-step 3c: Pull Z₂(ω) inside the inner integral
    -- (∫_u σ²(u,ω) du) * Z₂(ω) = ∫_u σ²(u,ω) * Z₂(ω) du
    simp_rw [show ∀ ω, (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω =
        ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 * Z₂ ω ∂volume from
      fun ω => (integral_mul_const (Z₂ ω) _).symm]
    -- Sub-step 3d: Swap integrals by Fubini
    set ν := volume.restrict (Icc s₁ t₁)
    -- Product integrability: |σ²(u,ω) * Z₂(ω)| ≤ Mσ² * |Z₂(ω)| is integrable
    have hν_finite : IsFiniteMeasure ν :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    -- AEStronglyMeasurable for the uncurried product function
    have h_meas_σ_sq : Measurable (fun p : Ω × ℝ => (X.diffusion p.2 p.1) ^ 2) :=
      (X.diffusion_jointly_measurable.comp measurable_swap).pow_const 2
    have h_meas_Z₂_fst : AEStronglyMeasurable (fun p : Ω × ℝ => Z₂ p.1) (μ.prod ν) :=
      hZ₂_int.aestronglyMeasurable.comp_fst
    have h_meas_uncurry : AEStronglyMeasurable
        (Function.uncurry (fun ω u => (X.diffusion u ω) ^ 2 * Z₂ ω)) (μ.prod ν) :=
      h_meas_σ_sq.aestronglyMeasurable.mul h_meas_Z₂_fst
    -- Product integrability via domination: |σ²·Z₂| ≤ Mσ²·|Z₂| (integrable on product)
    have h_product_int : Integrable
        (Function.uncurry (fun ω u => (X.diffusion u ω) ^ 2 * Z₂ ω)) (μ.prod ν) := by
      apply Integrable.mono' ((hZ₂_int.norm.const_mul (Mσ ^ 2)).comp_fst (ν := ν))
        h_meas_uncurry
      apply ae_of_all; intro ⟨ω, u⟩
      simp only [Function.uncurry, Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by calc (X.diffusion u ω) ^ 2 = |X.diffusion u ω| ^ 2 := (sq_abs _).symm
            _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ u ω) 2)
        (abs_nonneg _)
    rw [integral_integral_swap h_product_int]
    -- Sub-step 3e: Each inner integral is 0, so the whole integral is 0
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact h_inner_zero u hu
  linarith

/-- Core adapter for orthogonality of compensated squared SI increments. -/
theorem ItoProcessCore.stoch_integral_squared_orthogonal_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₁ t₁ s₂ t₂ : ℝ)
    (hs₁ : 0 ≤ s₁) (hst₁ : s₁ ≤ t₁) (ht₁s₂ : t₁ ≤ s₂) (hst₂ : s₂ ≤ t₂) :
    ∫ ω, ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
           ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) *
          ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
           ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  let R : ItoProcessRegularity X := ItoProcessRegularity.ofSplit C DR D FC
  let Xp : ItoProcess F μ := X.toItoProcess R
  -- Convenience abbreviations and basic facts
  set Z₂ := fun ω => (X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
    ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume
  have hs₂ : 0 ≤ s₂ := le_trans (le_trans hs₁ hst₁) ht₁s₂
  have ht₁ : 0 ≤ t₁ := le_trans hs₁ hst₁
  -- Integrability
  have hΔ₁_sq_int := X.si_increment_sq_integrable_core C DR D FC s₁ t₁ hs₁ hst₁
  have hQ₁_int := X.diffusion_sq_interval_integrable_core C DR D FC s₁ t₁ hs₁ hst₁
  have hZ₂_int := X.compensated_sq_integrable_core C DR D FC s₂ t₂ hs₂ hst₂
  have hZ₂_sq_int := X.compensated_sq_sq_integrable_core C DR D FC hMσ s₂ t₂ hs₂ hst₂
  have hΔ₁_L4 := stoch_integral_increment_L4_integrable_proof Xp hMσ s₁ t₁ hs₁ hst₁
  have hQ₁_bdd := X.diffusion_sq_integral_bound_core hMσ s₁ t₁ hst₁
  -- Δ₁²·Z₂ integrable (AM-GM: |ab| ≤ a² + b², Δ₁⁴ and Z₂² integrable)
  have hΔ₁_sq_Z₂_int : Integrable (fun ω =>
      (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω) μ := by
    have hdom : Integrable (fun ω =>
        (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 + Z₂ ω ^ 2) μ :=
      hΔ₁_L4.add hZ₂_sq_int
    exact hdom.mono'
      (hΔ₁_sq_int.aestronglyMeasurable.mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (sq_nonneg (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω))]
        have h4eq : (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 4 =
            ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2) ^ 2 := by ring
        rw [h4eq]
        nlinarith [sq_nonneg ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 - |Z₂ ω|),
          sq_abs (Z₂ ω)])
  -- Q₁·Z₂ integrable (Q₁ bounded, Z₂ integrable)
  have hQ₁_Z₂_int : Integrable (fun ω =>
      (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω) μ := by
    set C₁ := Mσ ^ 2 * (t₁ - s₁)
    exact (hZ₂_int.norm.const_mul C₁).mono'
      (hQ₁_int.aestronglyMeasurable.mul hZ₂_int.aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hQ₁_bdd ω) (abs_nonneg _))
  -- Step 1: Decompose ∫ (Δ₁²-Q₁)·Z₂ = ∫ Δ₁²·Z₂ - ∫ Q₁·Z₂
  have hdecomp : (fun ω => ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
      ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) *
      ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
       ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume)) =
      (fun ω => (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω -
        (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω) := by
    ext ω; ring
  rw [hdecomp, integral_sub hΔ₁_sq_Z₂_int hQ₁_Z₂_int]
  -- Step 2: E[Δ₁²·Z₂] = 0 by martingale orthogonality + conditional isometry
  have h_part1 : ∫ ω, (X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 * Z₂ ω ∂μ = 0 := by
    apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s₂)
    · exact ((Xp.stoch_integral_adapted t₁ ht₁).sub
          ((Xp.stoch_integral_adapted s₁ hs₁).mono (F.mono s₁ t₁ hst₁) le_rfl)).pow_const 2
          |>.mono (F.mono t₁ s₂ ht₁s₂) le_rfl
    · exact hZ₂_int
    · exact hΔ₁_sq_Z₂_int
    · exact X.compensated_sq_setIntegral_zero_core C DR D FC hMσ s₂ t₂ hs₂ hst₂
  -- Step 3: E[Q₁·Z₂] = 0 by Fubini + pointwise orthogonality
  have h_part2 : ∫ ω, (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω ∂μ = 0 := by
    have h_diff_Fs₂ : ∀ u, u ∈ Set.Icc s₁ t₁ →
        @Measurable Ω ℝ (F.σ_algebra s₂) _ (fun ω => (X.diffusion u ω) ^ 2) := by
      intro u ⟨_, hut⟩
      exact ((D.diffusion_adapted u).mono (F.mono u s₂ (le_trans hut ht₁s₂)) le_rfl).pow_const 2
    have h_inner_zero : ∀ u, u ∈ Set.Icc s₁ t₁ →
        ∫ ω, (X.diffusion u ω) ^ 2 * Z₂ ω ∂μ = 0 := by
      intro u hu
      apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s₂)
      · exact h_diff_Fs₂ u hu
      · exact hZ₂_int
      · exact (hZ₂_int.norm.const_mul (Mσ ^ 2)).mono'
          ((h_diff_Fs₂ u hu |>.mono (F.le_ambient s₂) le_rfl
            |>.aestronglyMeasurable).mul hZ₂_int.aestronglyMeasurable)
          (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
            exact mul_le_mul_of_nonneg_right
              (by calc (X.diffusion u ω) ^ 2 = |X.diffusion u ω| ^ 2 := (sq_abs _).symm
                  _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ u ω) 2)
              (abs_nonneg _))
      · exact X.compensated_sq_setIntegral_zero_core C DR D FC hMσ s₂ t₂ hs₂ hst₂
    simp_rw [show ∀ ω, (∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) * Z₂ ω =
        ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 * Z₂ ω ∂volume from
      fun ω => (integral_mul_const (Z₂ ω) _).symm]
    set ν := volume.restrict (Icc s₁ t₁)
    have hν_finite : IsFiniteMeasure ν :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have h_meas_σ_sq : Measurable (fun p : Ω × ℝ => (X.diffusion p.2 p.1) ^ 2) :=
      (D.diffusion_jointly_measurable.comp measurable_swap).pow_const 2
    have h_meas_Z₂_fst : AEStronglyMeasurable (fun p : Ω × ℝ => Z₂ p.1) (μ.prod ν) :=
      hZ₂_int.aestronglyMeasurable.comp_fst
    have h_meas_uncurry : AEStronglyMeasurable
        (Function.uncurry (fun ω u => (X.diffusion u ω) ^ 2 * Z₂ ω)) (μ.prod ν) :=
      h_meas_σ_sq.aestronglyMeasurable.mul h_meas_Z₂_fst
    have h_product_int : Integrable
        (Function.uncurry (fun ω u => (X.diffusion u ω) ^ 2 * Z₂ ω)) (μ.prod ν) := by
      apply Integrable.mono' ((hZ₂_int.norm.const_mul (Mσ ^ 2)).comp_fst (ν := ν))
        h_meas_uncurry
      apply ae_of_all; intro ⟨ω, u⟩
      simp only [Function.uncurry, Real.norm_eq_abs]
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by calc (X.diffusion u ω) ^ 2 = |X.diffusion u ω| ^ 2 := (sq_abs _).symm
            _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ u ω) 2)
        (abs_nonneg _)
    rw [integral_integral_swap h_product_int]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact h_inner_zero u hu
  linarith

/-- Regularity-first adapter for conditional compensated-square set-integral zero. -/
theorem ItoProcessCore.compensated_sq_setIntegral_zero_core_ofRegularity
    {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₂ t₂ : ℝ) (hs₂ : 0 ≤ s₂) (hst₂ : s₂ ≤ t₂)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s₂) A) :
    ∫ ω in A, ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
               ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  simpa using
    (X.compensated_sq_setIntegral_zero_core
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      hMσ s₂ t₂ hs₂ hst₂ A hA)

/-- Regularity-first adapter for orthogonality of compensated squared increments. -/
theorem ItoProcessCore.stoch_integral_squared_orthogonal_core_ofRegularity
    {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s₁ t₁ s₂ t₂ : ℝ)
    (hs₁ : 0 ≤ s₁) (hst₁ : s₁ ≤ t₁) (ht₁s₂ : t₁ ≤ s₂) (hst₂ : s₂ ≤ t₂) :
    ∫ ω, ((X.stoch_integral t₁ ω - X.stoch_integral s₁ ω) ^ 2 -
           ∫ u in Icc s₁ t₁, (X.diffusion u ω) ^ 2 ∂volume) *
          ((X.stoch_integral t₂ ω - X.stoch_integral s₂ ω) ^ 2 -
           ∫ u in Icc s₂ t₂, (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 := by
  simpa using
    (X.stoch_integral_squared_orthogonal_core
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      hMσ s₁ t₁ s₂ t₂ hs₁ hst₁ ht₁s₂ hst₂)

end SPDE
