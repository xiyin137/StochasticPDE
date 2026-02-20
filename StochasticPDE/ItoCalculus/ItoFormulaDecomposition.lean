/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.StochasticIntegration
import StochasticPDE.ItoCalculus.ItoFormulaInfrastructure
import StochasticPDE.ItoCalculus.QuarticBound
import StochasticPDE.ItoCalculus.QuadraticVariation
import StochasticPDE.ItoCalculus.QVConvergence
import StochasticPDE.ItoCalculus.IsometryTheorems
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Itô Formula Decomposition Infrastructure

Sub-lemmas for the Itô formula L² convergence proof.

## Key results

1. `integral_mul_eq_zero_of_setIntegral_eq_zero` — Martingale orthogonality
2. `simple_bilinear_isometry_different_times` — E[S(t)·S(s)] = E[S(s)²]
3. `stoch_integral_increment_L2_bound` — E[|SI(t) - SI(s)|²] ≤ Mσ²·(t-s)
4. `ito_process_increment_L2_bound` — E[|X(t)-X(s)|²] ≤ C·(t-s)
-/

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal

noncomputable section

namespace SPDE

variable {Ω : Type*} [instΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Square integrability of simple stochastic integrals -/

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-- Simple stochastic integrals of bounded adapted processes are square-integrable. -/
theorem stochasticIntegral_at_sq_integrable
    (H : SimpleProcess F) (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (H.stochasticIntegral_at W t ω) ^ 2) μ := by
  have h := stochasticIntegral_at_sub_sq_integrable H W hH_adapted hH_bdd hH_times_nn
    (fun _ => 0) (integrable_const 0) (by simp) t ht
  simp only [sub_zero] at h; exact h

/-- Simple stochastic integrals at time s are measurable w.r.t. the filtration at time s.
    Uses the min-capped reformulation: S(s) = Σ Hᵢ·ΔWᵢ_cap(s) where each summand
    only involves BM values at times ≤ s. -/
theorem stochasticIntegral_at_filtration_measurable
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (_hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s : ℝ) (_hs : 0 ≤ s) :
    @Measurable Ω ℝ (W.F.σ_algebra s) _ (H.stochasticIntegral_at W s) := by
  -- Rewrite as min-capped form
  have heq : H.stochasticIntegral_at W s = fun ω =>
      ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
        H.values i ω * (W.process (min (H.times ⟨i + 1, h⟩) s) ω -
                         W.process (min (H.times i) s) ω)
      else 0 := by
    ext ω; exact H.stochasticIntegral_at_eq_min W s ω
  rw [heq]
  -- Sum of measurable functions is measurable
  apply Finset.measurable_sum
  intro i _
  by_cases hi : (i : ℕ) + 1 < H.n
  · simp only [dif_pos hi]
    by_cases hts : H.times i ≤ s
    · -- t_i ≤ s: H_i is F_{t_i}-meas ≤ F_s, BM values at times ≤ s are F_s-meas
      exact ((hH_adapted i).mono (W.F.mono _ _ hts) le_rfl).mul
        (((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_right _ _)) le_rfl).sub
         ((W.toAdapted.adapted _).mono (W.F.mono _ _ (min_le_right _ _)) le_rfl))
    · -- t_i > s: increment = W(s)-W(s) = 0, so product = 0
      push_neg at hts
      have h1 : min (H.times i) s = s := min_eq_right (le_of_lt hts)
      have h2 : min (H.times ⟨i + 1, hi⟩) s = s :=
        min_eq_right (le_trans (le_of_lt hts)
          (le_of_lt (H.increasing i ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))))
      have : (fun ω => H.values i ω * (W.process (min (H.times ⟨i + 1, hi⟩) s) ω -
                         W.process (min (H.times i) s) ω)) = fun _ => 0 := by
        ext ω; rw [h1, h2, sub_self, mul_zero]
      rw [this]; exact measurable_const
  · simp only [dif_neg hi]; exact measurable_const

end SimpleProcess

/-! ## Martingale orthogonality via conditional expectation

If ∫_A Y = 0 for all A ∈ m, and X is m-measurable, Y integrable, X*Y integrable,
then ∫ X·Y = 0. Proof: condExp m μ Y = 0 a.e. → condExp m μ (X·Y) = X · 0 = 0 a.e.
→ ∫ X·Y = ∫ condExp(X·Y) = 0. -/

/-- Martingale orthogonality: if ∫_A Y = 0 for all A ∈ m, X is m-measurable,
    and X·Y is integrable, then ∫ X·Y = 0. -/
theorem integral_mul_eq_zero_of_setIntegral_eq_zero
    {m : MeasurableSpace Ω}
    (hm : m ≤ instΩ)
    {X Y : Ω → ℝ}
    (hX_meas : @Measurable Ω ℝ m _ X)
    (hY_int : Integrable Y μ)
    (hXY_int : Integrable (fun ω => X ω * Y ω) μ)
    [IsProbabilityMeasure μ]
    (hset : ∀ A : Set Ω, @MeasurableSet Ω m A → ∫ ω in A, Y ω ∂μ = 0) :
    ∫ ω, X ω * Y ω ∂μ = 0 := by
  -- SigmaFinite (μ.trim hm) holds since μ is a probability measure
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  -- Step 1: condExp m μ Y = 0 a.e.
  -- Use uniqueness: 0 satisfies the defining property of condExp m μ Y
  have hcondY0 : (0 : Ω → ℝ) =ᵐ[μ] μ[Y | m] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hY_int
    · intro s _ _; exact integrableOn_zero
    · intro s hs _
      simp only [Pi.zero_apply, integral_zero]
      exact (hset s hs).symm
    · exact aestronglyMeasurable_zero
  have hcondY : μ[Y | m] =ᵐ[μ] (0 : Ω → ℝ) := hcondY0.symm
  -- Step 2: condExp m μ (X·Y) =ᵐ X · condExp m μ Y =ᵐ 0
  have hX_asm : AEStronglyMeasurable[m] X μ :=
    (hX_meas.stronglyMeasurable).aestronglyMeasurable
  -- Pull-out: μ[X * Y | m] =ᵐ X * μ[Y | m]
  have hXY_eq : (fun ω => X ω * Y ω) = X * Y := rfl
  have hpull : μ[X * Y | m] =ᵐ[μ] X * μ[Y | m] :=
    condExp_mul_of_aestronglyMeasurable_left hX_asm (by rwa [← hXY_eq]) hY_int
  -- X * condExp Y =ᵐ X * 0 = 0
  have hXcond0 : X * μ[Y | m] =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [hcondY] with ω hω
    simp only [Pi.mul_apply, Pi.zero_apply, hω, mul_zero]
  have hcond0 : μ[X * Y | m] =ᵐ[μ] (0 : Ω → ℝ) := hpull.trans hXcond0
  -- Step 3: ∫ X·Y = ∫ condExp(X·Y) = ∫ 0 = 0
  calc ∫ ω, X ω * Y ω ∂μ
      = ∫ ω, (X * Y) ω ∂μ := by rfl
    _ = ∫ ω, μ[X * Y | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, (0 : Ω → ℝ) ω ∂μ := integral_congr_ae hcond0
    _ = 0 := by simp

/-! ## Bilinear isometry at different times -/

/-- E[S(t)·S(s)] = E[S(s)²] for s ≤ t. The increment S(t)-S(s) is orthogonal
    to S(s) by the martingale property and the orthogonality lemma. -/
theorem simple_bilinear_isometry_different_times
    {F : Filtration Ω ℝ} (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (H.stochasticIntegral_at W t ω) * (H.stochasticIntegral_at W s ω) ∂μ =
    ∫ ω, (H.stochasticIntegral_at W s ω)^2 ∂μ := by
  -- S(t) = S(s) + (S(t)-S(s)), so S(t)·S(s) = S(s)² + (S(t)-S(s))·S(s)
  have hdecomp : ∀ ω, H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω =
      (H.stochasticIntegral_at W s ω) ^ 2 +
      (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
       H.stochasticIntegral_at W s ω := by
    intro ω; ring
  simp_rw [hdecomp]
  -- Integrability
  have hS_s_int : Integrable (H.stochasticIntegral_at W s) μ :=
    SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  have hS_t_int : Integrable (H.stochasticIntegral_at W t) μ :=
    SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
  have hS_sq_int : Integrable (fun ω => (H.stochasticIntegral_at W s ω) ^ 2) μ :=
    SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  -- Cross term integrability: (S(t)-S(s))·S(s) integrable via AM-GM bound
  have hcross_int : Integrable (fun ω =>
      (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
      H.stochasticIntegral_at W s ω) μ := by
    have hSt_sq := SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
    apply Integrable.mono' ((hSt_sq.add hS_sq_int).add hS_sq_int)
    · exact (hS_t_int.sub hS_s_int).aestronglyMeasurable.mul hS_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      set a := H.stochasticIntegral_at W t ω
      set b := H.stochasticIntegral_at W s ω
      rw [abs_mul]
      nlinarith [sq_abs (a - b), sq_abs b, sq_abs a, sq_nonneg (|a - b| - |b|)]
  rw [integral_add hS_sq_int hcross_int]
  -- Suffices to show cross term = 0
  suffices hcross : ∫ ω, (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
      H.stochasticIntegral_at W s ω ∂μ = 0 by linarith
  -- Rewrite as ∫ S(s) · (S(t)-S(s)) by commutativity
  have hcomm : (fun ω => (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) *
      H.stochasticIntegral_at W s ω) =
      (fun ω => H.stochasticIntegral_at W s ω *
      (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω)) := by
    ext ω; ring
  rw [hcomm]
  -- Apply orthogonality: S(s) is F_s-measurable, S(t)-S(s) has zero set-integrals
  apply integral_mul_eq_zero_of_setIntegral_eq_zero (W.F.le_ambient s)
  · -- S(s) is F_s-measurable
    exact SimpleProcess.stochasticIntegral_at_filtration_measurable H W hH_adapted hH_times_nn s hs
  · -- S(t)-S(s) is integrable
    exact hS_t_int.sub hS_s_int
  · -- S(s)·(S(t)-S(s)) is integrable
    rw [← hcomm]; exact hcross_int
  · -- ∫_A (S(t)-S(s)) = 0 for all A ∈ F_s (martingale property)
    intro A hA
    rw [integral_sub (hS_t_int.integrableOn) (hS_s_int.integrableOn)]
    exact sub_eq_zero.mpr
      (SimpleProcess.stochasticIntegral_at_martingale H W hH_adapted hH_bdd hH_times_nn s t hs hst A hA)

/-- E[|S(t)-S(s)|²] = E[S(t)²] - E[S(s)²] for s ≤ t. -/
theorem simple_increment_L2 {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    [IsProbabilityMeasure μ]
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    (hH_bdd : ∀ i : Fin H.n, ∃ C : ℝ, ∀ ω, |H.values i ω| ≤ C)
    (hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω)^2 ∂μ =
    ∫ ω, (H.stochasticIntegral_at W t ω)^2 ∂μ -
    ∫ ω, (H.stochasticIntegral_at W s ω)^2 ∂μ := by
  -- Integrability
  have hS_s_int := SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  have hS_t_int := SimpleProcess.stochasticIntegral_at_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
  have hS_s_sq := SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn s hs
  have hS_t_sq := SimpleProcess.stochasticIntegral_at_sq_integrable H W hH_adapted hH_bdd hH_times_nn t (le_trans hs hst)
  -- Product S_t * S_s is integrable (|ab| ≤ (a²+b²)/2)
  have hprod_int : Integrable (fun ω =>
      H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω) μ := by
    apply Integrable.mono' (hS_t_sq.add hS_s_sq)
    · exact hS_t_int.aestronglyMeasurable.mul hS_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_mul]
      nlinarith [sq_abs (H.stochasticIntegral_at W t ω),
        sq_abs (H.stochasticIntegral_at W s ω),
        sq_nonneg (|H.stochasticIntegral_at W t ω| - |H.stochasticIntegral_at W s ω|)]
  -- Bilinear isometry: E[S_t·S_s] = E[S_s²]
  have hbil := simple_bilinear_isometry_different_times H W hH_adapted hH_bdd hH_times_nn s t hs hst
  -- Expand (a-b)² = a² + b² - 2ab pointwise, then split the integral
  have h_pw : ∫ ω, (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) ^ 2 ∂μ =
      ∫ ω, (H.stochasticIntegral_at W t ω ^ 2 + H.stochasticIntegral_at W s ω ^ 2 -
      2 * (H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω)) ∂μ :=
    integral_congr_ae (ae_of_all _ (fun ω => by ring))
  -- Split integrals using have lemmas (avoids rw pattern-matching issues)
  have h_sub := integral_sub (hS_t_sq.add hS_s_sq) (hprod_int.const_mul 2)
  have h_add := integral_add hS_t_sq hS_s_sq
  have h_mul := integral_const_mul (μ := μ) (2 : ℝ)
    (fun ω => H.stochasticIntegral_at W t ω * H.stochasticIntegral_at W s ω)
  -- Normalize function-level to value-level
  simp only [Pi.add_apply] at h_sub h_add
  -- Chain: ∫(a-b)² = ∫(a²+b²-2ab) = (∫a²+∫b²) - 2∫(ab) = ∫a²+∫b²-2∫b² = ∫a²-∫b²
  linarith

/-! ## Stochastic integral increment L² bound -/

/-- E[|SI(t) - SI(s)|²] ≤ Mσ² · (t - s) for ItoProcess with bounded diffusion. -/
theorem stoch_integral_increment_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω)^2 ∂μ ≤
    Mσ^2 * (t - s) := by
  -- Step 1: Apply the Itô isometry (now a proved theorem)
  have hiso := X.stoch_integral_isometry s t hs hst
  -- Step 2: Bound ∫_Ω ∫_{[s,t]} σ² ≤ Mσ²·(t-s) using pointwise bounds
  calc ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ
      = ∫ ω, (∫ u in Set.Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := hiso
    _ ≤ ∫ ω, (Mσ ^ 2 * (t - s)) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun ω => integral_nonneg (fun u => sq_nonneg _)
        · exact integrable_const _
        · exact ae_of_all _ fun ω => by
            calc ∫ u in Set.Icc s t, (X.diffusion u ω) ^ 2 ∂volume
                ≤ ∫ u in Set.Icc s t, Mσ ^ 2 ∂volume := by
                  apply setIntegral_mono_on
                    (X.diffusion_sq_time_integrable ω t (le_trans hs hst) |>.mono_set
                      (Set.Icc_subset_Icc_left hs))
                    (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
                    measurableSet_Icc
                    (fun u _ => sq_le_sq' (abs_le.mp (hMσ u ω)).1 (abs_le.mp (hMσ u ω)).2)
              _ = Mσ ^ 2 * (t - s) := by
                  rw [setIntegral_const]
                  simp only [Measure.real, Real.volume_Icc,
                    ENNReal.toReal_ofReal (sub_nonneg.mpr hst), smul_eq_mul]
                  ring
    _ = Mσ ^ 2 * (t - s) := by
        simp [integral_const, Measure.real, measure_univ, ENNReal.toReal_one]

/-! ## Process increment moment bounds -/

/-- E[|X(t) - X(s)|²] ≤ C · (t - s) for bounded coefficients. -/
theorem ito_process_increment_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (hdt : t - s ≤ 1) :
    ∫ ω, (X.process t ω - X.process s ω)^2 ∂μ ≤
    (2 * Mμ^2 + 2 * Mσ^2) * (t - s) := by
  -- Abbreviations
  set D : Ω → ℝ := fun ω =>
    ∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
    ∫ u in Set.Icc 0 s, X.drift u ω ∂volume with hD_def
  set S : Ω → ℝ := fun ω => X.stoch_integral t ω - X.stoch_integral s ω with hS_def
  -- Step 1: X(t) - X(s) = D + S a.e.
  have hdecomp : ∀ᵐ ω ∂μ, X.process t ω - X.process s ω = D ω + S ω := by
    filter_upwards [X.integral_form t (le_trans hs hst), X.integral_form s hs] with ω hωt hωs
    simp only [D, S]; linarith
  -- Step 2: Pointwise drift bound |D(ω)| ≤ Mμ·(t-s)
  have hD_bdd : ∀ ω, |D ω| ≤ Mμ * (t - s) := by
    intro ω
    have hint_t : IntegrableOn (fun u => X.drift u ω) (Set.Icc 0 t) volume :=
      X.drift_time_integrable ω t (le_trans hs hst)
    -- D(ω) = ∫_{Icc 0 t \ Icc 0 s} drift u ω dv
    have hD_eq : D ω = ∫ u in Set.Icc 0 t \ Set.Icc 0 s, X.drift u ω ∂volume :=
      (integral_diff measurableSet_Icc hint_t (Set.Icc_subset_Icc_right hst)).symm
    rw [hD_eq]
    -- volume(diff) is finite
    have hvol_ne_top : volume (Set.Icc 0 t \ Set.Icc 0 s) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.diff_subset)
    -- |∫_{diff} drift| ≤ Mμ · volume.real(diff)
    have hbnd : ‖∫ u in Set.Icc 0 t \ Set.Icc 0 s, X.drift u ω ∂volume‖ ≤
        Mμ * volume.real (Set.Icc 0 t \ Set.Icc 0 s) :=
      norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hvol_ne_top)
        fun u _ => Real.norm_eq_abs _ ▸ hMμ u ω
    rw [Real.norm_eq_abs] at hbnd
    -- volume.real(Icc 0 t \ Icc 0 s) = t - s
    have h_fin_s : volume (Set.Icc 0 s) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hvol_eq : volume.real (Set.Icc 0 t \ Set.Icc 0 s) = t - s := by
      show (volume (Set.Icc 0 t \ Set.Icc 0 s)).toReal = t - s
      rw [measure_diff (Set.Icc_subset_Icc_right hst) measurableSet_Icc.nullMeasurableSet h_fin_s]
      rw [Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero]
      rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_ofReal hst) ENNReal.ofReal_ne_top]
      rw [ENNReal.toReal_ofReal (le_trans hs hst), ENNReal.toReal_ofReal hs]
    rw [hvol_eq] at hbnd; linarith
  -- Step 3: D²(ω) ≤ Mμ²·(t-s)²
  have hD_sq_bdd : ∀ ω, D ω ^ 2 ≤ Mμ ^ 2 * (t - s) ^ 2 := fun ω => by
    have h := abs_le.mp (hD_bdd ω)
    calc D ω ^ 2 ≤ (Mμ * (t - s)) ^ 2 := sq_le_sq' h.1 h.2
      _ = Mμ ^ 2 * (t - s) ^ 2 := by ring
  -- Step 4: D is AEStronglyMeasurable (= X(t)-X(s)-S a.e., which is measurable)
  have hD_asm : AEStronglyMeasurable D μ := by
    have hXt : AEStronglyMeasurable (X.process t) μ :=
      ((X.process_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable
    have hXs : AEStronglyMeasurable (X.process s) μ :=
      ((X.process_adapted s).mono (F.le_ambient s) le_rfl).aestronglyMeasurable
    have hSt : AEStronglyMeasurable (X.stoch_integral t) μ :=
      ((X.stoch_integral_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable
    have hSs : AEStronglyMeasurable (X.stoch_integral s) μ :=
      ((X.stoch_integral_adapted s).mono (F.le_ambient s) le_rfl).aestronglyMeasurable
    exact ((hXt.sub hXs).sub (hSt.sub hSs)).congr
      (hdecomp.mono fun ω hω => by simp only [D, S, Pi.sub_apply] at hω ⊢; linarith)
  -- Step 5: D² integrable (bounded on probability space)
  have hD_sq_int : Integrable (fun ω => D ω ^ 2) μ :=
    (integrable_const (Mμ ^ 2 * (t - s) ^ 2)).mono' (hD_asm.pow 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hD_sq_bdd ω)
  -- Step 6: S² integrable
  have hS_sq_int : Integrable (fun ω => S ω ^ 2) μ := by
    show Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ
    have hSt_sq := X.stoch_integral_sq_integrable t (le_trans hs hst)
    have hSs_sq := X.stoch_integral_sq_integrable s hs
    exact ((hSt_sq.add hSs_sq).const_mul 2).mono'
      (((X.stoch_integral_adapted t).mono (F.le_ambient t) le_rfl |>.aestronglyMeasurable).sub
        ((X.stoch_integral_adapted s).mono (F.le_ambient s) le_rfl |>.aestronglyMeasurable)
        |>.pow 2)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs, Pi.add_apply]
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (X.stoch_integral t ω + X.stoch_integral s ω)])
  -- Step 7: E[S²] ≤ Mσ²·(t-s)
  have hSI := stoch_integral_increment_L2_bound X hMσ s t hs hst
  -- Step 8: E[D²] ≤ Mμ²·(t-s)²
  have hE_D_sq : ∫ ω, D ω ^ 2 ∂μ ≤ Mμ ^ 2 * (t - s) ^ 2 := by
    calc ∫ ω, D ω ^ 2 ∂μ
        ≤ ∫ ω, (Mμ ^ 2 * (t - s) ^ 2 : ℝ) ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
            (integrable_const _) (ae_of_all _ fun ω => hD_sq_bdd ω)
      _ = Mμ ^ 2 * (t - s) ^ 2 := by
          simp [integral_const, Measure.real, measure_univ, ENNReal.toReal_one]
  -- Step 9: Combine via (a+b)² ≤ 2a² + 2b² and split integrals
  calc ∫ ω, (X.process t ω - X.process s ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * D ω ^ 2 + 2 * S ω ^ 2) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun ω => sq_nonneg _
        · exact (hD_sq_int.const_mul 2).add (hS_sq_int.const_mul 2)
        · filter_upwards [hdecomp] with ω hω
          rw [hω]; nlinarith [sq_nonneg (D ω - S ω)]
    _ = 2 * ∫ ω, D ω ^ 2 ∂μ + 2 * ∫ ω, S ω ^ 2 ∂μ := by
        rw [integral_add (hD_sq_int.const_mul 2) (hS_sq_int.const_mul 2)]
        rw [integral_const_mul, integral_const_mul]
    _ ≤ 2 * (Mμ ^ 2 * (t - s) ^ 2) + 2 * (Mσ ^ 2 * (t - s)) :=
        add_le_add (mul_le_mul_of_nonneg_left hE_D_sq (by norm_num))
          (mul_le_mul_of_nonneg_left hSI (by norm_num))
    _ ≤ (2 * Mμ ^ 2 + 2 * Mσ ^ 2) * (t - s) := by
        have hts_sq : (t - s) ^ 2 ≤ (t - s) := by nlinarith [sub_nonneg.mpr hst]
        have h := mul_le_mul_of_nonneg_left hts_sq (sq_nonneg Mμ)
        nlinarith

/-- The fourth moment of the stochastic integral increment is integrable. -/
theorem stoch_integral_increment_L4_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω)^4) μ :=
  stoch_integral_increment_L4_integrable_proof X hMσ s t hs hst

/-- E[(SI(t) - SI(s))⁴] ≤ 3 Mσ⁴ (t - s)² for bounded diffusion.
    This is a consequence of the BDG inequality / quartic moment bound for
    stochastic integrals of bounded integrands. -/
theorem stoch_integral_increment_L4_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω)^4 ∂μ ≤
    3 * Mσ^4 * (t - s)^2 :=
  stoch_integral_increment_L4_bound_proof X hMσ s t hs hst

/-- E[|X(t) - X(s)|⁴] ≤ C · (t - s)² for bounded coefficients. -/
theorem ito_process_increment_L4_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (hdt : t - s ≤ 1) :
    ∫ ω, (X.process t ω - X.process s ω)^4 ∂μ ≤
    (8 * Mμ^4 + 8 * 3 * Mσ^4) * (t - s)^2 := by
  -- Abbreviations (same decomposition as L2 bound)
  set D : Ω → ℝ := fun ω =>
    ∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
    ∫ u in Set.Icc 0 s, X.drift u ω ∂volume with hD_def
  set S : Ω → ℝ := fun ω => X.stoch_integral t ω - X.stoch_integral s ω with hS_def
  -- Step 1: X(t) - X(s) = D + S a.e.
  have hdecomp : ∀ᵐ ω ∂μ, X.process t ω - X.process s ω = D ω + S ω := by
    filter_upwards [X.integral_form t (le_trans hs hst), X.integral_form s hs] with ω hωt hωs
    simp only [D, S]; linarith
  -- Step 2: Drift bound |D(ω)| ≤ Mμ·(t-s), hence D⁴ ≤ Mμ⁴·(t-s)⁴
  have hD_bdd : ∀ ω, |D ω| ≤ Mμ * (t - s) := by
    intro ω
    have hint_t : IntegrableOn (fun u => X.drift u ω) (Set.Icc 0 t) volume :=
      X.drift_time_integrable ω t (le_trans hs hst)
    have hD_eq : D ω = ∫ u in Set.Icc 0 t \ Set.Icc 0 s, X.drift u ω ∂volume :=
      (integral_diff measurableSet_Icc hint_t (Set.Icc_subset_Icc_right hst)).symm
    rw [hD_eq]
    have hvol_ne_top : volume (Set.Icc 0 t \ Set.Icc 0 s) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.diff_subset)
    have hbnd : ‖∫ u in Set.Icc 0 t \ Set.Icc 0 s, X.drift u ω ∂volume‖ ≤
        Mμ * volume.real (Set.Icc 0 t \ Set.Icc 0 s) :=
      norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hvol_ne_top)
        fun u _ => Real.norm_eq_abs _ ▸ hMμ u ω
    rw [Real.norm_eq_abs] at hbnd
    have h_fin_s : volume (Set.Icc 0 s) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hvol_eq : volume.real (Set.Icc 0 t \ Set.Icc 0 s) = t - s := by
      show (volume (Set.Icc 0 t \ Set.Icc 0 s)).toReal = t - s
      rw [measure_diff (Set.Icc_subset_Icc_right hst) measurableSet_Icc.nullMeasurableSet h_fin_s]
      rw [Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero]
      rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_ofReal hst) ENNReal.ofReal_ne_top]
      rw [ENNReal.toReal_ofReal (le_trans hs hst), ENNReal.toReal_ofReal hs]
    rw [hvol_eq] at hbnd; linarith
  have hD_fourth_bdd : ∀ ω, D ω ^ 4 ≤ Mμ ^ 4 * (t - s) ^ 4 := fun ω => by
    have h := abs_le.mp (hD_bdd ω)
    calc D ω ^ 4 = (D ω ^ 2) ^ 2 := by ring
      _ ≤ ((Mμ * (t - s)) ^ 2) ^ 2 := by
          apply sq_le_sq'
          · linarith [sq_nonneg (D ω), sq_nonneg (Mμ * (t - s)),
                       sq_le_sq' h.1 h.2]
          · exact sq_le_sq' h.1 h.2
      _ = Mμ ^ 4 * (t - s) ^ 4 := by ring
  -- Step 3: D is AEStronglyMeasurable
  have hD_asm : AEStronglyMeasurable D μ := by
    have hXt : AEStronglyMeasurable (X.process t) μ :=
      ((X.process_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable
    have hXs : AEStronglyMeasurable (X.process s) μ :=
      ((X.process_adapted s).mono (F.le_ambient s) le_rfl).aestronglyMeasurable
    have hSt : AEStronglyMeasurable (X.stoch_integral t) μ :=
      ((X.stoch_integral_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable
    have hSs : AEStronglyMeasurable (X.stoch_integral s) μ :=
      ((X.stoch_integral_adapted s).mono (F.le_ambient s) le_rfl).aestronglyMeasurable
    exact ((hXt.sub hXs).sub (hSt.sub hSs)).congr
      (hdecomp.mono fun ω hω => by simp only [D, S, Pi.sub_apply] at hω ⊢; linarith)
  -- Step 4: D⁴ integrable (bounded on probability space)
  have hD_fourth_int : Integrable (fun ω => D ω ^ 4) μ :=
    (integrable_const (Mμ ^ 4 * (t - s) ^ 4)).mono' (hD_asm.pow 4)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hD_fourth_bdd ω)
  -- Step 5: S⁴ integrable (from helper)
  have hS_fourth_int : Integrable (fun ω => S ω ^ 4) μ :=
    stoch_integral_increment_L4_integrable X hMσ s t hs hst
  -- Step 6: E[D⁴] ≤ Mμ⁴·(t-s)⁴
  have hE_D4 : ∫ ω, D ω ^ 4 ∂μ ≤ Mμ ^ 4 * (t - s) ^ 4 := by
    calc ∫ ω, D ω ^ 4 ∂μ
        ≤ ∫ ω, (Mμ ^ 4 * (t - s) ^ 4 : ℝ) ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => by positivity)
            (integrable_const _) (ae_of_all _ fun ω => hD_fourth_bdd ω)
      _ = Mμ ^ 4 * (t - s) ^ 4 := by
          simp [integral_const, Measure.real, measure_univ, ENNReal.toReal_one]
  -- Step 7: E[S⁴] ≤ 3Mσ⁴·(t-s)² (from helper)
  have hE_S4 := stoch_integral_increment_L4_bound X hMσ s t hs hst
  -- Step 8: (t-s)⁴ ≤ (t-s)² since t-s ≤ 1
  have hts_nn : 0 ≤ t - s := sub_nonneg.mpr hst
  have hts4_le_ts2 : (t - s) ^ 4 ≤ (t - s) ^ 2 := by
    calc (t - s) ^ 4 = (t - s) ^ 2 * (t - s) ^ 2 := by ring
      _ ≤ (t - s) ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          calc (t - s) ^ 2 = (t - s) * (t - s) := by ring
            _ ≤ 1 * 1 := mul_le_mul hdt (le_trans hdt (le_refl _)) hts_nn zero_le_one
            _ = 1 := one_mul 1
      _ = (t - s) ^ 2 := mul_one _
  -- Step 9: (a+b)⁴ ≤ 8(a⁴+b⁴)
  -- Proof: 8(a⁴+b⁴)-(a+b)⁴ = (a-b)²(7a²+10ab+7b²) ≥ 0 is complex;
  -- Instead use: |a+b|⁴ = ((a+b)²)² ≤ (2a²+2b²)² = 4(a²+b²)² ≤ 4·2(a⁴+b⁴) = 8(a⁴+b⁴)
  have h_fourth_split : ∀ ω, (D ω + S ω) ^ 4 ≤ 8 * (D ω ^ 4 + S ω ^ 4) := fun ω => by
    have h1 : (D ω + S ω) ^ 2 ≤ 2 * D ω ^ 2 + 2 * S ω ^ 2 := by
      nlinarith [sq_nonneg (D ω - S ω)]
    have h2 : (2 * D ω ^ 2 + 2 * S ω ^ 2) ^ 2 ≤ 8 * (D ω ^ 4 + S ω ^ 4) := by
      nlinarith [sq_nonneg (D ω ^ 2 - S ω ^ 2)]
    calc (D ω + S ω) ^ 4 = ((D ω + S ω) ^ 2) ^ 2 := by ring
      _ ≤ (2 * D ω ^ 2 + 2 * S ω ^ 2) ^ 2 := by
          apply sq_le_sq'
          · linarith [sq_nonneg (D ω), sq_nonneg (S ω), sq_nonneg (D ω + S ω)]
          · exact h1
      _ ≤ 8 * (D ω ^ 4 + S ω ^ 4) := h2
  -- Step 10: Combine
  calc ∫ ω, (X.process t ω - X.process s ω) ^ 4 ∂μ
      ≤ ∫ ω, (8 * (D ω ^ 4 + S ω ^ 4)) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun ω => by positivity
        · exact ((hD_fourth_int.add hS_fourth_int).const_mul 8)
        · filter_upwards [hdecomp] with ω hω
          rw [hω]; exact h_fourth_split ω
    _ = 8 * (∫ ω, D ω ^ 4 ∂μ + ∫ ω, S ω ^ 4 ∂μ) := by
        rw [integral_const_mul, integral_add hD_fourth_int hS_fourth_int]
    _ ≤ 8 * (Mμ ^ 4 * (t - s) ^ 4 + 3 * Mσ ^ 4 * (t - s) ^ 2) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hE_D4 hE_S4) (by norm_num)
    _ ≤ 8 * (Mμ ^ 4 * (t - s) ^ 2 + 3 * Mσ ^ 4 * (t - s) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
        exact add_le_add (mul_le_mul_of_nonneg_left hts4_le_ts2 (by positivity)) le_rfl
    _ = (8 * Mμ ^ 4 + 8 * 3 * Mσ ^ 4) * (t - s) ^ 2 := by ring

/-! ## Riemann sum and Taylor remainder convergence -/

/-- Riemann sum L² convergence for bounded continuous-in-time processes.

  For bounded g with |g(s, ω)| ≤ C and continuous s → g(s, ω) for each ω,
  the Riemann sum Σ g(tᵢ, ω) Δt converges to ∫₀ᵗ g(s, ω) ds in L²(Ω). -/
theorem riemann_sum_L2_convergence
    [IsProbabilityMeasure μ]
    (g : ℝ → Ω → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hg_bdd : ∀ s ω, |g s ω| ≤ C)
    (hg_meas : ∀ s, Measurable (g s))
    (t : ℝ) (ht : 0 < t)
    (hg_cont : ∀ ω, ContinuousOn (fun s => g s ω) (Set.Icc 0 t)) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1)) -
         ∫ s in Set.Icc 0 t, g s ω ∂volume)^2 ∂μ)
      atTop (nhds 0) := by
  -- Abbreviate the error for readability
  set err : ℕ → Ω → ℝ := fun n ω =>
    ∑ i : Fin (n + 1),
      g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1)) -
    ∫ s in Set.Icc 0 t, g s ω ∂volume
  -- Step 1: error is bounded by 2Ct
  have herr_bdd : ∀ n ω, |err n ω| ≤ 2 * C * t := by
    intro n ω
    -- Sum bound: |Σ g(tᵢ) Δt| ≤ C·t
    have hΔt_nn : (0 : ℝ) ≤ t / (↑(n + 1) : ℝ) := div_nonneg ht.le (Nat.cast_nonneg _)
    have hsum : |∑ i : Fin (n + 1), g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1))| ≤ C * t := by
      calc |∑ i : Fin (n + 1), g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1))|
          ≤ ∑ i : Fin (n + 1), |g (↑(i : ℕ) * t / ↑(n + 1)) ω * (t / ↑(n + 1))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (n + 1), C * (t / ↑(n + 1)) := by
            apply Finset.sum_le_sum; intro i _
            rw [abs_mul, abs_of_nonneg hΔt_nn]
            exact mul_le_mul_of_nonneg_right (hg_bdd _ _) hΔt_nn
        _ = C * t := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            field_simp
    -- Integral bound: |∫ g| ≤ C·t (using norm_setIntegral_le_of_norm_le_const)
    have hvol_ne_top : volume (Set.Icc 0 t) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hint : |∫ s in Set.Icc 0 t, g s ω ∂volume| ≤ C * t := by
      have key : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖g s ω‖ ≤ C :=
        fun s _ => by rw [Real.norm_eq_abs]; exact hg_bdd s ω
      have h := norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hvol_ne_top) key
      rw [Real.norm_eq_abs] at h
      have hvol : volume.real (Set.Icc (0 : ℝ) t) = t := by
        simp only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht.le]
      rw [hvol] at h; linarith
    -- Triangle inequality: |a - b| ≤ |a| + |b|
    have htri : |err n ω| ≤
        |∑ i : Fin (n + 1), g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1))| +
        |∫ s in Set.Icc 0 t, g s ω ∂volume| := by
      have := norm_sub_le
        (∑ i : Fin (n + 1), g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1)))
        (∫ s in Set.Icc 0 t, g s ω ∂volume)
      simp only [Real.norm_eq_abs] at this
      exact this
    linarith
  -- Step 2: error² bounded by (2Ct)²
  have herr_sq_bdd : ∀ n ω, (err n ω) ^ 2 ≤ (2 * C * t) ^ 2 := by
    intro n ω
    have h := herr_bdd n ω
    rw [abs_le] at h
    nlinarith [h.1, h.2]
  -- Step 3: error(ω) → 0 for each ω (Riemann sum convergence for continuous functions)
  have herr_ptwise : ∀ ω, Filter.Tendsto (err · ω) atTop (nhds 0) := by
    intro ω
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- g(·, ω) is uniformly continuous on compact [0, t]
    have huc : UniformContinuousOn (fun s => g s ω) (Set.Icc 0 t) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (hg_cont ω)
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ_pos, hδ⟩ := huc (ε / (t + 1)) (div_pos hε (by linarith))
    obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
    refine ⟨N, fun n hn => ?_⟩
    -- For n ≥ N, the mesh t/(n+1) < δ
    have hn1_pos : (0 : ℝ) < ↑(n + 1) := Nat.cast_pos.mpr (by omega)
    have hmesh : t / (↑(n + 1) : ℝ) < δ := by
      rw [div_lt_iff₀ hn1_pos]
      calc t < δ * (↑N + 1) := by
              calc t = (t / δ) * δ := by rw [div_mul_cancel₀ t (ne_of_gt hδ_pos)]
                _ < (↑N + 1) * δ := by nlinarith
                _ = δ * (↑N + 1) := by ring
        _ ≤ δ * ↑(n + 1) := by
              apply mul_le_mul_of_nonneg_left _ hδ_pos.le
              push_cast; linarith [show (N : ℝ) ≤ n from Nat.cast_le.mpr (by omega)]
    -- Bound: dist (err n ω) 0 < ε
    rw [Real.dist_eq, sub_zero]
    -- Set up partition function
    set Δ := t / (↑(n + 1) : ℝ) with hΔ_def
    have hΔ_pos : (0 : ℝ) < Δ := div_pos ht hn1_pos
    -- Partition points: ptFn k = k * Δ
    set ptFn : ℕ → ℝ := fun k => ↑k * Δ with hptFn_def
    have hpt0 : ptFn 0 = 0 := by simp [hptFn_def]
    have hptn1 : ptFn (n + 1) = t := by
      simp only [hptFn_def, hΔ_def, Nat.cast_add, Nat.cast_one]
      field_simp
    have hpt_step : ∀ k, ptFn (k + 1) - ptFn k = Δ := by
      intro k; simp only [hptFn_def, Nat.cast_add, Nat.cast_one]; ring
    -- Partition points lie in [0, t]
    have hpt_mem : ∀ k, k ≤ n + 1 → ptFn k ∈ Set.Icc 0 t := by
      intro k hk
      refine ⟨by positivity, ?_⟩
      calc (↑k : ℝ) * Δ ≤ ↑(n + 1) * Δ := by
              apply mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hΔ_pos.le
        _ = t := by simp [hΔ_def]; field_simp
    -- Subinterval endpoints are ordered
    have hpt_le : ∀ k, ptFn k ≤ ptFn (k + 1) := fun k => by linarith [hpt_step k]
    -- g(·, ω) is interval integrable on each subinterval
    have hg_ii : ∀ k < n + 1, IntervalIntegrable (g · ω) volume (ptFn k) (ptFn (k + 1)) := by
      intro k hk
      apply ContinuousOn.intervalIntegrable_of_Icc (hpt_le k)
      exact (hg_cont ω).mono (Set.Icc_subset_Icc (hpt_mem k (by omega)).1 (hpt_mem (k+1) (by omega)).2)
    -- Convert Set.Icc integral to intervalIntegral
    have hIcc_eq_ii : ∫ s in Set.Icc 0 t, g s ω ∂volume = ∫ s in (0:ℝ)..t, g s ω := by
      rw [intervalIntegral.integral_of_le ht.le]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm
    -- Split interval integral into sum over subintervals
    have hsplit : ∫ s in (0:ℝ)..t, g s ω =
        ∑ k ∈ Finset.range (n + 1), ∫ s in (ptFn k)..(ptFn (k + 1)), g s ω := by
      rw [← hpt0, ← hptn1]
      exact (intervalIntegral.sum_integral_adjacent_intervals hg_ii).symm
    -- Express Riemann sum using Finset.range and constant integrals
    have hRS_eq : ∑ i : Fin (n + 1), g (↑↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1)) =
        ∑ k ∈ Finset.range (n + 1), ∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω := by
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1; ext ⟨i, hi⟩
      rw [intervalIntegral.integral_const, smul_eq_mul, hpt_step]
      -- g(↑i * t / ↑(n+1)) ω * Δ = Δ * g(↑i * Δ) ω
      simp only [hptFn_def, hΔ_def, mul_div_assoc]
      ring
    -- Express error as sum of integral differences
    have herr_eq : err n ω =
        ∑ k ∈ Finset.range (n + 1),
          ((∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
           (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω)) := by
      simp only [err, hIcc_eq_ii, hsplit, hRS_eq, ← Finset.sum_sub_distrib]
    -- Bound each term using uniform continuity
    have hterm_bdd : ∀ k ∈ Finset.range (n + 1),
        |(∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
         (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω)| ≤ ε / (t + 1) * Δ := by
      intro k hk
      rw [Finset.mem_range] at hk
      -- Combine integrals: ∫ c - ∫ f = ∫ (c - f)
      rw [← intervalIntegral.integral_sub intervalIntegrable_const (hg_ii k hk)]
      -- Apply norm bound for interval integrals
      have hle : ‖∫ s in (ptFn k)..(ptFn (k + 1)), (g (ptFn k) ω - g s ω)‖ ≤
          ε / (t + 1) * |ptFn (k + 1) - ptFn k| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le (hpt_le k)] at hs
        rw [Real.norm_eq_abs]
        -- Need |g(ptFn k, ω) - g(s, ω)| ≤ ε / (t + 1)
        have hsk : ptFn k ∈ Set.Icc 0 t := hpt_mem k (by omega)
        have hs_mem : s ∈ Set.Icc 0 t := by
          constructor
          · linarith [hsk.1, hs.1]
          · exact le_trans hs.2 (hpt_mem (k + 1) (by omega)).2
        have hdist : dist (ptFn k) s < δ := by
          rw [Real.dist_eq]
          calc |ptFn k - s| = s - ptFn k := by
                  rw [abs_of_nonpos (by linarith [hs.1])]
                  ring
            _ ≤ ptFn (k + 1) - ptFn k := by linarith [hs.2]
            _ = Δ := hpt_step k
            _ < δ := hmesh
        exact le_of_lt (hδ (ptFn k) hsk s hs_mem hdist)
      rw [Real.norm_eq_abs] at hle
      calc |(∫ s in (ptFn k)..(ptFn (k + 1)), (g (ptFn k) ω - g s ω))|
          ≤ ε / (t + 1) * |ptFn (k + 1) - ptFn k| := hle
        _ = ε / (t + 1) * Δ := by
            rw [hpt_step, abs_of_pos hΔ_pos]
    -- Final bound: sum of (ε/(t+1)) * Δ over (n+1) terms = ε * t / (t+1) < ε
    calc |err n ω|
        = |∑ k ∈ Finset.range (n + 1),
            ((∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
             (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω))| := by rw [herr_eq]
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            |(∫ s in (ptFn k)..(ptFn (k + 1)), g (ptFn k) ω) -
             (∫ s in (ptFn k)..(ptFn (k + 1)), g s ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), ε / (t + 1) * Δ :=
          Finset.sum_le_sum hterm_bdd
      _ = ↑(n + 1) * (ε / (t + 1) * Δ) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ε * (t / (t + 1)) := by
          simp only [hΔ_def]; field_simp
      _ < ε * 1 := by
          apply mul_lt_mul_of_pos_left _ hε
          rw [div_lt_one (by linarith : (0:ℝ) < t + 1)]
          linarith
      _ = ε := mul_one ε
  -- Step 4: error²(ω) → 0 for each ω
  have herr_sq_ptwise : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (err n ω) ^ 2) atTop (nhds 0) := by
    filter_upwards with ω
    rw [show (0 : ℝ) = 0 ^ 2 from by norm_num]
    exact (herr_ptwise ω).pow 2
  -- Step 5: error² is AEStronglyMeasurable
  have herr_sq_meas : ∀ n, AEStronglyMeasurable (fun ω => (err n ω) ^ 2) μ := by
    intro n
    have hsum_meas : Measurable (fun ω => ∑ i : Fin (n + 1),
        g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1))) :=
      Finset.measurable_sum _ fun i _ => (hg_meas _).mul_const _
    -- Parametric integral measurability: pointwise limit of measurable Riemann sums
    have hint_meas : AEStronglyMeasurable (fun ω =>
        ∫ s in Set.Icc 0 t, g s ω ∂volume) μ := by
      -- The Riemann sums are measurable and converge pointwise to the integral
      apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
        (f := fun n ω => ∑ i : Fin (n + 1), g (↑i * t / ↑(n + 1)) ω * (t / ↑(n + 1)))
      · intro n
        exact (Finset.measurable_sum _ fun i _ => (hg_meas _).mul_const _).aestronglyMeasurable
      · -- From herr_ptwise: err n ω → 0, so Riemann sum → integral
        filter_upwards with ω
        have h := herr_ptwise ω
        have : Filter.Tendsto
            (fun n => err n ω + ∫ s in Set.Icc 0 t, g s ω ∂volume)
            atTop (nhds (0 + ∫ s in Set.Icc 0 t, g s ω ∂volume)) :=
          h.add tendsto_const_nhds
        simp only [err, sub_add_cancel, zero_add] at this
        exact this
    exact (hsum_meas.aestronglyMeasurable.sub hint_meas).pow 2
  -- Step 6: Apply DCT on Ω to get E[error²] → 0
  have hgoal : Filter.Tendsto (fun n => ∫ ω, (err n ω) ^ 2 ∂μ) atTop (nhds 0) := by
    rw [show (0 : ℝ) = ∫ _, (0 : ℝ) ∂μ from by simp]
    exact tendsto_integral_of_dominated_convergence (fun _ => (2 * C * t) ^ 2)
      herr_sq_meas (integrable_const _)
      (fun n => ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact herr_sq_bdd n ω)
      herr_sq_ptwise
  exact hgoal

/-! ## C² Taylor remainder bound

For C² function f with bounded second derivative, the Taylor remainder satisfies:
  |R_i| ≤ 2M · (ΔX_i)²
where R_i = f(x+h) - f(x) - f'(x)h - ½f''(x)h² and M = sup|f''|.

This is cruder than the C³ bound (|R_i| ≤ K|ΔX_i|³) but only needs C² regularity.
The convergence (∑ R_i)² → 0 in L² then follows from Fatou's lemma + the
modulus of continuity of f'' vanishing along process increments. -/

/-- For x ∈ [[a, b]], ‖x - a‖ ≤ ‖b - a‖. -/
private lemma norm_sub_le_of_mem_uIcc {a b x : ℝ} (hx : x ∈ Set.uIcc a b) :
    ‖x - a‖ ≤ ‖b - a‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · calc |x - a| = x - a := abs_of_nonneg (by linarith)
      _ ≤ b - a := by linarith
      _ = |b - a| := (abs_of_nonneg (by linarith)).symm
  · calc |x - a| = -(x - a) := abs_of_nonpos (by linarith)
      _ ≤ -(b - a) := by linarith
      _ = |b - a| := (abs_of_nonpos (by linarith)).symm

/-- First-order Taylor bound for C² functions, without ordering assumption.
    ‖g(b) - g(a) - g'(a)(b-a)‖ ≤ M * (b-a)² where M bounds ‖g''‖.

    Proof: Define h(x) = g(x) - g'(a)·x. Then h'(x) = g'(x) - g'(a),
    and MVT on g' gives |h'(x)| ≤ M·|b-a| on [[a,b]].
    MVT on h then gives |h(b)-h(a)| ≤ M·|b-a|². -/
private lemma c2_first_order_taylor_bound {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    {M : ℝ} (hM_nn : 0 ≤ M) (hM : ∀ x, ‖deriv (deriv g) x‖ ≤ M) (a b : ℝ) :
    ‖g b - g a - deriv g a * (b - a)‖ ≤ M * (b - a) ^ 2 := by
  -- g and g' are differentiable from C²
  have hg_diff : Differentiable ℝ g :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hg).1
  have hg'_diff : Differentiable ℝ (deriv g) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp hg).2.2.differentiable_one
  -- g' is Lipschitz: ‖g'(x) - g'(y)‖ ≤ M * ‖x - y‖ (MVT on g' with |g''| ≤ M)
  have hg'_lip : ∀ x y : ℝ, ‖deriv g x - deriv g y‖ ≤ M * ‖x - y‖ :=
    fun x y => Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => hg'_diff z) (fun z _ => hM z) convex_univ trivial trivial
  -- For x ∈ [[a,b]]: ‖g'(x) - g'(a)‖ ≤ M * ‖b - a‖
  set c := deriv g a with hc_def
  have hbound : ∀ x ∈ Set.uIcc a b, ‖deriv g x - c‖ ≤ M * ‖b - a‖ := by
    intro x hx
    calc ‖deriv g x - c‖ ≤ M * ‖x - a‖ := hg'_lip x a
      _ ≤ M * ‖b - a‖ := by exact mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_uIcc hx) hM_nn
  -- Define h(x) = g(x) - c·x, with h'(x) = g'(x) - c
  have hh_diff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ (fun x => g x - c * x) x :=
    fun x _ => (hg_diff x).sub (differentiableAt_id.const_mul c)
  have hh_deriv : ∀ x, deriv (fun x => g x - c * x) x = deriv g x - c := by
    intro x
    have hd : HasDerivAt (fun x => g x - c * x) (deriv g x - c * 1) x :=
      (hg_diff x).hasDerivAt.sub ((hasDerivAt_id x).const_mul c)
    simp only [mul_one] at hd
    exact hd.deriv
  have hh_bound : ∀ x ∈ Set.uIcc a b,
      ‖deriv (fun x => g x - c * x) x‖ ≤ M * ‖b - a‖ := by
    intro x hx; rw [hh_deriv x]; exact hbound x hx
  -- Apply MVT to h on [[a,b]]
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hh_diff hh_bound
    (convex_uIcc a b) Set.left_mem_uIcc Set.right_mem_uIcc
  -- Simplify: h(b) - h(a) = g(b) - g(a) - c·(b - a)
  have hsimp : (fun x => g x - c * x) b - (fun x => g x - c * x) a =
      g b - g a - c * (b - a) := by ring
  rw [hsimp] at hmvt
  -- Convert M * ‖b-a‖ * ‖b-a‖ to M * (b-a)²
  calc ‖g b - g a - deriv g a * (b - a)‖
      = ‖g b - g a - c * (b - a)‖ := by rfl
    _ ≤ M * ‖b - a‖ * ‖b - a‖ := hmvt
    _ = M * (‖b - a‖ * ‖b - a‖) := by ring
    _ = M * ‖b - a‖ ^ 2 := by rw [sq]
    _ = M * (b - a) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]

/-- C² Taylor bound: |R(x,h)| ≤ 2M · h² where M = sup|f''|.

    Proof: Triangle inequality splits into first-order Taylor remainder (≤ M·h²)
    and the second derivative term (≤ M/2·h²). Total ≤ 3/2·M·h² ≤ 2·M·h². -/
private lemma taylor_C2_bound_partition_term
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mf'' : ℝ} (hMf''_nn : 0 ≤ Mf'')
    (hMf'' : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mf'')
    (t : ℝ) (n : ℕ) (i : Fin (n + 1)) (ω : Ω) :
    |f (↑(i : ℕ) * t / ↑(n + 1))
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω) -
      f (↑(i : ℕ) * t / ↑(n + 1))
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) -
      deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x)
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) -
      (1 : ℝ) / 2 *
        deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
          (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2| ≤
    2 * Mf'' *
      (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 := by
  -- Abbreviations
  set t_i := ↑(i : ℕ) * t / ↑(n + 1)
  set x₀ := X.process t_i ω
  set x₁ := X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω
  set Δx := x₁ - x₀
  set g := fun x => f t_i x
  -- g is C² with |g''| ≤ Mf''
  have hg_cd : ContDiff ℝ 2 g := hf_x t_i
  have hg''_bdd : ∀ x, ‖deriv (deriv g) x‖ ≤ Mf'' := by
    intro x; rw [Real.norm_eq_abs]; exact hMf'' t_i x
  -- First-order Taylor bound: |g(x₁) - g(x₀) - g'(x₀)·Δx| ≤ Mf'' · Δx²
  have h_taylor := c2_first_order_taylor_bound hg_cd hMf''_nn hg''_bdd x₀ x₁
  -- Bound on g''(x₀): |g''(x₀)| ≤ Mf''
  have h_g''_at := hMf'' t_i x₀
  -- Triangle inequality: |A - B| ≤ |A| + |B|
  -- where A = g(x₁) - g(x₀) - g'(x₀)·Δx, B = ½·g''(x₀)·Δx²
  have h_triangle : |g x₁ - g x₀ - deriv g x₀ * Δx - 1 / 2 * deriv (deriv g) x₀ * Δx ^ 2|
      ≤ |g x₁ - g x₀ - deriv g x₀ * Δx| + |1 / 2 * deriv (deriv g) x₀ * Δx ^ 2| := by
    have heq : g x₁ - g x₀ - deriv g x₀ * Δx - 1 / 2 * deriv (deriv g) x₀ * Δx ^ 2 =
        (g x₁ - g x₀ - deriv g x₀ * Δx) + (-(1 / 2 * deriv (deriv g) x₀ * Δx ^ 2)) := by ring
    rw [heq]
    set p := g x₁ - g x₀ - deriv g x₀ * Δx
    set q := 1 / 2 * deriv (deriv g) x₀ * Δx ^ 2
    calc |p + (-q)| ≤ |p| + |-q| := by
            rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
            exact norm_add_le p (-q)
      _ = |p| + |q| := by rw [abs_neg]
  -- Bound second term: |½·g''(x₀)·Δx²| ≤ Mf''/2 · Δx²
  have h_g''_g : |deriv (deriv g) x₀| ≤ Mf'' := h_g''_at
  have h_second : |1 / 2 * deriv (deriv g) x₀ * Δx ^ 2| ≤ Mf'' / 2 * Δx ^ 2 := by
    rw [abs_mul, abs_mul]
    calc |1 / 2| * |deriv (deriv g) x₀| * |Δx ^ 2|
        = 1 / 2 * |deriv (deriv g) x₀| * |Δx ^ 2| := by
          rw [abs_of_nonneg (by norm_num : (1 : ℝ) / 2 ≥ 0)]
      _ ≤ 1 / 2 * Mf'' * |Δx ^ 2| := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left h_g''_g (by norm_num)
          · exact abs_nonneg _
      _ = 1 / 2 * Mf'' * Δx ^ 2 := by rw [abs_of_nonneg (sq_nonneg _)]
      _ = Mf'' / 2 * Δx ^ 2 := by ring
  -- Bound first term: ‖g(x₁) - g(x₀) - g'(x₀)·Δx‖ ≤ Mf'' · Δx²
  have h_first : |g x₁ - g x₀ - deriv g x₀ * Δx| ≤ Mf'' * Δx ^ 2 := by
    rw [← Real.norm_eq_abs]; exact h_taylor
  -- Combine: ≤ Mf''·Δx² + Mf''/2·Δx² = 3/2·Mf''·Δx² ≤ 2·Mf''·Δx²
  calc |g x₁ - g x₀ - deriv g x₀ * Δx - 1 / 2 * deriv (deriv g) x₀ * Δx ^ 2|
      ≤ |g x₁ - g x₀ - deriv g x₀ * Δx| +
        |1 / 2 * deriv (deriv g) x₀ * Δx ^ 2| := h_triangle
    _ ≤ Mf'' * Δx ^ 2 + Mf'' / 2 * Δx ^ 2 := add_le_add h_first h_second
    _ = 3 / 2 * Mf'' * Δx ^ 2 := by ring
    _ ≤ 2 * Mf'' * Δx ^ 2 := by nlinarith [sq_nonneg Δx]

/-! ## Abstract Fatou squeeze helper for L² convergence

Abstracts the Fatou squeeze argument used in taylor_remainder_L2_convergence
to avoid repeating the enormous Taylor/QV expressions. -/

/-- **Abstract Fatou squeeze for dominated L² convergence**.

    Given: fₖ ≥ 0 with fₖ ≤ Cf · Sₖ², fₖ → 0 a.e., Sₖ → QV a.e.,
    ∫(Sₖ - QV)² → 0, and integrability conditions,
    concludes ∫fₖ → 0.

    Proof: Fatou squeeze with gₖ = 2Cf(Sₖ-QV)² + 2Cf·QV² → G = 2Cf·QV². -/
theorem abstract_fatou_squeeze_L2 [IsProbabilityMeasure μ]
    {fk Sk : ℕ → Ω → ℝ} {QV : Ω → ℝ} {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hfk_nn : ∀ k ω, 0 ≤ fk k ω)
    (hfk_dom : ∀ k ω, fk k ω ≤ Cf * (Sk k ω) ^ 2)
    (hfk_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k => fk k ω) atTop (nhds 0))
    (hSk_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k => Sk k ω) atTop (nhds (QV ω)))
    (hSk_L2 : Filter.Tendsto (fun k => ∫ ω, (Sk k ω - QV ω) ^ 2 ∂μ) atTop (nhds 0))
    (hfk_int : ∀ k, Integrable (fk k) μ)
    (hSk_diff_int : ∀ k, Integrable (fun ω => (Sk k ω - QV ω) ^ 2) μ)
    (hQV_sq_int : Integrable (fun ω => QV ω ^ 2) μ) :
    Filter.Tendsto (fun k => ∫ ω, fk k ω ∂μ) atTop (nhds 0) := by
  apply fatou_squeeze_tendsto_zero
    (g := fun k ω => 2 * Cf * (Sk k ω - QV ω) ^ 2 + 2 * Cf * QV ω ^ 2)
    (G := fun ω => 2 * Cf * QV ω ^ 2)
  -- hf_nn
  · exact hfk_nn
  -- hfg: f_k ≤ g_k
  · intro k ω
    have h1 := hfk_dom k ω
    have h2 : (Sk k ω) ^ 2 ≤ 2 * (Sk k ω - QV ω) ^ 2 + 2 * QV ω ^ 2 := by
      nlinarith [sq_nonneg (Sk k ω - 2 * QV ω)]
    calc fk k ω ≤ Cf * (Sk k ω) ^ 2 := h1
      _ ≤ Cf * (2 * (Sk k ω - QV ω) ^ 2 + 2 * QV ω ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hCf
      _ = 2 * Cf * (Sk k ω - QV ω) ^ 2 + 2 * Cf * QV ω ^ 2 := by ring
  -- hf_ae
  · exact hfk_ae
  -- hg_ae: g_k → G a.e.
  · filter_upwards [hSk_ae] with ω hω
    have h1 : Filter.Tendsto (fun k => (Sk k ω - QV ω) ^ 2) atTop (nhds 0) := by
      have hc : Filter.Tendsto (fun _ : ℕ => QV ω) atTop (nhds (QV ω)) :=
        tendsto_const_nhds
      have h := (hω.sub hc).pow 2
      simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] at h; exact h
    have h2 := h1.const_mul (2 * Cf)
    rw [mul_zero] at h2
    convert h2.add tendsto_const_nhds using 1; ring_nf
  -- hf_int
  · exact hfk_int
  -- hg_int
  · intro k
    exact ((hSk_diff_int k).const_mul (2 * Cf)).add (hQV_sq_int.const_mul (2 * Cf))
  -- hG_int
  · exact hQV_sq_int.const_mul (2 * Cf)
  -- hg_tend: ∫g_k → ∫G
  · have h_first := hSk_L2.const_mul (2 * Cf)
    rw [mul_zero] at h_first
    have h_tend : Filter.Tendsto
        (fun k => 2 * Cf * ∫ ω, (Sk k ω - QV ω) ^ 2 ∂μ + ∫ ω, 2 * Cf * QV ω ^ 2 ∂μ)
        atTop (nhds (0 + ∫ ω, 2 * Cf * QV ω ^ 2 ∂μ)) :=
      h_first.add tendsto_const_nhds
    rw [zero_add] at h_tend
    refine h_tend.congr (fun k => ?_)
    rw [← integral_const_mul, ← integral_add
      ((hSk_diff_int k).const_mul _) (hQV_sq_int.const_mul _)]

/-! ## Integrability infrastructure for Fatou squeeze

Helper lemmas providing integrability of discrete QV sums squared, QV², etc.
Needed for the abstract Fatou squeeze in `taylor_remainder_L2_convergence`. -/

/-- Process values are AEStronglyMeasurable (from adapted + sub-σ-algebra). -/
lemma process_aesm {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) :
    AEStronglyMeasurable (X.process t) μ :=
  ((X.process_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable

/-- SI values are AEStronglyMeasurable. -/
private lemma si_aesm {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) :
    AEStronglyMeasurable (X.stoch_integral t) μ :=
  ((X.stoch_integral_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable

/-- (X(t) - X(s))⁴ is integrable for bounded-coefficient Itô processes.
    Proof: decompose ΔX = D + S a.e., then (D+S)⁴ ≤ 8(D⁴ + S⁴) where
    D⁴ is bounded and S⁴ is integrable from quartic bound. -/
lemma process_increment_fourth_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (X.process t ω - X.process s ω) ^ 4) μ := by
  set D : Ω → ℝ := fun ω =>
    ∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
    ∫ u in Set.Icc 0 s, X.drift u ω ∂volume
  set S : Ω → ℝ := fun ω => X.stoch_integral t ω - X.stoch_integral s ω
  -- ΔX = D + S a.e.
  have hdecomp : ∀ᵐ ω ∂μ, X.process t ω - X.process s ω = D ω + S ω := by
    filter_upwards [X.integral_form t (le_trans hs hst), X.integral_form s hs] with ω hωt hωs
    simp only [D, S]; linarith
  -- D bounded: |D| ≤ Mμ·(t-s)
  have hD_bdd : ∀ ω, |D ω| ≤ Mμ * (t - s) := by
    intro ω
    have hint_t : IntegrableOn (fun u => X.drift u ω) (Set.Icc 0 t) volume :=
      X.drift_time_integrable ω t (le_trans hs hst)
    have hD_eq : D ω = ∫ u in Set.Icc 0 t \ Set.Icc 0 s, X.drift u ω ∂volume :=
      (integral_diff measurableSet_Icc hint_t (Set.Icc_subset_Icc_right hst)).symm
    rw [hD_eq]
    have hvol_ne_top : volume (Set.Icc 0 t \ Set.Icc 0 s) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (measure_mono Set.diff_subset)
    have hbnd := norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hvol_ne_top)
      (fun u _ => Real.norm_eq_abs _ ▸ hMμ u ω)
    rw [Real.norm_eq_abs] at hbnd
    have h_fin_s : volume (Set.Icc 0 s) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hvol_eq : volume.real (Set.Icc 0 t \ Set.Icc 0 s) = t - s := by
      show (volume (Set.Icc 0 t \ Set.Icc 0 s)).toReal = t - s
      rw [measure_diff (Set.Icc_subset_Icc_right hst) measurableSet_Icc.nullMeasurableSet h_fin_s]
      rw [Real.volume_Icc, Real.volume_Icc, sub_zero, sub_zero]
      rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_ofReal hst) ENNReal.ofReal_ne_top]
      rw [ENNReal.toReal_ofReal (le_trans hs hst), ENNReal.toReal_ofReal hs]
    rw [hvol_eq] at hbnd; linarith
  -- D⁴ bounded
  have hD_fourth_bdd : ∀ ω, D ω ^ 4 ≤ (Mμ * (t - s)) ^ 4 := fun ω => by
    calc D ω ^ 4 = (D ω ^ 2) ^ 2 := by ring
      _ ≤ ((Mμ * (t - s)) ^ 2) ^ 2 := by
          apply sq_le_sq'
          · have := (abs_le.mp (hD_bdd ω)).1
            nlinarith [sq_nonneg (D ω), sq_nonneg (Mμ * (t - s))]
          · exact sq_le_sq' (abs_le.mp (hD_bdd ω)).1 (abs_le.mp (hD_bdd ω)).2
      _ = (Mμ * (t - s)) ^ 4 := by ring
  -- D AEStronglyMeasurable
  have hD_asm : AEStronglyMeasurable D μ :=
    ((process_aesm X t).sub (process_aesm X s)).sub
      ((si_aesm X t).sub (si_aesm X s)) |>.congr
      (hdecomp.mono fun ω hω => by simp only [D, S, Pi.sub_apply] at hω ⊢; linarith)
  -- D⁴ integrable (bounded)
  have hD_fourth_int : Integrable (fun ω => D ω ^ 4) μ :=
    (integrable_const ((Mμ * (t - s)) ^ 4)).mono' (hD_asm.pow 4)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hD_fourth_bdd ω)
  -- S⁴ integrable
  have hS_fourth_int : Integrable (fun ω => S ω ^ 4) μ :=
    stoch_integral_increment_L4_integrable X hMσ s t hs hst
  -- ΔX⁴ AEStronglyMeasurable
  have hΔX_asm : AEStronglyMeasurable (fun ω => (X.process t ω - X.process s ω) ^ 4) μ :=
    ((process_aesm X t).sub (process_aesm X s)).pow 4
  -- (D+S)⁴ ≤ 8(D⁴+S⁴)
  have h_split : ∀ ω, (D ω + S ω) ^ 4 ≤ 8 * (D ω ^ 4 + S ω ^ 4) := fun ω => by
    have h1 : (D ω + S ω) ^ 2 ≤ 2 * D ω ^ 2 + 2 * S ω ^ 2 := by
      nlinarith [sq_nonneg (D ω - S ω)]
    have h2 : (2 * D ω ^ 2 + 2 * S ω ^ 2) ^ 2 ≤ 8 * (D ω ^ 4 + S ω ^ 4) := by
      nlinarith [sq_nonneg (D ω ^ 2 - S ω ^ 2)]
    calc (D ω + S ω) ^ 4 = ((D ω + S ω) ^ 2) ^ 2 := by ring
      _ ≤ (2 * D ω ^ 2 + 2 * S ω ^ 2) ^ 2 := by
          apply sq_le_sq'
          · linarith [sq_nonneg (D ω), sq_nonneg (S ω), sq_nonneg (D ω + S ω)]
          · exact h1
      _ ≤ 8 * (D ω ^ 4 + S ω ^ 4) := h2
  -- Combine
  apply ((hD_fourth_int.add hS_fourth_int).const_mul 8).mono' hΔX_asm
  filter_upwards [hdecomp] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hω]
  calc (D ω + S ω) ^ 4 ≤ 8 * (D ω ^ 4 + S ω ^ 4) := h_split ω
    _ = 8 * ((fun ω => D ω ^ 4 + S ω ^ 4) ω) := by ring_nf

/-- Discrete QV sum is AEStronglyMeasurable. -/
lemma discrete_qv_aesm {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (n : ℕ) :
    AEStronglyMeasurable (fun ω =>
      ∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) μ := by
  have h := aestronglyMeasurable_sum (μ := μ) Finset.univ
    (f := fun (i : Fin (n + 1)) (ω : Ω) =>
      (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2)
    (fun i _ => ((process_aesm X _).sub (process_aesm X _)).pow 2)
  exact h.congr (ae_of_all _ fun ω => Finset.sum_apply ω Finset.univ _)

/-- QV is AEStronglyMeasurable (from integrability of diffusion_sq_integral). -/
lemma qv_aesm {F : Filtration Ω ℝ} [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (t : ℝ) (ht : 0 ≤ t) :
    AEStronglyMeasurable (fun ω => X.quadraticVariation t ω) μ :=
  (X.diffusion_sq_integral_integrable t ht).aestronglyMeasurable

/-- QV² is integrable when diffusion is bounded (bounded + AEStronglyMeasurable on prob space). -/
lemma qv_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (X.quadraticVariation t ω) ^ 2) μ := by
  have hQV_bdd : ∀ ω, ‖(X.quadraticVariation t ω) ^ 2‖ ≤ (Mσ ^ 2 * t) ^ 2 := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [X.quadraticVariation_nonneg t ω,
      X.quadraticVariation_le hMσ t ht ω])
      (X.quadraticVariation_le hMσ t ht ω)
  exact (integrable_const _).mono' ((qv_aesm X t ht).pow 2) (ae_of_all _ hQV_bdd)

/-- Discrete QV sum squared is integrable: (∑(ΔXᵢ)²)² ∈ L¹.
    Proof: Cauchy-Schwarz gives (∑aᵢ)² ≤ (n+1)·∑aᵢ², then each (ΔXᵢ)⁴ is
    integrable from quartic bounds. -/
lemma discrete_qv_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    Integrable (fun ω =>
      (∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) ^ 2) μ := by
  -- Cauchy-Schwarz: (∑aᵢ)² ≤ (n+1)·∑aᵢ²
  have hCS : ∀ ω, (∑ i : Fin (n + 1),
      (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) ^ 2 ≤
      ↑(n + 1) * ∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 4 := by
    intro ω
    have h := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ
      (fun i : Fin (n + 1) =>
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    calc (∑ i, (X.process _ ω - X.process _ ω) ^ 2) ^ 2
        ≤ ↑(n + 1) * ∑ i,
          ((X.process _ ω - X.process _ ω) ^ 2) ^ 2 := h
      _ = ↑(n + 1) * ∑ i,
          (X.process _ ω - X.process _ ω) ^ 4 := by
          congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  -- Each (ΔXᵢ)⁴ is integrable
  have hΔX4_int : ∀ i : Fin (n + 1),
      Integrable (fun ω => (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
        X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 4) μ := by
    intro i
    have hi_lt := i.isLt
    have hn_pos : (0 : ℝ) < ↑(n + 1) := by positivity
    exact process_increment_fourth_integrable X hMμ hMσ _ _
      (by positivity)
      (by apply div_le_div_of_nonneg_right _ hn_pos.le; linarith)
  -- Sum of integrable is integrable
  have hsum_int : Integrable (fun ω => ∑ i : Fin (n + 1),
      (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 4) μ :=
    integrable_finset_sum _ fun i _ => hΔX4_int i
  -- Dominate: (∑aᵢ)² ≤ (n+1)·∑aᵢ² ≤ integrable
  exact (hsum_int.const_mul _).mono' ((discrete_qv_aesm X t n).pow 2)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hCS ω)

/-- (discrete_QV - QV)² is integrable.
    Proof: (S-Q)² ≤ 2S² + 2Q², both integrable. -/
lemma qv_diff_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    Integrable (fun ω =>
      (∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       X.quadraticVariation t ω) ^ 2) μ := by
  have h_dom : ∀ ω, (∑ i : Fin (n + 1),
      (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
     X.quadraticVariation t ω) ^ 2 ≤
    2 * (∑ i : Fin (n + 1),
      (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) ^ 2 +
    2 * (X.quadraticVariation t ω) ^ 2 := by
    intro ω; nlinarith [sq_nonneg
      (∑ i : Fin (n + 1), (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 +
       X.quadraticVariation t ω)]
  exact ((discrete_qv_sq_integrable X hMμ hMσ t ht n).const_mul 2 |>.add
    ((qv_sq_integrable X hMσ t ht.le).const_mul 2)).mono'
    (((discrete_qv_aesm X t n).sub (qv_aesm X t ht.le)).pow 2)
    (ae_of_all _ fun ω => by
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact h_dom ω)

set_option maxHeartbeats 1600000 in
/-- Taylor remainder L² convergence summed over partition intervals.

    With C² regularity and bounded second derivative, the sum of Taylor remainders
    Σ R_i → 0 in L², where R_i = f(x + ΔX) - f(x) - f'(x)ΔX - (1/2)f''(x)(ΔX)².

    **Proof**: tendsto_of_subseq_tendsto + abstract Fatou squeeze. -/
theorem taylor_remainder_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mμ : ℝ} (_hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (_hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    {Mf'' : ℝ} (hMf'' : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mf'')
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (f (↑(i : ℕ) * t / ↑(n + 1))
             (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω) -
           f (↑(i : ℕ) * t / ↑(n + 1))
             (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) -
           deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x)
             (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
             (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
              X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) -
           (1 : ℝ) / 2 *
             deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
               (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
             (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
              X.process (↑(i : ℕ) * t / ↑(n + 1)) ω)^2))^2 ∂μ)
      atTop (nhds 0) := by
  have hMf''_nn : 0 ≤ Mf'' := by
    have := hMf'' 0 0; linarith [abs_nonneg (deriv (deriv (fun x => f 0 x)) 0)]
  apply tendsto_of_subseq_tendsto
  intro ns hns
  -- Step A: QV L² convergence along ns, then extract a.e. subseq
  have h_qv_L2_ns := (ito_process_discrete_qv_L2_convergence X _hMμ _hMσ t ht).comp hns
  -- Step B: L² → a.e. subseq (Chebyshev + TendstoInMeasure)
  have h_ae_subseq : ∃ (ms : ℕ → ℕ), StrictMono ms ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun k =>
        ∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(ns (ms k) + 1)) ω) ^ 2)
        atTop (nhds (X.quadraticVariation t ω)) := by
    -- Define f_n := Sk(ns n) as a function ℕ → Ω → ℝ
    set f_ns : ℕ → Ω → ℝ := fun n ω =>
      ∑ i : Fin (ns n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(ns n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(ns n + 1)) ω) ^ 2
    set QV_fn := fun ω => X.quadraticVariation t ω
    -- Prove TendstoInMeasure for f_ns → QV
    suffices h_tim : TendstoInMeasure μ f_ns atTop QV_fn by
      obtain ⟨ms, hms, hms_ae⟩ := h_tim.exists_seq_tendsto_ae
      exact ⟨ms, hms, hms_ae⟩
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hε_sq_pos : (0 : ℝ) < ε ^ 2 := by positivity
    -- Abbreviations for the discrete QV and QV
    set Sk := fun n (ω : Ω) => ∑ i : Fin (n + 1),
      (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2
    set QV := fun ω => X.quadraticVariation t ω
    -- L² integrability
    have hL2_int : ∀ n, Integrable (fun ω => (Sk (ns n) ω - QV ω) ^ 2) μ :=
      fun n => qv_diff_sq_integrable X _hMμ _hMσ t ht (ns n)
    -- AEStronglyMeasurable
    have hSk_asm : ∀ n, AEStronglyMeasurable (Sk (ns n)) μ :=
      fun n => discrete_qv_aesm X t (ns n)
    have hQV_asm : AEStronglyMeasurable QV μ := qv_aesm X t ht.le
    -- Step A: lintegral of (Sk - QV)² → 0 in ENNReal
    have h_lint_eq : ∀ n, ∫⁻ ω, ENNReal.ofReal ((Sk (ns n) ω - QV ω) ^ 2) ∂μ =
        ENNReal.ofReal (∫ ω, (Sk (ns n) ω - QV ω) ^ 2 ∂μ) :=
      fun n => (ofReal_integral_eq_lintegral_ofReal (hL2_int n)
        (ae_of_all _ fun ω => by positivity)).symm
    have h_tend_lint : Filter.Tendsto
        (fun n => ∫⁻ ω, ENNReal.ofReal ((Sk (ns n) ω - QV ω) ^ 2) ∂μ)
        atTop (nhds 0) := by
      simp_rw [h_lint_eq]
      have : Filter.Tendsto (fun n => ENNReal.ofReal (∫ ω, (Sk (ns n) ω - QV ω) ^ 2 ∂μ))
          atTop (nhds (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp h_qv_L2_ns
      rwa [ENNReal.ofReal_zero] at this
    -- Step B: dividing by ofReal(ε²)
    have hε2_pos : ENNReal.ofReal (ε ^ 2) ≠ 0 := by positivity
    have hε2_top : ENNReal.ofReal (ε ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_div_tend : Filter.Tendsto
        (fun n => (∫⁻ ω, ENNReal.ofReal ((Sk (ns n) ω - QV ω) ^ 2) ∂μ) /
          ENNReal.ofReal (ε ^ 2)) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.div_const h_tend_lint (Or.inr hε2_pos)
      rwa [ENNReal.zero_div] at h
    -- Step C: bound μ {ε ≤ ‖Sk - QV‖} by the ratio via Chebyshev
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_div_tend
    · intro n; exact zero_le _
    · intro n
      have h_subset : {ω | (ε : ℝ) ≤ ‖Sk (ns n) ω - QV ω‖} ⊆
          {ω | ε ^ 2 ≤ (Sk (ns n) ω - QV ω) ^ 2} := by
        intro ω (hω : ε ≤ ‖Sk (ns n) ω - QV ω‖)
        show ε ^ 2 ≤ (Sk (ns n) ω - QV ω) ^ 2
        rw [Real.norm_eq_abs] at hω
        nlinarith [abs_nonneg (Sk (ns n) ω - QV ω), sq_abs (Sk (ns n) ω - QV ω)]
      have h_aem : AEMeasurable (fun ω => ENNReal.ofReal ((Sk (ns n) ω - QV ω) ^ 2)) μ :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((continuous_pow 2).measurable.comp_aemeasurable
            ((hSk_asm n).sub hQV_asm).aemeasurable)
      have h_cheb := mul_meas_ge_le_lintegral₀ h_aem (ENNReal.ofReal (ε ^ 2))
      have h_set_eq : {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal ((Sk (ns n) ω - QV ω) ^ 2)} =
          {ω | ε ^ 2 ≤ (Sk (ns n) ω - QV ω) ^ 2} := by
        ext ω; simp only [Set.mem_setOf_eq]
        exact ENNReal.ofReal_le_ofReal_iff (by positivity)
      rw [h_set_eq] at h_cheb
      calc μ {ω | (ε : ℝ) ≤ ‖Sk (ns n) ω - QV ω‖}
          ≤ μ {ω | ε ^ 2 ≤ (Sk (ns n) ω - QV ω) ^ 2} := measure_mono h_subset
        _ ≤ (∫⁻ ω, ENNReal.ofReal ((Sk (ns n) ω - QV ω) ^ 2) ∂μ) / ENNReal.ofReal (ε ^ 2) :=
            ENNReal.le_div_iff_mul_le (Or.inl hε2_pos) (Or.inl hε2_top) |>.mpr <| by
              rw [mul_comm]; exact h_cheb
  obtain ⟨ms, hms, h_qv_ae⟩ := h_ae_subseq
  -- Step C: Taylor remainders → 0 a.e. along ns ∘ ms
  have h_taylor_ae := taylor_remainders_ae_tendsto_zero X f hf_x hMf'' hf''_cont t ht
    (fun k => ns (ms k)) (hns.comp hms.tendsto_atTop) h_qv_ae
  -- Step D: L² convergence along ns ∘ ms
  have h_qv_L2_nsms := h_qv_L2_ns.comp hms.tendsto_atTop
  -- Step E: Apply abstract Fatou squeeze
  refine ⟨ms, abstract_fatou_squeeze_L2 (sq_nonneg (2 * Mf''))
    (fun k ω => sq_nonneg _)  -- fk ≥ 0
    (fun k ω => ?_)            -- fk ≤ Cf · Sk²
    h_taylor_ae                -- fk → 0 a.e.
    h_qv_ae                    -- Sk → QV a.e.
    h_qv_L2_nsms               -- ∫(Sk-QV)² → 0
    ?_ ?_ ?_⟩                  -- integrability
  · -- fk ≤ Cf · Sk²: (∑ R_i)² ≤ (2Mf'')² · (∑(ΔX_i)²)²
    set N := ns (ms k)
    -- Each |R_i| ≤ 2Mf'' · (ΔX_i)²
    have h_single : ∀ i : Fin (N + 1),
        |f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2| ≤
        2 * Mf'' * (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
          X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2 :=
      fun i => taylor_C2_bound_partition_term X f hf_x hMf''_nn hMf'' t N i ω
    -- |∑ R_i| ≤ ∑|R_i| ≤ 2Mf'' · ∑(ΔX_i)²
    have h_tri := Finset.abs_sum_le_sum_abs
      (fun (i : Fin (N + 1)) =>
        f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
        f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
        deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
          (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
          (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
        (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
          (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
          (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2)
      Finset.univ
    have h_sum_bound : |∑ i : Fin (N + 1),
        (f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2)| ≤
        2 * Mf'' * ∑ i : Fin (N + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2 := by
      calc _ ≤ _ := h_tri
        _ ≤ ∑ i : Fin (N + 1), (2 * Mf'' *
            (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
             X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2) :=
          Finset.sum_le_sum fun i _ => h_single i
        _ = _ := by rw [← Finset.mul_sum]
    -- (∑ R_i)² ≤ (|∑ R_i|)² ≤ (2Mf'' · ∑(ΔX_i)²)² = (2Mf'')² · (∑(ΔX_i)²)²
    have h1 : (∑ i : Fin (N + 1),
        (f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2))^2 ≤
        (2 * Mf'' * ∑ i : Fin (N + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2) ^ 2 := by
      rw [← sq_abs (∑ i : Fin (N + 1), _)]
      exact pow_le_pow_left₀ (abs_nonneg _) h_sum_bound 2
    calc _ ≤ (2 * Mf'' * ∑ i : Fin (N + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2) ^ 2 := h1
      _ = (2 * Mf'') ^ 2 * (∑ i : Fin (N + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2) ^ 2 := by ring
  · -- fk integrable: dominated by (2Mf'')² · (discrete QV)², both integrable
    intro k
    set N := ns (ms k)
    -- The Taylor remainder sum squared is ≤ (2Mf'')² · (discrete QV)²
    have h_dom_k : ∀ ω, (∑ i : Fin (N + 1),
        (f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2))^2 ≤
        (2 * Mf'') ^ 2 * (∑ i : Fin (N + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2) ^ 2 := by
      intro ω
      have h_single := fun i => taylor_C2_bound_partition_term X f hf_x hMf''_nn hMf'' t N i ω
      have h_tri := Finset.abs_sum_le_sum_abs
        (fun (i : Fin (N + 1)) =>
          f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
          f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
          deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
            (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
            (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
             X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
          (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
            (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
            (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
             X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2)
        Finset.univ
      have h_sum_bound := le_trans h_tri
        (le_trans (Finset.sum_le_sum fun i _ => h_single i)
          (by rw [← Finset.mul_sum]))
      rw [← sq_abs (∑ i : Fin (N + 1), _)]
      have h_sq := pow_le_pow_left₀ (abs_nonneg _) h_sum_bound 2
      rw [mul_pow] at h_sq; exact h_sq
    -- AEStronglyMeasurable for the Taylor remainder sum squared
    have h_asm : AEStronglyMeasurable (fun ω => (∑ i : Fin (N + 1),
        (f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
         (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
           (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2))^2) μ := by
      apply AEStronglyMeasurable.pow
      -- Each summand is a composition of continuous functions with AEStronglyMeasurable process
      have h_summand_asm : ∀ i : Fin (N + 1), AEStronglyMeasurable (fun ω =>
          f (↑(i : ℕ) * t / ↑(N + 1)) (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω) -
          f (↑(i : ℕ) * t / ↑(N + 1)) (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
          deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x)
            (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
            (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
             X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) -
          (1 : ℝ) / 2 * deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(N + 1)) x))
            (X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) *
            (X.process ((↑(i : ℕ) + 1) * t / ↑(N + 1)) ω -
             X.process (↑(i : ℕ) * t / ↑(N + 1)) ω) ^ 2) μ := by
        intro i
        set ti := ↑(i : ℕ) * t / ↑(N + 1)
        -- f(ti, ·) is continuous, hence comp with process_aesm gives AEStronglyMeasurable
        have hf_asm1 := (hf_x ti).continuous.comp_aestronglyMeasurable
          (process_aesm X ((↑(i : ℕ) + 1) * t / ↑(N + 1)))
        have hf_asm2 := (hf_x ti).continuous.comp_aestronglyMeasurable (process_aesm X ti)
        -- deriv (f ti) is continuous
        have hf'_cont : Continuous (deriv (fun x => f ti x)) :=
          (hf_x ti).continuous_deriv (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
        have hf'_asm := hf'_cont.comp_aestronglyMeasurable (process_aesm X ti)
        -- deriv (deriv (f ti)) is continuous
        have hf_cd1 : ContDiff ℝ 1 (deriv (fun x => f ti x)) :=
          ((contDiff_succ_iff_deriv.mp (hf_x ti)).2.2)
        have hf''_cont : Continuous (deriv (deriv (fun x => f ti x))) :=
          hf_cd1.continuous_deriv le_rfl
        have hf''_asm := hf''_cont.comp_aestronglyMeasurable (process_aesm X ti)
        have hΔX_asm := (process_aesm X ((↑(i : ℕ) + 1) * t / ↑(N + 1))).sub
          (process_aesm X ti)
        exact ((hf_asm1.sub hf_asm2).sub (hf'_asm.mul hΔX_asm)).sub
          ((hf''_asm.const_mul _).mul (hΔX_asm.pow 2))
      exact (aestronglyMeasurable_sum Finset.univ fun i _ => h_summand_asm i).congr
        (ae_of_all _ fun ω => Finset.sum_apply ω Finset.univ _)
    exact ((discrete_qv_sq_integrable X _hMμ _hMσ t ht N).const_mul _).mono' h_asm
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h_dom_k ω)
  · -- (Sk - QV)² integrable
    intro k; exact qv_diff_sq_integrable X _hMμ _hMσ t ht (ns (ms k))
  · -- QV² integrable
    exact qv_sq_integrable X _hMσ t ht.le

end SPDE
