/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.StochasticIntegration
import StochasticPDE.ItoCalculus.ItoProcessCore
import StochasticPDE.ItoCalculus.QuarticBound
import StochasticPDE.ItoCalculus.RemainderIntegrability
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Itô Isometry and Orthogonality Theorems for ItoProcess

Proves the Itô isometry and compensated squared increment orthogonality
as theorems derived from the L² limit construction, not as structure fields.

## Main results

* `ItoProcess.stoch_integral_isometry_base` — Base isometry:
    E[SI(t)²] = E[∫₀ᵗ σ² ds]

* `ItoProcess.stoch_integral_cross_term` — Cross term:
    E[SI(t)·SI(s)] = E[SI(s)²] for s ≤ t

* `ItoProcess.stoch_integral_isometry` — Increment isometry:
    E[|SI(t)-SI(s)|²] = E[∫_s^t σ² du]

* Integrability infrastructure (`si_increment_sq_integrable'`, `compensated_sq_integrable'`,
    `compensated_sq_sq_integrable'`, `diffusion_sq_integral_bound`) used by
    `ConditionalIsometry.lean` for the squared orthogonality proof.
-/

noncomputable section

open MeasureTheory Set Filter

variable {Ω : Type*} [instΩ : MeasurableSpace Ω] {μ : Measure Ω}

namespace SPDE

/-! ## Base Isometry -/

/-- Base Itô isometry: E[SI(t)²] = E[∫₀ᵗ σ(s,ω)² ds].

    Proof follows `ItoIntegral.ito_isometry` exactly:
    1. From `stoch_integral_is_L2_limit`, extract approximating simple processes
    2. `sq_integral_tendsto_of_L2_tendsto` gives ∫ SI_n² → ∫ SI²
    3. Isometry convergence construction data gives ∫ SI_n² → ∫∫ σ²
    4. By uniqueness of limits: ∫ SI² = ∫∫ σ² -/
theorem ItoProcess.stoch_integral_isometry_base {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, (X.stoch_integral t ω) ^ 2 ∂μ =
    ∫ ω, (∫ s in Icc 0 t, (X.diffusion s ω) ^ 2 ∂volume) ∂μ := by
  obtain ⟨approx, hadapted_F, hbdd, hnn, hL2, hiso, _, _⟩ := X.stoch_integral_is_L2_limit
  -- Convert F-adapted to BM.F-adapted for SimpleProcess integration lemmas
  have hadapted : ∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (X.BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i) :=
    fun n i => (hadapted_F n i).mono (X.F_le_BM_F _) le_rfl
  -- Step 1: ∫ SI_n(t)² → ∫ SI(t)² (from L² convergence via sq_integral_tendsto)
  have hSI_sq := X.stoch_integral_sq_integrable t (ht)
  have hSI_int := X.stoch_integral_integrable t (ht)
  have hSn_int : ∀ n, Integrable
      (SimpleProcess.stochasticIntegral_at (approx n) X.BM t) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
      (hadapted n) (hbdd n) (hnn n) t ht
  have hSub_sq : ∀ n, Integrable (fun ω =>
      (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
       X.stoch_integral t ω) ^ 2) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (hadapted n) (hbdd n) (hnn n) (X.stoch_integral t) hSI_int hSI_sq t ht
  have h_sq_conv : Tendsto
      (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2 ∂μ)
      atTop (nhds (∫ ω, (X.stoch_integral t ω) ^ 2 ∂μ)) := by
    exact sq_integral_tendsto_of_L2_tendsto hSI_sq hSub_sq
      (fun n => by
        -- Cross-term integrability: |(g-f)*f| ≤ (g-f)² + f² by AM-GM
        refine ((hSub_sq n).add hSI_sq).mono'
          (((hSn_int n).sub hSI_int).aestronglyMeasurable.mul
            hSI_int.aestronglyMeasurable) ?_
        filter_upwards with ω
        simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
            X.stoch_integral t ω| - |X.stoch_integral t ω|),
          sq_abs (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
            X.stoch_integral t ω),
          sq_abs (X.stoch_integral t ω)])
      (hL2 t (ht))
  -- Step 2: ∫ SI_n(t)² → ∫∫ σ² (from isometry convergence construction data)
  have h_iso_conv := hiso t (ht)
  -- Step 3: Unique limits
  exact tendsto_nhds_unique h_sq_conv h_iso_conv

/-! ## Martingale Orthogonality -/

/-- Martingale orthogonality: if ∫_A Y = 0 for all A ∈ m, X is m-measurable,
    and X·Y is integrable, then ∫ X·Y = 0. -/
theorem integral_mul_eq_zero_of_setIntegral_eq_zero'
    {m : MeasurableSpace Ω}
    (hm : m ≤ instΩ)
    {X Y : Ω → ℝ}
    (hX_meas : @Measurable Ω ℝ m _ X)
    (hY_int : Integrable Y μ)
    (hXY_int : Integrable (fun ω => X ω * Y ω) μ)
    [IsProbabilityMeasure μ]
    (hset : ∀ A : Set Ω, @MeasurableSet Ω m A → ∫ ω in A, Y ω ∂μ = 0) :
    ∫ ω, X ω * Y ω ∂μ = 0 := by
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  -- Step 1: condExp m μ Y = 0 a.e.
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
  have hXY_eq : (fun ω => X ω * Y ω) = X * Y := rfl
  have hpull : μ[X * Y | m] =ᵐ[μ] X * μ[Y | m] :=
    condExp_mul_of_aestronglyMeasurable_left hX_asm (by rwa [← hXY_eq]) hY_int
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

/-! ## Cross Term via Martingale Orthogonality -/

/-- E[SI(t)·SI(s)] = E[SI(s)²] for s ≤ t.

    The increment SI(t)-SI(s) is orthogonal to SI(s) by the martingale property:
    ∫_A SI(t) = ∫_A SI(s) for all A ∈ F_s implies E[(SI(t)-SI(s))·SI(s)] = 0. -/
theorem ItoProcess.stoch_integral_cross_term {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, X.stoch_integral t ω * X.stoch_integral s ω ∂μ =
    ∫ ω, (X.stoch_integral s ω) ^ 2 ∂μ := by
  -- Decompose: SI(t)·SI(s) = SI(s)² + (SI(t)-SI(s))·SI(s)
  have hdecomp : ∀ ω,
      X.stoch_integral t ω * X.stoch_integral s ω =
      (X.stoch_integral s ω) ^ 2 +
      (X.stoch_integral t ω - X.stoch_integral s ω) * X.stoch_integral s ω := by
    intro ω; ring
  simp_rw [hdecomp]
  -- Integrability
  have hs_ge : s ≥ 0 := hs
  have ht_ge : t ≥ 0 := le_trans hs hst
  have hSI_s_int := X.stoch_integral_integrable s hs_ge
  have hSI_t_int := X.stoch_integral_integrable t ht_ge
  have hSI_s_sq := X.stoch_integral_sq_integrable s hs_ge
  have hSI_t_sq := X.stoch_integral_sq_integrable t ht_ge
  -- Cross term integrability
  have hcross_int : Integrable (fun ω =>
      (X.stoch_integral t ω - X.stoch_integral s ω) * X.stoch_integral s ω) μ := by
    apply Integrable.mono' ((hSI_t_sq.add hSI_s_sq).add hSI_s_sq)
    · exact (hSI_t_int.sub hSI_s_int).aestronglyMeasurable.mul hSI_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      set a := X.stoch_integral t ω
      set b := X.stoch_integral s ω
      rw [abs_mul]
      nlinarith [sq_abs (a - b), sq_abs b, sq_abs a, sq_nonneg (|a - b| - |b|)]
  rw [integral_add hSI_s_sq hcross_int]
  -- Suffices to show cross term = 0
  suffices hcross : ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) *
      X.stoch_integral s ω ∂μ = 0 by linarith
  -- Rewrite as ∫ SI(s) · (SI(t)-SI(s)) by commutativity
  have hcomm : (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) *
      X.stoch_integral s ω) =
      (fun ω => X.stoch_integral s ω *
      (X.stoch_integral t ω - X.stoch_integral s ω)) := by
    ext ω; ring
  rw [hcomm]
  -- Apply orthogonality: SI(s) is F_s-measurable, SI(t)-SI(s) has zero set-integrals
  apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s)
  · -- SI(s) is F_s-measurable
    exact X.stoch_integral_adapted s hs
  · -- SI(t)-SI(s) is integrable
    exact hSI_t_int.sub hSI_s_int
  · -- SI(s)·(SI(t)-SI(s)) is integrable
    rw [← hcomm]; exact hcross_int
  · -- ∫_A (SI(t)-SI(s)) = 0 for all A ∈ F_s (martingale property)
    intro A hA
    rw [integral_sub (hSI_t_int.integrableOn) (hSI_s_int.integrableOn)]
    exact sub_eq_zero.mpr (X.stoch_integral_martingale s t hs hst A hA)

/-! ## Interval Splitting Infrastructure -/

/-- For Lebesgue measure, ∫_{Icc 0 b} f = ∫_{Icc 0 a} f + ∫_{Icc a b} f when 0 ≤ a ≤ b
    and f is integrable on [0,b]. -/
lemma setIntegral_Icc_split' {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : IntegrableOn f (Icc 0 b) volume) :
    ∫ x in Icc 0 b, f x ∂volume =
    ∫ x in Icc 0 a, f x ∂volume + ∫ x in Icc a b, f x ∂volume := by
  -- Icc 0 b = Icc 0 a ∪ Icc a b
  have hunion : Icc 0 b = Icc 0 a ∪ Icc a b := (Icc_union_Icc_eq_Icc ha hab).symm
  -- The intersection {a} has Lebesgue measure 0
  have hae : AEDisjoint volume (Icc 0 a) (Icc a b) := by
    unfold AEDisjoint
    apply le_antisymm _ (zero_le _)
    calc volume (Icc 0 a ∩ Icc a b)
        ≤ volume ({a} : Set ℝ) := by
          apply measure_mono
          intro x hx
          rw [mem_inter_iff, mem_Icc, mem_Icc] at hx
          rw [mem_singleton_iff]
          linarith
      _ = 0 := Real.volume_singleton
  rw [hunion]
  exact integral_union_ae hae measurableSet_Icc.nullMeasurableSet
    (hf.mono_set (Icc_subset_Icc_right (le_trans hab le_rfl)))
    (hf.mono_set (Icc_subset_Icc_left ha))

/-! ## Increment Isometry -/

/-- Itô isometry for increments:
    E[|SI(t)-SI(s)|²] = E[∫_s^t σ(u,ω)² du].

    Proof: Expand (SI(t)-SI(s))² = SI(t)² - 2·SI(t)·SI(s) + SI(s)²,
    use base isometry + cross term, then split integrals using
    diffusion regularity conditions. -/
theorem ItoProcess.stoch_integral_isometry {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
    ∫ ω, (∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := by
  -- Integrability
  have hs_ge : s ≥ 0 := hs
  have ht_ge : t ≥ 0 := le_trans hs hst
  have hSI_s_int := X.stoch_integral_integrable s hs_ge
  have hSI_t_int := X.stoch_integral_integrable t ht_ge
  have hSI_s_sq := X.stoch_integral_sq_integrable s hs_ge
  have hSI_t_sq := X.stoch_integral_sq_integrable t ht_ge
  -- Product integrability
  have hprod_int : Integrable (fun ω =>
      X.stoch_integral t ω * X.stoch_integral s ω) μ := by
    apply Integrable.mono' (hSI_t_sq.add hSI_s_sq)
    · exact hSI_t_int.aestronglyMeasurable.mul hSI_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_mul]
      nlinarith [sq_abs (X.stoch_integral t ω),
        sq_abs (X.stoch_integral s ω),
        sq_nonneg (|X.stoch_integral t ω| - |X.stoch_integral s ω|)]
  -- Apply base isometries and cross term
  have hiso_t := X.stoch_integral_isometry_base t (le_trans hs hst)
  have hiso_s := X.stoch_integral_isometry_base s hs
  have hcross := X.stoch_integral_cross_term s t hs hst
  -- Algebraic reduction: ∫(a-b)² = ∫a² + ∫b² - 2∫(ab)
  --   = ∫∫₀ᵗ σ² + ∫∫₀ˢ σ² - 2·∫∫₀ˢ σ² = ∫∫₀ᵗ σ² - ∫∫₀ˢ σ²
  have h_diff : ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
      ∫ ω, (∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ -
      ∫ ω, (∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := by
    have h_pw : ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
        ∫ ω, (X.stoch_integral t ω ^ 2 + X.stoch_integral s ω ^ 2 -
        2 * (X.stoch_integral t ω * X.stoch_integral s ω)) ∂μ :=
      integral_congr_ae (ae_of_all _ (fun ω => by ring))
    have h_sub := integral_sub (hSI_t_sq.add hSI_s_sq) (hprod_int.const_mul 2)
    have h_add := integral_add hSI_t_sq hSI_s_sq
    have h_mul := integral_const_mul (μ := μ) (2 : ℝ)
      (fun ω => X.stoch_integral t ω * X.stoch_integral s ω)
    simp only [Pi.add_apply] at h_sub h_add
    linarith
  -- Integral splitting: ∫_Ω ∫_{[0,t]} σ² - ∫_Ω ∫_{[0,s]} σ² = ∫_Ω ∫_{[s,t]} σ²
  -- Step 1: Pointwise splitting using diffusion_sq_time_integrable
  have h_pw_split : ∀ ω, ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume =
      ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume +
      ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume := by
    intro ω
    exact setIntegral_Icc_split' hs hst (X.diffusion_sq_time_integrable ω t (le_trans hs hst))
  -- Step 2: Integrability of each part
  have h_int_t := X.diffusion_sq_integral_integrable t (le_trans hs hst)
  have h_int_s := X.diffusion_sq_integral_integrable s hs
  -- Integrability of ∫_{[s,t]} σ² as difference of integrable functions
  have h_int_st : Integrable
      (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ := by
    have heq : (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) =
        (fun ω => ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) -
        (fun ω => ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) := by
      ext ω; simp only [Pi.sub_apply]; linarith [h_pw_split ω]
    rw [heq]
    exact h_int_t.sub h_int_s
  -- Step 3: Rewrite using integral_sub
  have h_outer : ∫ ω, (∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ -
      ∫ ω, (∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) ∂μ =
      ∫ ω, (∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := by
    rw [← integral_sub h_int_t h_int_s]
    exact integral_congr_ae (ae_of_all _ (fun ω => by
      show (fun ω => ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) ω -
           (fun ω => ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) ω =
           ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume
      simp only []; linarith [h_pw_split ω]))
  linarith

/-! ## Integrability Infrastructure for Orthogonality -/

/-- ω ↦ ∫_{s}^{t} σ(u,ω)² du is integrable over Ω. -/
lemma diffusion_sq_interval_integrable {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ := by
  have ht : 0 ≤ t := le_trans hs hst
  have heq : (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) =
      (fun ω => ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) -
      (fun ω => ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) := by
    ext ω; simp only [Pi.sub_apply]
    linarith [setIntegral_Icc_split' hs hst (X.diffusion_sq_time_integrable ω t ht)]
  rw [heq]
  exact (X.diffusion_sq_integral_integrable t ht).sub
    (X.diffusion_sq_integral_integrable s hs)

/-- (SI(t)-SI(s))² is integrable. -/
lemma si_increment_sq_integrable' {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ := by
  have ht : 0 ≤ t := le_trans hs hst
  have ha := X.stoch_integral_sq_integrable t ht
  have hb := X.stoch_integral_sq_integrable s hs
  -- AEStronglyMeasurable via Measurable (adapted → measurable)
  have hasm : AEStronglyMeasurable
      (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ :=
    ((X.stoch_integral_aestronglyMeasurable t ht).sub
      (X.stoch_integral_aestronglyMeasurable s hs)).pow 2
  -- (a-b)² ≤ 2a² + 2b²
  exact ((ha.const_mul 2).add (hb.const_mul 2)).mono' hasm
    (ae_of_all _ fun ω => by
      simp only [Real.norm_eq_abs, Pi.add_apply]
      have h1 := sq_abs (X.stoch_integral t ω)
      have h2 := sq_abs (X.stoch_integral s ω)
      have h3 := sq_nonneg (X.stoch_integral t ω + X.stoch_integral s ω)
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith)

/-- The compensated squared increment Z = Δ² - ∫σ² is integrable. -/
lemma compensated_sq_integrable' {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω =>
      (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
      ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ :=
  (si_increment_sq_integrable' X s t hs hst).sub
    (diffusion_sq_interval_integrable X s t hs hst)

/-- ∫σ² is bounded: |∫_{s}^{t} σ²| ≤ Mσ²(t-s). -/
lemma diffusion_sq_integral_bound {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hst : s ≤ t)
    (ω : Ω) :
    |∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume| ≤ Mσ ^ 2 * (t - s) := by
  rw [abs_of_nonneg (integral_nonneg_of_ae (ae_of_all _ fun u => sq_nonneg (X.diffusion u ω)))]
  calc ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume
      ≤ ∫ u in Icc s t, Mσ ^ 2 ∂volume := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun _ => sq_nonneg _
        · exact integrable_const _
        · exact ae_of_all _ fun u => by
            calc (X.diffusion u ω) ^ 2 = |X.diffusion u ω| ^ 2 := by rw [sq_abs]
              _ ≤ Mσ ^ 2 := by exact pow_le_pow_left₀ (abs_nonneg _) (hMσ u ω) 2
    _ = Mσ ^ 2 * (t - s) := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hst, mul_comm]

/-- Z² is integrable with bounded diffusion.
    Uses: Z = Δ² - Q, so Z² ≤ 2Δ⁴ + 2Q². Δ⁴ integrable from QuarticBound, Q bounded. -/
lemma compensated_sq_sq_integrable' {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) [IsProbabilityMeasure μ]
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω =>
      ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
       ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ^ 2) μ := by
  -- (a-b)² ≤ 2a² + 2b², so Z² ≤ 2·Δ⁴ + 2·Q²
  have hΔ4 := stoch_integral_increment_L4_integrable_proof X hMσ s t hs hst
  have hQ_bdd := diffusion_sq_integral_bound X hMσ s t hst
  set C := Mσ ^ 2 * (t - s)
  -- AEStronglyMeasurable
  have hasm : AEStronglyMeasurable
      (fun ω => ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
       ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ^ 2) μ :=
    (compensated_sq_integrable' X s t hs hst).aestronglyMeasurable.pow 2
  -- Dominator: 2Δ⁴ + 2C², explicitly defined
  have hdom : Integrable
      (fun ω => 2 * (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4 + 2 * C ^ 2) μ :=
    (hΔ4.const_mul 2).add (integrable_const _)
  exact hdom.mono' hasm (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    -- Rewrite Δ⁴ = (Δ²)² for nlinarith
    have h4eq : (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4 =
        ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) ^ 2 := by ring
    rw [h4eq]
    have hQ_nn : 0 ≤ ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume :=
      integral_nonneg_of_ae (ae_of_all _ fun u => sq_nonneg (X.diffusion u ω))
    have hQ_le : ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume ≤ C := by
      have := hQ_bdd ω; rwa [abs_of_nonneg hQ_nn] at this
    nlinarith [sq_nonneg ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 +
        ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume),
      pow_le_pow_left₀ hQ_nn hQ_le 2])

/-! ## Core adapters -/

/-- Core Itô base isometry: `E[SI(t)^2] = E[∫_0^t σ^2]`. -/
theorem ItoProcessCore.stoch_integral_isometry_base_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ ω, (X.stoch_integral t ω) ^ 2 ∂μ =
    ∫ ω, (∫ s in Icc 0 t, (X.diffusion s ω) ^ 2 ∂volume) ∂μ := by
  obtain ⟨approx, hadapted_F, hbdd, hnn, hL2, hiso, _, _⟩ := C.stoch_integral_is_L2_limit
  have hadapted : ∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (X.BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i) :=
    fun n i => (hadapted_F n i).mono (FC.F_le_BM_F _) le_rfl
  have hSI_sq := stoch_integral_sq_integrable_core (X := X) C FC t ht
  have hSI_int := stoch_integral_integrable_core (X := X) C FC t ht
  have hSn_int : ∀ n, Integrable
      (SimpleProcess.stochasticIntegral_at (approx n) X.BM t) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
      (hadapted n) (hbdd n) (hnn n) t ht
  have hSub_sq : ∀ n, Integrable (fun ω =>
      (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
       X.stoch_integral t ω) ^ 2) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (hadapted n) (hbdd n) (hnn n) (X.stoch_integral t) hSI_int hSI_sq t ht
  have h_sq_conv : Tendsto
      (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2 ∂μ)
      atTop (nhds (∫ ω, (X.stoch_integral t ω) ^ 2 ∂μ)) := by
    exact sq_integral_tendsto_of_L2_tendsto hSI_sq hSub_sq
      (fun n => by
        refine ((hSub_sq n).add hSI_sq).mono'
          (((hSn_int n).sub hSI_int).aestronglyMeasurable.mul
            hSI_int.aestronglyMeasurable) ?_
        filter_upwards with ω
        simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
            X.stoch_integral t ω| - |X.stoch_integral t ω|),
          sq_abs (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
            X.stoch_integral t ω),
          sq_abs (X.stoch_integral t ω)])
      (hL2 t ht)
  have h_iso_conv := hiso t ht
  exact tendsto_nhds_unique h_sq_conv h_iso_conv

/-- Core martingale set-integral property for stochastic integrals. -/
theorem ItoProcessCore.stoch_integral_martingale_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra s) A) :
    ∫ ω in A, X.stoch_integral t ω ∂μ = ∫ ω in A, X.stoch_integral s ω ∂μ := by
  have hA' : MeasurableSet[X.BM.F.σ_algebra s] A := FC.F_le_BM_F s A hA
  obtain ⟨approx, hadapted, hbdd, hnn, hL2, _, _, _⟩ := C.stoch_integral_is_L2_limit
  exact ito_integral_martingale_setIntegral (T := t) X.BM X.stoch_integral approx
    (fun n i => (hadapted n i).mono (FC.F_le_BM_F _) le_rfl) hbdd hnn
    (fun u hu _ => hL2 u hu)
    (fun u hu _ => stoch_integral_integrable_core (X := X) C FC u hu)
    (fun u hu _ => stoch_integral_sq_integrable_core (X := X) C FC u hu)
    hs hst le_rfl hA'

/-- Core cross term: `E[SI(t) * SI(s)] = E[SI(s)^2]` for `s ≤ t`. -/
theorem ItoProcessCore.stoch_integral_cross_term_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, X.stoch_integral t ω * X.stoch_integral s ω ∂μ =
    ∫ ω, (X.stoch_integral s ω) ^ 2 ∂μ := by
  have hdecomp : ∀ ω,
      X.stoch_integral t ω * X.stoch_integral s ω =
      (X.stoch_integral s ω) ^ 2 +
      (X.stoch_integral t ω - X.stoch_integral s ω) * X.stoch_integral s ω := by
    intro ω; ring
  simp_rw [hdecomp]
  have hs_ge : s ≥ 0 := hs
  have ht_ge : t ≥ 0 := le_trans hs hst
  have hSI_s_int := stoch_integral_integrable_core (X := X) C FC s hs_ge
  have hSI_t_int := stoch_integral_integrable_core (X := X) C FC t ht_ge
  have hSI_s_sq := stoch_integral_sq_integrable_core (X := X) C FC s hs_ge
  have hSI_t_sq := stoch_integral_sq_integrable_core (X := X) C FC t ht_ge
  have hcross_int : Integrable (fun ω =>
      (X.stoch_integral t ω - X.stoch_integral s ω) * X.stoch_integral s ω) μ := by
    apply Integrable.mono' ((hSI_t_sq.add hSI_s_sq).add hSI_s_sq)
    · exact (hSI_t_int.sub hSI_s_int).aestronglyMeasurable.mul hSI_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      set a := X.stoch_integral t ω
      set b := X.stoch_integral s ω
      rw [abs_mul]
      nlinarith [sq_abs (a - b), sq_abs b, sq_abs a, sq_nonneg (|a - b| - |b|)]
  rw [integral_add hSI_s_sq hcross_int]
  suffices hcross : ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) *
      X.stoch_integral s ω ∂μ = 0 by linarith
  have hcomm : (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) *
      X.stoch_integral s ω) =
      (fun ω => X.stoch_integral s ω *
      (X.stoch_integral t ω - X.stoch_integral s ω)) := by
    ext ω; ring
  rw [hcomm]
  apply integral_mul_eq_zero_of_setIntegral_eq_zero' (F.le_ambient s)
  · exact stoch_integral_adapted_core (X := X) C FC s hs
  · exact hSI_t_int.sub hSI_s_int
  · rw [← hcomm]; exact hcross_int
  · intro A hA
    rw [integral_sub (hSI_t_int.integrableOn) (hSI_s_int.integrableOn)]
    exact sub_eq_zero.mpr (X.stoch_integral_martingale_core C FC s t hs hst A hA)

/-- Core adapter for Itô isometry of stochastic integral increments. -/
theorem ItoProcessCore.stoch_integral_isometry_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
    ∫ ω, (∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := by
  have hs_ge : s ≥ 0 := hs
  have ht_ge : t ≥ 0 := le_trans hs hst
  have hSI_s_int := stoch_integral_integrable_core (X := X) C FC s hs_ge
  have hSI_t_int := stoch_integral_integrable_core (X := X) C FC t ht_ge
  have hSI_s_sq := stoch_integral_sq_integrable_core (X := X) C FC s hs_ge
  have hSI_t_sq := stoch_integral_sq_integrable_core (X := X) C FC t ht_ge
  have hprod_int : Integrable (fun ω =>
      X.stoch_integral t ω * X.stoch_integral s ω) μ := by
    apply Integrable.mono' (hSI_t_sq.add hSI_s_sq)
    · exact hSI_t_int.aestronglyMeasurable.mul hSI_s_int.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_mul]
      nlinarith [sq_abs (X.stoch_integral t ω),
        sq_abs (X.stoch_integral s ω),
        sq_nonneg (|X.stoch_integral t ω| - |X.stoch_integral s ω|)]
  have hiso_t := X.stoch_integral_isometry_base_core C FC t (le_trans hs hst)
  have hiso_s := X.stoch_integral_isometry_base_core C FC s hs
  have hcross := X.stoch_integral_cross_term_core C FC s t hs hst
  have h_diff : ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
      ∫ ω, (∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ -
      ∫ ω, (∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := by
    have h_pw : ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
        ∫ ω, (X.stoch_integral t ω ^ 2 + X.stoch_integral s ω ^ 2 -
        2 * (X.stoch_integral t ω * X.stoch_integral s ω)) ∂μ :=
      integral_congr_ae (ae_of_all _ (fun ω => by ring))
    have h_sub := integral_sub (hSI_t_sq.add hSI_s_sq) (hprod_int.const_mul 2)
    have h_add := integral_add hSI_t_sq hSI_s_sq
    have h_mul := integral_const_mul (μ := μ) (2 : ℝ)
      (fun ω => X.stoch_integral t ω * X.stoch_integral s ω)
    simp only [Pi.add_apply] at h_sub h_add
    linarith
  have h_pw_split : ∀ ω, ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume =
      ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume +
      ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume := by
    intro ω
    exact setIntegral_Icc_split' hs hst (D.diffusion_sq_time_integrable ω t (le_trans hs hst))
  have h_int_t := D.diffusion_sq_integral_integrable t (le_trans hs hst)
  have h_int_s := D.diffusion_sq_integral_integrable s hs
  have h_int_st : Integrable
      (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ := by
    have heq : (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) =
        (fun ω => ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) -
        (fun ω => ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) := by
      ext ω; simp only [Pi.sub_apply]; linarith [h_pw_split ω]
    rw [heq]
    exact h_int_t.sub h_int_s
  have h_outer : ∫ ω, (∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ -
      ∫ ω, (∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) ∂μ =
      ∫ ω, (∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := by
    rw [← integral_sub h_int_t h_int_s]
    exact integral_congr_ae (ae_of_all _ (fun ω => by
      show (fun ω => ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) ω -
           (fun ω => ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) ω =
           ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume
      simp only []; linarith [h_pw_split ω]))
  linarith

/-- Core adapter for interval-integrability of `∫_s^t σ²`. -/
lemma ItoProcessCore.diffusion_sq_interval_integrable_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    (D : ItoProcessDiffusionRegularity X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ := by
  have ht : 0 ≤ t := le_trans hs hst
  have heq : (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) =
      (fun ω => ∫ u in Icc 0 t, (X.diffusion u ω) ^ 2 ∂volume) -
      (fun ω => ∫ u in Icc 0 s, (X.diffusion u ω) ^ 2 ∂volume) := by
    ext ω; simp only [Pi.sub_apply]
    linarith [setIntegral_Icc_split' hs hst (D.diffusion_sq_time_integrable ω t ht)]
  rw [heq]
  exact (D.diffusion_sq_integral_integrable t ht).sub
    (D.diffusion_sq_integral_integrable s hs)

/-- Core adapter for square-integrability of stochastic integral increments. -/
lemma ItoProcessCore.si_increment_sq_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ := by
  have ht : 0 ≤ t := le_trans hs hst
  have ha := stoch_integral_sq_integrable_core (X := X) C FC t ht
  have hb := stoch_integral_sq_integrable_core (X := X) C FC s hs
  have hasm : AEStronglyMeasurable
      (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ :=
    ((stoch_integral_aestronglyMeasurable_core (X := X) C FC t ht).sub
      (stoch_integral_aestronglyMeasurable_core (X := X) C FC s hs)).pow 2
  exact ((ha.const_mul 2).add (hb.const_mul 2)).mono' hasm
    (ae_of_all _ fun ω => by
      simp only [Real.norm_eq_abs, Pi.add_apply]
      have h1 := sq_abs (X.stoch_integral t ω)
      have h2 := sq_abs (X.stoch_integral s ω)
      have h3 := sq_nonneg (X.stoch_integral t ω + X.stoch_integral s ω)
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith)

/-- Core adapter for integrability of compensated squared increments. -/
lemma ItoProcessCore.compensated_sq_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω =>
      (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
      ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ := by
  exact (X.si_increment_sq_integrable_core C FC s t hs hst).sub
    (X.diffusion_sq_interval_integrable_core D s t hs hst)

/-- Core adapter for the deterministic bound on `∫_s^t σ²`. -/
lemma ItoProcessCore.diffusion_sq_integral_bound_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hst : s ≤ t)
    (ω : Ω) :
    |∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume| ≤ Mσ ^ 2 * (t - s) := by
  rw [abs_of_nonneg (integral_nonneg_of_ae (ae_of_all _ fun u => sq_nonneg (X.diffusion u ω)))]
  calc ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume
      ≤ ∫ u in Icc s t, Mσ ^ 2 ∂volume := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun _ => sq_nonneg _
        · exact integrable_const _
        · exact ae_of_all _ fun u => by
            calc (X.diffusion u ω) ^ 2 = |X.diffusion u ω| ^ 2 := by rw [sq_abs]
              _ ≤ Mσ ^ 2 := by
                simpa using (pow_le_pow_left₀ (abs_nonneg _) (hMσ u ω) 2)
    _ = Mσ ^ 2 * (t - s) := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le hst, mul_comm]

/-- Core adapter for square-integrability of compensated squared increments. -/
lemma ItoProcessCore.compensated_sq_sq_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4) μ →
    Integrable (fun ω =>
      ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
       ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ^ 2) μ := by
  intro hΔ4
  have hQ_bdd := X.diffusion_sq_integral_bound_core hMσ s t hst
  set C0 := Mσ ^ 2 * (t - s)
  have hasm : AEStronglyMeasurable
      (fun ω => ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
       ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ^ 2) μ :=
    (X.compensated_sq_integrable_core C D FC s t hs hst).aestronglyMeasurable.pow 2
  have hdom : Integrable
      (fun ω => 2 * (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4 + 2 * C0 ^ 2) μ := by
    have h1 : Integrable (fun ω => 2 * (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4) μ :=
      hΔ4.const_mul 2
    have h2 : Integrable (fun _ : Ω => 2 * C0 ^ 2) μ := integrable_const _
    exact h1.add h2
  exact hdom.mono' hasm (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h4eq : (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4 =
        ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) ^ 2 := by ring
    rw [h4eq]
    have hQ_nn : 0 ≤ ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume :=
      integral_nonneg_of_ae (ae_of_all _ fun u => sq_nonneg (X.diffusion u ω))
    have hQ_le : ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume ≤ C0 := by
      have := hQ_bdd ω; rwa [abs_of_nonneg hQ_nn] at this
    nlinarith [sq_nonneg ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 +
        ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume),
      pow_le_pow_left₀ hQ_nn hQ_le 2])

/-- Regularity-first adapter for Itô isometry of stochastic integral increments. -/
theorem ItoProcessCore.stoch_integral_isometry_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ =
    ∫ ω, (∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ := by
  simpa using
    (X.stoch_integral_isometry_core
      (C := R.toConstruction)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      s t hs hst)

/-- Regularity-first adapter for interval-integrability of `∫_s^t σ²`. -/
lemma ItoProcessCore.diffusion_sq_interval_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ := by
  simpa using
    (X.diffusion_sq_interval_integrable_core
      (D := R.toDiffusionRegularity)
      s t hs hst)

/-- Regularity-first adapter for square-integrability of stochastic integral increments. -/
lemma ItoProcessCore.si_increment_sq_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ := by
  simpa using
    (X.si_increment_sq_integrable_core
      (C := R.toConstruction) (FC := R.toFiltrationCompatibility)
      s t hs hst)

/-- Regularity-first adapter for integrability of compensated squared increments. -/
lemma ItoProcessCore.compensated_sq_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω =>
      (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
      ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) μ := by
  simpa using
    (X.compensated_sq_integrable_core
      (C := R.toConstruction)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      s t hs hst)

/-- Regularity-first adapter for the deterministic bound on `∫_s^t σ²`. -/
lemma ItoProcessCore.diffusion_sq_integral_bound_core_ofRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hst : s ≤ t)
    (ω : Ω) :
    |∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume| ≤ Mσ ^ 2 * (t - s) := by
  simpa using
    (X.diffusion_sq_integral_bound_core
      hMσ s t hst ω)

/-- Regularity-first adapter for square-integrability of compensated increments. -/
lemma ItoProcessCore.compensated_sq_sq_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω =>
      ((X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 -
       ∫ u in Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ^ 2) μ := by
  let Xp : ItoProcess F μ := X.toItoProcess R
  have hMσp : ∀ t ω, |Xp.diffusion t ω| ≤ Mσ := by
    intro t' ω
    change |X.diffusion t' ω| ≤ Mσ
    exact hMσ t' ω
  have hΔ4 : Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω) ^ 4) μ := by
    simpa [Xp] using stoch_integral_increment_L4_integrable_proof Xp hMσp s t hs hst
  simpa using
    (X.compensated_sq_sq_integrable_core
      (C := R.toConstruction)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      hMσ s t hs hst hΔ4)

end SPDE
