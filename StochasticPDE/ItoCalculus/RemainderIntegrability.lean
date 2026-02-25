/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.ProcessContinuity
import StochasticPDE.ItoCalculus.ItoRemainderDef
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Ito Remainder Integrability

Under the standard boundedness hypotheses of Itô's formula, the Itô remainder
`itoRemainder` is integrable (L¹) and square-integrable (L²).

## Main Results

* `integrable_of_sq_integrable` — L² implies L¹ for finite measures
* `process_integrable` — X_t ∈ L¹ under bounded drift + X_0 ∈ L¹
* `process_sq_integrable` — X_t ∈ L² under bounded drift + X_0 ∈ L²
* `itoRemainder_integrable` — the Itô remainder is in L¹
* `itoRemainder_sq_integrable` — the Itô remainder is in L²
-/

namespace SPDE

open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## L² to L¹ -/

/-- |x| ≤ x² + 1 for all real x. -/
private lemma abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x]

/-- L² implies L¹ for finite measures. -/
theorem integrable_of_sq_integrable [IsFiniteMeasure μ]
    {g : Ω → ℝ} (hg_meas : AEStronglyMeasurable g μ)
    (hg2 : Integrable (fun ω => (g ω) ^ 2) μ) :
    Integrable g μ :=
  (hg2.add (integrable_const 1)).mono' hg_meas
    (ae_of_all _ fun ω => by
      simp only [Real.norm_eq_abs, Pi.add_apply]
      exact abs_le_sq_add_one (g ω))

/-! ## Mean value bound -/

/-- Mean value bound: differentiable + bounded derivative → Lipschitz bound. -/
theorem abs_sub_le_of_deriv_bounded {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {M : ℝ} (hM : ∀ x, |deriv g x| ≤ M) (a b : ℝ) :
    |g a - g b| ≤ M * |a - b| := by
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs (a - b)]
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ => hg.differentiableAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact hM x)
    convex_univ (mem_univ _) (mem_univ _)

/-! ## Growth bounds -/

/-- Spatial growth: |f(t,x)| ≤ |f(t,0)| + Mx * |x| -/
theorem f_spatial_bound {f : ℝ → ℝ → ℝ}
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    (t x : ℝ) :
    |f t x| ≤ |f t 0| + Mx * |x| := by
  have hdiff : Differentiable ℝ (fun x => f t x) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp (hf_x t)).1
  have h : |f t x - f t 0| ≤ Mx * |x - 0| :=
    abs_sub_le_of_deriv_bounded hdiff (fun y => hMx t y) x 0
  simp only [sub_zero] at h
  linarith [abs_sub_abs_le_abs_sub (f t x) (f t 0)]

/-- Combined growth: |f(t,x)| ≤ |f(0,0)| + Mt*|t| + Mx*|x| -/
theorem f_growth_bound {f : ℝ → ℝ → ℝ}
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    {Mt : ℝ} (hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt)
    (t x : ℝ) :
    |f t x| ≤ |f 0 0| + Mt * |t| + Mx * |x| := by
  have h_time : |f t 0 - f 0 0| ≤ Mt * |t - 0| :=
    abs_sub_le_of_deriv_bounded (hf_t 0) (fun s => hMt s 0) t 0
  simp only [sub_zero] at h_time
  have h_space := f_spatial_bound hf_x hMx t x
  linarith [abs_sub_abs_le_abs_sub (f t 0) (f 0 0)]

/-! ## Process integrability -/

/-- Ambient measurability from filtration-adapted. -/
private lemma process_aesm {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) :
    AEStronglyMeasurable (X.process t) μ :=
  ((X.process_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable

private lemma si_aesm {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (ht : 0 ≤ t) :
    AEStronglyMeasurable (X.stoch_integral t) μ :=
  X.stoch_integral_aestronglyMeasurable t ht

/-- SI_t ∈ L¹ from SI_t ∈ L². -/
theorem stoch_integral_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (X.stoch_integral t) μ :=
  integrable_of_sq_integrable (si_aesm X t ht) (X.stoch_integral_sq_integrable t ht)

/-- Drift integral bound: |∫₀ᵗ μ ds| ≤ Md * t. -/
theorem drift_integral_abs_bound {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    (_hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    |∫ s in Icc 0 t, X.drift s ω ∂volume| ≤ Md * t := by
  rw [← Real.norm_eq_abs]
  have h_finite : volume (Icc (0 : ℝ) t) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have h_bound : ∀ s ∈ Icc (0 : ℝ) t, ‖X.drift s ω‖ ≤ Md :=
    fun s _ => by rw [Real.norm_eq_abs]; exact hd s ω
  calc ‖∫ s in Icc 0 t, X.drift s ω ∂volume‖
      ≤ Md * volume.real (Icc (0 : ℝ) t) := norm_setIntegral_le_of_norm_le_const h_finite h_bound
    _ = Md * t := by rw [Real.volume_real_Icc_of_le ht, sub_zero]

/-- X_t ∈ L¹ from X_0 ∈ L¹ + bounded drift. -/
theorem process_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (hX0 : Integrable (X.process 0) μ)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md) (hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (X.process t) μ := by
  -- Use Integrable.mono': |X_t| ≤ |X_0| + Md*t + |SI_t| a.e.
  apply Integrable.mono'
    ((hX0.norm.add (integrable_const (Md * t))).add (stoch_integral_integrable X t ht).norm)
    (process_aesm X t)
  filter_upwards [X.integral_form t ht] with ω hω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [hω]
  have h_drift := drift_integral_abs_bound X hd hMd t ht ω
  have h1 := norm_add_le (X.process 0 ω + ∫ s in Icc 0 t, X.drift s ω ∂volume)
    (X.stoch_integral t ω)
  have h2 := norm_add_le (X.process 0 ω) (∫ s in Icc 0 t, X.drift s ω ∂volume)
  simp only [Real.norm_eq_abs] at h1 h2
  linarith

/-- X_t ∈ L² from X_0 ∈ L² + bounded drift. -/
theorem process_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md) (hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (X.process t ω) ^ 2) μ := by
  -- |X_t|² ≤ 3(|X_0|² + (Md*t)² + |SI_t|²) a.e.
  have hasm : AEStronglyMeasurable (fun ω => (X.process t ω) ^ 2) μ :=
    (process_aesm X t).pow 2
  apply Integrable.mono'
    (((hX0_sq.add (integrable_const ((Md * t) ^ 2))).add
      (X.stoch_integral_sq_integrable t ht)).const_mul 3) hasm
  filter_upwards [X.integral_form t ht] with ω hω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [hω]
  have h_drift := drift_integral_abs_bound X hd hMd t ht ω
  set a := X.process 0 ω
  set b := ∫ s in Icc 0 t, X.drift s ω ∂volume
  set c := X.stoch_integral t ω
  have hb : b ^ 2 ≤ (Md * t) ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le h_drift) (le_of_abs_le h_drift)
  -- (a + b + c)² ≤ 3(a² + b² + c²)
  have h_sq_goal : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + (Md * t) ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  rw [abs_of_nonneg (sq_nonneg (a + b + c))]
  linarith

/-! ## Remainder integrability -/

/-- The Itô remainder is integrable (L¹).
    Requires X_0 ∈ L¹ and the standard boundedness hypotheses.
    The joint continuity hypotheses are needed for measurability of the Lebesgue
    integral term (they ensure the integrand is measurable in ω for each s). -/
theorem itoRemainder_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    {Mt : ℝ} (hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt)
    {Mxx : ℝ} (hMxx : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mxx)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    {Mσ : ℝ} (hσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    -- Joint continuity of derivatives (C^{1,2} regularity)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0 : Integrable (X.process 0) μ)
    (t' : ℝ) (ht' : 0 ≤ t') :
    Integrable (itoRemainder X f t') μ := by
  -- itoRemainder = f(t', X_{t'}) - f(0, X_0) - ∫₀^{t'} [bounded integrand] ds
  -- Each component is integrable
  unfold itoRemainder
  haveI : Nonempty Ω := by
    by_contra h; rw [not_nonempty_iff] at h
    have := @IsProbabilityMeasure.measure_univ _ _ μ _
    rw [univ_eq_empty_iff.mpr h, measure_empty] at this; exact zero_ne_one this
  have hMd : 0 ≤ Md := le_trans (abs_nonneg _) (hd 0 (Classical.arbitrary Ω))
  have hMσ : 0 ≤ Mσ := le_trans (abs_nonneg _) (hσ 0 (Classical.arbitrary Ω))
  apply Integrable.sub
  · apply Integrable.sub
    · -- f(t', X_{t'}) is integrable: |f(t', X_{t'})| ≤ C + Mx|X_{t'}|
      have hXt := process_integrable X hX0 hd hMd t' ht'
      apply Integrable.mono'
        ((integrable_const (|f 0 0| + Mt * |t'|)).add (hXt.norm.const_mul Mx))
        (((hf_x t').continuous.measurable.comp
          ((X.process_adapted t').mono (F.le_ambient t') le_rfl)).aestronglyMeasurable)
      filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply, Function.comp]
      exact le_trans (f_growth_bound hf_t hf_x hMx hMt t' (X.process t' ω))
        (by linarith [abs_nonneg (X.process t' ω)])
    · -- f(0, X_0) is integrable
      apply Integrable.mono'
        ((integrable_const (|f 0 0|)).add (hX0.norm.const_mul Mx))
        (((hf_x 0).continuous.measurable.comp
          ((X.process_adapted 0).mono (F.le_ambient 0) le_rfl)).aestronglyMeasurable)
      filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply, Function.comp]
      exact le_trans (f_spatial_bound hf_x hMx 0 (X.process 0 ω))
        (by linarith [abs_nonneg (X.process 0 ω)])
  · -- Lebesgue integral term is bounded → integrable
    -- The integrand is bounded by C = Mt + Mx*Md + ½*Mxx*Mσ² for all (s, ω)
    set C := Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2 with hC_def
    -- The integral is bounded by C * t' for all ω
    -- AEStronglyMeasurable follows from joint continuity of the derivatives
    -- composed with the measurable/adapted processes
    apply Integrable.mono' (integrable_const (|C| * t'))
    · -- AEStronglyMeasurable of the parametric integral.
      -- Strategy: construct a modification Y of X.process with everywhere-continuous
      -- paths (zeroing out on a null set), prove Y is jointly measurable via Mathlib's
      -- measurable_uncurry_of_continuous_of_measurable, then transfer back a.e.
      --
      -- Step 1: Extract a measurable null set containing bad paths
      have h_null : μ {ω | ¬Continuous (fun t => X.process t ω)} = 0 :=
        ae_iff.mp X.process_continuous
      let S := toMeasurable μ {ω | ¬Continuous (fun t => X.process t ω)}
      have hS_meas : MeasurableSet S := measurableSet_toMeasurable μ _
      have hS_null : μ S = 0 := by rw [measure_toMeasurable]; exact h_null
      have hS_super : {ω | ¬Continuous (fun t => X.process t ω)} ⊆ S :=
        subset_toMeasurable μ _
      -- Step 2: Define modification Y with everywhere-continuous paths
      let Y : ℝ → Ω → ℝ := fun t ω => Sᶜ.indicator (X.process t) ω
      -- Step 3: Y is measurable at each time
      have hY_meas : ∀ t, Measurable (Y t) := fun t =>
        ((X.process_adapted t).mono (F.le_ambient t) le_rfl).indicator hS_meas.compl
      -- Step 4: Y has continuous paths for ALL ω
      have hY_cont : ∀ ω, Continuous (fun t => Y t ω) := by
        intro ω
        by_cases h : ω ∈ S
        · -- ω ∈ S: Y(t, ω) = 0 for all t, since ω ∉ Sᶜ
          have hnotSc : ω ∉ Sᶜ := fun hc => hc h
          have : ∀ t, Y t ω = 0 := fun t =>
            Set.indicator_of_notMem hnotSc _
          simp_rw [this]; exact continuous_const
        · -- ω ∉ S: Y(t, ω) = X.process t ω which is continuous
          have hcont : Continuous (fun t => X.process t ω) := by
            by_contra hc; exact h (hS_super hc)
          have hSc : ω ∈ Sᶜ := h
          have : ∀ t, Y t ω = X.process t ω := fun t =>
            Set.indicator_of_mem hSc _
          simp_rw [this]; exact hcont
      -- Step 5: Y is jointly measurable (Mathlib's measurable_uncurry_of_continuous_of_measurable)
      have hY_jm : Measurable (Function.uncurry Y) :=
        measurable_uncurry_of_continuous_of_measurable hY_cont hY_meas
      -- Step 6: Build the jointly measurable integrand using Y
      have h_sY : Measurable (fun p : ℝ × Ω => (p.1, Y p.1 p.2)) :=
        measurable_fst.prodMk hY_jm
      have h_jm_Y : Measurable (fun p : ℝ × Ω =>
          deriv (fun u => f u (Y p.1 p.2)) p.1 +
          deriv (fun x => f p.1 x) (Y p.1 p.2) * X.drift p.1 p.2 +
          1 / 2 * deriv (deriv (fun x => f p.1 x)) (Y p.1 p.2) *
            (X.diffusion p.1 p.2) ^ 2) := by
        apply Measurable.add
        · apply Measurable.add
          · exact hf_t_cont.measurable.comp h_sY
          · exact (hf'_cont.measurable.comp h_sY).mul X.drift_jointly_measurable
        · exact (measurable_const.mul (hf''_cont.measurable.comp h_sY)).mul
            (X.diffusion_jointly_measurable.pow_const 2)
      -- Step 7: The parametric integral using Y is StronglyMeasurable
      have h_int_sm := h_jm_Y.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Icc 0 t'))
      -- Step 8: The integrals using Y and X agree a.e.
      have hS_ae : Sᶜ ∈ ae μ := by rw [mem_ae_iff, compl_compl]; exact hS_null
      exact h_int_sm.aestronglyMeasurable.congr (by
        filter_upwards [hS_ae] with ω hω
        congr 1; ext s
        show deriv (fun u => f u (Y s ω)) s +
          deriv (fun x => f s x) (Y s ω) * X.drift s ω +
          1 / 2 * deriv (deriv (fun x => f s x)) (Y s ω) * (X.diffusion s ω) ^ 2 =
          deriv (fun u => f u (X.process s ω)) s +
          deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
          1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω) ^ 2
        rw [show Y s ω = X.process s ω from Set.indicator_of_mem hω _])
    · filter_upwards with ω
      simp only [Real.norm_eq_abs]
      -- Bound the integral using boundedness of the integrand
      have h_finite : volume (Icc (0 : ℝ) t') < ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      have h_integrand_bound : ∀ s ∈ Icc (0 : ℝ) t',
          |deriv (fun u => f u (X.process s ω)) s +
           deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
           1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
             (X.diffusion s ω) ^ 2| ≤ |C| := by
        intro s _
        calc |deriv (fun u => f u (X.process s ω)) s +
              deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
              1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                (X.diffusion s ω) ^ 2|
            ≤ |deriv (fun u => f u (X.process s ω)) s| +
              |deriv (fun x => f s x) (X.process s ω) * X.drift s ω| +
              |1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                (X.diffusion s ω) ^ 2| := by
                  linarith [abs_add_le (deriv (fun u => f u (X.process s ω)) s +
                    deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
                    (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                      (X.diffusion s ω) ^ 2),
                    abs_add_le (deriv (fun u => f u (X.process s ω)) s)
                      (deriv (fun x => f s x) (X.process s ω) * X.drift s ω)]
          _ ≤ Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2 := by
                have h1 := hMt s (X.process s ω)
                have h2 := hMx s (X.process s ω)
                have h3 := hd s ω
                have h4 := hMxx s (X.process s ω)
                have h5 := hσ s ω
                have := abs_mul (deriv (fun x => f s x) (X.process s ω)) (X.drift s ω)
                have := abs_mul (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω))
                  ((X.diffusion s ω) ^ 2)
                have := abs_mul (1 / 2 : ℝ) (deriv (deriv (fun x => f s x)) (X.process s ω))
                have h_sq : |X.diffusion s ω ^ 2| ≤ Mσ ^ 2 := by
                  rw [abs_of_nonneg (sq_nonneg _)]
                  exact sq_le_sq' (neg_le_of_abs_le h5) (le_of_abs_le h5)
                nlinarith [abs_nonneg (deriv (fun x => f s x) (X.process s ω)),
                  abs_nonneg (X.drift s ω),
                  abs_nonneg (deriv (deriv (fun x => f s x)) (X.process s ω)),
                  abs_nonneg (X.diffusion s ω ^ 2)]
          _ ≤ |C| := by rw [hC_def]; exact le_abs_self _
      rw [← Real.norm_eq_abs (∫ s in Icc 0 t', _ ∂volume)]
      calc ‖∫ s in Icc 0 t', _ ∂volume‖
          ≤ |C| * volume.real (Icc (0 : ℝ) t') :=
            norm_setIntegral_le_of_norm_le_const h_finite
              (fun s hs => by rw [Real.norm_eq_abs]; exact h_integrand_bound s hs)
        _ = |C| * t' := by rw [Real.volume_real_Icc_of_le ht', sub_zero]

/-- The squared Itô remainder is integrable (remainder is in L²).
    Requires X_0 ∈ L² and the standard boundedness hypotheses. -/
theorem itoRemainder_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    {Mt : ℝ} (hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt)
    {Mxx : ℝ} (hMxx : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mxx)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    {Mσ : ℝ} (hσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    -- Joint continuity of derivatives (C^{1,2} regularity)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ)
    (t' : ℝ) (ht' : 0 ≤ t') :
    Integrable (fun ω => (itoRemainder X f t' ω) ^ 2) μ := by
  -- Strategy: |itoRemainder(ω)|² ≤ bound² which is integrable
  -- First derive L¹ integrability of X_0 from L²
  haveI : Nonempty Ω := by
    by_contra h; rw [not_nonempty_iff] at h
    have := @IsProbabilityMeasure.measure_univ _ _ μ _
    rw [univ_eq_empty_iff.mpr h, measure_empty] at this; exact zero_ne_one this
  have hMd : 0 ≤ Md := le_trans (abs_nonneg _) (hd 0 (Classical.arbitrary Ω))
  have hMσ : 0 ≤ Mσ := le_trans (abs_nonneg _) (hσ 0 (Classical.arbitrary Ω))
  have hX0 : Integrable (X.process 0) μ :=
    integrable_of_sq_integrable (process_aesm X 0) hX0_sq
  -- The itoRemainder is integrable (L¹)
  have hrem_int := itoRemainder_integrable X f hf_t hf_x hMx hMt hMxx hd hσ
    hf_t_cont hf'_cont hf''_cont hX0 t' ht'
  -- AEStronglyMeasurable of the squared remainder
  have hasm : AEStronglyMeasurable (fun ω => (itoRemainder X f t' ω) ^ 2) μ :=
    hrem_int.aestronglyMeasurable.pow 2
  -- Bound: |itoRemainder(ω)| ≤ C₁ + C₂|X_{t'}(ω)| + C₃|X_0(ω)|
  -- where C₁ = 2|f(0,0)| + Mt|t'| + C_int*t', C₂ = Mx, C₃ = Mx
  -- C_int = Mt + Mx*Md + ½Mxx*Mσ²
  set C_int := Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2
  set C₁ := 2 * |f 0 0| + Mt * |t'| + |C_int| * t' + Mx * Md * t'
  -- |itoRemainder(ω)|² ≤ (C₁ + Mx|X_{t'}| + Mx|X_0|)²
  --                     ≤ 3(C₁² + Mx²|X_{t'}|² + Mx²|X_0|²)
  apply Integrable.mono'
    ((((integrable_const (C₁ ^ 2)).add
      ((process_sq_integrable X hX0_sq hd hMd t' ht').const_mul (Mx ^ 2))).add
      (hX0_sq.const_mul (Mx ^ 2))).const_mul 3) hasm
  filter_upwards [X.integral_form t' ht'] with ω hω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (sq_nonneg (itoRemainder X f t' ω))]
  -- Bound |itoRemainder|
  unfold itoRemainder
  set Xt := X.process t' ω
  set X0 := X.process 0 ω
  set drift_int := ∫ s in Icc 0 t', X.drift s ω ∂volume
  set lebesgue_int := ∫ s in Icc 0 t',
    (deriv (fun u => f u (X.process s ω)) s +
     deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
     (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2) ∂volume
  -- |f(t', X_{t'})| ≤ |f(0,0)| + Mt|t'| + Mx|X_{t'}|
  have h_fXt := f_growth_bound hf_t hf_x hMx hMt t' Xt
  -- |f(0, X_0)| ≤ |f(0,0)| + Mx|X_0|
  have h_fX0 := f_spatial_bound hf_x hMx 0 X0
  -- |lebesgue_int| ≤ |C_int| * t'
  have h_lint : |lebesgue_int| ≤ |C_int| * t' := by
    rw [← Real.norm_eq_abs]
    have h_finite : volume (Icc (0 : ℝ) t') < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    calc ‖lebesgue_int‖
        ≤ |C_int| * volume.real (Icc (0 : ℝ) t') := by
          apply norm_setIntegral_le_of_norm_le_const h_finite
          intro s _
          rw [Real.norm_eq_abs]
          calc |deriv (fun u => f u (X.process s ω)) s +
                deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
                1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                  (X.diffusion s ω) ^ 2|
              ≤ |deriv (fun u => f u (X.process s ω)) s| +
                |deriv (fun x => f s x) (X.process s ω) * X.drift s ω| +
                |1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                  (X.diffusion s ω) ^ 2| := by
                    linarith [abs_add_le (deriv (fun u => f u (X.process s ω)) s +
                      deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
                      (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                        (X.diffusion s ω) ^ 2),
                      abs_add_le (deriv (fun u => f u (X.process s ω)) s)
                        (deriv (fun x => f s x) (X.process s ω) * X.drift s ω)]
            _ ≤ Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2 := by
                have h1 := hMt s (X.process s ω)
                have h2 := hMx s (X.process s ω)
                have h3 := hd s ω
                have h4 := hMxx s (X.process s ω)
                have h5 := hσ s ω
                have := abs_mul (deriv (fun x => f s x) (X.process s ω)) (X.drift s ω)
                have := abs_mul (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω))
                  ((X.diffusion s ω) ^ 2)
                have := abs_mul (1 / 2 : ℝ) (deriv (deriv (fun x => f s x)) (X.process s ω))
                have h_sq : |X.diffusion s ω ^ 2| ≤ Mσ ^ 2 := by
                  rw [abs_of_nonneg (sq_nonneg _)]
                  exact sq_le_sq' (neg_le_of_abs_le h5) (le_of_abs_le h5)
                nlinarith [abs_nonneg (deriv (fun x => f s x) (X.process s ω)),
                  abs_nonneg (X.drift s ω),
                  abs_nonneg (deriv (deriv (fun x => f s x)) (X.process s ω)),
                  abs_nonneg (X.diffusion s ω ^ 2)]
            _ ≤ |C_int| := le_abs_self _
      _ = |C_int| * t' := by rw [Real.volume_real_Icc_of_le ht', sub_zero]
  -- |itoRemainder| = |f(t', X_{t'}) - f(0, X_0) - lebesgue_int|
  -- ≤ |f(t', X_{t'})| + |f(0, X_0)| + |lebesgue_int|
  have h_rem_bound : |f t' Xt - f 0 X0 - lebesgue_int| ≤ C₁ + Mx * |Xt| + Mx * |X0| := by
    calc |f t' Xt - f 0 X0 - lebesgue_int|
        ≤ |f t' Xt| + |f 0 X0| + |lebesgue_int| := by
          linarith [abs_sub (f t' Xt) (f 0 X0),
            abs_sub (f t' Xt - f 0 X0) lebesgue_int]
      _ ≤ (|f 0 0| + Mt * |t'| + Mx * |Xt|) + (|f 0 0| + Mx * |X0|) +
            |C_int| * t' := by linarith
      _ = C₁ - Mx * Md * t' + Mx * |Xt| + Mx * |X0| := by ring
      _ ≤ C₁ + Mx * |Xt| + Mx * |X0| := by linarith [mul_nonneg (mul_nonneg (le_trans (abs_nonneg _) (hMx 0 0)) hMd) ht']
  -- Now square: |rem|² ≤ (C₁ + Mx|Xt| + Mx|X0|)² ≤ 3(C₁² + Mx²Xt² + Mx²X0²)
  have h_sq : (f t' Xt - f 0 X0 - lebesgue_int) ^ 2 ≤
      3 * (C₁ ^ 2 + Mx ^ 2 * Xt ^ 2 + Mx ^ 2 * X0 ^ 2) := by
    have h := h_rem_bound
    -- (a + b + c)² ≤ 3(a² + b² + c²)
    set a := C₁; set b := Mx * |Xt|; set c := Mx * |X0|
    have hab : |f t' Xt - f 0 X0 - lebesgue_int| ^ 2 ≤ (a + b + c) ^ 2 :=
      sq_le_sq' (by linarith [abs_nonneg (f t' Xt - f 0 X0 - lebesgue_int)]) h
    have h_3sq : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    calc (f t' Xt - f 0 X0 - lebesgue_int) ^ 2
        ≤ |f t' Xt - f 0 X0 - lebesgue_int| ^ 2 := by
          rw [sq_abs]
      _ ≤ (a + b + c) ^ 2 := hab
      _ ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := h_3sq
      _ = 3 * (C₁ ^ 2 + Mx ^ 2 * |Xt| ^ 2 + Mx ^ 2 * |X0| ^ 2) := by ring
      _ = 3 * (C₁ ^ 2 + Mx ^ 2 * Xt ^ 2 + Mx ^ 2 * X0 ^ 2) := by
          rw [sq_abs, sq_abs]
  linarith

/-! ## Core adapters -/

/-- Helper: core stochastic integral at time `t` is `F_t`-measurable. -/
private theorem stochasticIntegral_at_Ft_measurable_core
    {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (hBM_F : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (W.process t))
    (h_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (F.σ_algebra (H.times i)) _ (H.values i))
    (t : ℝ) :
    @Measurable Ω ℝ (F.σ_algebra t) _ (H.stochasticIntegral_at W t) := by
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
    · exact ((h_adapted i).mono (F.mono _ t hts) le_rfl).mul
        (((hBM_F _).mono (F.mono _ t (min_le_right _ _)) le_rfl).sub
         ((hBM_F _).mono (F.mono _ t (min_le_right _ _)) le_rfl))
    · push_neg at hts
      have h1 : min (H.times i) t = t := min_eq_right (le_of_lt hts)
      have h2 : min (H.times ⟨i + 1, hi⟩) t = t :=
        min_eq_right (le_trans (le_of_lt hts)
          (le_of_lt (H.increasing i ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))))
      have : (fun ω => H.values i ω * (W.process (min (H.times ⟨i + 1, hi⟩) t) ω -
                         W.process (min (H.times i) t) ω)) = fun _ => 0 := by
        ext ω; rw [h1, h2, sub_self, mul_zero]
      rw [this]; exact measurable_const
  · simp only [dif_neg hi]; exact measurable_const

/-- Core-version a.e.-strong measurability for `stoch_integral`. -/
private theorem stoch_integral_aestronglyMeasurable_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (t : ℝ) (ht : 0 ≤ t) :
    AEStronglyMeasurable (X.stoch_integral t) μ := by
  obtain ⟨approx, h_adapted, _, _, _, _, _, hae⟩ := C.stoch_integral_is_L2_limit
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n => ((stochasticIntegral_at_Ft_measurable_core (approx n) X.BM
      FC.BM_adapted_to_F (h_adapted n) t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable)
    (hae t ht)

/-- Core-version square-integrability for `stoch_integral`. -/
private theorem stoch_integral_sq_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ) (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (t : ℝ) (ht : t ≥ 0) :
    Integrable (fun ω => (X.stoch_integral t ω) ^ 2) μ := by
  obtain ⟨approx, h_adapted, h_bounded, h_nonneg, _, hiso, _, hae⟩ :=
    C.stoch_integral_is_L2_limit
  have hSI_asm := stoch_integral_aestronglyMeasurable_core X C FC t ht
  have hSI_n_meas : ∀ n, Measurable
      (fun ω => SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) :=
    fun n => (stochasticIntegral_at_Ft_measurable_core (approx n) X.BM
      FC.BM_adapted_to_F (h_adapted n) t).mono (F.le_ambient t) le_rfl
  have hSI_n_sq_int : ∀ n, Integrable
      (fun ω => (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2) μ := by
    intro n
    have h := SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (fun i => (h_adapted n i).mono (FC.F_le_BM_F _) le_rfl) (h_bounded n) (h_nonneg n)
      0 (integrable_const 0) (by simp) t ht
    simp [sub_zero] at h; exact h
  refine ⟨hSI_asm.pow _, ?_⟩
  show ∫⁻ ω, ‖(X.stoch_integral t ω) ^ 2‖ₑ ∂μ < ⊤
  have h_enorm_sq : ∀ (x : ℝ), ‖x ^ 2‖ₑ = ENNReal.ofReal (x ^ 2) :=
    fun x => Real.enorm_eq_ofReal (sq_nonneg x)
  simp_rw [h_enorm_sq]
  have hae_sq : ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => ENNReal.ofReal
        ((SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω) ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal ((X.stoch_integral t ω) ^ 2))) := by
    filter_upwards [hae t ht] with ω hω
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_pow 2).tendsto _).comp hω)
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

/-- Core-version integrability for `stoch_integral`. -/
theorem stoch_integral_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ) (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (X.stoch_integral t) μ := by
  have hsq := stoch_integral_sq_integrable_core X C FC t ht
  have hasm := stoch_integral_aestronglyMeasurable_core X C FC t ht
  refine (hsq.add (integrable_const 1)).mono' hasm ?_
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (|X.stoch_integral t ω| - 1), sq_abs (X.stoch_integral t ω),
    abs_nonneg (X.stoch_integral t ω)]

/-- Ambient measurability for `ItoProcessCore.process`. -/
private lemma process_aesm_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) (t : ℝ) :
    AEStronglyMeasurable (X.process t) μ :=
  ((X.process_adapted t).mono (F.le_ambient t) le_rfl).aestronglyMeasurable

/-- Core drift integral bound: `|∫₀ᵗ drift ds| ≤ Md * t`. -/
private theorem drift_integral_abs_bound_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    (_hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    |∫ s in Icc 0 t, X.drift s ω ∂volume| ≤ Md * t := by
  rw [← Real.norm_eq_abs]
  have h_finite : volume (Icc (0 : ℝ) t) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have h_bound : ∀ s ∈ Icc (0 : ℝ) t, ‖X.drift s ω‖ ≤ Md :=
    fun s _ => by rw [Real.norm_eq_abs]; exact hd s ω
  calc ‖∫ s in Icc 0 t, X.drift s ω ∂volume‖
      ≤ Md * volume.real (Icc (0 : ℝ) t) := norm_setIntegral_le_of_norm_le_const h_finite h_bound
    _ = Md * t := by rw [Real.volume_real_Icc_of_le ht, sub_zero]

/-- Core-version adapter for `process_integrable`. -/
theorem process_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ) (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (hX0 : Integrable (X.process 0) μ)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md) (hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (X.process t) μ := by
  apply Integrable.mono'
    ((hX0.norm.add (integrable_const (Md * t))).add (stoch_integral_integrable_core X C FC t ht).norm)
    (process_aesm_core X t)
  filter_upwards [X.integral_form t ht] with ω hω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [hω]
  have h_drift := drift_integral_abs_bound_core X hd hMd t ht ω
  have h1 := norm_add_le (X.process 0 ω + ∫ s in Icc 0 t, X.drift s ω ∂volume)
    (X.stoch_integral t ω)
  have h2 := norm_add_le (X.process 0 ω) (∫ s in Icc 0 t, X.drift s ω ∂volume)
  simp only [Real.norm_eq_abs] at h1 h2
  linarith

/-- Core-version adapter for `process_sq_integrable`. -/
theorem process_sq_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ) (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md) (hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (X.process t ω) ^ 2) μ := by
  have hasm : AEStronglyMeasurable (fun ω => (X.process t ω) ^ 2) μ :=
    (process_aesm_core X t).pow 2
  apply Integrable.mono'
    (((hX0_sq.add (integrable_const ((Md * t) ^ 2))).add
      (stoch_integral_sq_integrable_core X C FC t ht)).const_mul 3) hasm
  filter_upwards [X.integral_form t ht] with ω hω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [hω]
  have h_drift := drift_integral_abs_bound_core X hd hMd t ht ω
  set a := X.process 0 ω
  set b := ∫ s in Icc 0 t, X.drift s ω ∂volume
  set c := X.stoch_integral t ω
  have hb : b ^ 2 ≤ (Md * t) ^ 2 :=
    sq_le_sq' (neg_le_of_abs_le h_drift) (le_of_abs_le h_drift)
  have h_sq_goal : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + (Md * t) ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  rw [abs_of_nonneg (sq_nonneg (a + b + c))]
  linarith

/-- Core-version adapter for `itoRemainder_integrable`. -/
theorem itoRemainder_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (hdrift_jm : Measurable (Function.uncurry X.drift))
    (hdiffusion_jm : Measurable (Function.uncurry X.diffusion))
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    {Mt : ℝ} (hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt)
    {Mxx : ℝ} (hMxx : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mxx)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    {Mσ : ℝ} (hσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0 : Integrable (X.process 0) μ)
    (t' : ℝ) (ht' : 0 ≤ t') :
    Integrable (itoRemainderCore X f t') μ := by
  unfold itoRemainderCore
  haveI : Nonempty Ω := by
    by_contra h; rw [not_nonempty_iff] at h
    have := @IsProbabilityMeasure.measure_univ _ _ μ _
    rw [univ_eq_empty_iff.mpr h, measure_empty] at this; exact zero_ne_one this
  have hMd : 0 ≤ Md := le_trans (abs_nonneg _) (hd 0 (Classical.arbitrary Ω))
  have hMσ : 0 ≤ Mσ := le_trans (abs_nonneg _) (hσ 0 (Classical.arbitrary Ω))
  apply Integrable.sub
  · apply Integrable.sub
    · have hXt := process_integrable_core X C FC hX0 hd hMd t' ht'
      apply Integrable.mono'
        ((integrable_const (|f 0 0| + Mt * |t'|)).add (hXt.norm.const_mul Mx))
        (((hf_x t').continuous.measurable.comp
          ((X.process_adapted t').mono (F.le_ambient t') le_rfl)).aestronglyMeasurable)
      filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply, Function.comp]
      exact le_trans (f_growth_bound hf_t hf_x hMx hMt t' (X.process t' ω))
        (by linarith [abs_nonneg (X.process t' ω)])
    · apply Integrable.mono'
        ((integrable_const (|f 0 0|)).add (hX0.norm.const_mul Mx))
        (((hf_x 0).continuous.measurable.comp
          ((X.process_adapted 0).mono (F.le_ambient 0) le_rfl)).aestronglyMeasurable)
      filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply, Function.comp]
      exact le_trans (f_spatial_bound hf_x hMx 0 (X.process 0 ω))
        (by linarith [abs_nonneg (X.process 0 ω)])
  · set Cint := Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2 with hCint_def
    apply Integrable.mono' (integrable_const (|Cint| * t'))
    · have h_null : μ {ω | ¬Continuous (fun t => X.process t ω)} = 0 :=
        ae_iff.mp C.process_continuous
      let S := toMeasurable μ {ω | ¬Continuous (fun t => X.process t ω)}
      have hS_meas : MeasurableSet S := measurableSet_toMeasurable μ _
      have hS_null : μ S = 0 := by rw [measure_toMeasurable]; exact h_null
      have hS_super : {ω | ¬Continuous (fun t => X.process t ω)} ⊆ S :=
        subset_toMeasurable μ _
      let Y : ℝ → Ω → ℝ := fun t ω => Sᶜ.indicator (X.process t) ω
      have hY_meas : ∀ t, Measurable (Y t) := fun t =>
        ((X.process_adapted t).mono (F.le_ambient t) le_rfl).indicator hS_meas.compl
      have hY_cont : ∀ ω, Continuous (fun t => Y t ω) := by
        intro ω
        by_cases h : ω ∈ S
        · have hnotSc : ω ∉ Sᶜ := fun hc => hc h
          have : ∀ t, Y t ω = 0 := fun t =>
            Set.indicator_of_notMem hnotSc _
          simp_rw [this]; exact continuous_const
        · have hcont : Continuous (fun t => X.process t ω) := by
            by_contra hc; exact h (hS_super hc)
          have hSc : ω ∈ Sᶜ := h
          have : ∀ t, Y t ω = X.process t ω := fun t =>
            Set.indicator_of_mem hSc _
          simp_rw [this]; exact hcont
      have hY_jm : Measurable (Function.uncurry Y) :=
        measurable_uncurry_of_continuous_of_measurable hY_cont hY_meas
      have h_sY : Measurable (fun p : ℝ × Ω => (p.1, Y p.1 p.2)) :=
        measurable_fst.prodMk hY_jm
      have h_jm_Y : Measurable (fun p : ℝ × Ω =>
          deriv (fun u => f u (Y p.1 p.2)) p.1 +
          deriv (fun x => f p.1 x) (Y p.1 p.2) * X.drift p.1 p.2 +
          1 / 2 * deriv (deriv (fun x => f p.1 x)) (Y p.1 p.2) *
            (X.diffusion p.1 p.2) ^ 2) := by
        apply Measurable.add
        · apply Measurable.add
          · exact hf_t_cont.measurable.comp h_sY
          · exact (hf'_cont.measurable.comp h_sY).mul hdrift_jm
        · exact (measurable_const.mul (hf''_cont.measurable.comp h_sY)).mul
            (hdiffusion_jm.pow_const 2)
      have h_int_sm := h_jm_Y.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Icc 0 t'))
      have hS_ae : Sᶜ ∈ ae μ := by rw [mem_ae_iff, compl_compl]; exact hS_null
      exact h_int_sm.aestronglyMeasurable.congr (by
        filter_upwards [hS_ae] with ω hω
        congr 1; ext s
        show deriv (fun u => f u (Y s ω)) s +
          deriv (fun x => f s x) (Y s ω) * X.drift s ω +
          1 / 2 * deriv (deriv (fun x => f s x)) (Y s ω) * (X.diffusion s ω) ^ 2 =
          deriv (fun u => f u (X.process s ω)) s +
          deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
          1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω) ^ 2
        rw [show Y s ω = X.process s ω from Set.indicator_of_mem hω _])
    · filter_upwards with ω
      simp only [Real.norm_eq_abs]
      have h_finite : volume (Icc (0 : ℝ) t') < ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      have h_integrand_bound : ∀ s ∈ Icc (0 : ℝ) t',
          |deriv (fun u => f u (X.process s ω)) s +
           deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
           1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
             (X.diffusion s ω) ^ 2| ≤ |Cint| := by
        intro s _
        calc |deriv (fun u => f u (X.process s ω)) s +
              deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
              1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                (X.diffusion s ω) ^ 2|
            ≤ |deriv (fun u => f u (X.process s ω)) s| +
              |deriv (fun x => f s x) (X.process s ω) * X.drift s ω| +
              |1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                (X.diffusion s ω) ^ 2| := by
                  linarith [abs_add_le (deriv (fun u => f u (X.process s ω)) s +
                    deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
                    (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                      (X.diffusion s ω) ^ 2),
                    abs_add_le (deriv (fun u => f u (X.process s ω)) s)
                      (deriv (fun x => f s x) (X.process s ω) * X.drift s ω)]
          _ ≤ Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2 := by
                have h1 := hMt s (X.process s ω)
                have h2 := hMx s (X.process s ω)
                have h3 := hd s ω
                have h4 := hMxx s (X.process s ω)
                have h5 := hσ s ω
                have := abs_mul (deriv (fun x => f s x) (X.process s ω)) (X.drift s ω)
                have := abs_mul (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω))
                  ((X.diffusion s ω) ^ 2)
                have := abs_mul (1 / 2 : ℝ) (deriv (deriv (fun x => f s x)) (X.process s ω))
                have h_sq : |X.diffusion s ω ^ 2| ≤ Mσ ^ 2 := by
                  rw [abs_of_nonneg (sq_nonneg _)]
                  exact sq_le_sq' (neg_le_of_abs_le h5) (le_of_abs_le h5)
                nlinarith [abs_nonneg (deriv (fun x => f s x) (X.process s ω)),
                  abs_nonneg (X.drift s ω),
                  abs_nonneg (deriv (deriv (fun x => f s x)) (X.process s ω)),
                  abs_nonneg (X.diffusion s ω ^ 2)]
          _ ≤ |Cint| := by rw [hCint_def]; exact le_abs_self _
      rw [← Real.norm_eq_abs (∫ s in Icc 0 t', _ ∂volume)]
      calc ‖∫ s in Icc 0 t', _ ∂volume‖
          ≤ |Cint| * volume.real (Icc (0 : ℝ) t') :=
            norm_setIntegral_le_of_norm_le_const h_finite
              (fun s hs => by rw [Real.norm_eq_abs]; exact h_integrand_bound s hs)
        _ = |Cint| * t' := by rw [Real.volume_real_Icc_of_le ht', sub_zero]

/-- Core-version adapter for `itoRemainder_sq_integrable`. -/
theorem itoRemainder_sq_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (FC : ItoProcessFiltrationCompatibility X)
    (hdrift_jm : Measurable (Function.uncurry X.drift))
    (hdiffusion_jm : Measurable (Function.uncurry X.diffusion))
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    {Mt : ℝ} (hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt)
    {Mxx : ℝ} (hMxx : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mxx)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    {Mσ : ℝ} (hσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ)
    (t' : ℝ) (ht' : 0 ≤ t') :
    Integrable (fun ω => (itoRemainderCore X f t' ω) ^ 2) μ := by
  haveI : Nonempty Ω := by
    by_contra h; rw [not_nonempty_iff] at h
    have := @IsProbabilityMeasure.measure_univ _ _ μ _
    rw [univ_eq_empty_iff.mpr h, measure_empty] at this; exact zero_ne_one this
  have hMd : 0 ≤ Md := le_trans (abs_nonneg _) (hd 0 (Classical.arbitrary Ω))
  have hMσ : 0 ≤ Mσ := le_trans (abs_nonneg _) (hσ 0 (Classical.arbitrary Ω))
  have hX0 : Integrable (X.process 0) μ :=
    integrable_of_sq_integrable (process_aesm_core X 0) hX0_sq
  have hrem_int := itoRemainder_integrable_core X C FC hdrift_jm hdiffusion_jm f
    hf_t hf_x hMx hMt hMxx hd hσ hf_t_cont hf'_cont hf''_cont hX0 t' ht'
  have hasm : AEStronglyMeasurable (fun ω => (itoRemainderCore X f t' ω) ^ 2) μ :=
    hrem_int.aestronglyMeasurable.pow 2
  set Cint := Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2
  set C₁ := 2 * |f 0 0| + Mt * |t'| + |Cint| * t' + Mx * Md * t'
  apply Integrable.mono'
    ((((integrable_const (C₁ ^ 2)).add
      ((process_sq_integrable_core X C FC hX0_sq hd hMd t' ht').const_mul (Mx ^ 2))).add
      (hX0_sq.const_mul (Mx ^ 2))).const_mul 3) hasm
  filter_upwards [X.integral_form t' ht'] with ω hω
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (sq_nonneg (itoRemainderCore X f t' ω))]
  unfold itoRemainderCore
  set Xt := X.process t' ω
  set X0 := X.process 0 ω
  set drift_int := ∫ s in Icc 0 t', X.drift s ω ∂volume
  set lebesgue_int := ∫ s in Icc 0 t',
    (deriv (fun u => f u (X.process s ω)) s +
     deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
     (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2) ∂volume
  have h_fXt := f_growth_bound hf_t hf_x hMx hMt t' Xt
  have h_fX0 := f_spatial_bound hf_x hMx 0 X0
  have h_lint : |lebesgue_int| ≤ |Cint| * t' := by
    rw [← Real.norm_eq_abs]
    have h_finite : volume (Icc (0 : ℝ) t') < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    calc ‖lebesgue_int‖
        ≤ |Cint| * volume.real (Icc (0 : ℝ) t') := by
          apply norm_setIntegral_le_of_norm_le_const h_finite
          intro s _
          rw [Real.norm_eq_abs]
          calc |deriv (fun u => f u (X.process s ω)) s +
                deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
                1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                  (X.diffusion s ω) ^ 2|
              ≤ |deriv (fun u => f u (X.process s ω)) s| +
                |deriv (fun x => f s x) (X.process s ω) * X.drift s ω| +
                |1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                  (X.diffusion s ω) ^ 2| := by
                    linarith [abs_add_le (deriv (fun u => f u (X.process s ω)) s +
                      deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
                      (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
                        (X.diffusion s ω) ^ 2),
                      abs_add_le (deriv (fun u => f u (X.process s ω)) s)
                        (deriv (fun x => f s x) (X.process s ω) * X.drift s ω)]
            _ ≤ Mt + Mx * Md + 1/2 * Mxx * Mσ ^ 2 := by
                have h1 := hMt s (X.process s ω)
                have h2 := hMx s (X.process s ω)
                have h3 := hd s ω
                have h4 := hMxx s (X.process s ω)
                have h5 := hσ s ω
                have := abs_mul (deriv (fun x => f s x) (X.process s ω)) (X.drift s ω)
                have := abs_mul (1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω))
                  ((X.diffusion s ω) ^ 2)
                have := abs_mul (1 / 2 : ℝ) (deriv (deriv (fun x => f s x)) (X.process s ω))
                have h_sq : |X.diffusion s ω ^ 2| ≤ Mσ ^ 2 := by
                  rw [abs_of_nonneg (sq_nonneg _)]
                  exact sq_le_sq' (neg_le_of_abs_le h5) (le_of_abs_le h5)
                nlinarith [abs_nonneg (deriv (fun x => f s x) (X.process s ω)),
                  abs_nonneg (X.drift s ω),
                  abs_nonneg (deriv (deriv (fun x => f s x)) (X.process s ω)),
                  abs_nonneg (X.diffusion s ω ^ 2)]
            _ ≤ |Cint| := le_abs_self _
      _ = |Cint| * t' := by rw [Real.volume_real_Icc_of_le ht', sub_zero]
  have h_rem_bound : |f t' Xt - f 0 X0 - lebesgue_int| ≤ C₁ + Mx * |Xt| + Mx * |X0| := by
    calc |f t' Xt - f 0 X0 - lebesgue_int|
        ≤ |f t' Xt| + |f 0 X0| + |lebesgue_int| := by
          linarith [abs_sub (f t' Xt) (f 0 X0),
            abs_sub (f t' Xt - f 0 X0) lebesgue_int]
      _ ≤ (|f 0 0| + Mt * |t'| + Mx * |Xt|) + (|f 0 0| + Mx * |X0|) +
            |Cint| * t' := by linarith
      _ = C₁ - Mx * Md * t' + Mx * |Xt| + Mx * |X0| := by ring
      _ ≤ C₁ + Mx * |Xt| + Mx * |X0| := by
          linarith [mul_nonneg (mul_nonneg (le_trans (abs_nonneg _) (hMx 0 0)) hMd) ht']
  have h_sq : (f t' Xt - f 0 X0 - lebesgue_int) ^ 2 ≤
      3 * (C₁ ^ 2 + Mx ^ 2 * Xt ^ 2 + Mx ^ 2 * X0 ^ 2) := by
    have h := h_rem_bound
    set a := C₁; set b := Mx * |Xt|; set c := Mx * |X0|
    have hab : |f t' Xt - f 0 X0 - lebesgue_int| ^ 2 ≤ (a + b + c) ^ 2 :=
      sq_le_sq' (by linarith [abs_nonneg (f t' Xt - f 0 X0 - lebesgue_int)]) h
    have h_3sq : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    calc (f t' Xt - f 0 X0 - lebesgue_int) ^ 2
        ≤ |f t' Xt - f 0 X0 - lebesgue_int| ^ 2 := by
          rw [sq_abs]
      _ ≤ (a + b + c) ^ 2 := hab
      _ ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := h_3sq
      _ = 3 * (C₁ ^ 2 + Mx ^ 2 * |Xt| ^ 2 + Mx ^ 2 * |X0| ^ 2) := by ring
      _ = 3 * (C₁ ^ 2 + Mx ^ 2 * Xt ^ 2 + Mx ^ 2 * X0 ^ 2) := by
          rw [sq_abs, sq_abs]
  linarith

/-- Regularity-first adapter for `stoch_integral_integrable_core`. -/
theorem stoch_integral_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (X.stoch_integral t) μ := by
  simpa using
    (stoch_integral_integrable_core
      (X := X)
      (C := R.toConstruction) (FC := R.toFiltrationCompatibility)
      t ht)

/-- Regularity-first adapter for `process_integrable_core`. -/
theorem process_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (hX0 : Integrable (X.process 0) μ)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md) (hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (X.process t) μ := by
  simpa using
    (process_integrable_core
      (X := X)
      (C := R.toConstruction) (FC := R.toFiltrationCompatibility)
      hX0 hd hMd t ht)

/-- Regularity-first adapter for `process_sq_integrable_core`. -/
theorem process_sq_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md) (hMd : 0 ≤ Md)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (X.process t ω) ^ 2) μ := by
  simpa using
    (process_sq_integrable_core
      (X := X)
      (C := R.toConstruction) (FC := R.toFiltrationCompatibility)
      hX0_sq hd hMd t ht)

/-- Regularity-first adapter for `itoRemainder_integrable_core`. -/
theorem itoRemainder_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    {Mt : ℝ} (hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt)
    {Mxx : ℝ} (hMxx : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mxx)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    {Mσ : ℝ} (hσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0 : Integrable (X.process 0) μ)
    (t' : ℝ) (ht' : 0 ≤ t') :
    Integrable (itoRemainderCore X f t') μ := by
  simpa using
    (itoRemainder_integrable_core
      (X := X)
      (C := R.toConstruction) (FC := R.toFiltrationCompatibility)
      R.drift_jointly_measurable R.diffusion_jointly_measurable
      f hf_t hf_x hMx hMt hMxx hd hσ
      hf_t_cont hf'_cont hf''_cont hX0 t' ht')

/-- Regularity-first adapter for `itoRemainder_sq_integrable_core`. -/
theorem itoRemainder_sq_integrable_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mx : ℝ} (hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx)
    {Mt : ℝ} (hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt)
    {Mxx : ℝ} (hMxx : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mxx)
    {Md : ℝ} (hd : ∀ t ω, |X.drift t ω| ≤ Md)
    {Mσ : ℝ} (hσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ)
    (t' : ℝ) (ht' : 0 ≤ t') :
    Integrable (fun ω => (itoRemainderCore X f t' ω) ^ 2) μ := by
  simpa using
    (itoRemainder_sq_integrable_core
      (X := X)
      (C := R.toConstruction) (FC := R.toFiltrationCompatibility)
      R.drift_jointly_measurable R.diffusion_jointly_measurable
      f hf_t hf_x hMx hMt hMxx hd hσ
      hf_t_cont hf'_cont hf''_cont hX0_sq t' ht')

end SPDE
