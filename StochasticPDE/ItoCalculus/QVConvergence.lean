/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.QuadraticVariation
import StochasticPDE.ItoCalculus.QuarticBound
import StochasticPDE.ItoCalculus.ConditionalIsometry

/-!
# Quadratic Variation Convergence Helpers

Helper lemmas for proving ∑(ΔXᵢ)² → [X]_t in L².

## Main results

* `ito_process_increment_decomp_ae` - a.e. decomposition of process increments
* `si_compensated_sq_variance_bound` - variance bound for compensated SI² increments
* `ito_qv_L2_bound` - the main L² bound: E[(∑(ΔXᵢ)² - [X]_t)²] ≤ C/(n+1)

## Strategy

Decompose ΔXᵢ = ΔDᵢ + ΔSIᵢ (drift + stochastic integral) via `integral_form`.
Then ∑(ΔXᵢ)² - [X]_t = A + B + C where:
- A = ∑(ΔDᵢ)² = O(Mμ²t/n) → 0 deterministically
- B = 2∑ΔDᵢΔSIᵢ: cross terms bounded by CS + Itô isometry
- C = ∑((ΔSIᵢ)² - ∫σ²): uses orthogonality + L⁴ bound

The orthogonality `stoch_integral_squared_orthogonal` eliminates cross terms
in E[C²], giving E[C²] = ∑E[Zᵢ²] ≤ O(1/n).
-/

open MeasureTheory Filter Finset Set

namespace SPDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Partition time helpers -/

/-- Partition time i * t / (n+1) is nonneg for 0 ≤ t. -/
lemma partition_time_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (i : ℕ) :
    0 ≤ (↑i : ℝ) * t / ↑(n + 1) := by
  positivity

/-- Partition time (i+1) * t / (n+1) ≤ t for i < n+1. -/
lemma partition_time_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (i : Fin (n + 1)) :
    (↑(i : ℕ) + 1) * t / ↑(n + 1) ≤ t := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))]
  have : (↑(i : ℕ) : ℝ) + 1 ≤ ↑(n + 1) := by exact_mod_cast i.isLt
  nlinarith

/-- Partition times are ordered: i * t / (n+1) ≤ (i+1) * t / (n+1). -/
lemma partition_time_mono (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (i : ℕ) :
    (↑i : ℝ) * t / ↑(n + 1) ≤ (↑i + 1) * t / ↑(n + 1) := by
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < ↑(n + 1)).le
  nlinarith

/-- For i < j (both < n+1), t_{i+1} ≤ t_j. -/
lemma partition_time_disjoint (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (i j : Fin (n + 1)) (hij : (i : ℕ) < (j : ℕ)) :
    (↑(i : ℕ) + 1) * t / ↑(n + 1) ≤ (↑(j : ℕ)) * t / ↑(n + 1) := by
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < ↑(n + 1)).le
  have : (↑(i : ℕ) : ℝ) + 1 ≤ ↑(j : ℕ) := by exact_mod_cast hij
  nlinarith

/-! ## Integral splitting -/

/-- For Lebesgue measure, ∫_{Icc 0 b} f = ∫_{Icc 0 a} f + ∫_{Icc a b} f when 0 ≤ a ≤ b. -/
lemma setIntegral_Icc_split {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
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
        ≤ volume {a} := by
          apply measure_mono
          intro x hx
          rw [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Icc] at hx
          rw [Set.mem_singleton_iff]
          linarith
      _ = 0 := Real.volume_singleton
  rw [hunion]
  exact integral_union_ae hae measurableSet_Icc.nullMeasurableSet
    (hf.mono_set (Icc_subset_Icc_right (le_trans hab le_rfl)))
    (hf.mono_set (Icc_subset_Icc_left ha))

/-! ## Process increment decomposition -/

/-- For a.e. ω, the Itô process increment decomposes into drift + SI.
    This is a finite intersection of the a.e. sets from `integral_form`. -/
theorem ito_process_increment_decomp_ae {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
      X.process (↑(i : ℕ) * t / ↑(n + 1)) ω =
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) +
      (X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω) := by
  -- integral_form gives: X(s) = X(0) + ∫₀ˢ μ + SI(s) a.e. for each s ≥ 0
  have h_all_times : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 2),
      X.process (↑(i : ℕ) * t / ↑(n + 1)) ω =
        X.process 0 ω +
        (∫ s in Icc 0 (↑(i : ℕ) * t / ↑(n + 1)), X.drift s ω ∂volume) +
        X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω := by
    rw [ae_all_iff]
    intro i
    apply X.integral_form
    exact partition_time_nonneg t ht.le (n) (i : ℕ)
  filter_upwards [h_all_times] with ω hω
  intro i
  have hi := hω ⟨(i : ℕ), by omega⟩
  have hi1 := hω ⟨(i : ℕ) + 1, by exact Nat.succ_lt_succ i.isLt⟩
  -- Use integral splitting to decompose cumulative integrals
  set ti := (↑(i : ℕ) : ℝ) * t / ↑(n + 1) with hti_def
  set ti1 := ((↑(i : ℕ) : ℝ) + 1) * t / ↑(n + 1) with hti1_def
  have h_ti_nonneg : 0 ≤ ti := partition_time_nonneg t ht.le n (i : ℕ)
  have h_ti_le_ti1 : ti ≤ ti1 := partition_time_mono t ht.le n (i : ℕ)
  -- The drift is time-integrable
  have h_int : IntegrableOn (fun s => X.drift s ω) (Icc 0 ti1) volume :=
    X.drift_time_integrable ω ti1 (le_trans h_ti_nonneg h_ti_le_ti1)
  -- Split: ∫₀^{ti1} = ∫₀^{ti} + ∫_{ti}^{ti1}
  have hsplit := setIntegral_Icc_split h_ti_nonneg h_ti_le_ti1 h_int
  -- X(ti) = X(0) + ∫₀^{ti} μ + SI(ti)  and similarly for ti1
  -- After subtraction: X(ti1) - X(ti) = (∫₀^{ti1} - ∫₀^{ti}) μ + (SI(ti1) - SI(ti))
  --                                    = ∫_{ti}^{ti1} μ + (SI(ti1) - SI(ti))
  -- hi already uses ti from `set`. Normalize hi1: ↑↑⟨↑i+1, _⟩ → ↑↑i + 1
  have hcast : (↑((⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n+2)) : ℕ) : ℝ) =
      (↑(i : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hi1
  -- Now hi1 uses ti1 from `set`
  linarith

/-! ## Drift bound -/

/-- The drift increment is bounded: |∫_{tᵢ}^{t_{i+1}} μ ds| ≤ Mμ · Δt. -/
lemma drift_increment_bound {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    (s u : ℝ) (hsu : s ≤ u) (ω : Ω) :
    |∫ r in Icc s u, X.drift r ω ∂volume| ≤ Mμ * (u - s) := by
  by_cases hint : IntegrableOn (fun r => X.drift r ω) (Icc s u) volume
  · calc |∫ r in Icc s u, X.drift r ω ∂volume|
        ≤ ∫ r in Icc s u, |X.drift r ω| ∂volume := by
          rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
      _ ≤ ∫ r in Icc s u, Mμ ∂volume := by
          apply setIntegral_mono_on hint.norm
          · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          · exact measurableSet_Icc
          · intro r _; exact hMμ r ω
      _ = Mμ * (u - s) := by
          rw [setIntegral_const]; simp [Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hsu), smul_eq_mul, mul_comm]
  · rw [integral_undef hint, abs_zero]
    exact mul_nonneg (le_trans (abs_nonneg _) (hMμ 0 ω)) (sub_nonneg.mpr hsu)

/-- Sum of squared drift increments is bounded deterministically:
    ∑(ΔDᵢ)² ≤ Mμ² · t · Δt = Mμ² · t² / (n+1). -/
lemma drift_sq_sum_bound {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (ω : Ω) :
    ∑ i : Fin (n + 1),
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) ^ 2 ≤
    Mμ ^ 2 * t ^ 2 / ↑(n + 1) := by
  -- Each (ΔDᵢ)² ≤ (Mμ · Δt)² = Mμ² · (t/(n+1))²
  have h_bound : ∀ i : Fin (n + 1),
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) ^ 2 ≤ Mμ ^ 2 * (t / ↑(n + 1)) ^ 2 := by
    intro i
    have hle := drift_increment_bound X hMμ
      (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1))
      (partition_time_mono t ht n (i : ℕ)) ω
    calc (∫ s in Icc _ _, X.drift s ω ∂volume) ^ 2
        ≤ |∫ s in Icc _ _, X.drift s ω ∂volume| ^ 2 := by
          rw [sq_abs]
      _ ≤ (Mμ * ((↑(i : ℕ) + 1) * t / ↑(n + 1) - ↑(i : ℕ) * t / ↑(n + 1))) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) hle 2
      _ = Mμ ^ 2 * (t / ↑(n + 1)) ^ 2 := by ring_nf
  calc ∑ i : Fin (n + 1), _ ≤ ∑ i : Fin (n + 1), Mμ ^ 2 * (t / ↑(n + 1)) ^ 2 :=
      Finset.sum_le_sum (fun i _ => h_bound i)
    _ = ↑(n + 1) * (Mμ ^ 2 * (t / ↑(n + 1)) ^ 2) := by
        rw [Finset.sum_const, Finset.card_fin]; simp [nsmul_eq_mul]
    _ = Mμ ^ 2 * t ^ 2 / ↑(n + 1) := by
        have hn : (0 : ℝ) < ↑(n + 1) := by positivity
        field_simp

/-! ## SI compensated increment orthogonality -/

/-- The compensated squared SI increments on the partition are pairwise orthogonal in L².
    E[Zᵢ · Zⱼ] = 0 for i < j, where Zₖ = (ΔSIₖ)² - ∫σ²ₖ. -/
lemma si_compensated_orthogonal_partition {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (i j : Fin (n + 1)) (hij : (i : ℕ) < (j : ℕ)) :
    ∫ ω,
      ((X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
        X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       ∫ u in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
         (X.diffusion u ω) ^ 2 ∂volume) *
      ((X.stoch_integral ((↑(j : ℕ) + 1) * t / ↑(n + 1)) ω -
        X.stoch_integral (↑(j : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       ∫ u in Icc (↑(j : ℕ) * t / ↑(n + 1)) ((↑(j : ℕ) + 1) * t / ↑(n + 1)),
         (X.diffusion u ω) ^ 2 ∂volume) ∂μ = 0 :=
  ItoProcess.stoch_integral_squared_orthogonal X hMσ _ _ _ _
    (partition_time_nonneg t ht n (i : ℕ))
    (partition_time_mono t ht n (i : ℕ))
    (partition_time_disjoint t ht n i j hij)
    (partition_time_mono t ht n (j : ℕ))

/-! ## SI compensated increment L² bound -/

/-- Single compensated SI² increment variance bound:
    E[((ΔSIᵢ)² - ∫σ²ᵢ)²] ≤ 8Mσ⁴ · (Δt)². -/
lemma si_compensated_sq_L2_single {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    ∫ ω,
      ((X.stoch_integral u ω - X.stoch_integral s ω) ^ 2 -
       ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume) ^ 2 ∂μ ≤
    8 * Mσ ^ 4 * (u - s) ^ 2 := by
  -- Pointwise: Z(ω)² ≤ 2(ΔSI)⁴ + 2(Mσ²Δt)²
  -- Since ∫σ²(ω) ≤ Mσ²Δt, (a-b)² ≤ 2a² + 2b² gives the bound
  set ΔSI := fun ω => X.stoch_integral u ω - X.stoch_integral s ω with hΔSI_def
  set σ_int := fun ω => ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume with hσ_int_def
  -- σ_int(ω) ≤ Mσ²(u-s) for all ω
  have hσ_bound : ∀ ω, σ_int ω ≤ Mσ ^ 2 * (u - s) := by
    intro ω
    have h_each : ∀ r, (X.diffusion r ω) ^ 2 ≤ Mσ ^ 2 := by
      intro r
      calc (X.diffusion r ω) ^ 2 = |X.diffusion r ω| ^ 2 := by rw [sq_abs]
        _ ≤ Mσ ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω)
    calc σ_int ω = ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume := rfl
      _ ≤ ∫ r in Icc s u, Mσ ^ 2 ∂volume := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun r => sq_nonneg (X.diffusion r ω)
          · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          · exact ae_of_all _ fun r => h_each r
      _ = Mσ ^ 2 * (u - s) := by
          rw [setIntegral_const]; simp [Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hsu), smul_eq_mul, mul_comm]
  -- Pointwise: (a - b)² ≤ 2a² + 2b² where a = (ΔSI)², b = σ_int
  have h_pw : ∀ ω, (ΔSI ω ^ 2 - σ_int ω) ^ 2 ≤
      2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
    intro ω
    have h1 : (ΔSI ω ^ 2 - σ_int ω) ^ 2 ≤
        2 * (ΔSI ω ^ 2) ^ 2 + 2 * (σ_int ω) ^ 2 := by
      nlinarith [sq_nonneg (ΔSI ω ^ 2 + σ_int ω)]
    have h2 : (σ_int ω) ^ 2 ≤ (Mσ ^ 2 * (u - s)) ^ 2 := by
      apply sq_le_sq'
      · have hσ_nonneg : 0 ≤ σ_int ω :=
          setIntegral_nonneg measurableSet_Icc (fun r _ => sq_nonneg (X.diffusion r ω))
        have : 0 ≤ Mσ ^ 2 * (u - s) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsu)
        linarith
      · exact hσ_bound ω
    calc (ΔSI ω ^ 2 - σ_int ω) ^ 2
        ≤ 2 * (ΔSI ω ^ 2) ^ 2 + 2 * (σ_int ω) ^ 2 := h1
      _ ≤ 2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
          have : (ΔSI ω ^ 2) ^ 2 = ΔSI ω ^ 4 := by ring
          linarith
  -- L4 integrability
  have hL4 : Integrable (fun ω => ΔSI ω ^ 4) μ :=
    stoch_integral_increment_L4_integrable_proof X hMσ s u hs hsu
  -- Integrability of the upper bound
  have h_ub_int : Integrable (fun ω => 2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2) μ :=
    (hL4.const_mul 2).add (integrable_const _)
  -- E[Z²] ≤ E[2(ΔSI)⁴ + 2(Mσ²Δt)²]
  calc ∫ ω, (ΔSI ω ^ 2 - σ_int ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun ω => sq_nonneg _
        · exact h_ub_int
        · exact ae_of_all _ h_pw
    _ = 2 * ∫ ω, ΔSI ω ^ 4 ∂μ + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
        rw [integral_add (hL4.const_mul 2) (integrable_const _),
            integral_const_mul, integral_const, smul_eq_mul]
        congr 1
        rw [show μ.real Set.univ = 1 from by
          simp [Measure.real, measure_univ]]
        ring
    _ ≤ 2 * (3 * Mσ ^ 4 * (u - s) ^ 2) + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
        gcongr
        exact stoch_integral_increment_L4_bound_proof X hMσ s u hs hsu
    _ = 8 * Mσ ^ 4 * (u - s) ^ 2 := by ring

/-! ## Compensated SI increment integrability -/

/-- The compensated squared SI increment Z(ω) = (SI(u)-SI(s))² - ∫_{[s,u]} σ² is integrable. -/
private lemma compensated_si_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    Integrable (fun ω =>
      (X.stoch_integral u ω - X.stoch_integral s ω) ^ 2 -
      ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume) μ := by
  have hu := le_trans hs hsu
  have hΔSI_sq : Integrable (fun ω =>
      (X.stoch_integral u ω - X.stoch_integral s ω) ^ 2) μ := by
    apply ((X.stoch_integral_sq_integrable u hu).const_mul 2 |>.add
      ((X.stoch_integral_sq_integrable s hs).const_mul 2)).mono
    · exact ((X.stoch_integral_integrable u hu).aestronglyMeasurable.sub
        (X.stoch_integral_integrable s hs).aestronglyMeasurable).pow 2
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg (X.stoch_integral u ω + X.stoch_integral s ω)]
  exact hΔSI_sq.sub (diffusion_sq_interval_integrable X s u hs hsu)

/-- The square of the compensated increment is integrable.
    Dominated by 2(ΔSI)⁴ + 2(Mσ²Δt)² from L⁴ bound. -/
private lemma compensated_si_sq_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    Integrable (fun ω =>
      ((X.stoch_integral u ω - X.stoch_integral s ω) ^ 2 -
       ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume) ^ 2) μ := by
  have hZ_meas := (compensated_si_sq_integrable X s u hs hsu).aestronglyMeasurable
  have hL4 := stoch_integral_increment_L4_integrable_proof X hMσ s u hs hsu
  apply ((hL4.const_mul 2).add (integrable_const (2 * (Mσ ^ 2 * (u - s)) ^ 2))).mono
    (hZ_meas.pow 2)
  filter_upwards with ω
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.pow_apply]
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
  set a := (X.stoch_integral u ω - X.stoch_integral s ω) ^ 2
  set b := ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume
  have h1 : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
  have ha_eq : a ^ 2 = (X.stoch_integral u ω - X.stoch_integral s ω) ^ 4 := by
    simp only [a]; ring
  have hb_nn : 0 ≤ b := setIntegral_nonneg measurableSet_Icc (fun r _ => sq_nonneg _)
  have hb_bound : b ≤ Mσ ^ 2 * (u - s) := by
    calc b ≤ ∫ r in Icc s u, Mσ ^ 2 ∂volume := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun r => sq_nonneg _
          · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          · exact ae_of_all _ fun r => by
              show X.diffusion r ω ^ 2 ≤ Mσ ^ 2
              calc X.diffusion r ω ^ 2 = |X.diffusion r ω| ^ 2 := (sq_abs _).symm
                _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω) 2
      _ = Mσ ^ 2 * (u - s) := by
          rw [setIntegral_const]; simp [Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hsu), smul_eq_mul, mul_comm]
  have h2 : b ^ 2 ≤ (Mσ ^ 2 * (u - s)) ^ 2 :=
    sq_le_sq' (by linarith [mul_nonneg (sq_nonneg Mσ) (sub_nonneg.mpr hsu)]) hb_bound
  linarith

/-! ## QV partition splitting -/

/-- Helper: ∫_{Icc 0 (k*t/(n+1))} f = ∑_{i∈range k} ∫_{Icc tᵢ t_{i+1}} f. -/
private lemma integral_partition_sum_aux (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (n : ℕ)
    (hf : IntegrableOn f (Icc 0 t) volume) :
    ∀ k : ℕ, k ≤ n + 1 →
      ∫ x in Icc 0 (↑k * t / ↑(n + 1)), f x ∂volume =
      ∑ i ∈ Finset.range k,
        ∫ x in Icc (↑i * t / ↑(n + 1)) ((↑i + 1) * t / ↑(n + 1)), f x ∂volume := by
  intro k hk
  induction k with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, zero_div, Finset.range_zero,
      Finset.sum_empty]
    rw [show Icc (0 : ℝ) 0 = {0} from Icc_self 0]
    rw [show (volume.restrict {(0 : ℝ)}) = 0 from by
      rw [Measure.restrict_eq_zero]; exact Real.volume_singleton]
    simp
  | succ k ih =>
    have hk' : k ≤ n + 1 := Nat.le_of_succ_le hk
    rw [Finset.sum_range_succ]
    have h_sub : Icc 0 ((↑k + 1) * t / ↑(n + 1)) ⊆ Icc 0 t := by
      apply Set.Icc_subset_Icc le_rfl
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))]
      have : (↑k : ℝ) + 1 ≤ ↑(n + 1) := by exact_mod_cast hk
      nlinarith
    have h_split := setIntegral_Icc_split
      (partition_time_nonneg t ht n k)
      (partition_time_mono t ht n k)
      (hf.mono_set h_sub)
    rw [show (↑(k + 1) : ℝ) * t / ↑(n + 1) = (↑k + 1) * t / ↑(n + 1) from by push_cast; ring]
    rw [h_split, ih hk']

/-- The quadratic variation splits along the partition:
    [X]_t = ∑ ∫_{tᵢ}^{tᵢ₊₁} σ² ds.
    Requires IntegrableOn for σ² to ensure integral splitting is valid. -/
lemma qv_partition_sum {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (ω : Ω)
    (hf_int : IntegrableOn (fun s => (X.diffusion s ω) ^ 2) (Icc 0 t) volume) :
    X.quadraticVariation t ω =
    ∑ i : Fin (n + 1),
      ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        (X.diffusion s ω) ^ 2 ∂volume := by
  unfold ItoProcess.quadraticVariation
  -- Apply the partition sum auxiliary lemma at k = n+1
  have h := integral_partition_sum_aux (fun s => (X.diffusion s ω) ^ 2) t ht n hf_int (n + 1) le_rfl
  rw [show (↑(n + 1) : ℝ) * t / ↑(n + 1) = t from by field_simp] at h
  rw [h]
  -- Convert sum over range to sum over Fin
  rw [Finset.sum_range]

/-! ## Orthogonal sum L² bound -/

/-- For pairwise L²-orthogonal functions, E[(∑Zᵢ)²] = ∑E[Zᵢ²].
    This is the Pythagorean identity for L² random variables. -/
lemma integral_sq_sum_orthogonal {m : ℕ}
    (Z : Fin m → Ω → ℝ)
    (hZZ_int : ∀ i j : Fin m, Integrable (fun ω => Z i ω * Z j ω) μ)
    (horth : ∀ i j : Fin m, i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = 0) :
    ∫ ω, (∑ i, Z i ω) ^ 2 ∂μ = ∑ i, ∫ ω, (Z i ω) ^ 2 ∂μ := by
  -- (∑Z)² = ∑_i ∑_j Z_i Z_j pointwise
  have h_expand : (fun ω => (∑ i, Z i ω) ^ 2) =
      (fun ω => ∑ i, ∑ j, Z i ω * Z j ω) := by
    ext ω; rw [sq, Finset.sum_mul]; congr 1; ext i; rw [Finset.mul_sum]
  rw [h_expand]
  -- Exchange integral and sums
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hZZ_int i j))]
  congr 1; ext i
  rw [integral_finset_sum _ (fun j _ => hZZ_int i j)]
  -- Inner sum: ∑_j E[Z_i Z_j] = E[Z_i²]
  have h_sq : (fun ω => (Z i ω) ^ 2) = (fun ω => Z i ω * Z i ω) := by ext ω; ring
  rw [h_sq, Finset.sum_eq_single i
    (fun j _ hij => horth i j hij.symm)
    (fun h => absurd (Finset.mem_univ i) h)]

/-! ## SI sum variance via orthogonality -/

/-- Sum of compensated squared SI increments has variance ≤ 8Mσ⁴t²/(n+1).
    Uses orthogonality: E[(∑Zᵢ)²] = ∑E[Zᵢ²] ≤ ∑8Mσ⁴(Δt)² = 8Mσ⁴t²/(n+1). -/
lemma si_compensated_sum_variance {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        ((X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
          X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
           (X.diffusion s ω) ^ 2 ∂volume)) ^ 2 ∂μ ≤
    8 * Mσ ^ 4 * t ^ 2 / ↑(n + 1) := by
  -- Define Z abstractly for the helper
  set Z : Fin (n + 1) → Ω → ℝ := fun i ω =>
    (X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
     X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
    ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
      (X.diffusion s ω) ^ 2 ∂volume with hZ_def
  -- Integrability of products (sorry for now - needs L4 + measurability infrastructure)
  have hZZ_int : ∀ i j : Fin (n + 1), Integrable (fun ω => Z i ω * Z j ω) μ := by
    intro i j
    -- Each Z_k is integrable (hence AEStronglyMeasurable)
    have hZk_int : ∀ k : Fin (n + 1), Integrable (Z k) μ := by
      intro k; simp only [hZ_def]
      exact compensated_si_sq_integrable X _ _
        (partition_time_nonneg t ht n _) (partition_time_mono t ht n _)
    -- Each Z_k² is integrable (from L⁴ domination)
    have hZk_sq : ∀ k : Fin (n + 1), Integrable (fun ω => Z k ω ^ 2) μ := by
      intro k; simp only [hZ_def]
      exact compensated_si_sq_sq_integrable X hMσ _ _
        (partition_time_nonneg t ht n _) (partition_time_mono t ht n _)
    -- AM-GM: |Z_i · Z_j| ≤ (Z_i² + Z_j²)/2, dominated by integrable
    apply ((hZk_sq i).add (hZk_sq j)).div_const 2 |>.mono
      ((hZk_int i).aestronglyMeasurable.mul (hZk_int j).aestronglyMeasurable)
    filter_upwards with ω
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (by norm_num : (0:ℝ) ≤ 2))]
    calc |Z i ω * Z j ω| = |Z i ω| * |Z j ω| := abs_mul _ _
      _ ≤ (Z i ω ^ 2 + Z j ω ^ 2) / 2 := by
          nlinarith [sq_nonneg (|Z i ω| - |Z j ω|), sq_abs (Z i ω), sq_abs (Z j ω)]
  -- Orthogonality
  have horth : ∀ i j : Fin (n + 1), i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = 0 := by
    intro i j hij
    simp only [Z]
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact si_compensated_orthogonal_partition X hMσ t ht n i j h
    · rw [show (fun ω => _ * _) = (fun ω =>
        ((X.stoch_integral ((↑(j : ℕ) + 1) * t / ↑(n + 1)) ω -
          X.stoch_integral (↑(j : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         ∫ s in Icc (↑(j : ℕ) * t / ↑(n + 1)) ((↑(j : ℕ) + 1) * t / ↑(n + 1)),
           (X.diffusion s ω) ^ 2 ∂volume) *
        ((X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
          X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
           (X.diffusion s ω) ^ 2 ∂volume)) from by ext ω; ring]
      exact si_compensated_orthogonal_partition X hMσ t ht n j i h
  -- Apply Pythagorean identity
  rw [integral_sq_sum_orthogonal Z hZZ_int horth]
  -- Bound each diagonal term
  -- t_{i+1} - t_i = t/(n+1)
  have hΔt : ∀ i : Fin (n + 1),
      (↑(i : ℕ) + 1) * t / ↑(n + 1) - ↑(i : ℕ) * t / ↑(n + 1) = t / ↑(n + 1) := by
    intro i; ring
  calc ∑ i : Fin (n + 1), ∫ ω, (Z i ω) ^ 2 ∂μ
      ≤ ∑ i : Fin (n + 1), 8 * Mσ ^ 4 * (t / ↑(n + 1)) ^ 2 := by
        apply Finset.sum_le_sum; intro i _; simp only [Z]
        rw [← hΔt i]
        exact si_compensated_sq_L2_single X hMσ _ _
          (partition_time_nonneg t ht n (i : ℕ))
          (partition_time_mono t ht n (i : ℕ))
    _ = 8 * Mσ ^ 4 * t ^ 2 / ↑(n + 1) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        have hn : (0 : ℝ) < ↑(n + 1) := by positivity
        field_simp

/-! ## SI increment squared integrability -/

/-- (SI(u) - SI(s))² is integrable. -/
private lemma si_increment_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    Integrable (fun ω => (X.stoch_integral u ω - X.stoch_integral s ω) ^ 2) μ := by
  have hu := le_trans hs hsu
  apply ((X.stoch_integral_sq_integrable u hu).const_mul 2 |>.add
    ((X.stoch_integral_sq_integrable s hs).const_mul 2)).mono
  · exact ((X.stoch_integral_integrable u hu).aestronglyMeasurable.sub
      (X.stoch_integral_integrable s hs).aestronglyMeasurable).pow 2
  · filter_upwards with ω
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (X.stoch_integral u ω + X.stoch_integral s ω)]

/-! ## Cross term L² bound -/

/-- Cross terms between drift and SI increments: E[(∑ΔDᵢΔSIᵢ)²] ≤ Mμ²Mσ²t³/(n+1).
    Strategy: |ΔDᵢ| ≤ Mμ·Δt pointwise, then Cauchy-Schwarz + isometry. -/
lemma cross_term_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
          X.drift s ω ∂volume) *
        (X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω)) ^ 2 ∂μ ≤
    Mμ ^ 2 * Mσ ^ 2 * t ^ 3 / ↑(n + 1) := by
  have hn_pos : (0 : ℝ) < ↑(n + 1) := by positivity
  -- Abbreviate increments
  set ΔSI : Fin (n+1) → Ω → ℝ := fun i ω =>
    X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
    X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω
  set ΔD : Fin (n+1) → Ω → ℝ := fun i ω =>
    ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
      X.drift s ω ∂volume
  -- Partition time step
  have hΔt : ∀ i : Fin (n+1),
      (↑(i : ℕ) + 1) * t / ↑(n + 1) - ↑(i : ℕ) * t / ↑(n + 1) = t / ↑(n + 1) := by
    intro i; ring
  -- Step 1: Pointwise |ΔDᵢ| ≤ Mμ·Δt
  have hΔD_bound : ∀ ω, ∀ i : Fin (n+1), |ΔD i ω| ≤ Mμ * (t / ↑(n+1)) := by
    intro ω i; simp only [ΔD]
    have := drift_increment_bound X hMμ _ _ (partition_time_mono t ht.le n (i : ℕ)) ω
    rwa [hΔt i] at this
  -- Step 2: Pointwise bound (∑ ΔDᵢΔSIᵢ)² ≤ Mμ²Δt²·(n+1)·∑(ΔSIᵢ)²
  have h_pw : ∀ ω, (∑ i, ΔD i ω * ΔSI i ω) ^ 2 ≤
      Mμ ^ 2 * (t / ↑(n+1)) ^ 2 * ↑(n+1) * ∑ i, (ΔSI i ω) ^ 2 := by
    intro ω
    -- Triangle + drift bound: |∑ ΔDᵢΔSIᵢ| ≤ Mμ·Δt·∑|ΔSIᵢ|
    have h_tri : |∑ i, ΔD i ω * ΔSI i ω| ≤
        Mμ * (t / ↑(n+1)) * ∑ i, |ΔSI i ω| := by
      calc |∑ i, ΔD i ω * ΔSI i ω|
          ≤ ∑ i, ‖ΔD i ω * ΔSI i ω‖ := by
            rw [← Real.norm_eq_abs]; exact norm_sum_le Finset.univ _
        _ = ∑ i, |ΔD i ω| * |ΔSI i ω| := by
            congr 1; ext i; rw [Real.norm_eq_abs, abs_mul]
        _ ≤ ∑ i, (Mμ * (t / ↑(n+1))) * |ΔSI i ω| :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (hΔD_bound ω i) (abs_nonneg _)
        _ = Mμ * (t / ↑(n+1)) * ∑ i, |ΔSI i ω| := by rw [← Finset.mul_sum]
    -- Square + CS: (∑|ΔSIᵢ|)² ≤ (n+1)·∑(ΔSIᵢ)²
    have h_cs : (∑ i : Fin (n+1), |ΔSI i ω|) ^ 2 ≤
        ↑(n+1) * ∑ i : Fin (n+1), (ΔSI i ω) ^ 2 := by
      have := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ (fun i : Fin (n+1) => |ΔSI i ω|)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      calc (∑ i, |ΔSI i ω|) ^ 2 ≤ ↑(n+1) * ∑ i, |ΔSI i ω| ^ 2 := this
        _ = ↑(n+1) * ∑ i, (ΔSI i ω) ^ 2 := by
            congr 1; exact Finset.sum_congr rfl fun i _ => sq_abs _
    -- Combine
    calc (∑ i, ΔD i ω * ΔSI i ω) ^ 2
        = |∑ i, ΔD i ω * ΔSI i ω| ^ 2 := (sq_abs _).symm
      _ ≤ (Mμ * (t / ↑(n+1)) * ∑ i, |ΔSI i ω|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h_tri 2
      _ = (Mμ * (t / ↑(n+1))) ^ 2 * (∑ i, |ΔSI i ω|) ^ 2 := by ring
      _ ≤ (Mμ * (t / ↑(n+1))) ^ 2 * (↑(n+1) * ∑ i, (ΔSI i ω) ^ 2) :=
          mul_le_mul_of_nonneg_left h_cs (sq_nonneg _)
      _ = Mμ ^ 2 * (t / ↑(n+1)) ^ 2 * ↑(n+1) * ∑ i, (ΔSI i ω) ^ 2 := by ring
  -- Step 3: Integrability of ∑(ΔSIᵢ)²
  have hΔSI_sq_int : ∀ i : Fin (n+1), Integrable (fun ω => (ΔSI i ω) ^ 2) μ := by
    intro i; simp only [ΔSI]
    exact si_increment_sq_integrable X _ _
      (partition_time_nonneg t ht.le n _) (partition_time_mono t ht.le n _)
  have h_dom_int : Integrable (fun ω =>
      Mμ ^ 2 * (t / ↑(n+1)) ^ 2 * ↑(n+1) * ∑ i : Fin (n+1), (ΔSI i ω) ^ 2) μ :=
    (integrable_finset_sum _ fun i _ => hΔSI_sq_int i).const_mul _
  -- Step 4: Integrate + isometry + algebra
  calc ∫ ω, (∑ i, ΔD i ω * ΔSI i ω) ^ 2 ∂μ
      ≤ ∫ ω, (Mμ ^ 2 * (t / ↑(n+1)) ^ 2 * ↑(n+1) *
        ∑ i, (ΔSI i ω) ^ 2) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) h_dom_int
          (ae_of_all _ h_pw)
    _ = Mμ ^ 2 * (t / ↑(n+1)) ^ 2 * ↑(n+1) *
        ∑ i, ∫ ω, (ΔSI i ω) ^ 2 ∂μ := by
        rw [integral_const_mul, integral_finset_sum _ fun i _ => hΔSI_sq_int i]
    _ ≤ Mμ ^ 2 * (t / ↑(n+1)) ^ 2 * ↑(n+1) *
        ∑ i : Fin (n+1), Mσ ^ 2 * (t / ↑(n+1)) := by
        gcongr with i
        -- E[(ΔSIᵢ)²] = E[∫σ²] ≤ Mσ²·Δt by isometry + bound
        simp only [ΔSI]
        rw [ItoProcess.stoch_integral_isometry X _ _
          (partition_time_nonneg t ht.le n _) (partition_time_mono t ht.le n _)]
        calc ∫ ω, ∫ u in Icc _ _, (X.diffusion u ω) ^ 2 ∂volume ∂μ
            ≤ ∫ ω, (Mσ ^ 2 * (t / ↑(n+1))) ∂μ := by
              apply integral_mono_of_nonneg
              · exact ae_of_all _ fun ω =>
                  setIntegral_nonneg measurableSet_Icc fun r _ => sq_nonneg _
              · exact integrable_const _
              · exact ae_of_all _ fun ω => by
                  calc ∫ u in Icc _ _, (X.diffusion u ω) ^ 2 ∂volume
                      ≤ ∫ u in Icc _ _, Mσ ^ 2 ∂volume := by
                        apply integral_mono_of_nonneg
                        · exact ae_of_all _ fun _ => sq_nonneg _
                        · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
                        · exact ae_of_all _ fun r => by
                            show X.diffusion r ω ^ 2 ≤ Mσ ^ 2
                            calc X.diffusion r ω ^ 2 = |X.diffusion r ω| ^ 2 := (sq_abs _).symm
                              _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω) 2
                    _ = Mσ ^ 2 * (t / ↑(n+1)) := by
                        rw [setIntegral_const]
                        simp only [smul_eq_mul, Measure.real, Real.volume_Icc,
                          ENNReal.toReal_ofReal (sub_nonneg.mpr
                            (partition_time_mono t ht.le n (i : ℕ)))]
                        rw [hΔt i]; ring
          _ = Mσ ^ 2 * (t / ↑(n+1)) := by
              simp [integral_const, Measure.real, measure_univ]
    _ = Mμ ^ 2 * Mσ ^ 2 * t ^ 3 / ↑(n + 1) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        field_simp

/-! ## Main L² bound for QV convergence -/

/-- The main L² bound for discrete quadratic variation convergence.
    E[(∑(ΔXᵢ)² - [X]_t)²] ≤ C / (n+1)
    where C = 3Mμ⁴t⁴ + 12Mμ²Mσ²t³ + 24Mσ⁴t². -/
theorem ito_qv_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       X.quadraticVariation t ω) ^ 2 ∂μ ≤
    (3 * Mμ ^ 4 * t ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * t ^ 3 +
     24 * Mσ ^ 4 * t ^ 2) / ↑(n + 1) := by
  -- Bound by 3 terms: E[(A + 2B + C)²] ≤ 3E[A²] + 12E[B²] + 3E[C²]
  -- where A = ∑ΔDᵢ², B = ∑ΔDᵢΔSIᵢ, C = ∑Zᵢ
  -- A² ≤ (Mμ²t²/(n+1))², E[B²] ≤ Mμ²Mσ²t³/(n+1), E[C²] ≤ 8Mσ⁴t²/(n+1)
  -- Combine: ≤ 3Mμ⁴t⁴/(n+1)² + 12Mμ²Mσ²t³/(n+1) + 24Mσ⁴t²/(n+1)
  --         ≤ (3Mμ⁴t⁴ + 12Mμ²Mσ²t³ + 24Mσ⁴t²)/(n+1)  [using 1/(n+1)² ≤ 1/(n+1)]
  calc ∫ ω, (∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       X.quadraticVariation t ω) ^ 2 ∂μ
    ≤ 3 * (Mμ ^ 2 * t ^ 2 / ↑(n + 1)) ^ 2 +
      12 * (Mμ ^ 2 * Mσ ^ 2 * t ^ 3 / ↑(n + 1)) +
      3 * (8 * Mσ ^ 4 * t ^ 2 / ↑(n + 1)) := by
        -- Young's inequality: (a + 2b + c)² ≤ 3a² + 12b² + 3c²
        have h_young : ∀ a b c : ℝ, (a + 2 * b + c) ^ 2 ≤
            3 * a ^ 2 + 12 * b ^ 2 + 3 * c ^ 2 := by
          intro a b c
          nlinarith [sq_nonneg (a - c), sq_nonneg (a - 2 * b), sq_nonneg (c - 2 * b)]
        -- QV partition sum (valid for all ω since σ² is time-integrable)
        have h_qv : ∀ ω, X.quadraticVariation t ω =
            ∑ i : Fin (n + 1),
              ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1))
                ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
                (X.diffusion s ω) ^ 2 ∂volume :=
          fun ω => qv_partition_sum X t ht.le n ω
            (X.diffusion_sq_time_integrable ω t ht.le)
        -- A.e. decomposition: ΔXᵢ = ΔDᵢ + ΔSIᵢ
        have h_decomp := ito_process_increment_decomp_ae X t ht n
        -- Abbreviations for the three sums
        set ΔD : Fin (n+1) → Ω → ℝ := fun i ω =>
          ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1))
            ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
            X.drift s ω ∂volume
        set ΔSI : Fin (n+1) → Ω → ℝ := fun i ω =>
          X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
          X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω
        set A : Ω → ℝ := fun ω => ∑ i : Fin (n+1), (ΔD i ω) ^ 2
        set B : Ω → ℝ := fun ω => ∑ i : Fin (n+1), ΔD i ω * ΔSI i ω
        set C : Ω → ℝ := fun ω => ∑ i : Fin (n+1),
          ((ΔSI i ω) ^ 2 -
            ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1))
              ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
              (X.diffusion s ω) ^ 2 ∂volume)
        -- A.e. bound: S(ω)² ≤ 3A²(ω) + 12B²(ω) + 3C²(ω)
        have h_ae : ∀ᵐ ω ∂μ,
            (∑ i : Fin (n + 1),
              (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
               X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
             X.quadraticVariation t ω) ^ 2 ≤
            3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (C ω) ^ 2 := by
          filter_upwards [h_decomp] with ω hω
          -- Rewrite: ∑(ΔX)² - [X]_t = A + 2B + C
          have h_eq :
              ∑ i : Fin (n + 1),
                (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
                 X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
               X.quadraticVariation t ω =
              A ω + 2 * B ω + C ω := by
            simp only [A, B, C, ΔD, ΔSI]; rw [h_qv ω]
            rw [← Finset.sum_sub_distrib]; simp_rw [hω]
            simp_rw [show ∀ (a b c : ℝ), (a + b) ^ 2 - c =
                a ^ 2 + 2 * (a * b) + (b ^ 2 - c) from fun a b c => by ring]
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [h_eq]
          exact h_young (A ω) (B ω) (C ω)
        -- Integrability: SI increments squared
        have hΔSI_sq_int : ∀ i : Fin (n+1),
            Integrable (fun ω => (ΔSI i ω) ^ 2) μ := by
          intro i; simp only [ΔSI]
          exact si_increment_sq_integrable X _ _
            (partition_time_nonneg t ht.le n _)
            (partition_time_mono t ht.le n _)
        -- Integrability: compensated Z²
        have hZ_sq_int : ∀ i : Fin (n+1),
            Integrable (fun ω => ((ΔSI i ω) ^ 2 -
              ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1))
                ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
                (X.diffusion s ω) ^ 2 ∂volume) ^ 2) μ := by
          intro i; simp only [ΔSI]
          exact compensated_si_sq_sq_integrable X hMσ _ _
            (partition_time_nonneg t ht.le n _)
            (partition_time_mono t ht.le n _)
        -- Integrability of C² (finite sum of integrable products)
        -- Strong measurability of ΔSI and ΔX increments
        have hΔSI_sm : ∀ i : Fin (n+1), StronglyMeasurable (ΔSI i) := by
          intro i; simp only [ΔSI]
          exact (X.stoch_integral_measurable ((↑(i : ℕ) + 1) * t / ↑(n + 1))
              (by positivity)).stronglyMeasurable.sub
            (X.stoch_integral_measurable (↑(i : ℕ) * t / ↑(n + 1))
              (partition_time_nonneg t ht.le n _)).stronglyMeasurable
        have hΔX_sm : ∀ i : Fin (n+1), StronglyMeasurable (fun ω =>
            X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) := by
          intro i
          exact ((X.process_adapted ((↑(i : ℕ) + 1) * t / ↑(n + 1))).mono
              (F.le_ambient _) le_rfl).stronglyMeasurable.sub
            ((X.process_adapted (↑(i : ℕ) * t / ↑(n + 1))).mono
              (F.le_ambient _) le_rfl).stronglyMeasurable
        have hC_int : Integrable (fun ω => (C ω) ^ 2) μ := by
          -- C(ω)² ≤ (n+1) · ∑ Zᵢ² by Cauchy-Schwarz
          -- But we use the expansion: C² = (∑Z)² = ∑_i∑_j Z_i·Z_j
          have hZ_prod_int : ∀ i j : Fin (n+1),
              Integrable (fun ω =>
                ((ΔSI i ω) ^ 2 - ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1))
                    ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
                    (X.diffusion s ω) ^ 2 ∂volume) *
                ((ΔSI j ω) ^ 2 - ∫ s in Icc (↑(j : ℕ) * t / ↑(n + 1))
                    ((↑(j : ℕ) + 1) * t / ↑(n + 1)),
                    (X.diffusion s ω) ^ 2 ∂volume)) μ := by
            intro i j
            -- AM-GM domination (same as hZZ_int proof)
            have hZk_int : ∀ k : Fin (n+1),
                Integrable (fun ω => (ΔSI k ω) ^ 2 -
                  ∫ s in Icc (↑(k : ℕ) * t / ↑(n + 1))
                    ((↑(k : ℕ) + 1) * t / ↑(n + 1)),
                    (X.diffusion s ω) ^ 2 ∂volume) μ := by
              intro k; simp only [ΔSI]
              exact compensated_si_sq_integrable X _ _
                (partition_time_nonneg t ht.le n _)
                (partition_time_mono t ht.le n _)
            apply ((hZ_sq_int i).add (hZ_sq_int j)).div_const 2 |>.mono
              ((hZk_int i).aestronglyMeasurable.mul
                (hZk_int j).aestronglyMeasurable)
            filter_upwards with ω
            simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply]
            -- AM-GM: |ab| ≤ (a² + b²)/2
            set zi := ΔSI i ω ^ 2 - ∫ s in Set.Icc (↑(i : ℕ) * t / ↑(n + 1))
                ((↑(i : ℕ) + 1) * t / ↑(n + 1)), (X.diffusion s ω) ^ 2 ∂volume with hzi_def
            set zj := ΔSI j ω ^ 2 - ∫ s in Set.Icc (↑(j : ℕ) * t / ↑(n + 1))
                ((↑(j : ℕ) + 1) * t / ↑(n + 1)), (X.diffusion s ω) ^ 2 ∂volume with hzj_def
            have h_am := two_mul_le_add_sq (|zi|) (|zj|)
            rw [sq_abs, sq_abs] at h_am
            rw [abs_of_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
              (by norm_num : (0:ℝ) ≤ 2))]
            nlinarith [abs_mul zi zj, abs_nonneg zi, abs_nonneg zj]
          -- C² = (∑Z)·(∑Z) = ∑_i∑_j Z_i·Z_j
          have heq : (fun ω => (C ω) ^ 2) = (fun ω =>
              ∑ i : Fin (n+1), ∑ j : Fin (n+1),
                ((ΔSI i ω) ^ 2 - ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1))
                    ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
                    (X.diffusion s ω) ^ 2 ∂volume) *
                ((ΔSI j ω) ^ 2 - ∫ s in Icc (↑(j : ℕ) * t / ↑(n + 1))
                    ((↑(j : ℕ) + 1) * t / ↑(n + 1)),
                    (X.diffusion s ω) ^ 2 ∂volume)) := by
            ext ω; simp only [C]; rw [sq, Fintype.sum_mul_sum]
          rw [heq]
          exact integrable_finset_sum _ fun i _ =>
            integrable_finset_sum _ fun j _ => hZ_prod_int i j
        -- Integrability of B² (bounded drift × SI products)
        have hB_int : Integrable (fun ω => (B ω) ^ 2) μ := by
          -- B² ≤ (Mμ·Δt)²·(n+1)·∑(ΔSI)² — Cauchy-Schwarz + drift bound
          have hΔt : ∀ i : Fin (n+1),
              (↑(i : ℕ) + 1) * t / ↑(n + 1) - ↑(i : ℕ) * t / ↑(n + 1) =
              t / ↑(n + 1) := by intro i; ring
          have hB_bound : ∀ ω, (B ω) ^ 2 ≤
              (Mμ * (t / ↑(n+1))) ^ 2 * ↑(n+1) *
              ∑ i : Fin (n+1), (ΔSI i ω) ^ 2 := by
            intro ω
            -- |B| ≤ Mμ·Δt·∑|ΔSI| (triangle + drift bound)
            have h1 : |B ω| ≤ Mμ * (t / ↑(n+1)) * ∑ i, |ΔSI i ω| := by
              simp only [B]
              calc |∑ i, ΔD i ω * ΔSI i ω|
                  ≤ ∑ i, |ΔD i ω * ΔSI i ω| := by
                    rw [← Real.norm_eq_abs]; exact norm_sum_le _ _
                _ = ∑ i, |ΔD i ω| * |ΔSI i ω| := by
                    congr 1; ext i; exact abs_mul _ _
                _ ≤ ∑ i, Mμ * (t / ↑(n+1)) * |ΔSI i ω| := by
                    apply Finset.sum_le_sum; intro i _
                    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                    simp only [ΔD]
                    have := drift_increment_bound X hMμ _ _
                      (partition_time_mono t ht.le n (i : ℕ)) ω
                    rwa [hΔt i] at this
                _ = Mμ * (t / ↑(n+1)) * ∑ i, |ΔSI i ω| := by
                    rw [← Finset.mul_sum]
            -- B² ≤ (Mμ·Δt)²·(∑|ΔSI|)²
            have h2 : (B ω) ^ 2 ≤
                (Mμ * (t / ↑(n+1))) ^ 2 * (∑ i, |ΔSI i ω|) ^ 2 := by
              calc (B ω) ^ 2 = |B ω| ^ 2 := (sq_abs _).symm
                _ ≤ (Mμ * (t / ↑(n+1)) * ∑ i, |ΔSI i ω|) ^ 2 :=
                    pow_le_pow_left₀ (abs_nonneg _) h1 2
                _ = _ := by ring
            -- (∑|ΔSI|)² ≤ (n+1)·∑(ΔSI)² by Cauchy-Schwarz
            have h3 : (∑ i : Fin (n+1), |ΔSI i ω|) ^ 2 ≤
                ↑(n+1) * ∑ i : Fin (n+1), (ΔSI i ω) ^ 2 := by
              have h := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _
                Finset.univ (fun i : Fin (n+1) => |ΔSI i ω|)
              simp only [Finset.card_univ, Fintype.card_fin] at h
              calc (∑ i, |ΔSI i ω|) ^ 2 ≤ ↑(n+1) * ∑ i, |ΔSI i ω| ^ 2 := h
                _ = ↑(n+1) * ∑ i, (ΔSI i ω) ^ 2 := by
                    congr 1; exact Finset.sum_congr rfl fun i _ => sq_abs _
            calc (B ω) ^ 2 ≤ (Mμ * (t / ↑(n+1))) ^ 2 * (∑ i, |ΔSI i ω|) ^ 2 := h2
              _ ≤ (Mμ * (t / ↑(n+1))) ^ 2 * (↑(n+1) * ∑ i, (ΔSI i ω) ^ 2) :=
                  mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
              _ = _ := by ring
          -- B is a.e. equal to ∑((ΔX - ΔSI) · ΔSI) which is StronglyMeasurable
          have hB_aesm : AEStronglyMeasurable B μ :=
            (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
              ((hΔX_sm i).sub (hΔSI_sm i)).mul (hΔSI_sm i)).aestronglyMeasurable.congr
            (by filter_upwards [h_decomp] with ω hω
                simp only [Fintype.sum_apply, Pi.sub_apply, Pi.mul_apply, B]
                exact Finset.sum_congr rfl fun i _ => by
                  simp only [ΔD, ΔSI]; congr 1; linarith [hω i])
          apply Integrable.mono
            ((integrable_finset_sum _ fun i _ =>
              hΔSI_sq_int i).const_mul ((Mμ * (t / ↑(n+1))) ^ 2 * ↑(n+1)))
            (hB_aesm.pow 2)
          filter_upwards with ω
          simp only [Pi.pow_apply, Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (mul_nonneg (by positivity)
                (Finset.sum_nonneg fun i _ => sq_nonneg _))]
          exact hB_bound ω
        -- Integrability of A² (bounded)
        have hA_int : Integrable (fun ω => (A ω) ^ 2) μ := by
          apply (integrable_const ((Mμ ^ 2 * t ^ 2 / ↑(n + 1)) ^ 2)).mono
          · -- AEStronglyMeasurable for A²
            -- A is a.e. equal to ∑(ΔX - ΔSI)² which is StronglyMeasurable
            have hA_aesm : AEStronglyMeasurable A μ :=
              (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
                ((hΔX_sm i).sub (hΔSI_sm i)).pow 2).aestronglyMeasurable.congr
              (by filter_upwards [h_decomp] with ω hω
                  simp only [Fintype.sum_apply, Pi.sub_apply, Pi.pow_apply, A]
                  exact Finset.sum_congr rfl fun i _ => by
                    simp only [ΔD, ΔSI]; congr 1; linarith [hω i])
            exact hA_aesm.pow 2
          · filter_upwards with ω
            simp only [Real.norm_eq_abs]
            rw [abs_of_nonneg (sq_nonneg _),
                abs_of_nonneg (sq_nonneg _)]
            exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => sq_nonneg _)
              (drift_sq_sum_bound X hMμ t ht.le n ω) 2
        -- Integrability of dominator
        have h_dom_int : Integrable (fun ω =>
            3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (C ω) ^ 2) μ :=
          ((hA_int.const_mul 3).add (hB_int.const_mul 12)).add (hC_int.const_mul 3)
        -- Main calc
        calc ∫ ω, (∑ i : Fin (n + 1),
              (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
               X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
             X.quadraticVariation t ω) ^ 2 ∂μ
          ≤ ∫ ω, (3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (C ω) ^ 2) ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
              h_dom_int h_ae
          _ = 3 * ∫ ω, (A ω) ^ 2 ∂μ + 12 * ∫ ω, (B ω) ^ 2 ∂μ +
              3 * ∫ ω, (C ω) ^ 2 ∂μ := by
            have h_split1 := integral_add
              ((hA_int.const_mul 3).add (hB_int.const_mul 12))
              (hC_int.const_mul 3)
            have h_split2 := integral_add (hA_int.const_mul 3) (hB_int.const_mul 12)
            simp only [integral_const_mul, Pi.add_apply] at h_split1 h_split2
            linarith
          _ ≤ 3 * (Mμ ^ 2 * t ^ 2 / ↑(n + 1)) ^ 2 +
              12 * (Mμ ^ 2 * Mσ ^ 2 * t ^ 3 / ↑(n + 1)) +
              3 * (8 * Mσ ^ 4 * t ^ 2 / ↑(n + 1)) := by
            gcongr
            · -- E[A²] ≤ (Mμ²t²/(n+1))²
              calc ∫ ω, (A ω) ^ 2 ∂μ
                  ≤ ∫ _, (Mμ ^ 2 * t ^ 2 / ↑(n + 1)) ^ 2 ∂μ :=
                  integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
                    (integrable_const _)
                    (ae_of_all _ fun ω => pow_le_pow_left₀
                      (Finset.sum_nonneg fun i _ => sq_nonneg _)
                      (drift_sq_sum_bound X hMμ t ht.le n ω) 2)
                _ = (Mμ ^ 2 * t ^ 2 / ↑(n + 1)) ^ 2 := by
                  simp [integral_const, Measure.real, measure_univ]
            · -- E[B²] ≤ Mμ²Mσ²t³/(n+1)
              simp only [B, ΔD, ΔSI]
              exact cross_term_L2_bound X hMμ hMσ t ht n
            · -- E[C²] ≤ 8Mσ⁴t²/(n+1)
              simp only [C, ΔSI]
              exact si_compensated_sum_variance X hMσ t ht.le n
    _ ≤ (3 * Mμ ^ 4 * t ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * t ^ 3 +
         24 * Mσ ^ 4 * t ^ 2) / ↑(n + 1) := by
        have hn : (0 : ℝ) < ↑(n + 1) := by positivity
        have hn_ne : (↑(n + 1) : ℝ) ≠ 0 := ne_of_gt hn
        have hn1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_pos n
        -- Key: N ≤ N² when N ≥ 1
        have hN_le : (↑(n + 1) : ℝ) ≤ (↑(n + 1) : ℝ) ^ 2 := by
          rw [sq]; exact le_mul_of_one_le_right hn.le hn1
        -- (A/N)² = A²/N² ≤ A²/N since N ≤ N²
        have h_sq_le : (Mμ ^ 2 * t ^ 2 / ↑(n + 1)) ^ 2 ≤
            Mμ ^ 4 * t ^ 4 / ↑(n + 1) := by
          rw [div_pow, show (Mμ ^ 2 * t ^ 2) ^ 2 = Mμ ^ 4 * t ^ 4 from by ring]
          exact div_le_div_of_nonneg_left (by positivity) hn hN_le
        -- Rewrite RHS as sum of three fractions matching LHS structure
        have hrw : (3 * Mμ ^ 4 * t ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * t ^ 3 +
            24 * Mσ ^ 4 * t ^ 2) / ↑(n + 1) =
            3 * (Mμ ^ 4 * t ^ 4 / ↑(n + 1)) +
            12 * (Mμ ^ 2 * Mσ ^ 2 * t ^ 3 / ↑(n + 1)) +
            3 * (8 * Mσ ^ 4 * t ^ 2 / ↑(n + 1)) := by
          field_simp; ring
        rw [hrw]
        -- Last two terms match; first term bounded by h_sq_le
        linarith [mul_le_mul_of_nonneg_left h_sq_le (by norm_num : (0:ℝ) ≤ 3)]

/-! ## QV L² convergence -/

/-- Discrete quadratic variation converges to [X]_t in L².
    Follows from `ito_qv_L2_bound` via squeeze_zero. -/
theorem ito_process_discrete_qv_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         X.quadraticVariation t ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  set C := 3 * Mμ ^ 4 * t ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * t ^ 3 + 24 * Mσ ^ 4 * t ^ 2
  apply squeeze_zero
  · intro n; exact integral_nonneg (fun ω => sq_nonneg _)
  · intro n; exact ito_qv_L2_bound X hMμ hMσ t ht n
  · -- C/(n+1) → 0
    have h : (fun n : ℕ => C / (↑(n + 1) : ℝ)) =
        (fun n : ℕ => C * (1 / ((↑n : ℝ) + 1))) := by
      ext n; rw [Nat.cast_succ]; ring
    rw [h, show (0 : ℝ) = C * 0 from by ring]
    exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## Capped QV L² convergence

For the Itô formula, we need convergence of discrete QV over capped partition times
`min(i*T/(n+1), u)` where `u ≤ T`. The capped partition covers [0, u] with mesh ≤ T/(n+1),
so the same L² bound holds with the same constant. -/

/-- min(b,c) - min(a,c) ≤ b - a when a ≤ b. -/
private lemma min_sub_min_le {a b c : ℝ} (h : a ≤ b) :
    min b c - min a c ≤ b - a := by
  simp only [min_def]; split_ifs <;> linarith

/-- Capped partition times are nonneg. -/
private lemma capped_nonneg (T u : ℝ) (hT : 0 ≤ T) (hu : 0 ≤ u) (n : ℕ) (i : ℕ) :
    0 ≤ min (↑i * T / ↑(n + 1)) u :=
  le_min (by positivity) hu

/-- Capped partition times are monotone: min(iΔ, u) ≤ min((i+1)Δ, u). -/
private lemma capped_mono (T : ℝ) (hT : 0 ≤ T) (u : ℝ) (n : ℕ) (i : ℕ) :
    min (↑i * T / ↑(n + 1)) u ≤ min ((↑i + 1) * T / ↑(n + 1)) u :=
  min_le_min_right u (div_le_div_of_nonneg_right (by nlinarith)
    (by positivity : (0 : ℝ) < ↑(n + 1)).le)

/-- Capped t_{i+1} ≤ capped t_j for i < j (disjointness). -/
private lemma capped_disjoint (T : ℝ) (hT : 0 ≤ T) (u : ℝ) (n : ℕ)
    (i j : Fin (n + 1)) (hij : (i : ℕ) < (j : ℕ)) :
    min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u ≤ min (↑(j : ℕ) * T / ↑(n + 1)) u :=
  min_le_min_right u (partition_time_disjoint T hT n i j hij)

/-- Final capped time = u when u ≤ T. -/
private lemma capped_final (T u : ℝ) (huT : u ≤ T) (n : ℕ) :
    min ((↑(n + 1) : ℝ) * T / ↑(n + 1)) u = u := by
  rw [show (↑(n + 1) : ℝ) * T / ↑(n + 1) = T from by field_simp]
  exact min_eq_right huT

/-- QV(u) splits along capped partition. -/
private lemma capped_qv_partition_sum {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (T u : ℝ) (hu : 0 ≤ u) (huT : u ≤ T) (n : ℕ) (ω : Ω)
    (hf_int : IntegrableOn (fun s => (X.diffusion s ω) ^ 2) (Icc 0 u) volume) :
    X.quadraticVariation u ω =
    ∑ i : Fin (n + 1),
      ∫ s in Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
        (X.diffusion s ω) ^ 2 ∂volume := by
  unfold ItoProcess.quadraticVariation
  have hT := le_trans hu huT
  suffices h : ∀ k : ℕ, k ≤ n + 1 →
      ∫ x in Icc 0 (min (↑k * T / ↑(n + 1)) u),
        (X.diffusion x ω) ^ 2 ∂volume =
      ∑ i ∈ Finset.range k,
        ∫ x in Icc (min (↑i * T / ↑(n + 1)) u) (min ((↑i + 1) * T / ↑(n + 1)) u),
          (X.diffusion x ω) ^ 2 ∂volume by
    have := h (n + 1) le_rfl
    rw [capped_final T u huT n] at this
    rw [this, Finset.sum_range]
  intro k hk
  induction k with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, zero_div, min_eq_left hu,
      Finset.range_zero, Finset.sum_empty]
    rw [show Icc (0 : ℝ) 0 = {0} from Icc_self 0,
      show (volume.restrict {(0 : ℝ)}) = 0 from by
        rw [Measure.restrict_eq_zero]; exact Real.volume_singleton]
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hk)]
    have h_sub : Icc 0 (min ((↑k + 1) * T / ↑(n + 1)) u) ⊆ Icc 0 u :=
      Icc_subset_Icc le_rfl (min_le_right _ _)
    rw [show (↑(k + 1) : ℝ) = (↑k : ℝ) + 1 from by push_cast; ring]
    exact setIntegral_Icc_split
      (capped_nonneg T u hT hu n k)
      (capped_mono T hT u n k)
      (hf_int.mono_set h_sub)

/-- A.e. decomposition of capped process increments: ΔX = ΔD + ΔSI. -/
private theorem capped_increment_decomp_ae {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (_huT : u ≤ T) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
      X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω =
      (∫ s in Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
        X.drift s ω ∂volume) +
      (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) := by
  have h_all : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 2),
      X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω =
        X.process 0 ω +
        (∫ s in Icc 0 (min (↑(i : ℕ) * T / ↑(n + 1)) u), X.drift s ω ∂volume) +
        X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω := by
    rw [ae_all_iff]; intro i
    exact X.integral_form _ (capped_nonneg T u hT.le hu n (i : ℕ))
  filter_upwards [h_all] with ω hω
  intro i
  have hi := hω ⟨(i : ℕ), by omega⟩
  have hi1 := hω ⟨(i : ℕ) + 1, by omega⟩
  simp only [] at hi hi1
  rw [show (↑((i : ℕ) + 1) : ℝ) = (↑(i : ℕ) : ℝ) + 1 from by push_cast; ring] at hi1
  have h_nn := capped_nonneg T u hT.le hu n (i : ℕ)
  have h_mono := capped_mono T hT.le u n (i : ℕ)
  have h_int := X.drift_time_integrable ω _ (le_trans h_nn h_mono)
  have hsplit := setIntegral_Icc_split h_nn h_mono h_int
  linarith

set_option maxHeartbeats 400000 in
/-- Capped discrete QV approximation L² bound.
    E[(∑(ΔX_capped)² - QV(u))²] ≤ C / (n+1) where C = 3Mμ⁴T⁴ + 12Mμ²Mσ²T³ + 24Mσ⁴T². -/
theorem capped_ito_qv_L2_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2 ∂μ ≤
    (3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 +
     24 * Mσ ^ 4 * T ^ 2) / ↑(n + 1) := by
  -- Same decomposition as ito_qv_L2_bound, with capped partition times
  have hn_pos : (0 : ℝ) < ↑(n + 1) := by positivity
  -- Abbreviate capped partition times
  set sc : ℕ → ℝ := fun i => min (↑i * T / ↑(n + 1)) u
  -- Bridge: sc (k+1) = min ((↑k + 1) * T / ↑(n+1)) u (unmatched by `set`)
  have hsc_succ : ∀ k : ℕ, sc (k + 1) = min ((↑k + 1) * T / ↑(n + 1)) u := by
    intro k; simp only [sc, Nat.cast_succ]
  -- Replace remaining min ((↑k + 1) * ...) with sc (k + 1) everywhere
  simp_rw [← hsc_succ]
  -- Mesh bound: sc(i+1) - sc(i) ≤ T/(n+1)
  have hΔ_le : ∀ i : ℕ, sc (i + 1) - sc i ≤ T / ↑(n + 1) := by
    intro i
    show min _ _ - min _ _ ≤ _
    calc min (↑(i + 1) * T / ↑(n + 1)) u - min (↑i * T / ↑(n + 1)) u
        ≤ ↑(i + 1) * T / ↑(n + 1) - ↑i * T / ↑(n + 1) :=
          min_sub_min_le (by
            apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < ↑(n + 1)).le
            have : (↑i : ℝ) ≤ ↑(i + 1) := by exact_mod_cast Nat.le_succ i
            nlinarith)
      _ = T / ↑(n + 1) := by rw [Nat.cast_succ]; ring
  -- QV partition sum
  have h_qv : ∀ ω, X.quadraticVariation u ω =
      ∑ i : Fin (n + 1),
        ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume := by
    intro ω; simp only [hsc_succ]
    exact capped_qv_partition_sum X T u hu huT n ω
      (X.diffusion_sq_time_integrable ω u hu)
  -- A.e. decomposition
  have h_decomp := capped_increment_decomp_ae X T u hT hu huT n
  -- Define drift/SI increments
  set ΔD : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)), X.drift s ω ∂volume
  set ΔSI : Fin (n + 1) → Ω → ℝ := fun i ω =>
    X.stoch_integral (sc ((i : ℕ) + 1)) ω - X.stoch_integral (sc (i : ℕ)) ω
  set A : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), (ΔD i ω) ^ 2
  set B : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), ΔD i ω * ΔSI i ω
  set Cf : Ω → ℝ := fun ω => ∑ i : Fin (n + 1),
    ((ΔSI i ω) ^ 2 -
      ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
        (X.diffusion s ω) ^ 2 ∂volume)
  -- Convert h_decomp from min-form to sc/ΔD/ΔSI form
  have h_decomp_sc : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process (sc ((i : ℕ) + 1)) ω - X.process (sc (i : ℕ)) ω =
      ΔD i ω + ΔSI i ω := by
    filter_upwards [h_decomp] with ω hω i
    have := hω i
    simp only [sc, ΔD, ΔSI] at this ⊢
    exact_mod_cast this
  -- Capped time properties
  have hsc_nn : ∀ i : ℕ, 0 ≤ sc i := fun i =>
    capped_nonneg T u hT.le hu n i
  have hsc_mono : ∀ i : ℕ, sc i ≤ sc (i + 1) := fun i => by
    simp only [sc]; exact_mod_cast capped_mono T hT.le u n i
  -- A.e. bound: error² ≤ 3A² + 12B² + 3Cf²
  have h_ae : ∀ᵐ ω ∂μ,
      (∑ i : Fin (n + 1),
        (X.process (sc ((i : ℕ) + 1)) ω -
         X.process (sc (i : ℕ)) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2 ≤
      3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (Cf ω) ^ 2 := by
    have h_young : ∀ a b c : ℝ, (a + 2 * b + c) ^ 2 ≤
        3 * a ^ 2 + 12 * b ^ 2 + 3 * c ^ 2 := by
      intro a b c
      nlinarith [sq_nonneg (a - c), sq_nonneg (a - 2 * b), sq_nonneg (c - 2 * b)]
    filter_upwards [h_decomp_sc] with ω hω
    have h_eq :
        ∑ i : Fin (n + 1),
          (X.process (sc ((i : ℕ) + 1)) ω -
           X.process (sc (i : ℕ)) ω) ^ 2 -
         X.quadraticVariation u ω =
        A ω + 2 * B ω + Cf ω := by
      simp only [A, B, Cf]; rw [h_qv ω]
      rw [← Finset.sum_sub_distrib]; simp_rw [hω]
      simp_rw [show ∀ (a b c : ℝ), (a + b) ^ 2 - c =
          a ^ 2 + 2 * (a * b) + (b ^ 2 - c) from fun a b c => by ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h_eq]; exact h_young (A ω) (B ω) (Cf ω)
  -- Integrability: SI increments squared
  have hΔSI_sq_int : ∀ i : Fin (n + 1),
      Integrable (fun ω => (ΔSI i ω) ^ 2) μ := by
    intro i; simp only [ΔSI]
    exact si_increment_sq_integrable X _ _ (hsc_nn _) (hsc_mono _)
  -- Integrability: compensated Z² (from L⁴ domination)
  have hZ_sq_int : ∀ i : Fin (n + 1),
      Integrable (fun ω => ((ΔSI i ω) ^ 2 -
        ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume) ^ 2) μ := by
    intro i; simp only [ΔSI]
    exact compensated_si_sq_sq_integrable X hMσ _ _ (hsc_nn _) (hsc_mono _)
  -- Strong measurability of ΔSI and ΔX
  have hΔSI_sm : ∀ i : Fin (n + 1), StronglyMeasurable (ΔSI i) := by
    intro i; simp only [ΔSI]
    exact (X.stoch_integral_measurable _ (hsc_nn _)).stronglyMeasurable.sub
      (X.stoch_integral_measurable _ (hsc_nn _)).stronglyMeasurable
  have hΔX_sm : ∀ i : Fin (n + 1), StronglyMeasurable (fun ω =>
      X.process (sc ((i : ℕ) + 1)) ω - X.process (sc (i : ℕ)) ω) := by
    intro i
    exact ((X.process_adapted _).mono (F.le_ambient _) le_rfl).stronglyMeasurable.sub
      ((X.process_adapted _).mono (F.le_ambient _) le_rfl).stronglyMeasurable
  -- Integrability of Cf²
  have hCf_int : Integrable (fun ω => (Cf ω) ^ 2) μ := by
    have hZ_prod_int : ∀ i j : Fin (n + 1),
        Integrable (fun ω =>
          ((ΔSI i ω) ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume) *
          ((ΔSI j ω) ^ 2 - ∫ s in Icc (sc (j : ℕ)) (sc ((j : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume)) μ := by
      intro i j
      have hZk_int : ∀ k : Fin (n + 1),
          Integrable (fun ω => (ΔSI k ω) ^ 2 -
            ∫ s in Icc (sc (k : ℕ)) (sc ((k : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume) μ := by
        intro k; simp only [ΔSI]
        exact compensated_si_sq_integrable X _ _ (hsc_nn _) (hsc_mono _)
      apply ((hZ_sq_int i).add (hZ_sq_int j)).div_const 2 |>.mono
        ((hZk_int i).aestronglyMeasurable.mul (hZk_int j).aestronglyMeasurable)
      filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply]
      set zi := ΔSI i ω ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume
      set zj := ΔSI j ω ^ 2 - ∫ s in Icc (sc (j : ℕ)) (sc ((j : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume
      rw [abs_of_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
        (by norm_num : (0 : ℝ) ≤ 2))]
      have h1 : |zi * zj| = |zi| * |zj| := abs_mul zi zj
      have h2 : 2 * (|zi| * |zj|) ≤ zi ^ 2 + zj ^ 2 := by
        have h := two_mul_le_add_sq (|zi|) (|zj|)
        rw [sq_abs, sq_abs] at h; linarith
      linarith
    have heq : (fun ω => (Cf ω) ^ 2) = (fun ω =>
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          ((ΔSI i ω) ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume) *
          ((ΔSI j ω) ^ 2 - ∫ s in Icc (sc (j : ℕ)) (sc ((j : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume)) := by
      ext ω; simp only [Cf]; rw [sq, Fintype.sum_mul_sum]
    rw [heq]; exact integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => hZ_prod_int i j
  -- Pointwise bound on B²
  have hB_bound : ∀ ω, (B ω) ^ 2 ≤
      Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
      ∑ i : Fin (n + 1), (ΔSI i ω) ^ 2 := by
      intro ω
      have h1 : |B ω| ≤ Mμ * (T / ↑(n + 1)) * ∑ i, |ΔSI i ω| := by
        simp only [B]
        calc |∑ i, ΔD i ω * ΔSI i ω|
            ≤ ∑ i, |ΔD i ω * ΔSI i ω| := by
              rw [← Real.norm_eq_abs]; exact norm_sum_le _ _
          _ = ∑ i, |ΔD i ω| * |ΔSI i ω| := by
              congr 1; ext i; exact abs_mul _ _
          _ ≤ ∑ i, Mμ * (T / ↑(n + 1)) * |ΔSI i ω| :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by
                simp only [ΔD]
                calc |∫ s in Icc _ _, X.drift s ω ∂volume| ≤ Mμ * (_ - _) :=
                    drift_increment_bound X hMμ _ _ (hsc_mono _) ω
                  _ ≤ Mμ * (T / ↑(n + 1)) := by
                    exact mul_le_mul_of_nonneg_left (hΔ_le _) (le_trans (abs_nonneg _) (hMμ 0 ω)))
                (abs_nonneg _)
          _ = Mμ * (T / ↑(n + 1)) * ∑ i, |ΔSI i ω| := by rw [← Finset.mul_sum]
      have h_cs : (∑ i : Fin (n + 1), |ΔSI i ω|) ^ 2 ≤
          ↑(n + 1) * ∑ i : Fin (n + 1), (ΔSI i ω) ^ 2 := by
        have h := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ
          (fun i : Fin (n + 1) => |ΔSI i ω|)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        calc _ ≤ ↑(n + 1) * ∑ i, |ΔSI i ω| ^ 2 := h
          _ = _ := by congr 1; exact Finset.sum_congr rfl fun i _ => sq_abs _
      calc (B ω) ^ 2 = |B ω| ^ 2 := (sq_abs _).symm
        _ ≤ (Mμ * (T / ↑(n + 1)) * ∑ i, |ΔSI i ω|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = (Mμ * (T / ↑(n + 1))) ^ 2 * (∑ i, |ΔSI i ω|) ^ 2 := by ring
        _ ≤ (Mμ * (T / ↑(n + 1))) ^ 2 * (↑(n + 1) * ∑ i, (ΔSI i ω) ^ 2) :=
            mul_le_mul_of_nonneg_left h_cs (sq_nonneg _)
        _ = _ := by ring
  -- B is a.e. measurable
  have hB_aesm : AEStronglyMeasurable B μ :=
    (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
      ((hΔX_sm i).sub (hΔSI_sm i)).mul (hΔSI_sm i)).aestronglyMeasurable.congr
    (by filter_upwards [h_decomp_sc] with ω hω
        simp only [Fintype.sum_apply, Pi.sub_apply, Pi.mul_apply, B]
        exact Finset.sum_congr rfl fun i _ => by
          congr 1; linarith [hω i])
  have hB_int : Integrable (fun ω => (B ω) ^ 2) μ :=
    Integrable.mono
      ((integrable_finset_sum _ fun i _ => hΔSI_sq_int i).const_mul
        (Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1)))
      (hB_aesm.pow 2)
      (by filter_upwards with ω
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (mul_nonneg (by positivity)
                (Finset.sum_nonneg fun i _ => sq_nonneg _))]
          exact hB_bound ω)
  -- Integrability of A²
  have hA_int : Integrable (fun ω => (A ω) ^ 2) μ := by
    have hA_bound : ∀ ω, A ω ≤ Mμ ^ 2 * T ^ 2 / ↑(n + 1) := by
      intro ω; simp only [A]
      calc ∑ i : Fin (n + 1), (ΔD i ω) ^ 2
          ≤ ∑ i : Fin (n + 1), Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              simp only [ΔD]
              have h := drift_increment_bound X hMμ (sc ↑i) (sc (↑i + 1)) (hsc_mono ↑i) ω
              calc _ ≤ |∫ s in Icc _ _, X.drift s ω ∂volume| ^ 2 := by rw [sq_abs]
                _ ≤ (Mμ * (sc (↑i + 1) - sc ↑i)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
                _ ≤ (Mμ * (T / ↑(n + 1))) ^ 2 := by
                    apply pow_le_pow_left₀ (mul_nonneg (le_trans (abs_nonneg _) (hMμ 0 ω))
                      (sub_nonneg.mpr (hsc_mono _)))
                    exact mul_le_mul_of_nonneg_left (hΔ_le _) (le_trans (abs_nonneg _) (hMμ 0 ω))
                _ = _ := by ring
        _ = ↑(n + 1) * (Mμ ^ 2 * (T / ↑(n + 1)) ^ 2) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        _ = Mμ ^ 2 * T ^ 2 / ↑(n + 1) := by field_simp
    have hA_aesm : AEStronglyMeasurable A μ :=
      (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
        ((hΔX_sm i).sub (hΔSI_sm i)).pow 2).aestronglyMeasurable.congr
      (by filter_upwards [h_decomp_sc] with ω hω
          simp only [Fintype.sum_apply, Pi.sub_apply, Pi.pow_apply, A]
          exact Finset.sum_congr rfl fun i _ => by
            congr 1; linarith [hω i])
    exact (integrable_const ((Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2)).mono (hA_aesm.pow 2)
      (by filter_upwards with ω
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => sq_nonneg _)
            (hA_bound ω) 2)
  -- Integrability of dominator
  have h_dom_int : Integrable (fun ω =>
      3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (Cf ω) ^ 2) μ :=
    ((hA_int.const_mul 3).add (hB_int.const_mul 12)).add (hCf_int.const_mul 3)
  -- Main calc
  calc ∫ ω, (∑ i : Fin (n + 1),
        (X.process (sc ((i : ℕ) + 1)) ω -
         X.process (sc (i : ℕ)) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2 ∂μ
    ≤ ∫ ω, (3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (Cf ω) ^ 2) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) h_dom_int h_ae
    _ = 3 * ∫ ω, (A ω) ^ 2 ∂μ + 12 * ∫ ω, (B ω) ^ 2 ∂μ +
        3 * ∫ ω, (Cf ω) ^ 2 ∂μ := by
      have h1 := integral_add ((hA_int.const_mul 3).add (hB_int.const_mul 12))
        (hCf_int.const_mul 3)
      have h2 := integral_add (hA_int.const_mul 3) (hB_int.const_mul 12)
      simp only [integral_const_mul, Pi.add_apply] at h1 h2; linarith
    _ ≤ 3 * (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 +
        12 * (Mμ ^ 2 * Mσ ^ 2 * T ^ 3 / ↑(n + 1)) +
        3 * (8 * Mσ ^ 4 * T ^ 2 / ↑(n + 1)) := by
      gcongr
      · -- E[A²] ≤ (Mμ²T²/(n+1))²
        calc ∫ ω, (A ω) ^ 2 ∂μ
            ≤ ∫ _, (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
              (integrable_const _)
              (ae_of_all _ fun ω => pow_le_pow_left₀
                (Finset.sum_nonneg fun i _ => sq_nonneg _)
                (by simp only [A]
                    calc ∑ i : Fin (n + 1), (ΔD i ω) ^ 2
                        ≤ ∑ i : Fin (n + 1), Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 :=
                          Finset.sum_le_sum fun i _ => by
                            simp only [ΔD]
                            have h := drift_increment_bound X hMμ (sc ↑i) (sc (↑i + 1)) (hsc_mono ↑i) ω
                            calc _ ≤ |∫ s in Icc _ _, X.drift s ω ∂volume| ^ 2 := by rw [sq_abs]
                              _ ≤ (Mμ * (sc (↑i + 1) - sc ↑i)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
                              _ ≤ (Mμ * (T / ↑(n + 1))) ^ 2 := by
                                  apply pow_le_pow_left₀ (mul_nonneg (le_trans (abs_nonneg _) (hMμ 0 ω))
                                    (sub_nonneg.mpr (hsc_mono _)))
                                  exact mul_le_mul_of_nonneg_left (hΔ_le _)
                                    (le_trans (abs_nonneg _) (hMμ 0 ω))
                              _ = _ := by ring
                      _ = _ := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; field_simp) 2)
          _ = (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 := by
              simp [integral_const, Measure.real, measure_univ]
      · -- E[B²] ≤ Mμ²Mσ²T³/(n+1) via isometry
        calc ∫ ω, (B ω) ^ 2 ∂μ
            ≤ ∫ ω, (Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
              ∑ i, (ΔSI i ω) ^ 2) ∂μ :=
              integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
                ((integrable_finset_sum _ fun i _ => hΔSI_sq_int i).const_mul _)
                (ae_of_all _ hB_bound)
            _ = Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
                ∑ i, ∫ ω, (ΔSI i ω) ^ 2 ∂μ := by
              rw [integral_const_mul, integral_finset_sum _ fun i _ => hΔSI_sq_int i]
            _ ≤ Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
                ∑ i : Fin (n + 1), Mσ ^ 2 * (T / ↑(n + 1)) := by
              gcongr with i
              simp only [ΔSI]
              rw [ItoProcess.stoch_integral_isometry X _ _ (hsc_nn _) (hsc_mono _)]
              calc ∫ ω, ∫ r in Icc _ _, (X.diffusion r ω) ^ 2 ∂volume ∂μ
                  ≤ ∫ ω, (Mσ ^ 2 * (T / ↑(n + 1))) ∂μ := by
                    apply integral_mono_of_nonneg
                    · exact ae_of_all _ fun ω =>
                        setIntegral_nonneg measurableSet_Icc fun r _ => sq_nonneg _
                    · exact integrable_const _
                    · exact ae_of_all _ fun ω => by
                        calc ∫ r in Icc _ _, (X.diffusion r ω) ^ 2 ∂volume
                            ≤ ∫ r in Icc _ _, Mσ ^ 2 ∂volume := by
                              apply integral_mono_of_nonneg
                              · exact ae_of_all _ fun _ => sq_nonneg _
                              · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
                              · exact ae_of_all _ fun r => by
                                  calc _ = |X.diffusion r ω| ^ 2 := (sq_abs _).symm
                                    _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω) 2
                          _ ≤ Mσ ^ 2 * (T / ↑(n + 1)) := by
                              rw [setIntegral_const]
                              simp only [smul_eq_mul, Measure.real, Real.volume_Icc,
                                ENNReal.toReal_ofReal (sub_nonneg.mpr (hsc_mono _))]
                              rw [mul_comm]
                              exact mul_le_mul_of_nonneg_left (hΔ_le _) (sq_nonneg _)
                _ = Mσ ^ 2 * (T / ↑(n + 1)) := by
                    simp [integral_const, Measure.real, measure_univ]
            _ = Mμ ^ 2 * Mσ ^ 2 * T ^ 3 / ↑(n + 1) := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; field_simp
      · -- E[Cf²] ≤ 8Mσ⁴T²/(n+1) via Pythagorean + individual bound
        -- Set up Z functions
        set Z : Fin (n + 1) → Ω → ℝ := fun i ω =>
          (ΔSI i ω) ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
            (X.diffusion s ω) ^ 2 ∂volume
        -- Integrability of products
        have hZZ_int : ∀ i j : Fin (n + 1), Integrable (fun ω => Z i ω * Z j ω) μ := by
          intro i j
          have hZk_int : ∀ k : Fin (n + 1), Integrable (Z k) μ := by
            intro k; simp only [Z, ΔSI]
            exact compensated_si_sq_integrable X _ _ (hsc_nn _) (hsc_mono _)
          apply ((hZ_sq_int i).add (hZ_sq_int j)).div_const 2 |>.mono
            ((hZk_int i).aestronglyMeasurable.mul (hZk_int j).aestronglyMeasurable)
          filter_upwards with ω
          simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply]
          set zi := Z i ω
          set zj := Z j ω
          have h_am := two_mul_le_add_sq (|zi|) (|zj|)
          rw [sq_abs, sq_abs] at h_am
          rw [abs_of_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (by norm_num : (0 : ℝ) ≤ 2))]
          have h1 : |zi * zj| = |zi| * |zj| := abs_mul zi zj
          have h2 : 2 * (|zi| * |zj|) ≤ zi ^ 2 + zj ^ 2 := by
            have h := two_mul_le_add_sq (|zi|) (|zj|)
            rw [sq_abs, sq_abs] at h; linarith
          linarith
        -- Orthogonality
        have horth : ∀ i j : Fin (n + 1), i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = 0 := by
          intro i j hij
          rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
          · simp only [Z, ΔSI]
            exact ItoProcess.stoch_integral_squared_orthogonal X hMσ _ _ _ _
              (hsc_nn _) (hsc_mono _)
              (by exact_mod_cast capped_disjoint T hT.le u n i j h)
              (hsc_mono _)
          · rw [show (fun ω => Z i ω * Z j ω) = (fun ω => Z j ω * Z i ω) from by
                ext ω; ring]
            simp only [Z, ΔSI]
            exact ItoProcess.stoch_integral_squared_orthogonal X hMσ _ _ _ _
              (hsc_nn _) (hsc_mono _)
              (by exact_mod_cast capped_disjoint T hT.le u n j i h)
              (hsc_mono _)
        -- Pythagorean identity + individual bounds
        have hCf_eq : (fun ω => (Cf ω) ^ 2) = (fun ω => (∑ i, Z i ω) ^ 2) := by
          ext ω; simp only [Cf, Z]
        rw [hCf_eq, integral_sq_sum_orthogonal Z hZZ_int horth]
        calc ∑ i : Fin (n + 1), ∫ ω, (Z i ω) ^ 2 ∂μ
            ≤ ∑ i : Fin (n + 1), 8 * Mσ ^ 4 * (T / ↑(n + 1)) ^ 2 := by
              apply Finset.sum_le_sum; intro i _; simp only [Z, ΔSI]
              calc ∫ ω, _ ^ 2 ∂μ
                  ≤ 8 * Mσ ^ 4 * (sc ((i : ℕ) + 1) - sc (i : ℕ)) ^ 2 :=
                    si_compensated_sq_L2_single X hMσ _ _ (hsc_nn _) (hsc_mono _)
                _ ≤ 8 * Mσ ^ 4 * (T / ↑(n + 1)) ^ 2 := by
                    gcongr
                    · exact sub_nonneg.mpr (hsc_mono _)
                    · exact hΔ_le _
          _ = 8 * Mσ ^ 4 * T ^ 2 / ↑(n + 1) := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; field_simp
    _ ≤ (3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 +
         24 * Mσ ^ 4 * T ^ 2) / ↑(n + 1) := by
      have hn1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_pos n
      have hN_le : (↑(n + 1) : ℝ) ≤ (↑(n + 1) : ℝ) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_right hn_pos.le hn1
      have h_sq_le : (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 ≤ Mμ ^ 4 * T ^ 4 / ↑(n + 1) := by
        rw [div_pow, show (Mμ ^ 2 * T ^ 2) ^ 2 = Mμ ^ 4 * T ^ 4 from by ring]
        exact div_le_div_of_nonneg_left (by positivity) hn_pos hN_le
      have hrw : (3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 +
          24 * Mσ ^ 4 * T ^ 2) / ↑(n + 1) =
          3 * (Mμ ^ 4 * T ^ 4 / ↑(n + 1)) +
          12 * (Mμ ^ 2 * Mσ ^ 2 * T ^ 3 / ↑(n + 1)) +
          3 * (8 * Mσ ^ 4 * T ^ 2 / ↑(n + 1)) := by
        field_simp; ring
      rw [hrw]
      linarith [mul_le_mul_of_nonneg_left h_sq_le (by norm_num : (0 : ℝ) ≤ 3)]

/-- Capped discrete quadratic variation converges to QV(u) in L². -/
theorem capped_discrete_qv_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
         X.quadraticVariation u ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  set C := 3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 + 24 * Mσ ^ 4 * T ^ 2
  apply squeeze_zero
  · intro n; exact integral_nonneg (fun ω => sq_nonneg _)
  · intro n; exact capped_ito_qv_L2_bound X hMμ hMσ T u hT hu huT n
  · have h : (fun n : ℕ => C / (↑(n + 1) : ℝ)) =
        (fun n : ℕ => C * (1 / ((↑n : ℝ) + 1))) := by
      ext n; rw [Nat.cast_succ]; ring
    rw [h, show (0 : ℝ) = C * 0 from by ring]
    exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## Core helper adapters -/

/-- Core wrapper for L⁴-integrability of stochastic integral increments. -/
private lemma stoch_integral_increment_L4_integrable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    Integrable (fun ω => (X.stoch_integral u ω - X.stoch_integral s ω) ^ 4) μ := by
  let Xp : ItoProcess F μ := X.toItoProcess R
  have hMσp : ∀ t ω, |Xp.diffusion t ω| ≤ Mσ := by
    intro t ω
    change |X.diffusion t ω| ≤ Mσ
    exact hMσ t ω
  simpa [Xp] using stoch_integral_increment_L4_integrable_proof Xp hMσp s u hs hsu

/-- Core wrapper for the L⁴ bound of stochastic integral increments. -/
private lemma stoch_integral_increment_L4_bound_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    ∫ ω, (X.stoch_integral u ω - X.stoch_integral s ω) ^ 4 ∂μ ≤
      3 * Mσ ^ 4 * (u - s) ^ 2 := by
  let Xp : ItoProcess F μ := X.toItoProcess R
  have hMσp : ∀ t ω, |Xp.diffusion t ω| ≤ Mσ := by
    intro t ω
    change |X.diffusion t ω| ≤ Mσ
    exact hMσ t ω
  simpa [Xp] using stoch_integral_increment_L4_bound_proof Xp hMσp s u hs hsu

/-- Core wrapper for stochastic-integral measurability from split regularity bundles. -/
private theorem stoch_integral_measurable_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (t : ℝ) (ht : 0 ≤ t) :
    Measurable (X.stoch_integral t) := by
  let Xp : ItoProcess F μ := X.toItoProcess R
  simpa [Xp] using Xp.stoch_integral_measurable t ht

/-- Core version: QV(u) splits along capped partition times. -/
private lemma capped_qv_partition_sum_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) (T u : ℝ) (hu : 0 ≤ u) (huT : u ≤ T) (n : ℕ) (ω : Ω)
    (hf_int : IntegrableOn (fun s => (X.diffusion s ω) ^ 2) (Icc 0 u) volume) :
    X.quadraticVariation u ω =
    ∑ i : Fin (n + 1),
      ∫ s in Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
        (X.diffusion s ω) ^ 2 ∂volume := by
  unfold ItoProcessCore.quadraticVariation
  have hT := le_trans hu huT
  suffices h : ∀ k : ℕ, k ≤ n + 1 →
      ∫ x in Icc 0 (min (↑k * T / ↑(n + 1)) u),
        (X.diffusion x ω) ^ 2 ∂volume =
      ∑ i ∈ Finset.range k,
        ∫ x in Icc (min (↑i * T / ↑(n + 1)) u) (min ((↑i + 1) * T / ↑(n + 1)) u),
          (X.diffusion x ω) ^ 2 ∂volume by
    have := h (n + 1) le_rfl
    rw [capped_final T u huT n] at this
    rw [this, Finset.sum_range]
  intro k hk
  induction k with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, zero_div, min_eq_left hu,
      Finset.range_zero, Finset.sum_empty]
    rw [show Icc (0 : ℝ) 0 = {0} from Icc_self 0,
      show (volume.restrict {(0 : ℝ)}) = 0 from by
        rw [Measure.restrict_eq_zero]
        exact Real.volume_singleton]
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hk)]
    have h_sub : Icc 0 (min ((↑k + 1) * T / ↑(n + 1)) u) ⊆ Icc 0 u :=
      Icc_subset_Icc le_rfl (min_le_right _ _)
    rw [show (↑(k + 1) : ℝ) = (↑k : ℝ) + 1 from by push_cast; ring]
    exact setIntegral_Icc_split
      (capped_nonneg T u hT hu n k)
      (capped_mono T hT u n k)
      (hf_int.mono_set h_sub)

/-- Core version: a.e. decomposition of capped increments `ΔX = ΔD + ΔSI`. -/
private theorem capped_increment_decomp_ae_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (DR : ItoProcessDriftRegularity X)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (_huT : u ≤ T) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
      X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω =
      (∫ s in Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
        X.drift s ω ∂volume) +
      (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) := by
  have h_all : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 2),
      X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω =
        X.process 0 ω +
        (∫ s in Icc 0 (min (↑(i : ℕ) * T / ↑(n + 1)) u), X.drift s ω ∂volume) +
        X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω := by
    rw [ae_all_iff]
    intro i
    exact X.integral_form _ (capped_nonneg T u hT.le hu n (i : ℕ))
  filter_upwards [h_all] with ω hω
  intro i
  have hi := hω ⟨(i : ℕ), by omega⟩
  have hi1 := hω ⟨(i : ℕ) + 1, by omega⟩
  simp only [] at hi hi1
  rw [show (↑((i : ℕ) + 1) : ℝ) = (↑(i : ℕ) : ℝ) + 1 from by push_cast; ring] at hi1
  have h_nn := capped_nonneg T u hT.le hu n (i : ℕ)
  have h_mono := capped_mono T hT.le u n (i : ℕ)
  have h_int := DR.drift_time_integrable ω _ (le_trans h_nn h_mono)
  have hsplit := setIntegral_Icc_split h_nn h_mono h_int
  linarith

/-- Core adapter for a.e. increment decomposition `ΔX = ΔD + ΔSI` on partitions. -/
theorem ito_process_increment_decomp_ae_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (DR : ItoProcessDriftRegularity X)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
      X.process (↑(i : ℕ) * t / ↑(n + 1)) ω =
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) +
      (X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω) := by
  have h_all_times : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 2),
      X.process (↑(i : ℕ) * t / ↑(n + 1)) ω =
        X.process 0 ω +
        (∫ s in Icc 0 (↑(i : ℕ) * t / ↑(n + 1)), X.drift s ω ∂volume) +
        X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω := by
    rw [ae_all_iff]
    intro i
    apply X.integral_form
    exact partition_time_nonneg t ht.le n (i : ℕ)
  filter_upwards [h_all_times] with ω hω
  intro i
  have hi := hω ⟨(i : ℕ), by omega⟩
  have hi1 := hω ⟨(i : ℕ) + 1, by exact Nat.succ_lt_succ i.isLt⟩
  set ti := (↑(i : ℕ) : ℝ) * t / ↑(n + 1) with hti_def
  set ti1 := ((↑(i : ℕ) : ℝ) + 1) * t / ↑(n + 1) with hti1_def
  have h_ti_nonneg : 0 ≤ ti := partition_time_nonneg t ht.le n (i : ℕ)
  have h_ti_le_ti1 : ti ≤ ti1 := partition_time_mono t ht.le n (i : ℕ)
  have h_int : IntegrableOn (fun s => X.drift s ω) (Icc 0 ti1) volume :=
    DR.drift_time_integrable ω ti1 (le_trans h_ti_nonneg h_ti_le_ti1)
  have hsplit := setIntegral_Icc_split h_ti_nonneg h_ti_le_ti1 h_int
  have hcast : (↑((⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 2)) : ℕ) : ℝ) =
      (↑(i : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast] at hi1
  linarith

/-- Core adapter for drift increment bound. -/
lemma drift_increment_bound_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    (s u : ℝ) (hsu : s ≤ u) (ω : Ω) :
    |∫ r in Icc s u, X.drift r ω ∂volume| ≤ Mμ * (u - s) := by
  by_cases hint : IntegrableOn (fun r => X.drift r ω) (Icc s u) volume
  · calc |∫ r in Icc s u, X.drift r ω ∂volume|
        ≤ ∫ r in Icc s u, |X.drift r ω| ∂volume := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ r in Icc s u, Mμ ∂volume := by
          apply setIntegral_mono_on hint.norm
          · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          · exact measurableSet_Icc
          · intro r _
            exact hMμ r ω
      _ = Mμ * (u - s) := by
          rw [setIntegral_const]
          simp [Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hsu), smul_eq_mul, mul_comm]
  · rw [integral_undef hint, abs_zero]
    exact mul_nonneg (le_trans (abs_nonneg _) (hMμ 0 ω)) (sub_nonneg.mpr hsu)

/-- Core adapter for deterministic bound on squared drift increments. -/
lemma drift_sq_sum_bound_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (ω : Ω) :
    ∑ i : Fin (n + 1),
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) ^ 2 ≤
    Mμ ^ 2 * t ^ 2 / ↑(n + 1) := by
  have h_bound : ∀ i : Fin (n + 1),
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) ^ 2 ≤ Mμ ^ 2 * (t / ↑(n + 1)) ^ 2 := by
    intro i
    have hle := drift_increment_bound_core X hMμ
      (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1))
      (partition_time_mono t ht n (i : ℕ)) ω
    calc (∫ s in Icc _ _, X.drift s ω ∂volume) ^ 2
        ≤ |∫ s in Icc _ _, X.drift s ω ∂volume| ^ 2 := by
          rw [sq_abs]
      _ ≤ (Mμ * ((↑(i : ℕ) + 1) * t / ↑(n + 1) - ↑(i : ℕ) * t / ↑(n + 1))) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) hle 2
      _ = Mμ ^ 2 * (t / ↑(n + 1)) ^ 2 := by ring_nf
  calc ∑ i : Fin (n + 1), _ ≤ ∑ i : Fin (n + 1), Mμ ^ 2 * (t / ↑(n + 1)) ^ 2 :=
      Finset.sum_le_sum (fun i _ => h_bound i)
    _ = ↑(n + 1) * (Mμ ^ 2 * (t / ↑(n + 1)) ^ 2) := by
        rw [Finset.sum_const, Finset.card_fin]
        simp [nsmul_eq_mul]
    _ = Mμ ^ 2 * t ^ 2 / ↑(n + 1) := by
        have hn : (0 : ℝ) < ↑(n + 1) := by positivity
        field_simp

/-- Core adapter for partition splitting of quadratic variation. -/
lemma qv_partition_sum_core {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (ω : Ω)
    (hf_int : IntegrableOn (fun s => (X.diffusion s ω) ^ 2) (Icc 0 t) volume) :
    X.quadraticVariation t ω =
    ∑ i : Fin (n + 1),
      ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        (X.diffusion s ω) ^ 2 ∂volume := by
  unfold ItoProcessCore.quadraticVariation
  have h := integral_partition_sum_aux (fun s => (X.diffusion s ω) ^ 2) t ht n hf_int (n + 1) le_rfl
  rw [show (↑(n + 1) : ℝ) * t / ↑(n + 1) = t from by field_simp] at h
  rw [h]
  rw [Finset.sum_range]

/-- Core adapter for single compensated SI² increment L² bound. -/
lemma si_compensated_sq_L2_single_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    ∫ ω,
      ((X.stoch_integral u ω - X.stoch_integral s ω) ^ 2 -
       ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume) ^ 2 ∂μ ≤
    8 * Mσ ^ 4 * (u - s) ^ 2 := by
  set ΔSI := fun ω => X.stoch_integral u ω - X.stoch_integral s ω with hΔSI_def
  set σ_int := fun ω => ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume with hσ_int_def
  have hσ_bound : ∀ ω, σ_int ω ≤ Mσ ^ 2 * (u - s) := by
    intro ω
    have h_each : ∀ r, (X.diffusion r ω) ^ 2 ≤ Mσ ^ 2 := by
      intro r
      calc (X.diffusion r ω) ^ 2 = |X.diffusion r ω| ^ 2 := by rw [sq_abs]
        _ ≤ Mσ ^ 2 := by
          apply pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω)
    calc σ_int ω = ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume := rfl
      _ ≤ ∫ r in Icc s u, Mσ ^ 2 ∂volume := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun r => sq_nonneg (X.diffusion r ω)
          · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
          · exact ae_of_all _ fun r => h_each r
      _ = Mσ ^ 2 * (u - s) := by
          rw [setIntegral_const]
          simp [Measure.real, Real.volume_Icc,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hsu), smul_eq_mul, mul_comm]
  have h_pw : ∀ ω, (ΔSI ω ^ 2 - σ_int ω) ^ 2 ≤
      2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
    intro ω
    have h1 : (ΔSI ω ^ 2 - σ_int ω) ^ 2 ≤
        2 * (ΔSI ω ^ 2) ^ 2 + 2 * (σ_int ω) ^ 2 := by
      nlinarith [sq_nonneg (ΔSI ω ^ 2 + σ_int ω)]
    have h2 : (σ_int ω) ^ 2 ≤ (Mσ ^ 2 * (u - s)) ^ 2 := by
      apply sq_le_sq'
      · have hσ_nonneg : 0 ≤ σ_int ω :=
          setIntegral_nonneg measurableSet_Icc (fun r _ => sq_nonneg (X.diffusion r ω))
        have : 0 ≤ Mσ ^ 2 * (u - s) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsu)
        linarith
      · exact hσ_bound ω
    calc (ΔSI ω ^ 2 - σ_int ω) ^ 2
        ≤ 2 * (ΔSI ω ^ 2) ^ 2 + 2 * (σ_int ω) ^ 2 := h1
      _ ≤ 2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
          have : (ΔSI ω ^ 2) ^ 2 = ΔSI ω ^ 4 := by ring
          linarith
  have hL4 : Integrable (fun ω => ΔSI ω ^ 4) μ := by
    simpa [ΔSI] using
      stoch_integral_increment_L4_integrable_core X R hMσ s u hs hsu
  have h_ub_int : Integrable (fun ω => 2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2) μ :=
    (hL4.const_mul 2).add (integrable_const _)
  calc ∫ ω, (ΔSI ω ^ 2 - σ_int ω) ^ 2 ∂μ
      ≤ ∫ ω, (2 * ΔSI ω ^ 4 + 2 * (Mσ ^ 2 * (u - s)) ^ 2) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun ω => sq_nonneg _
        · exact h_ub_int
        · exact ae_of_all _ h_pw
    _ = 2 * ∫ ω, ΔSI ω ^ 4 ∂μ + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
        rw [integral_add (hL4.const_mul 2) (integrable_const _),
            integral_const_mul, integral_const, smul_eq_mul]
        congr 1
        rw [show μ.real Set.univ = 1 from by
          simp [Measure.real, measure_univ]]
        ring
    _ ≤ 2 * (3 * Mσ ^ 4 * (u - s) ^ 2) + 2 * (Mσ ^ 2 * (u - s)) ^ 2 := by
        gcongr
        simpa [ΔSI] using
          stoch_integral_increment_L4_bound_core X R hMσ s u hs hsu
    _ = 8 * Mσ ^ 4 * (u - s) ^ 2 := by ring

set_option maxHeartbeats 400000 in
/-- Core adapter for capped discrete QV L² bound. -/
theorem capped_ito_qv_L2_bound_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2 ∂μ ≤
    (3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 +
     24 * Mσ ^ 4 * T ^ 2) / ↑(n + 1) := by
  have hn_pos : (0 : ℝ) < ↑(n + 1) := by positivity
  have R : ItoProcessRegularity X :=
    ItoProcessRegularity.ofSplit C DR D FC
  -- Abbreviate capped partition times
  set sc : ℕ → ℝ := fun i => min (↑i * T / ↑(n + 1)) u
  -- Bridge: sc (k+1) = min ((↑k + 1) * T / ↑(n+1)) u (unmatched by `set`)
  have hsc_succ : ∀ k : ℕ, sc (k + 1) = min ((↑k + 1) * T / ↑(n + 1)) u := by
    intro k; simp only [sc, Nat.cast_succ]
  -- Replace remaining min ((↑k + 1) * ...) with sc (k + 1) everywhere
  simp_rw [← hsc_succ]
  -- Mesh bound: sc(i+1) - sc(i) ≤ T/(n+1)
  have hΔ_le : ∀ i : ℕ, sc (i + 1) - sc i ≤ T / ↑(n + 1) := by
    intro i
    show min _ _ - min _ _ ≤ _
    calc min (↑(i + 1) * T / ↑(n + 1)) u - min (↑i * T / ↑(n + 1)) u
        ≤ ↑(i + 1) * T / ↑(n + 1) - ↑i * T / ↑(n + 1) :=
          min_sub_min_le (by
            apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < ↑(n + 1)).le
            have : (↑i : ℝ) ≤ ↑(i + 1) := by exact_mod_cast Nat.le_succ i
            nlinarith)
      _ = T / ↑(n + 1) := by rw [Nat.cast_succ]; ring
  -- QV partition sum
  have h_qv : ∀ ω, X.quadraticVariation u ω =
      ∑ i : Fin (n + 1),
        ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume := by
    intro ω
    simpa [sc, hsc_succ] using
      (capped_qv_partition_sum_core X T u hu huT n ω
        (D.diffusion_sq_time_integrable ω u hu))
  -- A.e. decomposition
  have h_decomp := capped_increment_decomp_ae_core X DR T u hT hu huT n
  -- Define drift/SI increments
  set ΔD : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)), X.drift s ω ∂volume
  set ΔSI : Fin (n + 1) → Ω → ℝ := fun i ω =>
    X.stoch_integral (sc ((i : ℕ) + 1)) ω - X.stoch_integral (sc (i : ℕ)) ω
  set A : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), (ΔD i ω) ^ 2
  set B : Ω → ℝ := fun ω => ∑ i : Fin (n + 1), ΔD i ω * ΔSI i ω
  set Cf : Ω → ℝ := fun ω => ∑ i : Fin (n + 1),
    ((ΔSI i ω) ^ 2 -
      ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
        (X.diffusion s ω) ^ 2 ∂volume)
  -- Convert h_decomp from min-form to sc/ΔD/ΔSI form
  have h_decomp_sc : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process (sc ((i : ℕ) + 1)) ω - X.process (sc (i : ℕ)) ω =
      ΔD i ω + ΔSI i ω := by
    filter_upwards [h_decomp] with ω hω i
    have := hω i
    simp only [sc, ΔD, ΔSI] at this ⊢
    exact_mod_cast this
  -- Capped time properties
  have hsc_nn : ∀ i : ℕ, 0 ≤ sc i := fun i =>
    capped_nonneg T u hT.le hu n i
  have hsc_mono : ∀ i : ℕ, sc i ≤ sc (i + 1) := fun i => by
    simp only [sc]; exact_mod_cast capped_mono T hT.le u n i
  -- A.e. bound: error² ≤ 3A² + 12B² + 3Cf²
  have h_ae : ∀ᵐ ω ∂μ,
      (∑ i : Fin (n + 1),
        (X.process (sc ((i : ℕ) + 1)) ω -
         X.process (sc (i : ℕ)) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2 ≤
      3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (Cf ω) ^ 2 := by
    have h_young : ∀ a b c : ℝ, (a + 2 * b + c) ^ 2 ≤
        3 * a ^ 2 + 12 * b ^ 2 + 3 * c ^ 2 := by
      intro a b c
      nlinarith [sq_nonneg (a - c), sq_nonneg (a - 2 * b), sq_nonneg (c - 2 * b)]
    filter_upwards [h_decomp_sc] with ω hω
    have h_eq :
        ∑ i : Fin (n + 1),
          (X.process (sc ((i : ℕ) + 1)) ω -
           X.process (sc (i : ℕ)) ω) ^ 2 -
         X.quadraticVariation u ω =
        A ω + 2 * B ω + Cf ω := by
      simp only [A, B, Cf]; rw [h_qv ω]
      rw [← Finset.sum_sub_distrib]; simp_rw [hω]
      simp_rw [show ∀ (a b c : ℝ), (a + b) ^ 2 - c =
          a ^ 2 + 2 * (a * b) + (b ^ 2 - c) from fun a b c => by ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h_eq]; exact h_young (A ω) (B ω) (Cf ω)
  -- Integrability: SI increments squared
  have hΔSI_sq_int : ∀ i : Fin (n + 1),
      Integrable (fun ω => (ΔSI i ω) ^ 2) μ := by
    intro i; simp only [ΔSI]
    exact ItoProcessCore.si_increment_sq_integrable_core_ofRegularity
      X R _ _ (hsc_nn _) (hsc_mono _)
  -- Integrability: compensated Z² (from L⁴ domination)
  have hZ_sq_int : ∀ i : Fin (n + 1),
      Integrable (fun ω => ((ΔSI i ω) ^ 2 -
        ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume) ^ 2) μ := by
    intro i; simp only [ΔSI]
    exact ItoProcessCore.compensated_sq_sq_integrable_core_ofRegularity
      X R hMσ _ _ (hsc_nn _) (hsc_mono _)
  -- Strong measurability of ΔSI and ΔX
  have hΔSI_sm : ∀ i : Fin (n + 1), StronglyMeasurable (ΔSI i) := by
    intro i
    simp only [ΔSI]
    have hsm1 := stoch_integral_measurable_core X R (sc ((i : ℕ) + 1)) (hsc_nn _)
    have hsm0 := stoch_integral_measurable_core X R (sc (i : ℕ)) (hsc_nn _)
    exact hsm1.stronglyMeasurable.sub hsm0.stronglyMeasurable
  have hΔX_sm : ∀ i : Fin (n + 1), StronglyMeasurable (fun ω =>
      X.process (sc ((i : ℕ) + 1)) ω - X.process (sc (i : ℕ)) ω) := by
    intro i
    exact ((X.process_adapted _).mono (F.le_ambient _) le_rfl).stronglyMeasurable.sub
      ((X.process_adapted _).mono (F.le_ambient _) le_rfl).stronglyMeasurable
  -- Integrability of Cf²
  have hCf_int : Integrable (fun ω => (Cf ω) ^ 2) μ := by
    have hZ_prod_int : ∀ i j : Fin (n + 1),
        Integrable (fun ω =>
          ((ΔSI i ω) ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume) *
          ((ΔSI j ω) ^ 2 - ∫ s in Icc (sc (j : ℕ)) (sc ((j : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume)) μ := by
      intro i j
      have hZk_int : ∀ k : Fin (n + 1),
          Integrable (fun ω => (ΔSI k ω) ^ 2 -
            ∫ s in Icc (sc (k : ℕ)) (sc ((k : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume) μ := by
        intro k; simp only [ΔSI]
        exact ItoProcessCore.compensated_sq_integrable_core_ofRegularity
          X R _ _ (hsc_nn _) (hsc_mono _)
      apply ((hZ_sq_int i).add (hZ_sq_int j)).div_const 2 |>.mono
        ((hZk_int i).aestronglyMeasurable.mul (hZk_int j).aestronglyMeasurable)
      filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply]
      set zi := ΔSI i ω ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume
      set zj := ΔSI j ω ^ 2 - ∫ s in Icc (sc (j : ℕ)) (sc ((j : ℕ) + 1)),
          (X.diffusion s ω) ^ 2 ∂volume
      rw [abs_of_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
        (by norm_num : (0 : ℝ) ≤ 2))]
      have h1 : |zi * zj| = |zi| * |zj| := abs_mul zi zj
      have h2 : 2 * (|zi| * |zj|) ≤ zi ^ 2 + zj ^ 2 := by
        have h := two_mul_le_add_sq (|zi|) (|zj|)
        rw [sq_abs, sq_abs] at h; linarith
      linarith
    have heq : (fun ω => (Cf ω) ^ 2) = (fun ω =>
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          ((ΔSI i ω) ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume) *
          ((ΔSI j ω) ^ 2 - ∫ s in Icc (sc (j : ℕ)) (sc ((j : ℕ) + 1)),
              (X.diffusion s ω) ^ 2 ∂volume)) := by
      ext ω; simp only [Cf]; rw [sq, Fintype.sum_mul_sum]
    rw [heq]; exact integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => hZ_prod_int i j
  -- Pointwise bound on B²
  have hB_bound : ∀ ω, (B ω) ^ 2 ≤
      Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
      ∑ i : Fin (n + 1), (ΔSI i ω) ^ 2 := by
      intro ω
      have h1 : |B ω| ≤ Mμ * (T / ↑(n + 1)) * ∑ i, |ΔSI i ω| := by
        simp only [B]
        calc |∑ i, ΔD i ω * ΔSI i ω|
            ≤ ∑ i, |ΔD i ω * ΔSI i ω| := by
              rw [← Real.norm_eq_abs]; exact norm_sum_le _ _
          _ = ∑ i, |ΔD i ω| * |ΔSI i ω| := by
              congr 1; ext i; exact abs_mul _ _
          _ ≤ ∑ i, Mμ * (T / ↑(n + 1)) * |ΔSI i ω| :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (by
                simp only [ΔD]
                calc |∫ s in Icc _ _, X.drift s ω ∂volume| ≤ Mμ * (_ - _) :=
                    drift_increment_bound_core X hMμ _ _ (hsc_mono _) ω
                  _ ≤ Mμ * (T / ↑(n + 1)) := by
                    exact mul_le_mul_of_nonneg_left (hΔ_le _) (le_trans (abs_nonneg _) (hMμ 0 ω)))
                (abs_nonneg _)
          _ = Mμ * (T / ↑(n + 1)) * ∑ i, |ΔSI i ω| := by rw [← Finset.mul_sum]
      have h_cs : (∑ i : Fin (n + 1), |ΔSI i ω|) ^ 2 ≤
          ↑(n + 1) * ∑ i : Fin (n + 1), (ΔSI i ω) ^ 2 := by
        have h := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ
          (fun i : Fin (n + 1) => |ΔSI i ω|)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        calc _ ≤ ↑(n + 1) * ∑ i, |ΔSI i ω| ^ 2 := h
          _ = _ := by congr 1; exact Finset.sum_congr rfl fun i _ => sq_abs _
      calc (B ω) ^ 2 = |B ω| ^ 2 := (sq_abs _).symm
        _ ≤ (Mμ * (T / ↑(n + 1)) * ∑ i, |ΔSI i ω|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = (Mμ * (T / ↑(n + 1))) ^ 2 * (∑ i, |ΔSI i ω|) ^ 2 := by ring
        _ ≤ (Mμ * (T / ↑(n + 1))) ^ 2 * (↑(n + 1) * ∑ i, (ΔSI i ω) ^ 2) :=
            mul_le_mul_of_nonneg_left h_cs (sq_nonneg _)
        _ = _ := by ring
  -- B is a.e. measurable
  have hB_aesm : AEStronglyMeasurable B μ :=
    (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
      ((hΔX_sm i).sub (hΔSI_sm i)).mul (hΔSI_sm i)).aestronglyMeasurable.congr
    (by filter_upwards [h_decomp_sc] with ω hω
        simp only [Fintype.sum_apply, Pi.sub_apply, Pi.mul_apply, B]
        exact Finset.sum_congr rfl fun i _ => by
          congr 1; linarith [hω i])
  have hB_int : Integrable (fun ω => (B ω) ^ 2) μ :=
    Integrable.mono
      ((integrable_finset_sum _ fun i _ => hΔSI_sq_int i).const_mul
        (Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1)))
      (hB_aesm.pow 2)
      (by filter_upwards with ω
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (mul_nonneg (by positivity)
                (Finset.sum_nonneg fun i _ => sq_nonneg _))]
          exact hB_bound ω)
  -- Integrability of A²
  have hA_int : Integrable (fun ω => (A ω) ^ 2) μ := by
    have hA_bound : ∀ ω, A ω ≤ Mμ ^ 2 * T ^ 2 / ↑(n + 1) := by
      intro ω; simp only [A]
      calc ∑ i : Fin (n + 1), (ΔD i ω) ^ 2
          ≤ ∑ i : Fin (n + 1), Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              simp only [ΔD]
              have h := drift_increment_bound_core X hMμ (sc ↑i) (sc (↑i + 1)) (hsc_mono ↑i) ω
              calc _ ≤ |∫ s in Icc _ _, X.drift s ω ∂volume| ^ 2 := by rw [sq_abs]
                _ ≤ (Mμ * (sc (↑i + 1) - sc ↑i)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
                _ ≤ (Mμ * (T / ↑(n + 1))) ^ 2 := by
                    apply pow_le_pow_left₀ (mul_nonneg (le_trans (abs_nonneg _) (hMμ 0 ω))
                      (sub_nonneg.mpr (hsc_mono _)))
                    exact mul_le_mul_of_nonneg_left (hΔ_le _) (le_trans (abs_nonneg _) (hMμ 0 ω))
                _ = _ := by ring
        _ = ↑(n + 1) * (Mμ ^ 2 * (T / ↑(n + 1)) ^ 2) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        _ = Mμ ^ 2 * T ^ 2 / ↑(n + 1) := by field_simp
    have hA_aesm : AEStronglyMeasurable A μ :=
      (Finset.stronglyMeasurable_sum Finset.univ fun i _ =>
        ((hΔX_sm i).sub (hΔSI_sm i)).pow 2).aestronglyMeasurable.congr
      (by filter_upwards [h_decomp_sc] with ω hω
          simp only [Fintype.sum_apply, Pi.sub_apply, Pi.pow_apply, A]
          exact Finset.sum_congr rfl fun i _ => by
            congr 1; linarith [hω i])
    exact (integrable_const ((Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2)).mono (hA_aesm.pow 2)
      (by filter_upwards with ω
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => sq_nonneg _)
            (hA_bound ω) 2)
  -- Integrability of dominator
  have h_dom_int : Integrable (fun ω =>
      3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (Cf ω) ^ 2) μ :=
    ((hA_int.const_mul 3).add (hB_int.const_mul 12)).add (hCf_int.const_mul 3)
  -- Main calc
  calc ∫ ω, (∑ i : Fin (n + 1),
        (X.process (sc ((i : ℕ) + 1)) ω -
         X.process (sc (i : ℕ)) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2 ∂μ
    ≤ ∫ ω, (3 * (A ω) ^ 2 + 12 * (B ω) ^ 2 + 3 * (Cf ω) ^ 2) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) h_dom_int h_ae
    _ = 3 * ∫ ω, (A ω) ^ 2 ∂μ + 12 * ∫ ω, (B ω) ^ 2 ∂μ +
        3 * ∫ ω, (Cf ω) ^ 2 ∂μ := by
      have h1 := integral_add ((hA_int.const_mul 3).add (hB_int.const_mul 12))
        (hCf_int.const_mul 3)
      have h2 := integral_add (hA_int.const_mul 3) (hB_int.const_mul 12)
      simp only [integral_const_mul, Pi.add_apply] at h1 h2; linarith
    _ ≤ 3 * (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 +
        12 * (Mμ ^ 2 * Mσ ^ 2 * T ^ 3 / ↑(n + 1)) +
        3 * (8 * Mσ ^ 4 * T ^ 2 / ↑(n + 1)) := by
      gcongr
      · -- E[A²] ≤ (Mμ²T²/(n+1))²
        calc ∫ ω, (A ω) ^ 2 ∂μ
            ≤ ∫ _, (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
              (integrable_const _)
              (ae_of_all _ fun ω => pow_le_pow_left₀
                (Finset.sum_nonneg fun i _ => sq_nonneg _)
                (by simp only [A]
                    calc ∑ i : Fin (n + 1), (ΔD i ω) ^ 2
                        ≤ ∑ i : Fin (n + 1), Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 :=
                          Finset.sum_le_sum fun i _ => by
                            simp only [ΔD]
                            have h := drift_increment_bound_core X hMμ (sc ↑i) (sc (↑i + 1)) (hsc_mono ↑i) ω
                            calc _ ≤ |∫ s in Icc _ _, X.drift s ω ∂volume| ^ 2 := by rw [sq_abs]
                              _ ≤ (Mμ * (sc (↑i + 1) - sc ↑i)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
                              _ ≤ (Mμ * (T / ↑(n + 1))) ^ 2 := by
                                  apply pow_le_pow_left₀ (mul_nonneg (le_trans (abs_nonneg _) (hMμ 0 ω))
                                    (sub_nonneg.mpr (hsc_mono _)))
                                  exact mul_le_mul_of_nonneg_left (hΔ_le _)
                                    (le_trans (abs_nonneg _) (hMμ 0 ω))
                              _ = _ := by ring
                      _ = _ := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; field_simp) 2)
          _ = (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 := by
              simp [integral_const, Measure.real, measure_univ]
      · -- E[B²] ≤ Mμ²Mσ²T³/(n+1) via isometry
        calc ∫ ω, (B ω) ^ 2 ∂μ
            ≤ ∫ ω, (Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
              ∑ i, (ΔSI i ω) ^ 2) ∂μ :=
              integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
                ((integrable_finset_sum _ fun i _ => hΔSI_sq_int i).const_mul _)
                (ae_of_all _ hB_bound)
            _ = Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
                ∑ i, ∫ ω, (ΔSI i ω) ^ 2 ∂μ := by
              rw [integral_const_mul, integral_finset_sum _ fun i _ => hΔSI_sq_int i]
            _ ≤ Mμ ^ 2 * (T / ↑(n + 1)) ^ 2 * ↑(n + 1) *
                ∑ i : Fin (n + 1), Mσ ^ 2 * (T / ↑(n + 1)) := by
              gcongr with i
              simp only [ΔSI]
              rw [ItoProcessCore.stoch_integral_isometry_core_ofRegularity
                X R _ _ (hsc_nn _) (hsc_mono _)]
              calc ∫ ω, ∫ r in Icc _ _, (X.diffusion r ω) ^ 2 ∂volume ∂μ
                  ≤ ∫ ω, (Mσ ^ 2 * (T / ↑(n + 1))) ∂μ := by
                    apply integral_mono_of_nonneg
                    · exact ae_of_all _ fun ω =>
                        setIntegral_nonneg measurableSet_Icc fun r _ => sq_nonneg _
                    · exact integrable_const _
                    · exact ae_of_all _ fun ω => by
                        calc ∫ r in Icc _ _, (X.diffusion r ω) ^ 2 ∂volume
                            ≤ ∫ r in Icc _ _, Mσ ^ 2 ∂volume := by
                              apply integral_mono_of_nonneg
                              · exact ae_of_all _ fun _ => sq_nonneg _
                              · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
                              · exact ae_of_all _ fun r => by
                                  calc _ = |X.diffusion r ω| ^ 2 := (sq_abs _).symm
                                    _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ r ω) 2
                          _ ≤ Mσ ^ 2 * (T / ↑(n + 1)) := by
                              rw [setIntegral_const]
                              simp only [smul_eq_mul, Measure.real, Real.volume_Icc,
                                ENNReal.toReal_ofReal (sub_nonneg.mpr (hsc_mono _))]
                              rw [mul_comm]
                              exact mul_le_mul_of_nonneg_left (hΔ_le _) (sq_nonneg _)
                _ = Mσ ^ 2 * (T / ↑(n + 1)) := by
                    simp [integral_const, Measure.real, measure_univ]
            _ = Mμ ^ 2 * Mσ ^ 2 * T ^ 3 / ↑(n + 1) := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; field_simp
      · -- E[Cf²] ≤ 8Mσ⁴T²/(n+1) via Pythagorean + individual bound
        -- Set up Z functions
        set Z : Fin (n + 1) → Ω → ℝ := fun i ω =>
          (ΔSI i ω) ^ 2 - ∫ s in Icc (sc (i : ℕ)) (sc ((i : ℕ) + 1)),
            (X.diffusion s ω) ^ 2 ∂volume
        -- Integrability of products
        have hZZ_int : ∀ i j : Fin (n + 1), Integrable (fun ω => Z i ω * Z j ω) μ := by
          intro i j
          have hZk_int : ∀ k : Fin (n + 1), Integrable (Z k) μ := by
            intro k; simp only [Z, ΔSI]
            exact ItoProcessCore.compensated_sq_integrable_core_ofRegularity
              X R _ _ (hsc_nn _) (hsc_mono _)
          apply ((hZ_sq_int i).add (hZ_sq_int j)).div_const 2 |>.mono
            ((hZk_int i).aestronglyMeasurable.mul (hZk_int j).aestronglyMeasurable)
          filter_upwards with ω
          simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply]
          set zi := Z i ω
          set zj := Z j ω
          have h_am := two_mul_le_add_sq (|zi|) (|zj|)
          rw [sq_abs, sq_abs] at h_am
          rw [abs_of_nonneg (div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (by norm_num : (0 : ℝ) ≤ 2))]
          have h1 : |zi * zj| = |zi| * |zj| := abs_mul zi zj
          have h2 : 2 * (|zi| * |zj|) ≤ zi ^ 2 + zj ^ 2 := by
            have h := two_mul_le_add_sq (|zi|) (|zj|)
            rw [sq_abs, sq_abs] at h; linarith
          linarith
        -- Orthogonality
        have horth : ∀ i j : Fin (n + 1), i ≠ j → ∫ ω, Z i ω * Z j ω ∂μ = 0 := by
          intro i j hij
          rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
          · simp only [Z, ΔSI]
            exact ItoProcessCore.stoch_integral_squared_orthogonal_core_ofRegularity X R hMσ _ _ _ _
              (hsc_nn _) (hsc_mono _)
              (by exact_mod_cast capped_disjoint T hT.le u n i j h)
              (hsc_mono _)
          · rw [show (fun ω => Z i ω * Z j ω) = (fun ω => Z j ω * Z i ω) from by
                ext ω; ring]
            simp only [Z, ΔSI]
            exact ItoProcessCore.stoch_integral_squared_orthogonal_core_ofRegularity X R hMσ _ _ _ _
              (hsc_nn _) (hsc_mono _)
              (by exact_mod_cast capped_disjoint T hT.le u n j i h)
              (hsc_mono _)
        -- Pythagorean identity + individual bounds
        have hCf_eq : (fun ω => (Cf ω) ^ 2) = (fun ω => (∑ i, Z i ω) ^ 2) := by
          ext ω; simp only [Cf, Z]
        rw [hCf_eq, integral_sq_sum_orthogonal Z hZZ_int horth]
        calc ∑ i : Fin (n + 1), ∫ ω, (Z i ω) ^ 2 ∂μ
            ≤ ∑ i : Fin (n + 1), 8 * Mσ ^ 4 * (T / ↑(n + 1)) ^ 2 := by
              apply Finset.sum_le_sum; intro i _; simp only [Z, ΔSI]
              calc ∫ ω, _ ^ 2 ∂μ
                  ≤ 8 * Mσ ^ 4 * (sc ((i : ℕ) + 1) - sc (i : ℕ)) ^ 2 :=
                    si_compensated_sq_L2_single_core X R hMσ _ _ (hsc_nn _) (hsc_mono _)
                _ ≤ 8 * Mσ ^ 4 * (T / ↑(n + 1)) ^ 2 := by
                    gcongr
                    · exact sub_nonneg.mpr (hsc_mono _)
                    · exact hΔ_le _
          _ = 8 * Mσ ^ 4 * T ^ 2 / ↑(n + 1) := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; field_simp
    _ ≤ (3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 +
         24 * Mσ ^ 4 * T ^ 2) / ↑(n + 1) := by
      have hn1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_pos n
      have hN_le : (↑(n + 1) : ℝ) ≤ (↑(n + 1) : ℝ) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_right hn_pos.le hn1
      have h_sq_le : (Mμ ^ 2 * T ^ 2 / ↑(n + 1)) ^ 2 ≤ Mμ ^ 4 * T ^ 4 / ↑(n + 1) := by
        rw [div_pow, show (Mμ ^ 2 * T ^ 2) ^ 2 = Mμ ^ 4 * T ^ 4 from by ring]
        exact div_le_div_of_nonneg_left (by positivity) hn_pos hN_le
      have hrw : (3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 +
          24 * Mσ ^ 4 * T ^ 2) / ↑(n + 1) =
          3 * (Mμ ^ 4 * T ^ 4 / ↑(n + 1)) +
          12 * (Mμ ^ 2 * Mσ ^ 2 * T ^ 3 / ↑(n + 1)) +
          3 * (8 * Mσ ^ 4 * T ^ 2 / ↑(n + 1)) := by
        field_simp; ring
      rw [hrw]
      linarith [mul_le_mul_of_nonneg_left h_sq_le (by norm_num : (0 : ℝ) ≤ 3)]

/-- Core adapter for discrete quadratic variation convergence in L². -/
theorem ito_qv_L2_bound_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       X.quadraticVariation t ω) ^ 2 ∂μ ≤
    (3 * Mμ ^ 4 * t ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * t ^ 3 +
     24 * Mσ ^ 4 * t ^ 2) / ↑(n + 1) := by
  have h_cap := capped_ito_qv_L2_bound_core (X := X) C DR D FC hMμ hMσ t t ht ht.le le_rfl n
  have hrew :
      (fun ω =>
        (∑ i : Fin (n + 1),
          (X.process (min ((↑(i : ℕ) + 1) * t / ↑(n + 1)) t) ω -
           X.process (min (↑(i : ℕ) * t / ↑(n + 1)) t) ω) ^ 2 -
         X.quadraticVariation t ω) ^ 2) =
      (fun ω =>
        (∑ i : Fin (n + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         X.quadraticVariation t ω) ^ 2) := by
    ext ω
    have hsum :
        ∑ i : Fin (n + 1),
          (X.process (min ((↑(i : ℕ) + 1) * t / ↑(n + 1)) t) ω -
           X.process (min (↑(i : ℕ) * t / ↑(n + 1)) t) ω) ^ 2 =
        ∑ i : Fin (n + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have hsucc_le : ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ≤ t :=
        partition_time_le t ht.le n i
      have hcurr_le : (↑(i : ℕ) * t / ↑(n + 1)) ≤ t :=
        le_trans (partition_time_mono t ht.le n (i : ℕ)) hsucc_le
      rw [min_eq_left hsucc_le, min_eq_left hcurr_le]
    have hsub :
        (∑ i : Fin (n + 1),
          (X.process (min ((↑(i : ℕ) + 1) * t / ↑(n + 1)) t) ω -
           X.process (min (↑(i : ℕ) * t / ↑(n + 1)) t) ω) ^ 2 -
         X.quadraticVariation t ω) =
        (∑ i : Fin (n + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         X.quadraticVariation t ω) := by
      linarith [hsum]
    exact congrArg (fun z : ℝ => z ^ 2) hsub
  rw [hrew] at h_cap
  exact h_cap

theorem ito_process_discrete_qv_L2_convergence_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         X.quadraticVariation t ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  have R : ItoProcessRegularity X :=
    ItoProcessRegularity.ofSplit C DR D FC
  set Cst := 3 * Mμ ^ 4 * t ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * t ^ 3 + 24 * Mσ ^ 4 * t ^ 2
  apply squeeze_zero
  · intro n; exact integral_nonneg (fun ω => sq_nonneg _)
  · intro n
    exact ito_qv_L2_bound_core X
      R.toConstruction R.toDriftRegularity
      R.toDiffusionRegularity R.toFiltrationCompatibility
      hMμ hMσ t ht n
  · have h : (fun n : ℕ => Cst / (↑(n + 1) : ℝ)) =
        (fun n : ℕ => Cst * (1 / ((↑n : ℝ) + 1))) := by
      ext n; rw [Nat.cast_succ]; ring
    rw [h, show (0 : ℝ) = Cst * 0 from by ring]
    exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

/-- Core adapter for capped discrete quadratic variation convergence in L². -/
theorem capped_discrete_qv_L2_convergence_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
         X.quadraticVariation u ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  have R : ItoProcessRegularity X :=
    ItoProcessRegularity.ofSplit C DR D FC
  set Cst := 3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 + 24 * Mσ ^ 4 * T ^ 2
  apply squeeze_zero
  · intro n; exact integral_nonneg (fun ω => sq_nonneg _)
  · intro n
    exact capped_ito_qv_L2_bound_core X
      R.toConstruction R.toDriftRegularity
      R.toDiffusionRegularity R.toFiltrationCompatibility
      hMμ hMσ T u hT hu huT n
  · have h : (fun n : ℕ => Cst / (↑(n + 1) : ℝ)) =
        (fun n : ℕ => Cst * (1 / ((↑n : ℝ) + 1))) := by
      ext n; rw [Nat.cast_succ]; ring
    rw [h, show (0 : ℝ) = Cst * 0 from by ring]
    exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

/-- Regularity-first adapter for a.e. increment decomposition on partitions. -/
theorem ito_process_increment_decomp_ae_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
      X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
      X.process (↑(i : ℕ) * t / ↑(n + 1)) ω =
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) +
      (X.stoch_integral ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
       X.stoch_integral (↑(i : ℕ) * t / ↑(n + 1)) ω) := by
  simpa using
    (ito_process_increment_decomp_ae_core (X := X)
      (DR := R.toDriftRegularity)
      t ht n)

/-- Regularity-first adapter for drift increment bound. -/
lemma drift_increment_bound_core_ofRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    (s u : ℝ) (hsu : s ≤ u) (ω : Ω) :
    |∫ r in Icc s u, X.drift r ω ∂volume| ≤ Mμ * (u - s) := by
  simpa using
    (drift_increment_bound_core (X := X)
      hMμ s u hsu ω)

/-- Regularity-first adapter for deterministic bound on squared drift increments. -/
lemma drift_sq_sum_bound_core_ofRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (ω : Ω) :
    ∑ i : Fin (n + 1),
      (∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        X.drift s ω ∂volume) ^ 2 ≤
    Mμ ^ 2 * t ^ 2 / ↑(n + 1) := by
  simpa using
    (drift_sq_sum_bound_core (X := X)
      hMμ t ht n ω)

/-- Regularity-first adapter for partition splitting of quadratic variation. -/
lemma qv_partition_sum_core_ofRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (ω : Ω)
    (hf_int : IntegrableOn (fun s => (X.diffusion s ω) ^ 2) (Icc 0 t) volume) :
    X.quadraticVariation t ω =
    ∑ i : Fin (n + 1),
      ∫ s in Icc (↑(i : ℕ) * t / ↑(n + 1)) ((↑(i : ℕ) + 1) * t / ↑(n + 1)),
        (X.diffusion s ω) ^ 2 ∂volume := by
  simpa using
    (qv_partition_sum_core (X := X)
      t ht n ω hf_int)

/-- Regularity-first adapter for single compensated SI² increment L² bound. -/
lemma si_compensated_sq_L2_single_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s u : ℝ) (hs : 0 ≤ s) (hsu : s ≤ u) :
    ∫ ω,
      ((X.stoch_integral u ω - X.stoch_integral s ω) ^ 2 -
       ∫ r in Icc s u, (X.diffusion r ω) ^ 2 ∂volume) ^ 2 ∂μ ≤
    8 * Mσ ^ 4 * (u - s) ^ 2 := by
  simpa using
    (si_compensated_sq_L2_single_core (X := X)
      (R := R)
      hMσ s u hs hsu)

/-- Regularity-first adapter for capped discrete QV L² bound. -/
theorem capped_ito_qv_L2_bound_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2 ∂μ ≤
    (3 * Mμ ^ 4 * T ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * T ^ 3 +
     24 * Mσ ^ 4 * T ^ 2) / ↑(n + 1) := by
  simpa using
    (capped_ito_qv_L2_bound_core (X := X)
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      hMμ hMσ T u hT hu huT n)

/-- Regularity-first adapter for endpoint discrete QV L² bound. -/
theorem ito_qv_L2_bound_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∫ ω,
      (∑ i : Fin (n + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
       X.quadraticVariation t ω) ^ 2 ∂μ ≤
    (3 * Mμ ^ 4 * t ^ 4 + 12 * Mμ ^ 2 * Mσ ^ 2 * t ^ 3 +
     24 * Mσ ^ 4 * t ^ 2) / ↑(n + 1) := by
  simpa using
    (ito_qv_L2_bound_core (X := X)
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      hMμ hMσ t ht n)

/-- Regularity-first adapter for discrete QV convergence in L². -/
theorem ito_process_discrete_qv_L2_convergence_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (X.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
           X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
         X.quadraticVariation t ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  simpa using
    (ito_process_discrete_qv_L2_convergence_core (X := X)
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      hMμ hMσ t ht)

/-- Regularity-first adapter for capped discrete QV convergence in L². -/
theorem capped_discrete_qv_L2_convergence_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T u : ℝ) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
         X.quadraticVariation u ω) ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  simpa using
    (capped_discrete_qv_L2_convergence_core (X := X)
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      hMμ hMσ T u hT hu huT)

end SPDE
