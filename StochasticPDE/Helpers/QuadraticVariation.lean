/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.StochasticIntegration
import StochasticPDE.Helpers.ItoFormulaInfrastructure
import StochasticPDE.Helpers.QuarticBound
import StochasticPDE.Helpers.TaylorRemainder
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Quadratic Variation Infrastructure for Itô Processes

This file provides the quadratic variation definition and convergence results
needed for the C² Itô formula proof.

## Main definitions

* `ItoProcess.quadraticVariation` - The quadratic variation [X]_t = ∫₀ᵗ σ(s,ω)² ds.

## Main results

* `ito_process_discrete_qv_L2_convergence` - ∑(ΔXᵢ)² → [X]_t in L².
* `ito_process_qv_sq_integrable` - [X]_t² is integrable when σ is bounded.
* `fatou_squeeze_tendsto_zero` - Fatou squeeze lemma for L¹ convergence to 0.
* `max_partition_increment_ae_zero` - max|ΔXᵢ| → 0 a.s. from path continuity.

## Proof strategy for discrete QV convergence

Decompose ΔXᵢ = drift_i + SI_i where drift_i = ∫_{tᵢ}^{tᵢ₊₁} μ ds and
SI_i = SI(tᵢ₊₁) - SI(tᵢ). Then:
  ∑(ΔXᵢ)² = ∑ drift_i² + 2∑ drift_i·SI_i + ∑ SI_i²

- Term 1: ∑ drift_i² = O(t²/n) → 0 (from |drift_i| ≤ Mμ·Δt)
- Term 2: cross terms → 0 by Cauchy-Schwarz
- Term 3: ∑ SI_i² → ∫₀ᵗ σ² ds via BM QV convergence + weighted QV
-/

open MeasureTheory Filter Finset

namespace SPDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Quadratic variation definition -/

/-- Quadratic variation of an Itô process: [X]_t(ω) = ∫₀ᵗ σ(s,ω)² ds.

    For an Itô process dX_t = μ_t dt + σ_t dW_t, the quadratic variation is
    the total accumulated variance from the diffusion term. The drift does NOT
    contribute to the quadratic variation (its contribution is o(dt)). -/
noncomputable def ItoProcess.quadraticVariation {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in Set.Icc 0 t, (X.diffusion s ω) ^ 2 ∂MeasureTheory.volume

/-- QV is nonneg (integral of nonneg function). -/
theorem ItoProcess.quadraticVariation_nonneg {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (ω : Ω) :
    0 ≤ X.quadraticVariation t ω :=
  MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun _s _ => sq_nonneg _)

/-- QV is bounded when diffusion is bounded: [X]_t ≤ Mσ² · t. -/
theorem ItoProcess.quadraticVariation_le {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) :
    X.quadraticVariation t ω ≤ Mσ ^ 2 * t := by
  unfold ItoProcess.quadraticVariation
  -- Pointwise bound: σ(s,ω)² ≤ Mσ² from |σ| ≤ Mσ
  have h_pw : ∀ s, (X.diffusion s ω) ^ 2 ≤ Mσ ^ 2 := by
    intro s; exact sq_le_sq' (neg_le_of_abs_le (hMσ s ω)) (abs_le.mp (hMσ s ω)).2
  by_cases h_int : IntegrableOn (fun s => (X.diffusion s ω) ^ 2) (Set.Icc 0 t) volume
  · -- Integrable case: use setIntegral_mono_on
    have h_fin : IsFiniteMeasure (volume.restrict (Set.Icc 0 t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have h_const_int : IntegrableOn (fun _ : ℝ => Mσ ^ 2) (Set.Icc 0 t) volume :=
      integrable_const _
    calc ∫ s in Set.Icc 0 t, (X.diffusion s ω) ^ 2 ∂volume
        ≤ ∫ s in Set.Icc 0 t, Mσ ^ 2 ∂volume :=
          setIntegral_mono_on h_int h_const_int measurableSet_Icc (fun s _ => h_pw s)
      _ = Mσ ^ 2 * t := by
          rw [setIntegral_const]
          simp only [Measure.real, Real.volume_Icc, sub_zero,
            ENNReal.toReal_ofReal ht, smul_eq_mul]
          ring
  · -- Non-integrable case: integral = 0 by Bochner convention
    rw [integral_undef h_int]
    exact mul_nonneg (sq_nonneg Mσ) ht

/-- QV squared is integrable when diffusion is bounded.
    Uses: QV ≤ Mσ²t (bounded on probability space → integrable).
    Needs measurability of QV (from measurability of set integral of σ²). -/
theorem ItoProcess.quadraticVariation_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) {Mσ : ℝ} (_hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (hdiff_jm : Measurable (Function.uncurry X.diffusion))
    (t : ℝ) (_ht : 0 ≤ t) :
    Integrable (fun ω => (X.quadraticVariation t ω) ^ 2) μ := by
  -- QV(t,ω) ≤ Mσ²·t for all ω (from quadraticVariation_le), so QV² ≤ (Mσ²·t)²
  -- Bounded functions on probability spaces are integrable (if AEStronglyMeasurable)
  have h_bdd : ∀ ω, ‖(X.quadraticVariation t ω) ^ 2‖ ≤ (Mσ ^ 2 * t) ^ 2 := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [X.quadraticVariation_nonneg t ω,
      X.quadraticVariation_le _hMσ t _ht ω])
      (X.quadraticVariation_le _hMσ t _ht ω)
  -- AEStronglyMeasurable: QV(t,ω) = ∫₀ᵗ σ²(s,ω)ds is strongly measurable via joint measurability
  have h_asm : AEStronglyMeasurable (fun ω => (X.quadraticVariation t ω) ^ 2) μ := by
    -- (s,ω) ↦ σ(s,ω)² is jointly strongly measurable
    have h_sm_sq : StronglyMeasurable (Function.uncurry (fun s (ω : Ω) =>
        (X.diffusion s ω) ^ 2)) :=
      (hdiff_jm.pow_const 2).stronglyMeasurable
    -- ω ↦ ∫₀ᵗ σ²(s,ω)ds is strongly measurable via Fubini
    have h_sm : StronglyMeasurable (fun ω => ∫ s in Set.Icc 0 t,
        (X.diffusion s ω) ^ 2 ∂MeasureTheory.volume) :=
      StronglyMeasurable.integral_prod_left
        (μ := MeasureTheory.volume.restrict (Set.Icc 0 t)) h_sm_sq
    exact (h_sm.measurable.pow_const 2).aestronglyMeasurable
  exact (integrable_const ((Mσ ^ 2 * t) ^ 2)).mono' h_asm (ae_of_all _ h_bdd)

/-! ## Discrete QV L² convergence

The theorem `ito_process_discrete_qv_L2_convergence` is proved in
`Helpers/QVConvergence.lean` to avoid a circular import. -/

/-! ## Max partition increment -/

/-- For a.e. ω (where path is continuous), every partition increment → 0.

    This uses: continuous function on compact [0,t] is uniformly continuous,
    so |X(t_{i+1},ω) - X(t_i,ω)| → 0 as mesh → 0.

    We prove the pointwise version: for each i, the increment → 0. -/
theorem partition_increment_ae_zero {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (t : ℝ) (ht : 0 < t) :
    ∀ᵐ ω ∂μ, ∀ (i_fn : ∀ n, Fin (n + 1)),
      Filter.Tendsto (fun n =>
        |X.process ((↑(i_fn n : ℕ) + 1) * t / ↑(n + 1)) ω -
         X.process (↑(i_fn n : ℕ) * t / ↑(n + 1)) ω|)
      atTop (nhds 0) := by
  filter_upwards [X.process_continuous] with ω hω_cont
  intro i_fn
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- X(·, ω) is uniformly continuous on compact [0, t]
  have huc : UniformContinuousOn (fun s => X.process s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hω_cont.continuousOn.mono
      (fun s hs => hs))
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N, fun n hn => ?_⟩
  set i := i_fn n
  rw [Real.dist_eq, sub_zero]
  -- |ΔXᵢ| = dist(X(tᵢ₊₁,ω), X(tᵢ,ω)) < ε, from uniform continuity + mesh < δ
  have h_dist := hδ
    (↑(i : ℕ) * t / ↑(n + 1)) ?_ ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ?_ ?_
  rw [abs_abs]
  rwa [Real.dist_eq, abs_sub_comm] at h_dist
  -- tᵢ ∈ [0, t]
  · have hi_lt : (i : ℕ) < n + 1 := i.isLt
    constructor
    · positivity
    · have hn1_pos : (0 : ℝ) < ↑(n + 1) := by positivity
      rw [div_le_iff₀ hn1_pos]
      have hi_le : (↑(i : ℕ) : ℝ) ≤ ↑n := by exact_mod_cast Nat.lt_succ_iff.mp hi_lt
      have hn_le : (↑n : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.le_succ n
      linarith [mul_le_mul_of_nonneg_right (hi_le.trans hn_le) (le_of_lt ht)]
  -- tᵢ₊₁ ∈ [0, t]
  · have hi_lt : (i : ℕ) < n + 1 := i.isLt
    constructor
    · positivity
    · have hn1_pos : (0 : ℝ) < ↑(n + 1) := by positivity
      rw [div_le_iff₀ hn1_pos]
      have hi1_le : (↑(i : ℕ) : ℝ) + 1 ≤ ↑(n + 1) := by exact_mod_cast hi_lt
      linarith [mul_le_mul_of_nonneg_right hi1_le (le_of_lt ht)]
  -- dist(tᵢ, tᵢ₊₁) = t/(n+1) < δ
  · rw [Real.dist_eq, show ↑(i : ℕ) * t / ↑(n + 1) - (↑(i : ℕ) + 1) * t / ↑(n + 1) =
      -(t / ↑(n + 1)) from by ring]
    rw [abs_neg, abs_of_nonneg (div_nonneg (le_of_lt ht) (by positivity))]
    have hn1_pos : (0 : ℝ) < ↑(n + 1) := by positivity
    rw [div_lt_iff₀ hn1_pos]
    have hN_le_n : (↑N : ℝ) ≤ ↑n := Nat.cast_le.mpr hn
    have hn_le_n1 : (↑n : ℝ) ≤ ↑(n + 1) := Nat.cast_le.mpr (Nat.le_succ n)
    have h1 : t < ↑N * δ := by
      calc t = (t / δ) * δ := (div_mul_cancel₀ t (ne_of_gt hδ_pos)).symm
        _ < ↑N * δ := by nlinarith
    linarith [mul_le_mul_of_nonneg_right hN_le_n (le_of_lt hδ_pos),
              mul_le_mul_of_nonneg_right hn_le_n1 (le_of_lt hδ_pos)]

/-! ## Fatou squeeze lemma -/

/-- **Fatou squeeze lemma**: If 0 ≤ fₙ ≤ gₙ, fₙ → 0 a.e., gₙ → G a.e.,
    and ∫gₙ → ∫G, then ∫fₙ → 0.

    **Proof**: Apply Fatou's lemma to hₙ := gₙ - fₙ ≥ 0.
    Since hₙ → G a.e.: ∫G = ∫ liminf hₙ ≤ liminf ∫hₙ (Fatou)
                       = liminf(∫gₙ - ∫fₙ) = ∫G - limsup ∫fₙ.
    Hence limsup ∫fₙ ≤ 0. Combined with ∫fₙ ≥ 0: ∫fₙ → 0. -/
theorem fatou_squeeze_tendsto_zero [IsProbabilityMeasure μ]
    {f g : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hf_nn : ∀ n, ∀ ω, 0 ≤ f n ω)
    (hfg : ∀ n, ∀ ω, f n ω ≤ g n ω)
    (hf_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => f n ω) atTop (nhds 0))
    (hg_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => g n ω) atTop (nhds (G ω)))
    (hf_int : ∀ n, Integrable (f n) μ) (hg_int : ∀ n, Integrable (g n) μ)
    (hG_int : Integrable G μ)
    (hg_tend : Filter.Tendsto (fun n => ∫ ω, g n ω ∂μ)
      atTop (nhds (∫ ω, G ω ∂μ))) :
    Filter.Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (nhds 0) := by
  -- Proof: squeeze between 0 and ∫gₙ - ∫G + ε for large n, using Fatou on gₙ - fₙ.
  -- Equivalently: 0 ≤ ∫fₙ ≤ ∫gₙ - ∫(gₙ - fₙ), and Fatou gives ∫G ≤ liminf ∫(gₙ - fₙ).

  -- Lower bound
  have hf_int_nn : ∀ n, 0 ≤ ∫ ω, f n ω ∂μ :=
    fun n => integral_nonneg (hf_nn n)
  -- Upper bound: ∫fₙ ≤ ∫gₙ
  have hf_le_g : ∀ n, ∫ ω, f n ω ∂μ ≤ ∫ ω, g n ω ∂μ :=
    fun n => integral_mono (hf_int n) (hg_int n) (fun ω => hfg n ω)
  -- Define hₙ = gₙ - fₙ ≥ 0
  set h : ℕ → Ω → ℝ := fun n ω => g n ω - f n ω with hh_def
  -- hₙ → G a.e. (since gₙ → G and fₙ → 0)
  have hh_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => h n ω) atTop (nhds (G ω)) := by
    filter_upwards [hg_ae, hf_ae] with ω hg_ω hf_ω
    have : Filter.Tendsto (fun n => g n ω - f n ω) atTop (nhds (G ω - 0)) :=
      hg_ω.sub hf_ω
    rwa [sub_zero] at this
  -- hₙ ≥ 0
  have hh_nn : ∀ n, ∀ ω, 0 ≤ h n ω :=
    fun n ω => sub_nonneg.mpr (hfg n ω)
  -- hₙ integrable
  have hh_int : ∀ n, Integrable (h n) μ :=
    fun n => (hg_int n).sub (hf_int n)
  -- ∫hₙ = ∫gₙ - ∫fₙ
  have hh_int_eq : ∀ n, ∫ ω, h n ω ∂μ = ∫ ω, g n ω ∂μ - ∫ ω, f n ω ∂μ :=
    fun n => integral_sub (hg_int n) (hf_int n)
  -- Key: ∫fₙ = ∫gₙ - ∫hₙ
  have hf_eq : ∀ n, ∫ ω, f n ω ∂μ = ∫ ω, g n ω ∂μ - ∫ ω, h n ω ∂μ := by
    intro n; linarith [hh_int_eq n]
  -- ∫hₙ ≤ ∫gₙ (since fₙ ≥ 0, so hₙ = gₙ - fₙ ≤ gₙ)
  have hh_le_g_int : ∀ n, ∫ ω, h n ω ∂μ ≤ ∫ ω, g n ω ∂μ :=
    fun n => by linarith [hh_int_eq n, hf_int_nn n]
  -- G ≥ 0 a.e. (limit of nonneg sequence hₙ)
  have hG_nn : 0 ≤ᵐ[μ] G := by
    filter_upwards [hh_ae] with ω hω
    exact ge_of_tendsto' hω (fun n => hh_nn n ω)
  -- Rewrite: ∫fₙ = ∫gₙ - ∫hₙ
  rw [show (fun n => ∫ ω, f n ω ∂μ) = fun n => ∫ ω, g n ω ∂μ - ∫ ω, h n ω ∂μ
    from funext hf_eq,
    show (0 : ℝ) = ∫ ω, G ω ∂μ - ∫ ω, G ω ∂μ from (sub_self _).symm]
  apply Filter.Tendsto.sub hg_tend
  -- Goal: Tendsto (fun n => ∫ ω, h n ω ∂μ) atTop (nhds (∫ ω, G ω ∂μ))
  -- Prove via ENNReal: Fatou gives lower bound, monotonicity gives upper bound.
  -- Step A: Fatou in ENNReal — ofReal(∫G) ≤ liminf ofReal(∫hₙ)
  have h_fatou : ENNReal.ofReal (∫ ω, G ω ∂μ) ≤
      Filter.liminf (fun n => ENNReal.ofReal (∫ ω, h n ω ∂μ)) atTop := by
    rw [ofReal_integral_eq_lintegral_ofReal hG_int hG_nn]
    simp_rw [fun n => ofReal_integral_eq_lintegral_ofReal (hh_int n) (ae_of_all _ (hh_nn n))]
    have h_liminf_ae : ∀ᵐ ω ∂μ, Filter.liminf (fun n => ENNReal.ofReal (h n ω)) atTop =
        ENNReal.ofReal (G ω) := by
      filter_upwards [hh_ae] with ω hω
      exact ((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq
    calc ∫⁻ ω, ENNReal.ofReal (G ω) ∂μ
        = ∫⁻ ω, Filter.liminf (fun n => ENNReal.ofReal (h n ω)) atTop ∂μ :=
          lintegral_congr_ae (h_liminf_ae.mono fun ω hω => hω.symm)
      _ ≤ Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (h n ω) ∂μ) atTop :=
          lintegral_liminf_le' fun n =>
            ENNReal.continuous_ofReal.measurable.comp_aemeasurable
              (hh_int n).aestronglyMeasurable.aemeasurable
  -- Step B: limsup ofReal(∫hₙ) ≤ ofReal(∫G)
  have h_limsup : Filter.limsup (fun n => ENNReal.ofReal (∫ ω, h n ω ∂μ)) atTop ≤
      ENNReal.ofReal (∫ ω, G ω ∂μ) :=
    calc Filter.limsup (fun n => ENNReal.ofReal (∫ ω, h n ω ∂μ)) atTop
        ≤ Filter.limsup (fun n => ENNReal.ofReal (∫ ω, g n ω ∂μ)) atTop :=
          Filter.limsup_le_limsup (Filter.Eventually.of_forall fun n =>
            ENNReal.ofReal_le_ofReal (hh_le_g_int n))
      _ = ENNReal.ofReal (∫ ω, G ω ∂μ) :=
          ((ENNReal.continuous_ofReal.tendsto _).comp hg_tend).limsup_eq
  -- Step C: ofReal(∫hₙ) → ofReal(∫G) in ENNReal (liminf/limsup squeeze)
  have h_ennreal_tend := tendsto_of_le_liminf_of_limsup_le h_fatou h_limsup
  -- Step D: Convert back to ℝ via toReal
  have h_toReal := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h_ennreal_tend
  simp only [Function.comp_def] at h_toReal
  rwa [show (fun n => (ENNReal.ofReal (∫ ω, h n ω ∂μ)).toReal) =
      fun n => ∫ ω, h n ω ∂μ from
      funext fun n => ENNReal.toReal_ofReal (integral_nonneg (hh_nn n)),
    show (ENNReal.ofReal (∫ ω, G ω ∂μ)).toReal = ∫ ω, G ω ∂μ from
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hG_nn)] at h_toReal

/-- A.e. version of `fatou_squeeze_tendsto_zero`: domination need only hold a.e.
    Uses the min trick: `min(f, g)` satisfies pointwise domination, equals `f` a.e. -/
theorem fatou_squeeze_tendsto_zero_ae [IsProbabilityMeasure μ]
    {f g : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hf_nn : ∀ n, ∀ ω, 0 ≤ f n ω)
    (hg_nn : ∀ n, ∀ ω, 0 ≤ g n ω)
    (hfg : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ g n ω)
    (hf_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => f n ω) atTop (nhds 0))
    (hg_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => g n ω) atTop (nhds (G ω)))
    (hf_int : ∀ n, Integrable (f n) μ) (hg_int : ∀ n, Integrable (g n) μ)
    (hG_int : Integrable G μ)
    (hg_tend : Filter.Tendsto (fun n => ∫ ω, g n ω ∂μ)
      atTop (nhds (∫ ω, G ω ∂μ))) :
    Filter.Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (nhds 0) := by
  -- Define f' = min(f, g), which equals f a.e. but satisfies pointwise domination
  set f' : ℕ → Ω → ℝ := fun n ω => min (f n ω) (g n ω)
  -- f' = f a.e. for each n
  have hf'_eq : ∀ n, (fun ω => f' n ω) =ᵐ[μ] f n := by
    intro n; filter_upwards [hfg] with ω hω; exact min_eq_left (hω n)
  -- f' satisfies pointwise hypotheses of fatou_squeeze_tendsto_zero
  have hf'_nn : ∀ n ω, 0 ≤ f' n ω := fun n ω => le_min (hf_nn n ω) (hg_nn n ω)
  have hf'g : ∀ n ω, f' n ω ≤ g n ω := fun n ω => min_le_right _ _
  have hf'_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => f' n ω) atTop (nhds 0) := by
    filter_upwards [hfg, hf_ae] with ω hω hf_ω
    have heq : ∀ n, f' n ω = f n ω := fun n => min_eq_left (hω n)
    simp_rw [heq]; exact hf_ω
  have hf'_int : ∀ n, Integrable (f' n) μ := by
    intro n
    -- 0 ≤ f' ≤ g and g integrable → f' integrable
    -- f' = min(f, g) is measurable since f, g are measurable
    have : ∀ ω, ‖f' n ω‖ ≤ g n ω := fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf'_nn n ω)]
      exact min_le_right _ _
    exact Integrable.mono' (hg_int n)
      ((hf_int n).aestronglyMeasurable.inf (hg_int n).aestronglyMeasurable)
      (ae_of_all _ this)
  -- Apply pointwise version
  have h := fatou_squeeze_tendsto_zero hf'_nn hf'g hf'_ae hg_ae hf'_int hg_int hG_int hg_tend
  -- Transfer: ∫ f' = ∫ f since f' = f a.e.
  exact h.congr (fun n => integral_congr_ae (hf'_eq n))

/-- Measure-convergence version of `fatou_squeeze_tendsto_zero_ae`:
    Instead of requiring `f → 0` a.e., it suffices that `f → 0` in measure.
    The conclusion `∫ f_n → 0` still follows by subsequence extraction
    and the a.e. version. -/
theorem fatou_squeeze_tendsto_zero_measure [IsProbabilityMeasure μ]
    {f g : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hf_nn : ∀ n, ∀ ω, 0 ≤ f n ω)
    (hg_nn : ∀ n, ∀ ω, 0 ≤ g n ω)
    (hfg : ∀ᵐ ω ∂μ, ∀ n, f n ω ≤ g n ω)
    (hf_meas : TendstoInMeasure μ f atTop (fun _ => (0 : ℝ)))
    (hg_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => g n ω) atTop (nhds (G ω)))
    (hf_int : ∀ n, Integrable (f n) μ) (hg_int : ∀ n, Integrable (g n) μ)
    (hG_int : Integrable G μ)
    (hg_tend : Filter.Tendsto (fun n => ∫ ω, g n ω ∂μ)
      atTop (nhds (∫ ω, G ω ∂μ))) :
    Filter.Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (nhds 0) := by
  -- Use the subsequence characterization: every subsequence has a further
  -- subsequence along which ∫f → 0.
  apply tendsto_of_subseq_tendsto
  intro ns hns
  -- TendstoInMeasure along ns
  have h_tim_ns : TendstoInMeasure μ (fun k => f (ns k)) atTop
      (fun _ => (0 : ℝ)) := by
    intro ε hε; exact (hf_meas ε hε).comp hns
  -- Extract a.e.-convergent sub-subsequence from measure convergence
  obtain ⟨ms, hms, hms_ae⟩ := h_tim_ns.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  -- Apply fatou_squeeze_tendsto_zero_ae along ns ∘ ms
  exact fatou_squeeze_tendsto_zero_ae
    (fun k ω => hf_nn (ns (ms k)) ω)
    (fun k ω => hg_nn (ns (ms k)) ω)
    (hfg.mono fun ω hω => fun k => hω (ns (ms k)))
    hms_ae
    (hg_ae.mono fun ω hω => hω.comp (hns.comp hms.tendsto_atTop))
    (fun k => hf_int (ns (ms k)))
    (fun k => hg_int (ns (ms k)))
    hG_int
    (hg_tend.comp (hns.comp hms.tendsto_atTop))

/-! ## L² to a.e. extraction -/

/-- L² convergence implies existence of an a.e.-convergent subsequence.
    Proof: L² → 0 implies TendstoInMeasure via Chebyshev, then
    `TendstoInMeasure.exists_seq_tendsto_ae` extracts the a.e. subsequence. -/
theorem L2_to_ae_subseq [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hL2 : Filter.Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂μ) atTop (nhds 0))
    (hint : ∀ n, Integrable (fun ω => (f n ω - g ω) ^ 2) μ)
    (hf_asm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg_asm : AEStronglyMeasurable g μ) :
    ∃ (ms : ℕ → ℕ), StrictMono ms ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun k => f (ms k) ω) atTop (nhds (g ω)) := by
  -- Step 1: Show TendstoInMeasure via Chebyshev inequality
  have h_tim : TendstoInMeasure μ f atTop g := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hε_sq_pos : (0 : ℝ) < ε ^ 2 := by positivity
    have hL2_int := hint
    -- Convert Bochner integral to lintegral for Chebyshev
    have h_lint_eq : ∀ n, ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ =
        ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ) :=
      fun n => (ofReal_integral_eq_lintegral_ofReal (hint n)
        (ae_of_all _ fun ω => sq_nonneg _)).symm
    have h_tend_lint : Filter.Tendsto
        (fun n => ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ)
        atTop (nhds 0) := by
      simp_rw [h_lint_eq]
      have : Filter.Tendsto (fun n => ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ))
          atTop (nhds (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp hL2
      rwa [ENNReal.ofReal_zero] at this
    have hε2_pos : ENNReal.ofReal (ε ^ 2) ≠ 0 := by positivity
    have hε2_top : ENNReal.ofReal (ε ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_div_tend : Filter.Tendsto
        (fun n => (∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ) /
          ENNReal.ofReal (ε ^ 2)) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.div_const h_tend_lint (Or.inr hε2_pos)
      rwa [ENNReal.zero_div] at h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_div_tend
    · intro n; exact zero_le _
    · intro n
      have h_subset : {ω | (ε : ℝ) ≤ ‖f n ω - g ω‖} ⊆
          {ω | ε ^ 2 ≤ (f n ω - g ω) ^ 2} := by
        intro ω (hω : ε ≤ ‖f n ω - g ω‖)
        show ε ^ 2 ≤ (f n ω - g ω) ^ 2
        rw [Real.norm_eq_abs] at hω
        nlinarith [abs_nonneg (f n ω - g ω), sq_abs (f n ω - g ω)]
      have h_aem : AEMeasurable (fun ω => ENNReal.ofReal ((f n ω - g ω) ^ 2)) μ :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((continuous_pow 2).measurable.comp_aemeasurable
            ((hf_asm n).sub hg_asm).aemeasurable)
      have h_cheb := mul_meas_ge_le_lintegral₀ h_aem (ENNReal.ofReal (ε ^ 2))
      have h_set_eq : {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal ((f n ω - g ω) ^ 2)} =
          {ω | ε ^ 2 ≤ (f n ω - g ω) ^ 2} := by
        ext ω; simp only [Set.mem_setOf_eq]
        exact ENNReal.ofReal_le_ofReal_iff (by positivity)
      rw [h_set_eq] at h_cheb
      calc μ {ω | (ε : ℝ) ≤ ‖f n ω - g ω‖}
          ≤ μ {ω | ε ^ 2 ≤ (f n ω - g ω) ^ 2} := measure_mono h_subset
        _ ≤ (∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ) / ENNReal.ofReal (ε ^ 2) :=
            ENNReal.le_div_iff_mul_le (Or.inl hε2_pos) (Or.inl hε2_top) |>.mpr <| by
              rw [mul_comm]; exact h_cheb
  -- Step 2: Extract a.e.-convergent subsequence
  exact h_tim.exists_seq_tendsto_ae

/-! ## Taylor remainder a.e. convergence -/

/-- Along an a.e.-convergent subsequence for QV, the Taylor remainders
    converge to 0 a.e.

    **Key argument**: For a.e. ω where path is continuous:
    - max|ΔXᵢ(ω)| → 0 (from uniform continuity on compact interval)
    - f''_t is uniformly continuous on the compact range of X(·,ω)
    - By integral form of C² Taylor remainder:
      |Rᵢ| ≤ ω_{f''}(|ΔXᵢ|) · (ΔXᵢ)²/2
    - Hence |∑ Rᵢ| ≤ ω_{f''}(max|ΔXⱼ|)/2 · ∑(ΔXᵢ)²
    - Since ∑(ΔXᵢ)² → [X]_t and ω_{f''}(max|ΔXⱼ|) → 0:
      (∑ Rᵢ)² → 0 · [X]_t² = 0 a.s. -/
theorem taylor_remainders_ae_tendsto_zero {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    {Mf'' : ℝ} (_hMf'' : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mf'')
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (t : ℝ) (_ht : 0 < t)
    (ns : ℕ → ℕ) (_hns : Filter.Tendsto ns Filter.atTop Filter.atTop)
    (_h_qv_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k =>
      ∑ i : Fin (ns k + 1),
        (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
         X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) ^ 2)
      atTop (nhds (X.quadraticVariation t ω))) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun k =>
      (∑ i : Fin (ns k + 1),
        (f (↑(i : ℕ) * t / ↑(ns k + 1))
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(ns k + 1))
           (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(ns k + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) -
         (1 : ℝ) / 2 *
           deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(ns k + 1)) x))
             (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) ^ 2)) ^ 2)
      atTop (nhds 0) := by
  filter_upwards [X.process_continuous, _h_qv_ae] with ω hω_cont hω_qv
  -- Step A: Reduce (∑ Rᵢ)² → 0 to ∑ Rᵢ → 0
  suffices hsuff : Filter.Tendsto (fun k =>
      ∑ i : Fin (ns k + 1),
        (f (↑(i : ℕ) * t / ↑(ns k + 1))
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω) -
         f (↑(i : ℕ) * t / ↑(ns k + 1))
           (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑(ns k + 1)) x)
           (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) -
         (1 : ℝ) / 2 *
           deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(ns k + 1)) x))
             (X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
            X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) ^ 2))
      atTop (nhds 0) by
    have h2 := hsuff.pow 2
    simp only [zero_pow (by norm_num : 2 ≠ 0)] at h2
    exact h2
  -- Step B: ∑ Rᵢ → 0 via Metric.tendsto_atTop (ε-δ argument)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Path continuous on [0,t] ⟹ uniformly continuous
  have hXω_uc : UniformContinuousOn (fun s => X.process s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hω_cont.continuousOn
  -- Path continuous on [0,t]
  have hXω_cont_on : ContinuousOn (fun s => X.process s ω) (Set.Icc 0 t) :=
    hω_cont.continuousOn
  -- Path range bounded
  have hXω_bdd : ∃ R : ℝ, 0 < R ∧ ∀ s ∈ Set.Icc (0 : ℝ) t, |X.process s ω| ≤ R := by
    have himg := isCompact_Icc.image_of_continuousOn hXω_cont_on
    obtain ⟨R₀, hR₀⟩ := himg.isBounded.subset_closedBall 0
    refine ⟨max R₀ 1, by positivity, fun s hs => ?_⟩
    have := hR₀ ⟨s, hs, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact (Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _)
  obtain ⟨R, hR_pos, hR⟩ := hXω_bdd
  -- QV convergence ⟹ ∑(ΔXᵢ)² eventually bounded
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hω_qv) 1 one_pos
  set QV_ω := X.quadraticVariation t ω with hQV_def
  have hQV_nn := X.quadraticVariation_nonneg t ω
  have hS_bdd : ∀ k ≥ N₁, ∑ i : Fin (ns k + 1),
      (X.process ((↑(i : ℕ) + 1) * t / ↑(ns k + 1)) ω -
       X.process (↑(i : ℕ) * t / ↑(ns k + 1)) ω) ^ 2 ≤ QV_ω + 1 := by
    intro k hk
    have h := hN₁ k hk
    rw [Real.dist_eq] at h
    have hab := abs_lt.mp h
    linarith
  -- f'' uniformly continuous on compact [0,t] × closedBall 0 (R+1)
  set K := Set.Icc (0 : ℝ) t ×ˢ Metric.closedBall (0 : ℝ) (R + 1) with hK_def
  have hK_compact : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 (R + 1))
  have hf''_uc : UniformContinuousOn
      (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2) K :=
    hK_compact.uniformContinuousOn_of_continuous hf''_cont.continuousOn
  -- Get δ_f from UC of f'' for tolerance η = ε / (QV_ω + 2)
  set η := ε / (QV_ω + 2) with hη_def
  have hη_pos : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ_f, hδ_f_pos, hδ_f⟩ := (Metric.uniformContinuousOn_iff.mp hf''_uc) η hη_pos
  -- Get δ_X from path UC for tolerance min(δ_f, 1)
  set δ := min δ_f 1 with hδ_def
  have hδ_pos : 0 < δ := lt_min hδ_f_pos one_pos
  obtain ⟨δ_X, hδ_X_pos, hδ_X⟩ := (Metric.uniformContinuousOn_iff.mp hXω_uc) δ hδ_pos
  -- Get N₂ from mesh(ns k) < δ_X (need ns k + 1 > t/δ_X)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (t / δ_X)
  -- From Tendsto ns atTop atTop: eventually ns k ≥ N₁ and ns k ≥ N₂
  have hns_large := Filter.tendsto_atTop_atTop.mp _hns
  obtain ⟨K₁, hK₁⟩ := hns_large N₁
  obtain ⟨K₂, hK₂⟩ := hns_large N₂
  -- Main bound: for k ≥ max(N₁, max(K₁, K₂))
  refine ⟨max N₁ (max K₁ K₂), fun k hk => ?_⟩
  have hk_N₁ : N₁ ≤ k := le_of_max_le_left hk
  have hk_K₁ : K₁ ≤ k := le_trans (le_max_left _ _) (le_of_max_le_right hk)
  have hk_K₂ : K₂ ≤ k := le_trans (le_max_right _ _) (le_of_max_le_right hk)
  rw [Real.dist_eq, sub_zero]
  -- Abbreviate per-partition quantities
  set nk := ns k + 1 with hnk_def
  have hnk_pos : (0 : ℝ) < ↑nk := by positivity
  -- Mesh = t/nk < δ_X (from ns k ≥ N₂ ⟹ nk > t/δ_X)
  have hmesh : t / ↑nk < δ_X := by
    rw [div_lt_iff₀ hnk_pos]
    have : N₂ ≤ ns k := hK₂ k hk_K₂
    have hN₂_lt : t / δ_X < ↑N₂ := hN₂
    have hnk_ge : (↑N₂ : ℝ) ≤ ↑nk := by exact_mod_cast Nat.le_succ_of_le this
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < δ_X)).mp hN₂_lt
    linarith [mul_le_mul_of_nonneg_right hnk_ge (le_of_lt hδ_X_pos)]
  -- All partition increments |ΔXᵢ| < δ
  have h_incr_small : ∀ i : Fin nk,
      |X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω - X.process (↑(i : ℕ) * t / ↑nk) ω| < δ := by
    intro i
    -- Both time points are in [0, t], and their distance = t/nk < δ_X
    have hi_lt : (i : ℕ) < nk := i.isLt
    -- tᵢ ∈ [0, t]
    have htᵢ : ↑(i : ℕ) * t / ↑nk ∈ Set.Icc (0 : ℝ) t := by
      constructor
      · positivity
      · rw [div_le_iff₀ hnk_pos]
        have : (↑(i : ℕ) : ℝ) ≤ ↑nk := by exact_mod_cast le_of_lt hi_lt
        linarith [mul_le_mul_of_nonneg_right this (le_of_lt _ht)]
    -- t_{i+1} ∈ [0, t]
    have hti1 : (↑(i : ℕ) + 1) * t / ↑nk ∈ Set.Icc (0 : ℝ) t := by
      constructor
      · positivity
      · rw [div_le_iff₀ hnk_pos]
        have : (↑(i : ℕ) + 1 : ℝ) ≤ ↑nk := by norm_cast
        nlinarith
    -- dist(t_i, t_{i+1}) = t/nk < δ_X
    have hdist : dist (↑(i : ℕ) * t / ↑nk) ((↑(i : ℕ) + 1) * t / ↑nk) < δ_X := by
      rw [Real.dist_eq, show ↑(i : ℕ) * t / ↑nk - (↑(i : ℕ) + 1) * t / ↑nk =
        -(t / ↑nk) from by ring, abs_neg, abs_of_nonneg (div_nonneg (le_of_lt _ht)
        (le_of_lt hnk_pos))]
      exact hmesh
    -- By path UC: |X(t_i) - X(t_{i+1})| < δ
    have := hδ_X (↑(i : ℕ) * t / ↑nk) htᵢ ((↑(i : ℕ) + 1) * t / ↑nk) hti1 hdist
    rw [Real.dist_eq] at this
    rwa [abs_sub_comm] at this
  -- Per-term Taylor bound: |Rᵢ| ≤ η * (ΔXᵢ)²
  -- Using c2_taylor_remainder_bound with oscillation of f'' bounded by η
  have h_per_term : ∀ i : Fin nk,
      |f (↑(i : ℕ) * t / ↑nk)
         (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω) -
       f (↑(i : ℕ) * t / ↑nk)
         (X.process (↑(i : ℕ) * t / ↑nk) ω) -
       deriv (fun x => f (↑(i : ℕ) * t / ↑nk) x)
         (X.process (↑(i : ℕ) * t / ↑nk) ω) *
         (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω -
          X.process (↑(i : ℕ) * t / ↑nk) ω) -
       (1 : ℝ) / 2 *
         deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑nk) x))
           (X.process (↑(i : ℕ) * t / ↑nk) ω) *
         (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω -
          X.process (↑(i : ℕ) * t / ↑nk) ω) ^ 2|
      ≤ η * (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω -
             X.process (↑(i : ℕ) * t / ↑nk) ω) ^ 2 := by
    intro i
    set tᵢ := ↑(i : ℕ) * t / ↑nk
    set xᵢ := X.process tᵢ ω
    set hᵢ := X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω - xᵢ
    -- g(x) = f(tᵢ, x) is C²
    have hg : ContDiff ℝ 2 (fun x => f tᵢ x) := hf_x tᵢ
    -- Apply c2_taylor_remainder_bound: need |g''(y) - g''(xᵢ)| ≤ η for y near xᵢ
    -- First show the function value matches
    have hform : f tᵢ (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω) = (fun x => f tᵢ x) (xᵢ + hᵢ) := by
      simp [hᵢ, xᵢ]
    rw [hform]
    -- Now apply c2_taylor_remainder_bound
    apply le_trans (c2_taylor_remainder_bound hg xᵢ hᵢ (le_of_lt hη_pos) ?_)
    · exact le_rfl
    -- Bound oscillation of g'' = f''(tᵢ, ·) by η on uIcc(xᵢ, xᵢ + hᵢ)
    intro y hy
    -- y ∈ uIcc(xᵢ, xᵢ + hᵢ) ⟹ |y - xᵢ| ≤ |hᵢ|
    have hy_near := abs_sub_le_of_mem_uIcc hy
    -- |hᵢ| < δ ≤ δ_f (from h_incr_small)
    have hhi_small := h_incr_small i
    -- |y - xᵢ| < δ ≤ 1
    have hy_dist : |y - xᵢ| < δ := lt_of_le_of_lt hy_near hhi_small
    -- tᵢ ∈ [0, t]
    have htᵢ_mem : tᵢ ∈ Set.Icc (0 : ℝ) t := by
      constructor
      · positivity
      · rw [div_le_iff₀ hnk_pos]
        have : (↑(i : ℕ) : ℝ) ≤ ↑nk := by exact_mod_cast le_of_lt i.isLt
        linarith [mul_le_mul_of_nonneg_right this (le_of_lt _ht)]
    -- xᵢ ∈ closedBall 0 R (path value in [0,t])
    have hxᵢ_bdd : |xᵢ| ≤ R := hR tᵢ htᵢ_mem
    -- y ∈ closedBall 0 (R+1) (since |y - xᵢ| < 1 and |xᵢ| ≤ R)
    have hy_bdd : |y| ≤ R + 1 := by
      have h1 : |y| ≤ |y - xᵢ| + |xᵢ| := by
        calc |y| = |(y - xᵢ) + xᵢ| := by ring_nf
          _ ≤ |y - xᵢ| + |xᵢ| := abs_add_le _ _
      linarith [min_le_right δ_f 1]
    -- Both (tᵢ, xᵢ) and (tᵢ, y) are in K
    have hxᵢ_in_K : (tᵢ, xᵢ) ∈ K := by
      refine ⟨htᵢ_mem, Metric.mem_closedBall.mpr ?_⟩
      rw [dist_zero_right, Real.norm_eq_abs]; exact le_trans hxᵢ_bdd (by linarith)
    have hy_in_K : (tᵢ, y) ∈ K := by
      refine ⟨htᵢ_mem, Metric.mem_closedBall.mpr ?_⟩
      rw [dist_zero_right, Real.norm_eq_abs]; exact hy_bdd
    -- dist((tᵢ,y), (tᵢ,xᵢ)) = |y - xᵢ| < δ ≤ δ_f
    have hdist_pair : dist (tᵢ, y) (tᵢ, xᵢ) < δ_f := by
      calc dist (tᵢ, y) (tᵢ, xᵢ)
          = max (dist tᵢ tᵢ) (dist y xᵢ) := Prod.dist_eq
        _ = max 0 (dist y xᵢ) := by rw [dist_self]
        _ = dist y xᵢ := max_eq_right dist_nonneg
        _ < δ := by rwa [Real.dist_eq]
        _ ≤ δ_f := min_le_left _ _
    -- By UC of f'' on K: |f''(tᵢ, y) - f''(tᵢ, xᵢ)| < η
    have h_uc := hδ_f (tᵢ, y) hy_in_K (tᵢ, xᵢ) hxᵢ_in_K hdist_pair
    rw [Real.dist_eq] at h_uc
    simp only [] at h_uc
    exact le_of_lt h_uc
  -- Triangle inequality: |∑ Rᵢ| ≤ ∑ |Rᵢ|
  calc |∑ i : Fin nk,
        (f (↑(i : ℕ) * t / ↑nk) (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω) -
         f (↑(i : ℕ) * t / ↑nk) (X.process (↑(i : ℕ) * t / ↑nk) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑nk) x) (X.process (↑(i : ℕ) * t / ↑nk) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω - X.process (↑(i : ℕ) * t / ↑nk) ω) -
         (1 : ℝ) / 2 *
           deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑nk) x))
             (X.process (↑(i : ℕ) * t / ↑nk) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω -
            X.process (↑(i : ℕ) * t / ↑nk) ω) ^ 2)|
      ≤ ∑ i : Fin nk,
        |f (↑(i : ℕ) * t / ↑nk) (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω) -
         f (↑(i : ℕ) * t / ↑nk) (X.process (↑(i : ℕ) * t / ↑nk) ω) -
         deriv (fun x => f (↑(i : ℕ) * t / ↑nk) x) (X.process (↑(i : ℕ) * t / ↑nk) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω - X.process (↑(i : ℕ) * t / ↑nk) ω) -
         (1 : ℝ) / 2 *
           deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑nk) x))
             (X.process (↑(i : ℕ) * t / ↑nk) ω) *
           (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω -
            X.process (↑(i : ℕ) * t / ↑nk) ω) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin nk,
        η * (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω -
             X.process (↑(i : ℕ) * t / ↑nk) ω) ^ 2 :=
        Finset.sum_le_sum (fun i _ => h_per_term i)
    _ = η * ∑ i : Fin nk,
        (X.process ((↑(i : ℕ) + 1) * t / ↑nk) ω -
         X.process (↑(i : ℕ) * t / ↑nk) ω) ^ 2 :=
        (Finset.mul_sum ..).symm
    _ ≤ η * (QV_ω + 1) := by
        apply mul_le_mul_of_nonneg_left (hS_bdd k hk_N₁) (le_of_lt hη_pos)
    _ < ε := by
        rw [hη_def, div_mul_eq_mul_div]
        have hqv2 : (0 : ℝ) < QV_ω + 2 := by linarith
        rw [div_lt_iff₀ hqv2]
        nlinarith

end SPDE
