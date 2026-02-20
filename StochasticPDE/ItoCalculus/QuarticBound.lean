/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.StochasticIntegration
import StochasticPDE.ItoCalculus.ItoFormulaInfrastructure
import StochasticPDE.ItoCalculus.ItoIntegralProperties
import StochasticPDE.ItoCalculus.Probability.IndependenceHelpers

/-!
# Quartic Moment Bound for Stochastic Integrals

This file proves E[(∫σ dW)⁴] ≤ 3Mσ⁴(t-s)² for bounded integrands.

## Strategy

1. Prove the bound for finite sums Σ Hᵢ ΔWᵢ by induction on the number of terms
2. Transfer to the full stochastic integral via L² limit + Fatou's lemma

## Key Results

* `quartic_sum_bound` — E[(Σ Hᵢ ΔWᵢ)⁴] ≤ 3M⁴(Σ Δtᵢ)² for bounded Hᵢ
* `stoch_integral_increment_L4_bound_proof` — The L4 bound for ItoProcess stochastic integrals

## Mathematical Proof (Induction)

For S_k = Σ_{i<k} H_i · ΔW_i with |H_i| ≤ M:

**Base:** S_0 = 0, E[0⁴] = 0 ≤ 0.

**Step:** S_{k+1} = S_k + H_k · ΔW_k. Expand:
  E[S_{k+1}⁴] = E[S_k⁴] + 4E[S_k³ H_k ΔW_k] + 6E[S_k² H_k² ΔW_k²]
               + 4E[S_k H_k³ ΔW_k³] + E[H_k⁴ ΔW_k⁴]

By independence (S_k, H_k are F_{t_k}-measurable, ΔW_k independent of F_{t_k}):
- Terms 2, 4 = 0 (odd moments E[ΔW] = E[ΔW³] = 0)
- Term 3: E[S_k² H_k²] · Δt_k (E[ΔW²] = Δt)
- Term 5: E[H_k⁴] · 3Δt_k² (E[ΔW⁴] = 3Δt²)

With IH (E[S_k⁴] ≤ 3M⁴T_k²) and bounds:
- E[S_k² H_k²] ≤ M² E[S_k²] ≤ M⁴ T_k (Itô isometry)
- E[H_k⁴] ≤ M⁴

We get: E[S_{k+1}⁴] ≤ 3M⁴T_k² + 6Δt·M⁴T_k + 3Δt²·M⁴ = 3M⁴(T_k + Δt)² = 3M⁴T_{k+1}²

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal

noncomputable section

namespace SPDE

variable {Ω : Type*} [instΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Quartic step: the induction step for the quartic bound

The key calculation: given S, X : Ω → ℝ where X = H·ΔW with |H| ≤ M and
ΔW is a BM increment independent of S, H, we have:
  E[(S+X)²] ≤ E[S²] + M²Δt  (using E[SX] = 0 by independence)
  E[(S+X)⁴] ≤ E[S⁴] + 6M²Δt·E[S²] + 3M⁴Δt²

This follows from the binomial expansion, vanishing of odd-moment
cross terms by independence, and boundedness of H.
-/

/-- **Quartic induction step.** If E[S⁴] ≤ 3M⁴T² and E[S²] ≤ M²T,
    and X = H·ΔW with |H| ≤ M, ΔW ~ N(0, Δt), ΔW independent of (S, H),
    then E[(S+X)⁴] ≤ 3M⁴(T+Δt)² and E[(S+X)²] ≤ M²(T+Δt).

    Proof: Expand (S+X)⁴, use independence to factor, use BM moments,
    bound H, and combine using 3T² + 6TΔt + 3Δt² = 3(T+Δt)². -/
theorem quartic_step
    [IsProbabilityMeasure μ]
    (W : BrownianMotion Ω μ)
    (S : Ω → ℝ) (H_k : Ω → ℝ)
    (s_time t_time : ℝ) (hs_nn : 0 ≤ s_time) (hst : s_time ≤ t_time)
    -- Adaptedness
    (hS_meas : @Measurable Ω ℝ (W.F.σ_algebra s_time) _ S)
    (hH_meas : @Measurable Ω ℝ (W.F.σ_algebra s_time) _ H_k)
    -- Boundedness
    {M : ℝ} (_hM_nn : 0 ≤ M) (hH_bdd : ∀ ω, |H_k ω| ≤ M)
    -- Time parameter
    (T : ℝ) (_hT_nn : 0 ≤ T)
    -- Integrability
    (hS2_int : Integrable (fun ω => (S ω) ^ 2) μ)
    (hS4_int : Integrable (fun ω => (S ω) ^ 4) μ)
    -- IH bounds
    (hIH2 : ∫ ω, (S ω) ^ 2 ∂μ ≤ M ^ 2 * T)
    (hIH4 : ∫ ω, (S ω) ^ 4 ∂μ ≤ 3 * M ^ 4 * T ^ 2) :
    let X : Ω → ℝ := fun ω => H_k ω *
      (W.toAdapted.process t_time ω - W.toAdapted.process s_time ω)
    let Δt := t_time - s_time
    Integrable (fun ω => (S ω + X ω) ^ 2) μ ∧
    Integrable (fun ω => (S ω + X ω) ^ 4) μ ∧
    (∫ ω, (S ω + X ω) ^ 2 ∂μ ≤ M ^ 2 * (T + Δt)) ∧
    (∫ ω, (S ω + X ω) ^ 4 ∂μ ≤ 3 * M ^ 4 * (T + Δt) ^ 2) := by
  intro X Δt
  -- The ΔW increment
  set ΔW : Ω → ℝ := fun ω =>
    W.toAdapted.process t_time ω - W.toAdapted.process s_time ω with hΔW_def
  -- BM infrastructure
  have hindep := W.independent_increments s_time t_time hs_nn hst
  have hΔW_int := W.increment_integrable s_time t_time hs_nn hst
  have hΔW2_int := W.increment_sq_integrable s_time t_time hs_nn hst
  have hΔW3_int := W.increment_all_moments s_time t_time hs_nn hst 3
  have hΔW4_int := W.increment_all_moments s_time t_time hs_nn hst 4
  -- BM moments
  have hΔW_mean : ∫ ω, ΔW ω ∂μ = 0 :=
    W.increment_mean_zero s_time t_time hs_nn hst
  have hΔW_var : ∫ ω, (ΔW ω) ^ 2 ∂μ = Δt :=
    W.increment_variance s_time t_time hs_nn hst
  have hΔW3_mean : ∫ ω, (ΔW ω) ^ 3 ∂μ = 0 :=
    W.increment_third_moment s_time t_time hs_nn hst
  have hΔW4_val : ∫ ω, (ΔW ω) ^ 4 ∂μ = 3 * Δt ^ 2 :=
    W.increment_fourth_moment s_time t_time hs_nn hst
  have hΔt_nn : 0 ≤ Δt := by linarith
  -- Ambient measurability
  have hS_amb : Measurable S := hS_meas.mono (W.F.le_ambient s_time) le_rfl
  have hH_amb : Measurable H_k := hH_meas.mono (W.F.le_ambient s_time) le_rfl
  -- Boundedness of H²
  have hH2_bdd : ∀ ω, |(H_k ω) ^ 2| ≤ M ^ 2 := fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 2
  -- Independence for ΔW^k
  have hindep_pow : ∀ (k : ℕ), @Indep Ω (W.F.σ_algebra s_time)
      (MeasurableSpace.comap (fun ω => (ΔW ω) ^ k) inferInstance) instΩ μ := by
    intro k
    apply indep_of_indep_of_le_right hindep
    intro s hs; obtain ⟨u, hu, rfl⟩ := hs
    exact ⟨(fun x => x ^ k) ⁻¹' u, (measurable_id.pow_const k) hu, rfl⟩
  -- Key factorization: E[f · ΔW] = 0 for F_s-measurable integrable f
  have hfactor_zero : ∀ {f : Ω → ℝ}
      (_ : @Measurable Ω ℝ (W.F.σ_algebra s_time) _ f)
      (_ : Integrable f μ),
      ∫ ω, f ω * ΔW ω ∂μ = 0 :=
    fun hf_meas hf_int => Probability.integral_mul_zero_of_indep_zero_mean
      (W.F.le_ambient _) hf_meas hf_int hΔW_int hindep hΔW_mean
  -- E[f · ΔW³] = 0 for F_s-measurable integrable f
  have hfactor_zero_3 : ∀ {f : Ω → ℝ}
      (_ : @Measurable Ω ℝ (W.F.σ_algebra s_time) _ f)
      (_ : Integrable f μ),
      ∫ ω, f ω * (ΔW ω) ^ 3 ∂μ = 0 := by
    intro f hf_meas hf_int
    rw [Probability.integral_mul_of_indep_sigma_algebra
      (W.F.le_ambient _) hf_meas hf_int hΔW3_int (hindep_pow 3)]
    rw [hΔW3_mean, mul_zero]
  -- E[f · ΔW²] = E[f] · Δt for F_s-measurable integrable f
  have hfactor_sq : ∀ {f : Ω → ℝ}
      (_ : @Measurable Ω ℝ (W.F.σ_algebra s_time) _ f)
      (_ : Integrable f μ),
      ∫ ω, f ω * (ΔW ω) ^ 2 ∂μ = (∫ ω, f ω ∂μ) * Δt := by
    intro f hf_meas hf_int
    rw [Probability.integral_mul_of_indep_sigma_algebra
      (W.F.le_ambient _) hf_meas hf_int hΔW2_int (hindep_pow 2)]
    rw [hΔW_var]
  -- E[f · ΔW⁴] = E[f] · 3Δt² for F_s-measurable integrable f
  have hfactor_4th : ∀ {f : Ω → ℝ}
      (_ : @Measurable Ω ℝ (W.F.σ_algebra s_time) _ f)
      (_ : Integrable f μ),
      ∫ ω, f ω * (ΔW ω) ^ 4 ∂μ = (∫ ω, f ω ∂μ) * (3 * Δt ^ 2) := by
    intro f hf_meas hf_int
    rw [Probability.integral_mul_of_indep_sigma_algebra
      (W.F.le_ambient _) hf_meas hf_int hΔW4_int (hindep_pow 4)]
    rw [hΔW4_val]
  -- Integrability helpers (routine: products of bounded/Lp functions on probability space)
  have hS_int : Integrable S μ := by
    apply Integrable.mono' (hS2_int.add (integrable_const 1))
    · exact hS_amb.aestronglyMeasurable
    · exact ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs, Pi.add_apply]
        nlinarith [sq_abs (S ω), sq_nonneg (|S ω| - 1), abs_nonneg (S ω)]
  have hSH_int : Integrable (fun ω => S ω * H_k ω) μ := by
    have h := hS_int.bdd_mul hH_amb.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs]
        exact le_trans (hH_bdd ω) (le_abs_self _))
    exact h.congr (ae_of_all _ fun ω => mul_comm _ _)
  have hH2_int : Integrable (fun ω => (H_k ω) ^ 2) μ := by
    apply Integrable.mono' (integrable_const (M ^ 2))
    · exact (hH_amb.pow_const 2).aestronglyMeasurable
    · exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 2
  have hH2ΔW2_int : Integrable (fun ω => (H_k ω) ^ 2 * (ΔW ω) ^ 2) μ :=
    hΔW2_int.bdd_mul ((hH_amb.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [show (H_k ω) ^ 2 = |H_k ω| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 2)
  have hSHΔW_int : Integrable (fun ω => S ω * H_k ω * ΔW ω) μ :=
    (Probability.indepFun_of_measurable_and_indep (hS_meas.mul hH_meas) hindep).integrable_mul
      hSH_int hΔW_int
  -- E[H²] ≤ M²
  have hH2_bound : ∫ ω, (H_k ω) ^ 2 ∂μ ≤ M ^ 2 := by
    have hpw : ∀ ω, (H_k ω) ^ 2 ≤ M ^ 2 := fun ω => by
      rw [show (H_k ω) ^ 2 = |H_k ω| ^ 2 from (sq_abs _).symm]
      exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 2
    have h1 := integral_mono hH2_int (integrable_const (M ^ 2)) hpw
    simp only [integral_const] at h1
    rwa [show μ.real Set.univ = 1 from by
      simp [Measure.real, measure_univ, ENNReal.toReal_one], one_smul] at h1
  -- Ambient measurability for ΔW and X
  have hΔW_amb : Measurable ΔW :=
    ((W.toAdapted.adapted t_time).mono (W.F.le_ambient _) le_rfl).sub
      ((W.toAdapted.adapted s_time).mono (W.F.le_ambient _) le_rfl)
  have hX_amb : Measurable X := hH_amb.mul hΔW_amb
  -- X² integrable (= H²ΔW², bounded × integrable)
  have hX2_int : Integrable (fun ω => (X ω) ^ 2) μ :=
    hH2ΔW2_int.congr (ae_of_all _ fun ω => by
      show (H_k ω) ^ 2 * (ΔW ω) ^ 2 = (X ω) ^ 2
      simp only [X, hΔW_def, mul_pow])
  -- (S+X)² integrability via domination: (a+b)² ≤ 2(a²+b²)
  have hSX2_int : Integrable (fun ω => (S ω + X ω) ^ 2) μ := by
    have hdom2 : Integrable (fun ω => 2 * ((S ω) ^ 2 + (X ω) ^ 2)) μ :=
      (hS2_int.add hX2_int).const_mul 2
    exact hdom2.mono' ((hS_amb.add hX_amb).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (S ω - X ω)])
  -- X⁴ integrable (= H⁴ΔW⁴, bounded × integrable)
  have hX4_int : Integrable (fun ω => (X ω) ^ 4) μ := by
    have heq : (fun ω => (X ω) ^ 4) = fun ω => (H_k ω) ^ 4 * (ΔW ω) ^ 4 := by
      ext ω; simp only [X, hΔW_def, mul_pow]
    rw [heq]
    exact hΔW4_int.bdd_mul ((hH_amb.pow_const 4).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 4)
  -- (S+X)⁴ integrability via domination: (a+b)⁴ ≤ 8(a⁴+b⁴)
  have hSX4_int : Integrable (fun ω => (S ω + X ω) ^ 4) μ := by
    have hdom : Integrable (fun ω => 8 * ((S ω) ^ 4 + (X ω) ^ 4)) μ :=
      (hS4_int.add hX4_int).const_mul 8
    exact hdom.mono' ((hS_amb.add hX_amb).pow_const 4).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have h0 := mul_nonneg (sq_nonneg (S ω - X ω))
          (show (0 : ℝ) ≤ 3 * (S ω + X ω) ^ 2 + (2 * S ω + X ω) ^ 2 + 3 * (X ω) ^ 2
            from by positivity)
        linarith [show (S ω - X ω) ^ 2 *
          (3 * (S ω + X ω) ^ 2 + (2 * S ω + X ω) ^ 2 + 3 * (X ω) ^ 2) =
          8 * ((S ω) ^ 4 + (X ω) ^ 4) - (S ω + X ω) ^ 4 from by ring])
  refine ⟨hSX2_int, hSX4_int, ?_, ?_⟩
  · -- === L² bound: E[(S+X)²] ≤ M²(T+Δt) ===
    -- Integrability for the remainder terms
    have hrest_int : Integrable
        (fun ω => 2 * (S ω * H_k ω * ΔW ω) + (H_k ω) ^ 2 * (ΔW ω) ^ 2) μ :=
      (hSHΔW_int.const_mul 2).add hH2ΔW2_int
    -- Split ∫(S+X)² into ∫S² + ∫(rest)
    have hsplit : ∫ ω, (S ω + X ω) ^ 2 ∂μ =
        ∫ ω, (S ω) ^ 2 ∂μ +
        ∫ ω, (2 * (S ω * H_k ω * ΔW ω) + (H_k ω) ^ 2 * (ΔW ω) ^ 2) ∂μ := by
      have : ∀ ω, (S ω + X ω) ^ 2 =
          (S ω) ^ 2 + (2 * (S ω * H_k ω * ΔW ω) + (H_k ω) ^ 2 * (ΔW ω) ^ 2) := by
        intro ω; simp only [X]; ring
      simp_rw [this]; exact integral_add hS2_int hrest_int
    -- Split ∫(rest) into ∫(cross) + ∫(H²ΔW²)
    have hsplit2 : ∫ ω, (2 * (S ω * H_k ω * ΔW ω) + (H_k ω) ^ 2 * (ΔW ω) ^ 2) ∂μ =
        ∫ ω, 2 * (S ω * H_k ω * ΔW ω) ∂μ +
        ∫ ω, (H_k ω) ^ 2 * (ΔW ω) ^ 2 ∂μ :=
      integral_add (hSHΔW_int.const_mul 2) hH2ΔW2_int
    rw [hsplit, hsplit2]
    -- Cross term vanishes: E[2·S·H·ΔW] = 2·E[S·H·ΔW] = 2·0 = 0
    have hcross_zero : ∫ ω, 2 * (S ω * H_k ω * ΔW ω) ∂μ = 0 := by
      have h0 := hfactor_zero (hS_meas.mul hH_meas) hSH_int
      simp only [integral_const_mul, h0, mul_zero]
    rw [hcross_zero, zero_add]
    -- H² term: E[H²·ΔW²] = E[H²]·Δt ≤ M²·Δt
    have hH2ΔW2_bound : ∫ ω, (H_k ω) ^ 2 * (ΔW ω) ^ 2 ∂μ ≤ M ^ 2 * Δt := by
      rw [hfactor_sq (hH_meas.pow_const 2) hH2_int]
      exact mul_le_mul_of_nonneg_right hH2_bound hΔt_nn
    -- Combine: ∫S² + ∫H²ΔW² ≤ M²T + M²Δt = M²(T+Δt)
    calc ∫ ω, (S ω) ^ 2 ∂μ + ∫ ω, (H_k ω) ^ 2 * (ΔW ω) ^ 2 ∂μ
      ≤ M ^ 2 * T + M ^ 2 * Δt := add_le_add hIH2 hH2ΔW2_bound
      _ = M ^ 2 * (T + Δt) := by ring
  · -- === L⁴ bound: E[(S+X)⁴] ≤ 3M⁴(T+Δt)² ===
    -- Expand: (S+X)⁴ = S⁴ + 4S³·H·ΔW + 6S²·H²·ΔW² + 4S·H³·ΔW³ + H⁴·ΔW⁴
    -- Terms with odd powers of ΔW vanish by independence + zero mean.
    -- Term 3: E[S²H²·ΔW²] = E[S²H²]·Δt ≤ M²·E[S²]·Δt ≤ M⁴TΔt
    -- Term 5: E[H⁴·ΔW⁴] = E[H⁴]·3Δt² ≤ M⁴·3Δt²
    -- Total: ≤ 3M⁴T² + 6M⁴TΔt + 3M⁴Δt² = 3M⁴(T+Δt)²
    have hexpand4 : ∀ ω, (S ω + X ω) ^ 4 =
        (S ω) ^ 4 + 4 * ((S ω) ^ 3 * H_k ω * ΔW ω) +
        6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2) +
        4 * (S ω * (H_k ω) ^ 3 * (ΔW ω) ^ 3) +
        (H_k ω) ^ 4 * (ΔW ω) ^ 4 := by
      intro ω; simp only [X]; ring
    simp_rw [hexpand4]
    -- Integrability of each term
    -- S³H is F_s-measurable and integrable (from S⁴ and H bounded)
    have hS3H_meas : @Measurable Ω ℝ (W.F.σ_algebra s_time) _
        (fun ω => (S ω) ^ 3 * H_k ω) := (hS_meas.pow_const 3).mul hH_meas
    have hS3_int : Integrable (fun ω => (S ω) ^ 3) μ :=
      (hS4_int.add (integrable_const 1)).mono'
        ((hS_amb.pow_const 3).aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          simp only [Real.norm_eq_abs, Pi.add_apply, abs_pow]
          -- Goal: |S ω| ^ 3 ≤ (S ω) ^ 4 + 1
          -- Bridge (S ω) ^ 4 = |S ω| ^ 4 (even power)
          have hpow4 : (S ω) ^ 4 = |S ω| ^ 4 := by
            rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
          rw [hpow4]
          -- Now: |S ω| ^ 3 ≤ |S ω| ^ 4 + 1
          nlinarith [sq_nonneg (|S ω| ^ 2 - |S ω|),
            mul_nonneg (abs_nonneg (S ω)) (sq_nonneg (|S ω| - 1)),
            sq_nonneg (|S ω| - 1), abs_nonneg (S ω)])
    have hS3H_int : Integrable (fun ω => (S ω) ^ 3 * H_k ω) μ :=
      (hS3_int.bdd_mul hH_amb.aestronglyMeasurable
        (ae_of_all _ fun ω => by
          simp only [Real.norm_eq_abs]
          exact le_trans (hH_bdd ω) (le_abs_self _))).congr
        (ae_of_all _ fun ω => mul_comm _ _)
    -- S²H² term
    have hS2H2_meas : @Measurable Ω ℝ (W.F.σ_algebra s_time) _
        (fun ω => (S ω) ^ 2 * (H_k ω) ^ 2) := (hS_meas.pow_const 2).mul (hH_meas.pow_const 2)
    have hS2H2_int : Integrable (fun ω => (S ω) ^ 2 * (H_k ω) ^ 2) μ := by
      have h := hS2_int.bdd_mul ((hH_amb.pow_const 2).aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          rw [show (H_k ω) ^ 2 = |H_k ω| ^ 2 from (sq_abs _).symm]
          exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 2)
      exact h.congr (ae_of_all _ fun ω => mul_comm _ _)
    -- SH³ term
    have hSH3_meas : @Measurable Ω ℝ (W.F.σ_algebra s_time) _
        (fun ω => S ω * (H_k ω) ^ 3) := hS_meas.mul (hH_meas.pow_const 3)
    have hSH3_int : Integrable (fun ω => S ω * (H_k ω) ^ 3) μ :=
      (hS_int.bdd_mul ((hH_amb.pow_const 3).aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          simp only [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 3)).congr
        (ae_of_all _ fun ω => mul_comm _ _)
    -- H⁴ is integrable (bounded)
    have hH4_int : Integrable (fun ω => (H_k ω) ^ 4) μ :=
      (integrable_const (M ^ 4)).mono'
        ((hH_amb.pow_const 4).aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          simp only [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 4)
    -- H⁴·ΔW⁴ integrable
    have hH4ΔW4_int : Integrable (fun ω => (H_k ω) ^ 4 * (ΔW ω) ^ 4) μ :=
      hΔW4_int.bdd_mul ((hH_amb.pow_const 4).aestronglyMeasurable)
        (ae_of_all _ fun ω => by
          simp only [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 4)
    -- Integrability of the full terms (with constants)
    -- Product integrability via independence: f·(ΔW^k) integrable when f adapted integrable
    have hS3HΔW_int : Integrable (fun ω => (S ω) ^ 3 * H_k ω * ΔW ω) μ :=
      (Probability.indepFun_of_measurable_and_indep hS3H_meas hindep).integrable_mul
        hS3H_int hΔW_int
    have hS2H2ΔW2_int : Integrable (fun ω => (S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2) μ :=
      (Probability.indepFun_of_measurable_and_indep hS2H2_meas (hindep_pow 2)).integrable_mul
        hS2H2_int hΔW2_int
    have hSH3ΔW3_int : Integrable (fun ω => S ω * (H_k ω) ^ 3 * (ΔW ω) ^ 3) μ :=
      (Probability.indepFun_of_measurable_and_indep hSH3_meas (hindep_pow 3)).integrable_mul
        hSH3_int hΔW3_int
    have hint1 : Integrable (fun ω => 4 * ((S ω) ^ 3 * H_k ω * ΔW ω)) μ :=
      hS3HΔW_int.const_mul 4
    have hint2 : Integrable (fun ω => 6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2)) μ :=
      hS2H2ΔW2_int.const_mul 6
    have hint3 : Integrable (fun ω => 4 * (S ω * (H_k ω) ^ 3 * (ΔW ω) ^ 3)) μ :=
      hSH3ΔW3_int.const_mul 4
    -- Split the integral
    -- ∫ (a + b + c + d + e) = ∫a + ∫b + ∫c + ∫d + ∫e
    have hsplit : ∫ ω, ((S ω) ^ 4 + 4 * ((S ω) ^ 3 * H_k ω * ΔW ω) +
        6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2) +
        4 * (S ω * (H_k ω) ^ 3 * (ΔW ω) ^ 3) +
        (H_k ω) ^ 4 * (ΔW ω) ^ 4) ∂μ =
        ∫ ω, (S ω) ^ 4 ∂μ + ∫ ω, 4 * ((S ω) ^ 3 * H_k ω * ΔW ω) ∂μ +
        ∫ ω, 6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2) ∂μ +
        ∫ ω, 4 * (S ω * (H_k ω) ^ 3 * (ΔW ω) ^ 3) ∂μ +
        ∫ ω, (H_k ω) ^ 4 * (ΔW ω) ^ 4 ∂μ := by
      -- Force value-level type annotations so integral_add pattern matches the goal
      have hf4_int : Integrable (fun ω => (S ω) ^ 4 + 4 * ((S ω) ^ 3 * H_k ω * ΔW ω) +
          6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2) +
          4 * (S ω * (H_k ω) ^ 3 * (ΔW ω) ^ 3)) μ :=
        (((hS4_int.add hint1).add hint2).add hint3)
      have hf3_int : Integrable (fun ω => (S ω) ^ 4 + 4 * ((S ω) ^ 3 * H_k ω * ΔW ω) +
          6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2)) μ :=
        ((hS4_int.add hint1).add hint2)
      have hf2_int : Integrable (fun ω => (S ω) ^ 4 +
          4 * ((S ω) ^ 3 * H_k ω * ΔW ω)) μ :=
        (hS4_int.add hint1)
      rw [integral_add hf4_int hH4ΔW4_int,
        integral_add hf3_int hint3,
        integral_add hf2_int hint2,
        integral_add hS4_int hint1]
    rw [hsplit]
    -- Odd-moment terms vanish
    -- Term 2: E[4·S³H·ΔW] = 4·E[(S³H)·ΔW] = 4·0 = 0
    have hterm2 : ∫ ω, 4 * ((S ω) ^ 3 * H_k ω * ΔW ω) ∂μ = 0 := by
      have h0 := hfactor_zero hS3H_meas hS3H_int
      simp only [integral_const_mul, h0, mul_zero]
    -- Term 4: E[4·SH³·ΔW³] = 4·E[(SH³)·ΔW³] = 4·0 = 0
    have hterm4 : ∫ ω, 4 * (S ω * (H_k ω) ^ 3 * (ΔW ω) ^ 3) ∂μ = 0 := by
      have h0 := hfactor_zero_3 hSH3_meas hSH3_int
      simp only [integral_const_mul, h0, mul_zero]
    rw [hterm2, hterm4]
    -- Remaining: E[S⁴] + 0 + E[6S²H²ΔW²] + 0 + E[H⁴ΔW⁴]
    simp only [add_zero]
    -- Term 3: E[6S²H²ΔW²] = 6·E[S²H²]·Δt ≤ 6M²·E[S²]·Δt
    have hterm3 : ∫ ω, 6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2) ∂μ ≤
        6 * M ^ 2 * (∫ ω, (S ω) ^ 2 ∂μ) * Δt := by
      -- Use simp only for integral_const_mul and hfactor_sq
      have h_sq := hfactor_sq hS2H2_meas hS2H2_int
      simp only [integral_const_mul, h_sq]
      -- Goal: 6 * ((∫ ω, S ω ^ 2 * H_k ω ^ 2 ∂μ) * Δt) ≤ 6 * M ^ 2 * (∫ ω, S ω ^ 2 ∂μ) * Δt
      -- Bound E[S²H²] ≤ M² · E[S²]
      have hS2H2_bound : ∫ ω, (S ω) ^ 2 * (H_k ω) ^ 2 ∂μ ≤
          M ^ 2 * ∫ ω, (S ω) ^ 2 ∂μ := by
        calc ∫ ω, (S ω) ^ 2 * (H_k ω) ^ 2 ∂μ
          ≤ ∫ ω, (S ω) ^ 2 * M ^ 2 ∂μ :=
            integral_mono hS2H2_int (hS2_int.mul_const (M ^ 2)) (fun ω => by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
              rw [show (H_k ω) ^ 2 = |H_k ω| ^ 2 from (sq_abs _).symm]
              exact pow_le_pow_left₀ (abs_nonneg _) (hH_bdd ω) 2)
          _ = M ^ 2 * ∫ ω, (S ω) ^ 2 ∂μ := by
            rw [integral_mul_const]; ring
      nlinarith
    -- Term 5: E[H⁴ΔW⁴] = E[H⁴]·3Δt² ≤ M⁴·3Δt²
    have hH4_meas : @Measurable Ω ℝ (W.F.σ_algebra s_time) _
        (fun ω => (H_k ω) ^ 4) := hH_meas.pow_const 4
    have hterm5 : ∫ ω, (H_k ω) ^ 4 * (ΔW ω) ^ 4 ∂μ ≤ M ^ 4 * (3 * Δt ^ 2) := by
      rw [hfactor_4th hH4_meas hH4_int]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      -- E[H⁴] ≤ M⁴
      have hpw : ∀ ω, (H_k ω) ^ 4 ≤ M ^ 4 := fun ω => by
        nlinarith [hH_bdd ω, sq_abs (H_k ω), sq_abs M,
          pow_le_pow_left₀ (abs_nonneg (H_k ω)) (hH_bdd ω) 4]
      have h := integral_mono hH4_int (integrable_const (M ^ 4)) hpw
      simp only [integral_const] at h
      rwa [show μ.real Set.univ = 1 from by
        simp [Measure.real, measure_univ, ENNReal.toReal_one], one_smul] at h
    -- Combine: E[S⁴] + 6·M²E[S²]·Δt + M⁴·3Δt² ≤ 3M⁴(T+Δt)²
    calc ∫ ω, (S ω) ^ 4 ∂μ +
        ∫ ω, 6 * ((S ω) ^ 2 * (H_k ω) ^ 2 * (ΔW ω) ^ 2) ∂μ +
        ∫ ω, (H_k ω) ^ 4 * (ΔW ω) ^ 4 ∂μ
      ≤ 3 * M ^ 4 * T ^ 2 + 6 * M ^ 2 * (∫ ω, (S ω) ^ 2 ∂μ) * Δt +
        M ^ 4 * (3 * Δt ^ 2) := by linarith [hIH4, hterm3, hterm5]
      _ ≤ 3 * M ^ 4 * T ^ 2 + 6 * M ^ 2 * (M ^ 2 * T) * Δt +
        M ^ 4 * (3 * Δt ^ 2) := by
        have : 6 * M ^ 2 * (∫ ω, (S ω) ^ 2 ∂μ) * Δt ≤
            6 * M ^ 2 * (M ^ 2 * T) * Δt := by
          have hES2 : ∫ ω, (S ω) ^ 2 ∂μ ≤ M ^ 2 * T := hIH2
          have h6M2_nn : (0 : ℝ) ≤ 6 * M ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hES2 h6M2_nn) hΔt_nn
        linarith
      _ = 3 * M ^ 4 * (T + Δt) ^ 2 := by ring

/-! ## Quartic bound for bounded martingale sums

The key induction result for the quartic moment bound.
See the module docstring for the full proof.
-/

/-- **Quartic bound for bounded martingale sums.**

    Given:
    - H_i are F_{t_i}-measurable random variables with |H_i(ω)| ≤ M
    - ΔW_i = W(t_{i+1}) - W(t_i) are BM increments
    - S_k = Σ_{i<k} H_i · ΔW_i

    Then: E[S_k⁴] ≤ 3 · M⁴ · (Σ_{i<k} Δt_i)²

    Proof by induction on k (see module docstring). -/
theorem quartic_sum_bound
    {_F : Filtration Ω ℝ} [IsProbabilityMeasure μ]
    (W : BrownianMotion Ω μ)
    {n : ℕ}
    (times : Fin (n + 1) → ℝ)
    (htimes_nn : ∀ i, 0 ≤ times i)
    (htimes_inc : ∀ i j : Fin (n + 1), i < j → times i < times j)
    (H : Fin n → Ω → ℝ)
    (H_adapted : ∀ i : Fin n, @Measurable Ω ℝ (W.F.σ_algebra (times i.castSucc)) _ (H i))
    {M : ℝ} (hM_nn : 0 ≤ M) (H_bounded : ∀ i : Fin n, ∀ ω, |H i ω| ≤ M)
    (k : ℕ) (hk : k ≤ n) :
    let S : Ω → ℝ := fun ω =>
      ∑ i : Fin k, H ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩ ω *
        (W.toAdapted.process (times ⟨(i : ℕ) + 1, by omega⟩) ω -
         W.toAdapted.process (times ⟨i, by omega⟩) ω)
    let T : ℝ := ∑ i : Fin k,
      (times ⟨(i : ℕ) + 1, by omega⟩ - times ⟨i, by omega⟩)
    ∫ ω, (S ω) ^ 4 ∂μ ≤ 3 * M ^ 4 * T ^ 2 := by
  -- Strengthen the IH to include L² bound and integrability
  suffices h : ∀ (j : ℕ) (hj : j ≤ n),
    let Sj : Ω → ℝ := fun ω =>
      ∑ i : Fin j, H ⟨i, Nat.lt_of_lt_of_le i.isLt hj⟩ ω *
        (W.toAdapted.process (times ⟨(i : ℕ) + 1, by omega⟩) ω -
         W.toAdapted.process (times ⟨i, by omega⟩) ω)
    let Tj : ℝ := ∑ i : Fin j,
      (times ⟨(i : ℕ) + 1, by omega⟩ - times ⟨i, by omega⟩)
    Integrable (fun ω => (Sj ω) ^ 2) μ ∧
    Integrable (fun ω => (Sj ω) ^ 4) μ ∧
    ∫ ω, (Sj ω) ^ 2 ∂μ ≤ M ^ 2 * Tj ∧
    ∫ ω, (Sj ω) ^ 4 ∂μ ≤ 3 * M ^ 4 * Tj ^ 2 by
    exact (h k hk).2.2.2
  intro j
  induction j with
  | zero =>
    intro hj
    simp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- S_0 = 0, (0)² = 0 is integrable
      exact (integrable_const (0 : ℝ)).congr
        (ae_of_all _ fun ω => by simp)
    · exact (integrable_const (0 : ℝ)).congr
        (ae_of_all _ fun ω => by simp)
    · simp
    · simp
  | succ j ih =>
    intro hj
    have hj' : j ≤ n := Nat.le_of_succ_le hj
    obtain ⟨ih_s2_int, ih_s4_int, ih2, ih4⟩ := ih hj'
    -- Define the previous partial sum S_j and the new term X_j = H_j · ΔW_j
    set S_prev : Ω → ℝ := fun ω =>
      ∑ i : Fin j, H ⟨i, Nat.lt_of_lt_of_le i.isLt hj'⟩ ω *
        (W.toAdapted.process (times ⟨(i : ℕ) + 1, by omega⟩) ω -
         W.toAdapted.process (times ⟨i, by omega⟩) ω) with hS_prev
    set T_prev : ℝ := ∑ i : Fin j,
      (times ⟨(i : ℕ) + 1, by omega⟩ - times ⟨i, by omega⟩) with hT_prev
    set H_j := H ⟨j, by omega⟩ with hH_j
    set ΔW_j : Ω → ℝ := fun ω =>
      W.toAdapted.process (times ⟨j + 1, by omega⟩) ω -
      W.toAdapted.process (times ⟨j, by omega⟩) ω with hΔW_j
    set X_j : Ω → ℝ := fun ω => H_j ω * ΔW_j ω with hX_j
    set Δt_j : ℝ := times ⟨j + 1, by omega⟩ - times ⟨j, by omega⟩ with hΔt_j
    -- S_{j+1} = S_j + X_j
    have hS_eq : ∀ ω, (∑ i : Fin (j + 1),
        H ⟨i, Nat.lt_of_lt_of_le i.isLt hj⟩ ω *
        (W.toAdapted.process (times ⟨(i : ℕ) + 1, by omega⟩) ω -
         W.toAdapted.process (times ⟨i, by omega⟩) ω)) =
      S_prev ω + X_j ω := by
      intro ω; rw [Fin.sum_univ_castSucc]; rfl
    -- T_{j+1} = T_j + Δt_j
    have hT_eq : (∑ i : Fin (j + 1),
        (times ⟨(i : ℕ) + 1, by omega⟩ - times ⟨i, by omega⟩)) =
      T_prev + Δt_j := by
      rw [Fin.sum_univ_castSucc]; rfl
    -- Rewrite using S_{j+1} = S_prev + X_j
    simp only
    rw [show (fun ω => (∑ i : Fin (j + 1),
        H ⟨↑i, Nat.lt_of_lt_of_le i.isLt hj⟩ ω *
        (W.toAdapted.process (times ⟨↑i + 1, by omega⟩) ω -
         W.toAdapted.process (times ⟨↑i, by omega⟩) ω)) ^ 2) =
      fun ω => (S_prev ω + X_j ω) ^ 2 from by ext ω; rw [hS_eq]]
    rw [show (fun ω => (∑ i : Fin (j + 1),
        H ⟨↑i, Nat.lt_of_lt_of_le i.isLt hj⟩ ω *
        (W.toAdapted.process (times ⟨↑i + 1, by omega⟩) ω -
         W.toAdapted.process (times ⟨↑i, by omega⟩) ω)) ^ 4) =
      fun ω => (S_prev ω + X_j ω) ^ 4 from by ext ω; rw [hS_eq]]
    rw [hT_eq]
    -- Time ordering
    have hj_lt_j1 : (⟨j, by omega⟩ : Fin (n + 1)) < ⟨j + 1, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    have hΔt_nn : 0 ≤ Δt_j := by
      simp only [hΔt_j]; linarith [htimes_inc _ _ hj_lt_j1]
    have hT_nn : 0 ≤ T_prev := by
      simp only [hT_prev]
      apply Finset.sum_nonneg
      intro i _
      have : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) < ⟨(i : ℕ) + 1, by omega⟩ :=
        Fin.mk_lt_mk.mpr (by omega)
      linarith [htimes_inc _ _ this]
    -- Measurability
    have hS_prev_meas : @Measurable Ω ℝ (W.F.σ_algebra (times ⟨j, by omega⟩)) _ S_prev := by
      apply Finset.measurable_sum
      intro i _
      have hi_lt : (i : ℕ) < j := i.isLt
      have hle_i : times ⟨(i : ℕ), by omega⟩ ≤ times ⟨j, by omega⟩ :=
        le_of_lt (htimes_inc _ _ (Fin.mk_lt_mk.mpr hi_lt))
      have hle_i1 : times ⟨(i : ℕ) + 1, by omega⟩ ≤ times ⟨j, by omega⟩ := by
        rcases (Nat.succ_le_of_lt hi_lt).eq_or_lt with h | h
        · exact le_of_eq (congrArg times (Fin.ext h))
        · exact le_of_lt (htimes_inc _ _ (Fin.mk_lt_mk.mpr h))
      exact ((H_adapted ⟨(i : ℕ), by omega⟩).mono (W.F.mono _ _ hle_i) le_rfl).mul
        (((W.toAdapted.adapted _).mono (W.F.mono _ _ hle_i1) le_rfl).sub
         ((W.toAdapted.adapted _).mono (W.F.mono _ _ hle_i) le_rfl))
    have hH_j_meas : @Measurable Ω ℝ (W.F.σ_algebra (times ⟨j, by omega⟩)) _ H_j :=
      H_adapted ⟨j, by omega⟩
    -- Apply quartic_step
    have hstep := quartic_step W S_prev H_j
      (times ⟨j, by omega⟩) (times ⟨j + 1, by omega⟩)
      (htimes_nn ⟨j, by omega⟩)
      (le_of_lt (htimes_inc _ _ hj_lt_j1))
      hS_prev_meas hH_j_meas
      hM_nn (H_bounded ⟨j, by omega⟩)
      T_prev hT_nn
      ih_s2_int ih_s4_int
      ih2 ih4
    obtain ⟨hSX2_int, hSX4_int, hstep2, hstep4⟩ := hstep
    exact ⟨hSX2_int, hSX4_int, hstep2, hstep4⟩

/-! ## Reformulation of stochasticIntegral_at terms -/

/-- The i-th summand of stochasticIntegral_at at time u, when i+1 < n, equals
    H_i * (W(min(t_{i+1}, u)) - W(t_i)) when t_i ≤ u, else 0. -/
private lemma si_at_term_eq {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (i : Fin H.n) (h : (i : ℕ) + 1 < H.n) (u : ℝ) (ω : Ω) :
    (if H.times ⟨(i : ℕ) + 1, h⟩ ≤ u then
       H.values i ω * (W.process (H.times ⟨(i : ℕ) + 1, h⟩) ω - W.process (H.times i) ω)
     else if H.times i ≤ u then
       H.values i ω * (W.process u ω - W.process (H.times i) ω)
     else 0) =
    if H.times i ≤ u then
      H.values i ω * (W.process (min (H.times ⟨(i : ℕ) + 1, h⟩) u) ω -
                       W.process (H.times i) ω)
    else 0 := by
  by_cases h1 : H.times ⟨(i : ℕ) + 1, h⟩ ≤ u
  · have hti_le : H.times i ≤ u :=
      le_trans (le_of_lt (H.increasing i ⟨(i : ℕ) + 1, h⟩ (Fin.mk_lt_mk.mpr (by omega)))) h1
    simp only [if_pos h1, if_pos hti_le, min_eq_left h1]
  · push_neg at h1
    by_cases h2 : H.times i ≤ u
    · simp only [if_neg (not_le.mpr h1), if_pos h2, min_eq_right (le_of_lt h1)]
    · simp only [if_neg (not_le.mpr h1), if_neg h2]

/-- The term-wise difference of stochasticIntegral_at at times t and s equals
    a clipped BM increment contribution. -/
private lemma si_at_term_diff {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (i : Fin H.n) (h : (i : ℕ) + 1 < H.n) (s t : ℝ) (hst : s ≤ t) (ω : Ω) :
    (if H.times i ≤ t then
      H.values i ω * (W.process (min (H.times ⟨(i : ℕ) + 1, h⟩) t) ω -
                       W.process (H.times i) ω)
    else 0) -
    (if H.times i ≤ s then
      H.values i ω * (W.process (min (H.times ⟨(i : ℕ) + 1, h⟩) s) ω -
                       W.process (H.times i) ω)
    else 0) =
    if max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, h⟩) t then
      H.values i ω * (W.process (min (H.times ⟨(i : ℕ) + 1, h⟩) t) ω -
                       W.process (max (H.times i) s) ω)
    else 0 := by
  set ti := H.times i
  set ti1 := H.times ⟨(i : ℕ) + 1, h⟩
  have hti_lt_ti1 : ti < ti1 := H.increasing i ⟨(i : ℕ) + 1, h⟩ (Fin.mk_lt_mk.mpr (by omega))
  by_cases h_ti_le_t : ti ≤ t
  · -- ti ≤ t
    rw [if_pos h_ti_le_t]
    by_cases h_ti_le_s : ti ≤ s
    · -- ti ≤ s ≤ t
      rw [if_pos h_ti_le_s]
      have hmax : max ti s = s := max_eq_right h_ti_le_s
      by_cases h_active : s < min ti1 t
      · -- Active: s < min(ti1, t)
        have hmin_s : min ti1 s = s :=
          min_eq_right (le_of_lt (lt_of_lt_of_le h_active (min_le_left _ _)))
        rw [if_pos (show max ti s < min ti1 t by rw [hmax]; exact h_active)]
        rw [hmin_s, hmax]; ring
      · -- Inactive: min(ti1,t) ≤ s
        push_neg at h_active
        rw [if_neg (show ¬(max ti s < min ti1 t) by rw [hmax]; exact not_lt.mpr h_active)]
        suffices h_eq : min ti1 t = min ti1 s by rw [h_eq]; ring
        by_cases hle : ti1 ≤ s
        · rw [min_eq_left (le_trans hle hst), min_eq_left hle]
        · push_neg at hle
          by_cases htl : ti1 ≤ t
          · exact absurd (min_eq_left htl ▸ h_active) (not_le.mpr hle)
          · push_neg at htl
            have : s = t := le_antisymm hst (min_eq_right (le_of_lt htl) ▸ h_active)
            subst this; rfl
    · -- s < ti ≤ t
      push_neg at h_ti_le_s
      rw [if_neg (not_le.mpr h_ti_le_s), sub_zero]
      have hmax : max ti s = ti := max_eq_left (le_of_lt h_ti_le_s)
      by_cases h_active : ti < min ti1 t
      · rw [if_pos (show max ti s < min ti1 t by rw [hmax]; exact h_active), hmax]
      · push_neg at h_active -- min ti1 t ≤ ti
        rw [if_neg (show ¬(max ti s < min ti1 t) by rw [hmax]; exact not_lt.mpr h_active)]
        -- min(ti1,t) ≤ ti and ti < ti1 → t ≤ ti → ti = t
        have h_min : min ti1 t = t := by
          by_cases ht : ti1 ≤ t
          · exact absurd (min_eq_left ht ▸ h_active) (not_le.mpr hti_lt_ti1)
          · push_neg at ht; exact min_eq_right (le_of_lt ht)
        rw [h_min, show ti = t from le_antisymm h_ti_le_t (h_min ▸ h_active), sub_self, mul_zero]
  · -- t < ti → s < ti too, both 0
    push_neg at h_ti_le_t
    rw [if_neg (not_le.mpr h_ti_le_t),
        if_neg (not_le.mpr (lt_of_le_of_lt hst h_ti_le_t)), sub_self]
    rw [if_neg (show ¬(max ti s < min ti1 t) by
      rw [not_lt]; exact le_trans (min_le_right _ _)
        (le_trans (le_of_lt h_ti_le_t) (le_max_left _ _)))]

/-- Disjoint ordered subintervals of [lo, hi] have total length ≤ hi - lo.
    Used to bound the total clipped time in the quartic bound proof. -/
private lemma ordered_interval_sum_le :
    ∀ (n : ℕ) {a b : Fin n → ℝ} {lo hi : ℝ},
    lo ≤ hi →
    (∀ i, lo ≤ a i) → (∀ i, b i ≤ hi) →
    (∀ i, a i ≤ b i) →
    (∀ i j : Fin n, i < j → b i ≤ a j) →
    ∑ i : Fin n, (b i - a i) ≤ hi - lo := by
  intro n
  induction n with
  | zero => intros; simp; linarith
  | succ n ih =>
    intro a b lo hi hlo_hi h_lo h_hi h_pos h_ordered
    rw [Fin.sum_univ_castSucc]
    -- Apply IH to first n intervals with upper bound = a (Fin.last n)
    have hpre := ih (a := fun i => a (Fin.castSucc i)) (b := fun i => b (Fin.castSucc i))
      (lo := lo) (hi := a (Fin.last n))
      (h_lo (Fin.last n))
      (fun i => h_lo _)
      (fun i => h_ordered _ _ (Fin.castSucc_lt_last i))
      (fun i => h_pos _)
      (fun i j hij => h_ordered _ _ (show Fin.castSucc i < Fin.castSucc j by
        simp only [Fin.lt_def, Fin.val_castSucc]; exact hij))
    linarith [h_pos (Fin.last n), h_hi (Fin.last n)]

/-- Total clipped time for a SimpleProcess partition intersecting [s, t] is ≤ t - s.
    The clipped intervals [max(t_i, s), min(t_{i+1}, t)] are disjoint subintervals of [s, t]. -/
private lemma clipped_time_total_le {F : Filtration Ω ℝ}
    (H : SimpleProcess F) (s t : ℝ) (hst : s ≤ t) :
    ∑ i : Fin H.n, (if h : (i : ℕ) + 1 < H.n then
        if max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, h⟩) t then
          min (H.times ⟨(i : ℕ) + 1, h⟩) t - max (H.times i) s
        else 0
      else 0) ≤ t - s := by
  -- Use ordered_interval_sum_le with a'(i) = min(max(t_i, s), t)
  set δ : Fin H.n → ℝ := fun i => if h : (i : ℕ) + 1 < H.n then
      if max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, h⟩) t then
        min (H.times ⟨(i : ℕ) + 1, h⟩) t - max (H.times i) s
      else 0
    else 0
  set a' : Fin H.n → ℝ := fun i => min (max (H.times i) s) t
  -- δ(i) ≥ 0
  have hδ_nn : ∀ i, 0 ≤ δ i := by
    intro i; simp only [δ]
    by_cases hi : (i : ℕ) + 1 < H.n
    · simp only [dif_pos hi]
      by_cases hact : max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, hi⟩) t
      · simp only [if_pos hact]; linarith
      · simp only [if_neg hact]; exact le_refl 0
    · simp only [dif_neg hi]; exact le_refl 0
  -- Convert sum to (a' + δ) - a' form
  have hconv : (∑ i : Fin H.n, δ i) = ∑ i : Fin H.n, ((a' i + δ i) - a' i) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hconv]
  apply ordered_interval_sum_le H.n hst
  · -- s ≤ a'(i)
    exact fun i => le_min (le_max_right _ _) hst
  · -- a'(i) + δ(i) ≤ t
    intro i; simp only [a', δ]
    by_cases hi : (i : ℕ) + 1 < H.n
    · simp only [dif_pos hi]
      by_cases hact : max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, hi⟩) t
      · simp only [if_pos hact]
        have : min (max (H.times i) s) t = max (H.times i) s :=
          min_eq_left (le_of_lt (lt_of_lt_of_le hact (min_le_right _ _)))
        rw [this]; linarith [min_le_right (H.times ⟨(i : ℕ) + 1, hi⟩) t]
      · simp only [if_neg hact, add_zero]; exact min_le_right _ _
    · simp only [dif_neg hi, add_zero]; exact min_le_right _ _
  · -- a'(i) ≤ a'(i) + δ(i)
    exact fun i => le_add_of_nonneg_right (hδ_nn i)
  · -- Ordering: a'(i) + δ(i) ≤ a'(j) for i < j
    intro i j hij
    simp only [a', δ]
    by_cases hi : (i : ℕ) + 1 < H.n
    · simp only [dif_pos hi]
      by_cases hact : max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, hi⟩) t
      · simp only [if_pos hact]
        -- LHS = min(max(t_i, s), t) + (min(t_{i+1}, t) - max(t_i, s)) = min(t_{i+1}, t)
        have ha_eq : min (max (H.times i) s) t = max (H.times i) s :=
          min_eq_left (le_of_lt (lt_of_lt_of_le hact (min_le_right _ _)))
        rw [ha_eq]
        -- Need: max(t_i,s) + (min(t_{i+1},t) - max(t_i,s)) ≤ min(max(t_j,s), t)
        -- i.e., min(t_{i+1},t) ≤ min(max(t_j,s), t)
        have h_i1_le_j : H.times ⟨(i : ℕ) + 1, hi⟩ ≤ H.times j := by
          have h_le : (i : ℕ) + 1 ≤ (j : ℕ) := Nat.succ_le_of_lt (Fin.lt_def.mp hij)
          rcases Nat.eq_or_lt_of_le h_le with heq | hgt
          · exact le_of_eq (congrArg H.times (Fin.ext heq))
          · exact le_of_lt (H.increasing _ _ (Fin.mk_lt_mk.mpr hgt))
        calc max (H.times i) s + (min (H.times ⟨(i : ℕ) + 1, hi⟩) t - max (H.times i) s)
            = min (H.times ⟨(i : ℕ) + 1, hi⟩) t := by ring
          _ ≤ min (max (H.times j) s) t :=
            min_le_min_right t (le_trans h_i1_le_j (le_max_left _ _))
      · simp only [if_neg hact, add_zero]
        exact min_le_min_right t (max_le_max_right s
          (le_of_lt (H.increasing i j hij)))
    · simp only [dif_neg hi, add_zero]
      exact min_le_min_right t (max_le_max_right s
        (le_of_lt (H.increasing i j hij)))

/-! ## Transfer infrastructure -/

/-- Projection contraction: clamping to [-M, M] doesn't increase distance to points in [-M, M]. -/
private lemma clamp_contraction_sq (M x y : ℝ) (hM : 0 ≤ M) (hy : |y| ≤ M) :
    (max (-M) (min M x) - x) ^ 2 ≤ (x - y) ^ 2 := by
  -- Strategy: |clamp(x) - x| ≤ |x - y| when |y| ≤ M, then square both sides
  obtain ⟨hy_lo, hy_hi⟩ := abs_le.mp hy  -- -M ≤ y ∧ y ≤ M
  suffices h : |max (-M) (min M x) - x| ≤ |x - y| by
    calc (max (-M) (min M x) - x) ^ 2
        = |max (-M) (min M x) - x| ^ 2 := (sq_abs _).symm
      _ ≤ |x - y| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (x - y) ^ 2 := sq_abs _
  by_cases hx_le : x ≤ M
  · by_cases hx_ge : -M ≤ x
    · -- |x| ≤ M: clamp(x) = x, so |clamp(x) - x| = 0
      rw [min_eq_right hx_le, max_eq_right hx_ge, sub_self, abs_zero]
      exact abs_nonneg _
    · -- x < -M: clamp(x) = -M, |-M - x| = -M - x, |x - y| = y - x ≥ -M - x
      push_neg at hx_ge
      rw [min_eq_right hx_le, max_eq_left (le_of_lt hx_ge)]
      rw [abs_of_nonneg (by linarith)]  -- -M - x ≥ 0
      rw [abs_of_nonpos (by linarith)]  -- x - y ≤ 0 (x < -M ≤ y)
      linarith
  · -- x > M: clamp(x) = M, |M - x| = x - M, |x - y| = x - y ≥ x - M
    push_neg at hx_le
    rw [min_eq_left (le_of_lt hx_le), max_eq_right (by linarith)]
    rw [abs_of_nonpos (by linarith)]  -- M - x ≤ 0
    rw [abs_of_nonneg (by linarith)]  -- x - y ≥ 0 (x > M ≥ y)
    linarith

theorem stoch_integral_bounded_approx {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ_nn : 0 ≤ Mσ) (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ) :
    ∃ (approx : ℕ → SimpleProcess F),
      (∀ n, ∀ i : Fin (approx n).n,
        @Measurable Ω ℝ (X.BM.F.σ_algebra ((approx n).times i)) _ ((approx n).values i)) ∧
      (∀ n, ∀ i : Fin (approx n).n, ∀ ω, |(approx n).values i ω| ≤ Mσ) ∧
      (∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i) ∧
      (∀ t : ℝ, t ≥ 0 →
        Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
                                         X.stoch_integral t ω)^2 ∂μ)
          Filter.atTop (nhds 0)) := by
  -- Step 1: Extract existing approximants from L² limit construction
  obtain ⟨orig, horig_adapt, horig_bdd, horig_nn, horig_conv, _horig_iso, horig_integrand⟩ :=
    X.stoch_integral_is_L2_limit
  -- Step 2: Define clamped approximants with values in [-Mσ, Mσ]
  set clamp : ℕ → SimpleProcess F := fun n => {
    n := (orig n).n
    times := (orig n).times
    values := fun i ω => max (-Mσ) (min Mσ ((orig n).values i ω))
    increasing := (orig n).increasing
    adapted := fun i => by
      apply Measurable.max measurable_const
      exact Measurable.min measurable_const ((orig n).adapted i)
  }
  refine ⟨clamp, ?_, ?_, ?_, ?_⟩
  · -- Property 1: BM.F-adapted
    intro n i
    show @Measurable Ω ℝ (X.BM.F.σ_algebra ((orig n).times i)) _
      (fun ω => max (-Mσ) (min Mσ ((orig n).values i ω)))
    letI : MeasurableSpace Ω := X.BM.F.σ_algebra ((orig n).times i)
    exact Measurable.max measurable_const
      (Measurable.min measurable_const (horig_adapt n i))
  · -- Property 2: Uniform bound |values| ≤ Mσ
    intro n i ω
    show |max (-Mσ) (min Mσ ((orig n).values i ω))| ≤ Mσ
    rw [abs_le]
    constructor
    · linarith [le_max_left (-Mσ) (min Mσ ((orig n).values i ω))]
    · exact le_trans (max_le_max_left _ (min_le_left Mσ _))
        (le_of_eq (max_eq_right (neg_le_self hMσ_nn)))
  · -- Property 3: Nonneg times (inherited)
    intro n i; exact horig_nn n i
  · -- Property 4: L² convergence of clamped SI → stoch_integral
    intro t ht
    -- Strategy: E[|SI(clamp) - SI|²] ≤ 2·E[|SI(clamp) - SI(orig)|²] + 2·E[|SI(orig) - SI|²]
    -- Second term → 0 by horig_conv. First term → 0 by projection contraction + integrand conv.
    -- Step A: Construct difference process D with values = clamp(v) - v, same partition
    -- Step B: SI(clamp)(t) - SI(orig)(t) = SI(D)(t)
    -- Step C: E[SI(D)(t)²] = E[∫ valueAtTime(D)²] by isometry_at
    -- Step D: ∫ valueAtTime(D)² ≤ ∫ (valueAtTime(orig) - σ)² by projection contraction
    -- Step E: E[∫(valueAtTime(orig) - σ)²] → 0 by horig_integrand
    -- Step F: Triangle inequality gives the result
    -- Upper bound: 2 * diff_bound(n) + 2 * orig_error(n) where both → 0
    set diff_bound : ℕ → ℝ := fun n =>
      ∫ ω, (∫ s in Set.Icc 0 t,
        (SimpleProcess.valueAtTime (orig n) s ω - X.diffusion s ω) ^ 2 ∂volume) ∂μ
    set orig_error : ℕ → ℝ := fun n =>
      ∫ ω, (SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω -
        X.stoch_integral t ω) ^ 2 ∂μ
    apply squeeze_zero (g := fun n => 2 * diff_bound n + 2 * orig_error n)
    · intro n; exact integral_nonneg (fun ω => sq_nonneg _)
    · -- Bound: E[|SI(clamp) - SI|²] ≤ 2 * diff_bound + 2 * orig_error
      intro n
      -- Pointwise triangle: (a - c)² ≤ 2(a-b)² + 2(b-c)²
      have h_tri : ∀ ω,
          (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
            X.stoch_integral t ω) ^ 2 ≤
          2 * (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
            SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2 +
          2 * (SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω -
            X.stoch_integral t ω) ^ 2 := fun ω => by
        nlinarith [sq_nonneg (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
            SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω -
            (SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω -
            X.stoch_integral t ω))]
      -- Construct difference process: values = clamp(v) - v, same partition
      set diff_n : SimpleProcess F := {
        n := (orig n).n, times := (orig n).times,
        values := fun i ω => max (-Mσ) (min Mσ ((orig n).values i ω)) - (orig n).values i ω,
        increasing := (orig n).increasing,
        adapted := fun i => (Measurable.max measurable_const
          (Measurable.min measurable_const ((orig n).adapted i))).sub ((orig n).adapted i)
      }
      -- SI(clamp n) - SI(orig n) = SI(diff_n) pointwise
      have hSI_diff : ∀ ω,
          SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
          SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω =
          SimpleProcess.stochasticIntegral_at diff_n X.BM t ω := by
        intro ω
        simp only [SimpleProcess.stochasticIntegral_at, clamp, diff_n,
          ← Finset.sum_sub_distrib]
        congr 1; ext i
        by_cases hi : (i : ℕ) + 1 < (orig n).n
        · simp only [dif_pos hi]
          by_cases hf : (orig n).times ⟨(i : ℕ) + 1, hi⟩ ≤ t
          · simp only [if_pos hf]; ring
          · simp only [if_neg hf]
            by_cases hs : (orig n).times i ≤ t
            · simp only [if_pos hs]; ring
            · simp only [if_neg hs]; ring
        · simp only [dif_neg hi]; ring
      -- diff_n properties for isometry_at
      have hdiff_adapt : ∀ i : Fin diff_n.n,
          @Measurable Ω ℝ (X.BM.F.σ_algebra (diff_n.times i)) _ (diff_n.values i) := by
        intro i
        show @Measurable Ω ℝ (X.BM.F.σ_algebra ((orig n).times i)) _
          (fun ω => max (-Mσ) (min Mσ ((orig n).values i ω)) - (orig n).values i ω)
        letI : MeasurableSpace Ω := X.BM.F.σ_algebra ((orig n).times i)
        exact (Measurable.max measurable_const
          (Measurable.min measurable_const (horig_adapt n i))).sub (horig_adapt n i)
      have hdiff_bdd : ∀ i : Fin diff_n.n, ∃ C : ℝ, ∀ ω, |diff_n.values i ω| ≤ C := by
        intro i; obtain ⟨Ci, hCi⟩ := horig_bdd n i
        refine ⟨Ci, fun ω => ?_⟩
        show |max (-Mσ) (min Mσ ((orig n).values i ω)) - (orig n).values i ω| ≤ Ci
        -- |clamp(x) - x| ≤ |x| since clamp projects onto [-M,M] ∋ 0
        have habs : |max (-Mσ) (min Mσ ((orig n).values i ω)) - (orig n).values i ω| ≤
            |(orig n).values i ω| := by
          set v := (orig n).values i ω
          by_cases h1 : -Mσ ≤ v
          · by_cases h2 : v ≤ Mσ
            · simp [min_eq_right h2, max_eq_right h1]
            · push_neg at h2
              rw [min_eq_left (le_of_lt h2), max_eq_right (by linarith)]
              rw [show Mσ - v = -(v - Mσ) from by ring, abs_neg, abs_of_nonneg (by linarith)]
              linarith [le_abs_self v]
          · push_neg at h1
            rw [min_eq_right (le_trans (le_of_lt h1) (by linarith))]
            rw [max_eq_left (le_of_lt h1)]
            rw [show -Mσ - v = -(v + Mσ) from by ring, abs_neg, abs_of_nonpos (by linarith)]
            rw [abs_of_nonpos (by linarith)]; linarith
        linarith [habs, hCi ω]
      have hdiff_nn : ∀ i : Fin diff_n.n, 0 ≤ diff_n.times i := horig_nn n
      -- Apply isometry: E[SI(diff_n)(t)²] = E[∫₀ᵗ valueAtTime(diff_n)²]
      have hiso := SimpleProcess.isometry_at diff_n X.BM hdiff_adapt hdiff_bdd hdiff_nn t ht
      -- valueAtTime(diff_n)(s)² ≤ (valueAtTime(orig n)(s) - σ(s))² by projection contraction
      have hval_bound : ∀ s' ω',
          (SimpleProcess.valueAtTime diff_n s' ω') ^ 2 ≤
          (SimpleProcess.valueAtTime (orig n) s' ω' - X.diffusion s' ω') ^ 2 := by
        intro s' ω'
        simp only [SimpleProcess.valueAtTime, diff_n]
        split
        · next h => exact clamp_contraction_sq Mσ _ _ hMσ_nn (hMσ s' ω')
        · simp [sq_nonneg]
      -- Inner integrability: bounded step functions on [0,t]
      have hIcc_finite : volume (Set.Icc (0 : ℝ) t) ≠ ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      have hinner_diff_int : ∀ ω',
          IntegrableOn (fun s => (SimpleProcess.valueAtTime diff_n s ω') ^ 2)
            (Set.Icc 0 t) volume := fun ω' => by
        obtain ⟨C, _, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded diff_n hdiff_bdd
        exact (integrableOn_const hIcc_finite :
          IntegrableOn (fun _ : ℝ => C ^ 2) _ _).mono'
          (((SimpleProcess.valueAtTime_jointly_measurable diff_n).comp
            (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable
          (ae_of_all _ fun s => by
            simp only [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hC s ω') 2)
      have hinner_orig_int : ∀ ω',
          IntegrableOn (fun s => (SimpleProcess.valueAtTime (orig n) s ω' -
            X.diffusion s ω') ^ 2) (Set.Icc 0 t) volume := fun ω' => by
        obtain ⟨C, _, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded (orig n) (horig_bdd n)
        exact (integrableOn_const hIcc_finite :
          IntegrableOn (fun _ : ℝ => (C + Mσ) ^ 2) _ _).mono'
          ((((SimpleProcess.valueAtTime_jointly_measurable (orig n)).comp
            (measurable_id.prodMk measurable_const)).sub
            (X.diffusion_jointly_measurable.comp (measurable_id.prodMk measurable_const))).pow_const 2
            ).aestronglyMeasurable
          (ae_of_all _ fun s => by
            simp only [Real.norm_eq_abs, abs_pow]
            apply pow_le_pow_left₀ (abs_nonneg _)
            calc |SimpleProcess.valueAtTime (orig n) s ω' - X.diffusion s ω'|
                ≤ |SimpleProcess.valueAtTime (orig n) s ω'| + |X.diffusion s ω'| := by
                  simp only [← Real.norm_eq_abs]; exact norm_sub_le _ _
              _ ≤ C + Mσ := add_le_add (hC s ω') (hMσ s ω'))
      -- E[SI(diff_n)(t)²] ≤ diff_bound n
      -- h_diff_L2: E[SI(diff_n)²] ≤ diff_bound n
      -- By isometry, LHS = E[∫ vT(diff_n)²]. By projection contraction,
      -- vT(diff_n)² ≤ (vT(orig)-σ)² pointwise. Integrate over [0,t] then over Ω.
      have h_diff_L2 : ∫ ω, (SimpleProcess.stochasticIntegral_at diff_n X.BM t ω) ^ 2 ∂μ ≤
          diff_bound n := by
        rw [hiso]
        -- Inner integral bound: for each ω, ∫ vT(diff_n)² ≤ ∫ (vT(orig)-σ)²
        have hinner_le : ∀ ω,
            ∫ s in Set.Icc 0 t, diff_n.valueAtTime s ω ^ 2 ∂volume ≤
            ∫ s in Set.Icc 0 t, ((orig n).valueAtTime s ω - X.diffusion s ω) ^ 2 ∂volume :=
          fun ω => setIntegral_mono_on (hinner_diff_int ω) (hinner_orig_int ω)
            measurableSet_Icc (fun s' _ => hval_bound s' ω)
        -- The inner integral for diff_n is a finite sum of bounded terms → integrable in ω
        have hf_int : Integrable (fun ω =>
            ∫ s in Set.Icc 0 t, diff_n.valueAtTime s ω ^ 2 ∂volume) μ := by
          obtain ⟨C_d, hC_d_nn, hC_d⟩ := SimpleProcess.valueAtTime_uniform_bounded diff_n hdiff_bdd
          apply Integrable.mono' (integrable_const (C_d ^ 2 * t))
          · have hsm := ((SimpleProcess.valueAtTime_jointly_measurable diff_n).pow_const 2
                ).stronglyMeasurable.integral_prod_left'
                (μ := volume.restrict (Set.Icc 0 t))
            exact hsm.aestronglyMeasurable
          · exact ae_of_all μ (fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg
                (setIntegral_nonneg measurableSet_Icc (fun s _ => sq_nonneg _))]
              calc ∫ s in Set.Icc 0 t, diff_n.valueAtTime s ω ^ 2 ∂volume
                  ≤ ∫ s in Set.Icc 0 t, C_d ^ 2 ∂volume :=
                    setIntegral_mono_on (hinner_diff_int ω)
                      (integrableOn_const hIcc_finite)
                      measurableSet_Icc (fun s _ => by
                        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hC_d s ω) 2)
                _ = C_d ^ 2 * t := by
                    rw [setIntegral_const, smul_eq_mul, mul_comm]
                    congr 1
                    show (volume (Set.Icc (0 : ℝ) t)).toReal = t
                    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
                    ring)
        -- g integrable: bounded inner integral
        have hg_int : Integrable (fun ω =>
            ∫ s in Set.Icc 0 t, ((orig n).valueAtTime s ω - X.diffusion s ω) ^ 2 ∂volume) μ := by
          obtain ⟨C, hC_nn, hC⟩ := SimpleProcess.valueAtTime_uniform_bounded (orig n) (horig_bdd n)
          apply Integrable.mono' (integrable_const ((C + Mσ) ^ 2 * t))
          · have hsm := ((SimpleProcess.valueAtTime_jointly_measurable (orig n)).sub
                X.diffusion_jointly_measurable).pow_const 2
                |>.stronglyMeasurable.integral_prod_left'
                (μ := volume.restrict (Set.Icc 0 t))
            exact hsm.aestronglyMeasurable
          · exact ae_of_all μ (fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg
                (setIntegral_nonneg measurableSet_Icc (fun s _ => sq_nonneg _))]
              calc ∫ s in Set.Icc 0 t, ((orig n).valueAtTime s ω -
                      X.diffusion s ω) ^ 2 ∂volume
                  ≤ ∫ s in Set.Icc 0 t, (C + Mσ) ^ 2 ∂volume :=
                    setIntegral_mono_on (hinner_orig_int ω)
                      (integrableOn_const hIcc_finite)
                      measurableSet_Icc (fun s _ => by
                        have h1 : |SimpleProcess.valueAtTime (orig n) s ω - X.diffusion s ω|
                            ≤ C + Mσ := calc
                          |SimpleProcess.valueAtTime (orig n) s ω - X.diffusion s ω|
                              ≤ |SimpleProcess.valueAtTime (orig n) s ω| +
                                |X.diffusion s ω| := by
                                simp only [← Real.norm_eq_abs]; exact norm_sub_le _ _
                            _ ≤ C + Mσ := add_le_add (hC s ω) (hMσ s ω)
                        exact sq_le_sq' (by linarith [(abs_le.mp h1).1]) (abs_le.mp h1).2)
                _ = (C + Mσ) ^ 2 * t := by
                    rw [setIntegral_const, smul_eq_mul, mul_comm]
                    congr 1
                    show (volume (Set.Icc (0 : ℝ) t)).toReal = t
                    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
                    ring)
        exact integral_mono hf_int hg_int hinner_le
      -- Integrability for wiring the triangle inequality
      have h_clamp_adapt : ∀ i : Fin (clamp n).n,
          @Measurable Ω ℝ (X.BM.F.σ_algebra ((clamp n).times i)) _ ((clamp n).values i) := by
        intro i
        show @Measurable Ω ℝ (X.BM.F.σ_algebra ((orig n).times i)) _
          (fun ω => max (-Mσ) (min Mσ ((orig n).values i ω)))
        letI : MeasurableSpace Ω := X.BM.F.σ_algebra ((orig n).times i)
        exact Measurable.max measurable_const
          (Measurable.min measurable_const (horig_adapt n i))
      have h_clamp_bdd : ∀ i : Fin (clamp n).n, ∃ C : ℝ, ∀ ω, |(clamp n).values i ω| ≤ C := by
        intro i; exact ⟨Mσ, fun ω => by
          show |max (-Mσ) (min Mσ ((orig n).values i ω))| ≤ Mσ
          rw [abs_le]; constructor
          · linarith [le_max_left (-Mσ) (min Mσ ((orig n).values i ω))]
          · exact le_trans (max_le_max_left _ (min_le_left Mσ _))
              (le_of_eq (max_eq_right (neg_le_self hMσ_nn)))⟩
      have h_clamp_nn : ∀ i : Fin (clamp n).n, 0 ≤ (clamp n).times i := horig_nn n
      have h_diff_sq_int : Integrable (fun ω =>
          (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
            SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2) μ := by
        have heq : (fun ω => (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
            SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2) =
            (fun ω => (SimpleProcess.stochasticIntegral_at diff_n X.BM t ω) ^ 2) := by
          ext ω; rw [← hSI_diff]
        rw [heq]
        have h := SimpleProcess.stochasticIntegral_at_sub_sq_integrable diff_n X.BM
          hdiff_adapt hdiff_bdd hdiff_nn (fun _ => 0) (integrable_const 0) (by simp) t ht
        simp only [sub_zero] at h; exact h
      have h_orig_sub_sq_int : Integrable (fun ω =>
          (SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω -
            X.stoch_integral t ω) ^ 2) μ :=
        SimpleProcess.stochasticIntegral_at_sub_sq_integrable (orig n) X.BM
          (horig_adapt n) (horig_bdd n) (horig_nn n)
          (X.stoch_integral t) (X.stoch_integral_integrable t ht)
          (X.stoch_integral_sq_integrable t ht) t ht
      -- Calc: ∫(SI(clamp)-SI)² ≤ 2·∫(SI(clamp)-SI(orig))² + 2·∫(SI(orig)-SI)² ≤ 2·diff + 2·orig
      calc ∫ ω, (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
                  X.stoch_integral t ω) ^ 2 ∂μ
          ≤ ∫ ω, (2 * (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
                    SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2 +
                  2 * (SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω -
                    X.stoch_integral t ω) ^ 2) ∂μ := by
            apply integral_mono
              (SimpleProcess.stochasticIntegral_at_sub_sq_integrable (clamp n) X.BM
                h_clamp_adapt h_clamp_bdd h_clamp_nn
                (X.stoch_integral t) (X.stoch_integral_integrable t ht)
                (X.stoch_integral_sq_integrable t ht) t ht)
              ((h_diff_sq_int.const_mul 2).add (h_orig_sub_sq_int.const_mul 2))
              h_tri
        _ = 2 * ∫ ω, (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
                    SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2 ∂μ +
            2 * ∫ ω, (SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω -
                    X.stoch_integral t ω) ^ 2 ∂μ := by
            rw [integral_add (h_diff_sq_int.const_mul 2) (h_orig_sub_sq_int.const_mul 2)]
            simp only [integral_const_mul]
        _ ≤ 2 * diff_bound n + 2 * orig_error n := by
            have h1 : ∫ ω, (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
                SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2 ∂μ ≤
                diff_bound n := by
              have heq : (fun ω => (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
                  SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2) =
                  (fun ω => (SimpleProcess.stochasticIntegral_at diff_n X.BM t ω) ^ 2) := by
                ext ω; rw [← hSI_diff]
              rw [show ∫ ω, (SimpleProcess.stochasticIntegral_at (clamp n) X.BM t ω -
                  SimpleProcess.stochasticIntegral_at (orig n) X.BM t ω) ^ 2 ∂μ =
                  ∫ ω, (SimpleProcess.stochasticIntegral_at diff_n X.BM t ω) ^ 2 ∂μ from by
                congr 1]
              exact h_diff_L2
            linarith
    · -- RHS → 0: 2 * diff_bound + 2 * orig_error → 0
      have h1 : Filter.Tendsto diff_bound Filter.atTop (nhds 0) := horig_integrand t ht
      have h2 : Filter.Tendsto orig_error Filter.atTop (nhds 0) := horig_conv t ht
      have h3 : Filter.Tendsto (fun n => 2 * diff_bound n + 2 * orig_error n)
          Filter.atTop (nhds 0) := by
        have := (h1.const_mul 2).add (h2.const_mul 2)
        simp only [mul_zero, add_zero] at this; exact this
      exact h3

/-- Quartic bound for simple process stochastic integral increments.

    For a SimpleProcess H with |H(i,ω)| ≤ M for all i,ω:
    E[(SI_H(t) - SI_H(s))⁴] ≤ 3 · M⁴ · (t - s)²

    Proof sketch: SI_H(t) - SI_H(s) equals a finite sum of H_i · ΔW_i over
    partition intervals intersecting [s, t]. This sub-sum has the same martingale
    structure as in `quartic_sum_bound`, with total time = t - s. -/
theorem simple_integral_increment_quartic_bound
    {F : Filtration Ω ℝ} [IsProbabilityMeasure μ]
    (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (hH_adapted : ∀ i : Fin H.n,
      @Measurable Ω ℝ (W.F.σ_algebra (H.times i)) _ (H.values i))
    {M : ℝ} (hM : 0 ≤ M) (hH_bdd : ∀ i : Fin H.n, ∀ ω, |H.values i ω| ≤ M)
    (_hH_times_nn : ∀ i : Fin H.n, 0 ≤ H.times i)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (H.stochasticIntegral_at W t ω -
      H.stochasticIntegral_at W s ω)^4) μ ∧
    ∫ ω, (H.stochasticIntegral_at W t ω -
      H.stochasticIntegral_at W s ω)^4 ∂μ ≤ 3 * M^4 * (t - s)^2 := by
  -- Define clipped contribution and clipped time at each partition index
  set contrib : Fin H.n → Ω → ℝ := fun i ω =>
    if h : (i : ℕ) + 1 < H.n then
      if max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, h⟩) t then
        H.values i ω * (W.process (min (H.times ⟨(i : ℕ) + 1, h⟩) t) ω -
                         W.process (max (H.times i) s) ω)
      else 0
    else 0 with hcontrib_def
  set δt : Fin H.n → ℝ := fun i =>
    if h : (i : ℕ) + 1 < H.n then
      if max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, h⟩) t then
        min (H.times ⟨(i : ℕ) + 1, h⟩) t - max (H.times i) s
      else 0
    else 0 with hδt_def
  -- SI(t) - SI(s) = Σ contrib
  have hdiff : ∀ ω, H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω =
      ∑ i : Fin H.n, contrib i ω := by
    intro ω; simp only [SimpleProcess.stochasticIntegral_at, ← Finset.sum_sub_distrib]
    congr 1; ext i; simp only [contrib]
    by_cases hi : (i : ℕ) + 1 < H.n
    · simp only [dif_pos hi]
      rw [si_at_term_eq H W i hi t ω, si_at_term_eq H W i hi s ω]
      exact si_at_term_diff H W i hi s t hst ω
    · simp only [dif_neg hi, sub_self]
  -- Total time bound
  have htotal : ∑ i : Fin H.n, δt i ≤ t - s := clipped_time_total_le H s t hst
  -- δt ≥ 0
  have hδt_nn : ∀ i, 0 ≤ δt i := by
    intro i; simp only [δt]
    by_cases hi : (i : ℕ) + 1 < H.n
    · simp only [dif_pos hi]
      by_cases hact : max (H.times i) s < min (H.times ⟨(i : ℕ) + 1, hi⟩) t
      · simp only [if_pos hact]; linarith
      · simp only [if_neg hact]; exact le_refl 0
    · simp only [dif_neg hi]; exact le_refl 0
  -- Main induction: for j ≤ H.n, the partial clipped sum D_j satisfies quartic bound
  suffices hind : ∀ (j : ℕ) (hj : j ≤ H.n),
      Integrable (fun ω => (∑ i : Fin j, contrib ⟨i, by omega⟩ ω) ^ 2) μ ∧
      Integrable (fun ω => (∑ i : Fin j, contrib ⟨i, by omega⟩ ω) ^ 4) μ ∧
      (∫ ω, (∑ i : Fin j, contrib ⟨i, by omega⟩ ω) ^ 2 ∂μ ≤
        M ^ 2 * ∑ i : Fin j, δt ⟨i, by omega⟩) ∧
      (∫ ω, (∑ i : Fin j, contrib ⟨i, by omega⟩ ω) ^ 4 ∂μ ≤
        3 * M ^ 4 * (∑ i : Fin j, δt ⟨i, by omega⟩) ^ 2) by
    -- Extract at j = H.n and combine with total time bound
    obtain ⟨_, h4_int, _, h4_bound⟩ := hind H.n le_rfl
    constructor
    · exact h4_int.congr (ae_of_all _ fun ω => congr_arg (· ^ 4) (hdiff ω).symm)
    · calc ∫ ω, (H.stochasticIntegral_at W t ω - H.stochasticIntegral_at W s ω) ^ 4 ∂μ
          = ∫ ω, (∑ i : Fin H.n, contrib ⟨(i : ℕ), by omega⟩ ω) ^ 4 ∂μ := by
            congr 1; ext ω; exact congr_arg (· ^ 4) (hdiff ω)
        _ ≤ 3 * M ^ 4 * (∑ i : Fin H.n, δt ⟨(i : ℕ), by omega⟩) ^ 2 := h4_bound
        _ ≤ 3 * M ^ 4 * (t - s) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hδt_nn _) htotal 2
  -- Induction on j
  intro j; induction j with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (integrable_const (0 : ℝ)).congr (ae_of_all _ fun ω => by simp)
    · exact (integrable_const (0 : ℝ)).congr (ae_of_all _ fun ω => by simp)
    · simp
    · simp
  | succ j ih =>
    intro hj
    obtain ⟨ih_s2, ih_s4, ih2, ih4⟩ := ih (by omega)
    -- Split: D_{j+1} = D_j + contrib(j), T_{j+1} = T_j + δt(j)
    have hD_split : ∀ ω, (∑ i : Fin (j + 1), contrib ⟨(i : ℕ), by omega⟩ ω) =
        (∑ i : Fin j, contrib ⟨(i : ℕ), by omega⟩ ω) + contrib ⟨j, by omega⟩ ω := by
      intro ω; rw [Fin.sum_univ_castSucc]; rfl
    have hT_split : (∑ i : Fin (j + 1), δt ⟨(i : ℕ), by omega⟩) =
        (∑ i : Fin j, δt ⟨(i : ℕ), by omega⟩) + δt ⟨j, by omega⟩ := by
      rw [Fin.sum_univ_castSucc]; rfl
    -- Check if index j is active
    by_cases hjn : (j : ℕ) + 1 < H.n
    · by_cases hact : max (H.times ⟨j, by omega⟩) s <
          min (H.times ⟨j + 1, hjn⟩) t
      · -- ACTIVE CASE: apply quartic_step
        -- Abbreviations
        set a_j := max (H.times ⟨j, by omega⟩) s
        set b_j := min (H.times ⟨j + 1, hjn⟩) t
        -- contrib(j) = H_j * ΔW
        have hc_eq : ∀ ω, contrib ⟨j, by omega⟩ ω =
            H.values ⟨j, by omega⟩ ω *
              (W.toAdapted.process b_j ω - W.toAdapted.process a_j ω) := by
          intro ω; show (if h : j + 1 < H.n then _ else _) = _
          rw [dif_pos hjn]; exact if_pos hact
        have hδ_eq : δt ⟨j, by omega⟩ = b_j - a_j := by
          show (if h : j + 1 < H.n then _ else _) = _
          rw [dif_pos hjn]; exact if_pos hact
        -- D_prev measurability w.r.t. F_{a_j}
        have hD_meas : @Measurable Ω ℝ (W.F.σ_algebra a_j) _
            (fun ω => ∑ i : Fin j, contrib ⟨(i : ℕ), by omega⟩ ω) := by
          apply Finset.measurable_sum; intro i _
          by_cases hi_n : ((i : ℕ) : ℕ) + 1 < H.n
          · by_cases hi_a : max (H.times ⟨(i : ℕ), by omega⟩) s <
                min (H.times ⟨(i : ℕ) + 1, hi_n⟩) t
            · have hc_i : contrib ⟨(i : ℕ), by omega⟩ = fun ω =>
                  H.values ⟨(i : ℕ), by omega⟩ ω *
                    (W.process (min (H.times ⟨(i : ℕ) + 1, hi_n⟩) t) ω -
                     W.process (max (H.times ⟨(i : ℕ), by omega⟩) s) ω) := by
                ext ω; show (if h : _ then _ else _) = _
                rw [dif_pos hi_n]; exact if_pos hi_a
              rw [hc_i]
              have hti_le : H.times ⟨(i : ℕ), by omega⟩ ≤ H.times ⟨j, by omega⟩ :=
                le_of_lt (H.increasing ⟨(i : ℕ), by omega⟩ ⟨j, by omega⟩
                  (Fin.mk_lt_mk.mpr i.isLt))
              have hbi_le : min (H.times ⟨(i : ℕ) + 1, hi_n⟩) t ≤ a_j := by
                rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt i.isLt) with heq | hgt
                · exact (min_le_left _ _).trans ((le_of_eq (congrArg H.times (Fin.ext heq))).trans
                    (le_max_left _ _))
                · exact (min_le_left _ _).trans ((le_of_lt (H.increasing _ _
                    (Fin.mk_lt_mk.mpr hgt))).trans (le_max_left _ _))
              exact ((hH_adapted ⟨(i : ℕ), by omega⟩).mono
                (W.F.mono _ _ (hti_le.trans (le_max_left _ _))) le_rfl).mul
                (((W.toAdapted.adapted _).mono (W.F.mono _ _ hbi_le) le_rfl).sub
                 ((W.toAdapted.adapted _).mono
                   (W.F.mono _ _ (max_le_max_right s hti_le)) le_rfl))
            · have : contrib ⟨(i : ℕ), by omega⟩ = fun _ => (0 : ℝ) := by
                ext ω; show (if h : _ then _ else _) = _
                rw [dif_pos hi_n]; exact if_neg hi_a
              rw [this]; exact measurable_const
          · have : contrib ⟨(i : ℕ), by omega⟩ = fun _ => (0 : ℝ) := by
              ext ω; show (if h : _ then _ else _) = _; exact dif_neg hi_n
            rw [this]; exact measurable_const
        -- Function equalities (sum over j+1 = sum over j + contrib(j))
        have hfn2 : (fun ω => (∑ i : Fin (j + 1), contrib ⟨(i : ℕ), by omega⟩ ω) ^ 2) =
            (fun ω => ((∑ i : Fin j, contrib ⟨(i : ℕ), by omega⟩ ω) +
              H.values ⟨j, by omega⟩ ω *
                (W.toAdapted.process b_j ω - W.toAdapted.process a_j ω)) ^ 2) :=
          funext fun ω => by rw [hD_split, hc_eq]
        have hfn4 : (fun ω => (∑ i : Fin (j + 1), contrib ⟨(i : ℕ), by omega⟩ ω) ^ 4) =
            (fun ω => ((∑ i : Fin j, contrib ⟨(i : ℕ), by omega⟩ ω) +
              H.values ⟨j, by omega⟩ ω *
                (W.toAdapted.process b_j ω - W.toAdapted.process a_j ω)) ^ 4) :=
          funext fun ω => by rw [hD_split, hc_eq]
        -- Apply quartic_step
        have hstep := quartic_step W
          (fun ω => ∑ i : Fin j, contrib ⟨(i : ℕ), by omega⟩ ω)
          (H.values ⟨j, by omega⟩) a_j b_j
          (le_max_of_le_right hs) (le_of_lt hact) hD_meas
          ((hH_adapted ⟨j, by omega⟩).mono (W.F.mono _ _ (le_max_left _ _)) le_rfl)
          hM (hH_bdd ⟨j, by omega⟩)
          (∑ i : Fin j, δt ⟨(i : ℕ), by omega⟩)
          (Finset.sum_nonneg fun i _ => hδt_nn ⟨(i : ℕ), by omega⟩)
          ih_s2 ih_s4 ih2 ih4
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hfn2]; exact hstep.1
        · rw [hfn4]; exact hstep.2.1
        · rw [hfn2, hT_split, hδ_eq]; exact hstep.2.2.1
        · rw [hfn4, hT_split, hδ_eq]; exact hstep.2.2.2
      · -- INACTIVE (j+1 < H.n but interval doesn't cross [s,t])
        have hc0 : ∀ ω, contrib ⟨j, by omega⟩ ω = 0 := by
          intro ω; simp only [contrib, dif_pos hjn, if_neg hact]
        have hδ0 : δt ⟨j, by omega⟩ = 0 := by simp only [δt, dif_pos hjn, if_neg hact]
        rw [show (fun ω => (∑ i : Fin (j+1), contrib ⟨(i:ℕ), by omega⟩ ω) ^ 2) =
            (fun ω => (∑ i : Fin j, contrib ⟨(i:ℕ), by omega⟩ ω) ^ 2) from
            funext (fun ω => by rw [hD_split, hc0, add_zero]),
          show (fun ω => (∑ i : Fin (j+1), contrib ⟨(i:ℕ), by omega⟩ ω) ^ 4) =
            (fun ω => (∑ i : Fin j, contrib ⟨(i:ℕ), by omega⟩ ω) ^ 4) from
            funext (fun ω => by rw [hD_split, hc0, add_zero]),
          hT_split, hδ0, add_zero]
        exact ⟨ih_s2, ih_s4, ih2, ih4⟩
    · -- LAST INDEX (j+1 ≥ H.n)
      have hc0 : ∀ ω, contrib ⟨j, by omega⟩ ω = 0 := by
        intro ω; simp only [contrib, dif_neg hjn]
      have hδ0 : δt ⟨j, by omega⟩ = 0 := by simp only [δt, dif_neg hjn]
      rw [show (fun ω => (∑ i : Fin (j+1), contrib ⟨(i:ℕ), by omega⟩ ω) ^ 2) =
          (fun ω => (∑ i : Fin j, contrib ⟨(i:ℕ), by omega⟩ ω) ^ 2) from
          funext (fun ω => by rw [hD_split, hc0, add_zero]),
        show (fun ω => (∑ i : Fin (j+1), contrib ⟨(i:ℕ), by omega⟩ ω) ^ 4) =
          (fun ω => (∑ i : Fin j, contrib ⟨(i:ℕ), by omega⟩ ω) ^ 4) from
          funext (fun ω => by rw [hD_split, hc0, add_zero]),
        hT_split, hδ0, add_zero]
      exact ⟨ih_s2, ih_s4, ih2, ih4⟩

/-- Transfer of L⁴ bounds through L² convergence (Fatou transfer).

    If f_n → g in L² and E[f_n⁴] ≤ C for all n, then E[g⁴] ≤ C.

    Proof: L² convergence → convergence in measure → a.e. convergent
    subsequence → Fatou's lemma (`lintegral_liminf_le'`) → convert back.

    References: Mathlib `lintegral_liminf_le'` in
    `Mathlib.MeasureTheory.Integral.Lebesgue.Add`,
    `TendstoInMeasure.exists_seq_tendsto_ae` in
    `Mathlib.MeasureTheory.Function.ConvergenceInMeasure` -/
theorem integral_pow4_le_of_L2_convergence
    [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg_meas : AEStronglyMeasurable g μ)
    (hL2 : Filter.Tendsto (fun n => ∫ ω, (f n ω - g ω)^2 ∂μ) atTop (nhds 0))
    (hL2_int : ∀ n, Integrable (fun ω => (f n ω - g ω)^2) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ∫ ω, (f n ω)^4 ∂μ ≤ C)
    (hf4_int : ∀ n, Integrable (fun ω => (f n ω)^4) μ) :
    ∫ ω, (g ω)^4 ∂μ ≤ C := by
  -- Step 1: Extract a.e. convergent subsequence from L² convergence
  -- L² Bochner → eLpNorm → TendstoInMeasure → a.e. convergent subsequence
  have h_ae_subseq : ∃ (ns : ℕ → ℕ), StrictMono ns ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun k => f (ns k) ω) atTop (nhds (g ω)) := by
    -- L² Bochner convergence → TendstoInMeasure via Chebyshev → a.e. subseq
    apply TendstoInMeasure.exists_seq_tendsto_ae
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hε_sq_pos : (0 : ℝ) < ε ^ 2 := by positivity
    -- Step A: lintegral of (f n - g)² → 0 in ENNReal
    have h_lint_eq : ∀ n, ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ =
        ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ) :=
      fun n => (ofReal_integral_eq_lintegral_ofReal (hL2_int n)
        (ae_of_all _ fun ω => by positivity)).symm
    have h_tend_lint : Filter.Tendsto
        (fun n => ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ) atTop (nhds 0) := by
      simp_rw [h_lint_eq]
      have : Filter.Tendsto (fun n => ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ))
          atTop (nhds (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp hL2
      rwa [ENNReal.ofReal_zero] at this
    -- Step B: dividing by ofReal(ε²) preserves convergence to 0
    have hε2_pos : ENNReal.ofReal (ε ^ 2) ≠ 0 := by positivity
    have hε2_top : ENNReal.ofReal (ε ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_div_tend : Filter.Tendsto
        (fun n => (∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ) /
          ENNReal.ofReal (ε ^ 2)) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.div_const h_tend_lint (Or.inr hε2_pos)
      rwa [ENNReal.zero_div] at h
    -- Step C: bound μ {ε ≤ ‖f n - g‖} by the ratio via Chebyshev
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_div_tend
    · intro n; exact zero_le _
    · intro n
      -- {ε ≤ ‖f n - g‖} ⊆ {ε² ≤ (f n - g)²}
      have h_subset : {ω | (ε : ℝ) ≤ ‖f n ω - g ω‖} ⊆
          {ω | ε ^ 2 ≤ (f n ω - g ω) ^ 2} := by
        intro ω (hω : ε ≤ ‖f n ω - g ω‖)
        show ε ^ 2 ≤ (f n ω - g ω) ^ 2
        rw [Real.norm_eq_abs] at hω
        nlinarith [abs_nonneg (f n ω - g ω), sq_abs (f n ω - g ω)]
      -- Chebyshev: ofReal(ε²) * μ {ofReal(ε²) ≤ ofReal((f n - g)²)} ≤ ∫⁻ ofReal((f n - g)²)
      have h_aem : AEMeasurable (fun ω => ENNReal.ofReal ((f n ω - g ω) ^ 2)) μ :=
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((continuous_pow 2).measurable.comp_aemeasurable
            ((hf_meas n).sub hg_meas).aemeasurable)
      have h_cheb := mul_meas_ge_le_lintegral₀ h_aem (ENNReal.ofReal (ε ^ 2))
      -- Convert set: {ofReal(ε²) ≤ ofReal((f n - g)²)} = {ε² ≤ (f n - g)²}
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
  obtain ⟨ns, _, hns_ae⟩ := h_ae_subseq
  -- Step 2: (f(ns k))⁴ → g⁴ a.e. (continuity of x⁴ + a.e. convergence)
  have h_pow4_ae : ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun k => ENNReal.ofReal ((f (ns k) ω) ^ 4)) atTop
        (nhds (ENNReal.ofReal ((g ω) ^ 4))) := by
    filter_upwards [hns_ae] with ω hω
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_pow 4).tendsto _).comp hω)
  -- Step 3: Convert Bochner integral bounds to lintegral bounds
  have h_pow4_nn : ∀ n, 0 ≤ᵐ[μ] fun ω => (f n ω) ^ 4 :=
    fun n => ae_of_all _ fun ω => by positivity
  have h_lint_bound : ∀ k,
      ∫⁻ ω, ENNReal.ofReal ((f (ns k) ω) ^ 4) ∂μ ≤ ENNReal.ofReal C := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hf4_int (ns k)) (h_pow4_nn (ns k))]
    exact ENNReal.ofReal_le_ofReal (hbound (ns k))
  -- Step 4: Fatou's lemma (lintegral_liminf_le')
  have h_ae_meas : ∀ k,
      AEMeasurable (fun ω => ENNReal.ofReal ((f (ns k) ω) ^ 4)) μ :=
    fun k => ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_pow 4).measurable.comp_aemeasurable (hf_meas (ns k)).aemeasurable)
  -- liminf at each point = ofReal(g⁴) a.e. (convergent sequence has liminf = limit)
  have h_liminf_ae : ∀ᵐ ω ∂μ,
      Filter.liminf (fun k => ENNReal.ofReal ((f (ns k) ω) ^ 4)) atTop =
        ENNReal.ofReal ((g ω) ^ 4) := by
    filter_upwards [h_pow4_ae] with ω hω
    exact hω.liminf_eq
  -- Combine: Fatou + liminf bound → ∫⁻ ofReal(g⁴) ≤ ofReal(C)
  have h_lint_le : ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 4) ∂μ ≤ ENNReal.ofReal C :=
    calc ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 4) ∂μ
        ≤ ∫⁻ ω, Filter.liminf (fun k => ENNReal.ofReal ((f (ns k) ω) ^ 4)) atTop ∂μ :=
          lintegral_mono_ae (h_liminf_ae.mono fun ω hω => hω ▸ le_refl _)
      _ ≤ Filter.liminf (fun k => ∫⁻ ω, ENNReal.ofReal ((f (ns k) ω) ^ 4) ∂μ) atTop :=
          lintegral_liminf_le' h_ae_meas
      _ ≤ ENNReal.ofReal C :=
          Filter.liminf_le_of_frequently_le'
            (Filter.Eventually.of_forall h_lint_bound).frequently
  -- Step 5: Convert back to Bochner integral via toReal
  rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => by positivity)
      ((continuous_pow 4).comp_aestronglyMeasurable hg_meas)]
  exact ENNReal.toReal_le_of_le_ofReal hC h_lint_le

/-- Integrability version of `integral_pow4_le_of_L2_convergence`.
    Under the same hypotheses, g⁴ is integrable.
    Proof: the Fatou argument gives ∫⁻ g⁴ ≤ ofReal C < ⊤. -/
theorem integrable_pow4_of_L2_convergence
    [IsProbabilityMeasure μ]
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg_meas : AEStronglyMeasurable g μ)
    (hL2 : Filter.Tendsto (fun n => ∫ ω, (f n ω - g ω)^2 ∂μ) atTop (nhds 0))
    (hL2_int : ∀ n, Integrable (fun ω => (f n ω - g ω)^2) μ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ n, ∫ ω, (f n ω)^4 ∂μ ≤ C)
    (hf4_int : ∀ n, Integrable (fun ω => (f n ω)^4) μ) :
    Integrable (fun ω => (g ω)^4) μ := by
  -- Step 1: Extract a.e. convergent subsequence (same as integral_pow4_le_of_L2_convergence)
  have h_ae_subseq : ∃ (ns : ℕ → ℕ), StrictMono ns ∧
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun k => f (ns k) ω) atTop (nhds (g ω)) := by
    apply TendstoInMeasure.exists_seq_tendsto_ae
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have h_lint_eq : ∀ n, ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ =
        ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ) :=
      fun n => (ofReal_integral_eq_lintegral_ofReal (hL2_int n)
        (ae_of_all _ fun ω => by positivity)).symm
    have h_tend_lint : Filter.Tendsto
        (fun n => ∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ) atTop (nhds 0) := by
      simp_rw [h_lint_eq]
      have : Filter.Tendsto (fun n => ENNReal.ofReal (∫ ω, (f n ω - g ω) ^ 2 ∂μ))
          atTop (nhds (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto 0).comp hL2
      rwa [ENNReal.ofReal_zero] at this
    have hε2_pos : ENNReal.ofReal (ε ^ 2) ≠ 0 := by positivity
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
            ((hf_meas n).sub hg_meas).aemeasurable)
      have h_cheb := mul_meas_ge_le_lintegral₀ h_aem (ENNReal.ofReal (ε ^ 2))
      have h_set_eq : {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal ((f n ω - g ω) ^ 2)} =
          {ω | ε ^ 2 ≤ (f n ω - g ω) ^ 2} := by
        ext ω; simp only [Set.mem_setOf_eq]
        exact ENNReal.ofReal_le_ofReal_iff (by positivity)
      rw [h_set_eq] at h_cheb
      calc μ {ω | (ε : ℝ) ≤ ‖f n ω - g ω‖}
          ≤ μ {ω | ε ^ 2 ≤ (f n ω - g ω) ^ 2} := measure_mono h_subset
        _ ≤ (∫⁻ ω, ENNReal.ofReal ((f n ω - g ω) ^ 2) ∂μ) / ENNReal.ofReal (ε ^ 2) :=
            ENNReal.le_div_iff_mul_le (Or.inl hε2_pos) (Or.inl ENNReal.ofReal_ne_top) |>.mpr <|
              by rw [mul_comm]; exact h_cheb
  obtain ⟨ns, _, hns_ae⟩ := h_ae_subseq
  -- Step 2: Fatou on lintegral of g⁴
  have h_pow4_nn : ∀ n, 0 ≤ᵐ[μ] fun ω => (f n ω) ^ 4 :=
    fun n => ae_of_all _ fun ω => by positivity
  have h_ae_meas : ∀ k,
      AEMeasurable (fun ω => ENNReal.ofReal ((f (ns k) ω) ^ 4)) μ :=
    fun k => ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_pow 4).measurable.comp_aemeasurable (hf_meas (ns k)).aemeasurable)
  have h_lint_bound : ∀ k,
      ∫⁻ ω, ENNReal.ofReal ((f (ns k) ω) ^ 4) ∂μ ≤ ENNReal.ofReal C := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hf4_int (ns k)) (h_pow4_nn (ns k))]
    exact ENNReal.ofReal_le_ofReal (hbound (ns k))
  have h_liminf_ae : ∀ᵐ ω ∂μ,
      Filter.liminf (fun k => ENNReal.ofReal ((f (ns k) ω) ^ 4)) atTop =
        ENNReal.ofReal ((g ω) ^ 4) := by
    filter_upwards [hns_ae] with ω hω
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_pow 4).tendsto _).comp hω)).liminf_eq
  have h_lint_le : ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 4) ∂μ ≤ ENNReal.ofReal C :=
    calc ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 4) ∂μ
        ≤ ∫⁻ ω, Filter.liminf (fun k => ENNReal.ofReal ((f (ns k) ω) ^ 4)) atTop ∂μ :=
          lintegral_mono_ae (h_liminf_ae.mono fun ω hω => hω ▸ le_refl _)
      _ ≤ Filter.liminf (fun k => ∫⁻ ω, ENNReal.ofReal ((f (ns k) ω) ^ 4) ∂μ) atTop :=
          lintegral_liminf_le' h_ae_meas
      _ ≤ ENNReal.ofReal C :=
          Filter.liminf_le_of_frequently_le'
            (Filter.Eventually.of_forall h_lint_bound).frequently
  -- Step 3: Finite lintegral → Integrable
  refine ⟨hg_meas.pow 4, ?_⟩
  show ∫⁻ ω, ↑‖(g ω) ^ 4‖₊ ∂μ < ⊤
  have h_convert : ∫⁻ ω, ↑‖(g ω) ^ 4‖₊ ∂μ = ∫⁻ ω, ENNReal.ofReal ((g ω) ^ 4) ∂μ := by
    congr 1; ext ω
    rw [← enorm_eq_nnnorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]
  rw [h_convert]
  exact lt_of_le_of_lt h_lint_le ENNReal.ofReal_lt_top

/-! ## Transfer to ItoProcess stochastic integral

The proof strategy for transferring the quartic bound from simple processes to the
Itô integral uses the three helper lemmas above:

1. `stoch_integral_bounded_approx`: get uniformly Mσ-bounded approximating processes
2. `simple_integral_increment_quartic_bound`: each approximant satisfies E[(ΔSI)⁴] ≤ 3M⁴(Δt)²
3. `integral_pow4_le_of_L2_convergence`: transfer the bound to the limit via Fatou

The L² convergence of increments (S_n(t)-S_n(s) → SI(t)-SI(s) in L²) follows from
the individual convergences at t and s via (a-b)² ≤ 2a² + 2b².
-/

/-- The stochastic integral increment is L⁴ integrable when diffusion is bounded.
    Delegates to `integrable_pow4_of_L2_convergence` with the same setup as the bound proof. -/
theorem stoch_integral_increment_L4_integrable_proof {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Integrable (fun ω => (X.stoch_integral t ω - X.stoch_integral s ω)^4) μ := by
  -- Ω is nonempty since μ is a probability measure
  haveI : Nonempty Ω := by
    by_contra h; rw [not_nonempty_iff] at h
    have h1 := @IsProbabilityMeasure.measure_univ _ _ μ _
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  have hMσ_nn : 0 ≤ Mσ := le_trans (abs_nonneg _) (hMσ 0 (Classical.arbitrary Ω))
  -- Get bounded approximating simple processes
  obtain ⟨approx, hadapt, hbdd, htimes_nn, hL2_conv⟩ :=
    stoch_integral_bounded_approx X hMσ_nn hMσ
  -- Define approximating increments and target
  set f : ℕ → Ω → ℝ := fun n ω =>
    (approx n).stochasticIntegral_at X.BM t ω -
    (approx n).stochasticIntegral_at X.BM s ω
  set g : Ω → ℝ := fun ω => X.stoch_integral t ω - X.stoch_integral s ω
  -- Each f_n satisfies quartic bound and integrability
  have hf4_data : ∀ n,
      Integrable (fun ω => (f n ω) ^ 4) μ ∧
      ∫ ω, (f n ω) ^ 4 ∂μ ≤ 3 * Mσ ^ 4 * (t - s) ^ 2 := by
    intro n
    exact simple_integral_increment_quartic_bound (approx n) X.BM
      (hadapt n) hMσ_nn (hbdd n) (htimes_nn n) s t hs hst
  -- Helper: convert uniform bound to existential bound
  have hbdd_ex : ∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C :=
    fun n i => ⟨Mσ, hbdd n i⟩
  have ht_nn : 0 ≤ t := le_trans hs hst
  -- L² integrability of stochastic integral approximation errors
  have hSI_sub_sq_int_t : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at X.BM t ω - X.stoch_integral t ω) ^ 2) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (hadapt n) (hbdd_ex n) (htimes_nn n)
      (X.stoch_integral t) (X.stoch_integral_integrable t ht_nn)
      (X.stoch_integral_sq_integrable t ht_nn) t ht_nn
  have hSI_sub_sq_int_s : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at X.BM s ω - X.stoch_integral s ω) ^ 2) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (hadapt n) (hbdd_ex n) (htimes_nn n)
      (X.stoch_integral s) (X.stoch_integral_integrable s hs)
      (X.stoch_integral_sq_integrable s hs) s hs
  -- f_n → g in L²
  have hL2_incr : Filter.Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂μ)
      atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun n => integral_nonneg fun ω => sq_nonneg _
    · intro n
      calc ∫ ω, (f n ω - g ω) ^ 2 ∂μ
          ≤ ∫ ω, (2 * ((approx n).stochasticIntegral_at X.BM t ω -
                      X.stoch_integral t ω) ^ 2 +
                  2 * ((approx n).stochasticIntegral_at X.BM s ω -
                      X.stoch_integral s ω) ^ 2) ∂μ := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ fun ω => sq_nonneg _
            · exact ((hSI_sub_sq_int_t n).const_mul 2).add
                ((hSI_sub_sq_int_s n).const_mul 2)
            · exact ae_of_all _ fun ω => by
                show (f n ω - g ω) ^ 2 ≤ _
                simp only [f, g]
                nlinarith [sq_nonneg ((approx n).stochasticIntegral_at X.BM t ω -
                    X.stoch_integral t ω +
                    ((approx n).stochasticIntegral_at X.BM s ω -
                    X.stoch_integral s ω))]
        _ = 2 * ∫ ω, ((approx n).stochasticIntegral_at X.BM t ω -
                      X.stoch_integral t ω) ^ 2 ∂μ +
            2 * ∫ ω, ((approx n).stochasticIntegral_at X.BM s ω -
                      X.stoch_integral s ω) ^ 2 ∂μ := by
            rw [integral_add ((hSI_sub_sq_int_t n).const_mul 2)
                ((hSI_sub_sq_int_s n).const_mul 2),
              integral_const_mul, integral_const_mul]
    · have h_sum := (hL2_conv t ht_nn).add (hL2_conv s hs)
      simp only [add_zero] at h_sum
      have h2 := h_sum.const_mul 2
      rw [mul_zero] at h2
      exact h2.congr (fun n => by ring)
  -- Apply Fatou transfer for integrability
  exact integrable_pow4_of_L2_convergence
    (fun n =>
      (SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
        (hadapt n) (hbdd_ex n) (htimes_nn n) t ht_nn).aestronglyMeasurable.sub
      (SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
        (hadapt n) (hbdd_ex n) (htimes_nn n) s hs).aestronglyMeasurable)
    ((X.stoch_integral_integrable t ht_nn).aestronglyMeasurable.sub
      (X.stoch_integral_integrable s hs).aestronglyMeasurable)
    hL2_incr
    (fun n => by
      apply Integrable.mono'
        (((hSI_sub_sq_int_t n).const_mul 2).add ((hSI_sub_sq_int_s n).const_mul 2))
      · exact (continuous_pow 2).comp_aestronglyMeasurable
          (((SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
              (hadapt n) (hbdd_ex n) (htimes_nn n) t ht_nn).sub
            (SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
              (hadapt n) (hbdd_ex n) (htimes_nn n) s hs)).sub
          ((X.stoch_integral_integrable t ht_nn).sub
            (X.stoch_integral_integrable s hs))).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Pi.add_apply, Pi.sub_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg ((approx n).stochasticIntegral_at X.BM t ω -
            X.stoch_integral t ω +
            ((approx n).stochasticIntegral_at X.BM s ω -
            X.stoch_integral s ω))])
    (by positivity)
    (fun n => (hf4_data n).2)
    (fun n => (hf4_data n).1)

/-- The quartic bound for stochastic integral increments.
    E[(SI(t) - SI(s))⁴] ≤ 3 Mσ⁴ (t - s)²

    Proof strategy:
    1. Get uniformly Mσ-bounded approximating simple processes (stoch_integral_bounded_approx)
    2. Each satisfies E[(ΔSI_n)⁴] ≤ 3Mσ⁴(t-s)² (simple_integral_increment_quartic_bound)
    3. SI_n(t) - SI_n(s) → SI(t) - SI(s) in L² (from individual convergences)
    4. Transfer via Fatou (integral_pow4_le_of_L2_convergence) -/
theorem stoch_integral_increment_L4_bound_proof {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω)^4 ∂μ ≤
    3 * Mσ^4 * (t - s)^2 := by
  -- Ω is nonempty since μ is a probability measure
  haveI : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := @IsProbabilityMeasure.measure_univ _ _ μ _
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  -- Mσ ≥ 0 from the absolute value bound
  have hMσ_nn : 0 ≤ Mσ :=
    le_trans (abs_nonneg _) (hMσ 0 (Classical.arbitrary Ω))
  -- Step 1: Get bounded approximating simple processes
  obtain ⟨approx, hadapt, hbdd, htimes_nn, hL2_conv⟩ :=
    stoch_integral_bounded_approx X hMσ_nn hMσ
  -- Step 2: Define approximating increments and target
  set f : ℕ → Ω → ℝ := fun n ω =>
    (approx n).stochasticIntegral_at X.BM t ω -
    (approx n).stochasticIntegral_at X.BM s ω
  set g : Ω → ℝ := fun ω => X.stoch_integral t ω - X.stoch_integral s ω
  -- Step 3: Each f_n satisfies quartic bound and integrability
  have hf4_data : ∀ n,
      Integrable (fun ω => (f n ω) ^ 4) μ ∧
      ∫ ω, (f n ω) ^ 4 ∂μ ≤ 3 * Mσ ^ 4 * (t - s) ^ 2 := by
    intro n
    exact simple_integral_increment_quartic_bound (approx n) X.BM
      (hadapt n) hMσ_nn (hbdd n) (htimes_nn n) s t hs hst
  -- Step 4: f_n → g in L² (from individual convergences at t and s)
  have hL2_t := hL2_conv t (le_trans hs hst)
  have hL2_s := hL2_conv s hs
  -- Helper: convert uniform bound to existential bound for stochasticIntegral_at lemmas
  have hbdd_ex : ∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C :=
    fun n i => ⟨Mσ, hbdd n i⟩
  have ht_nn : 0 ≤ t := le_trans hs hst
  -- L² integrability of stochastic integral approximation errors
  have hSI_sub_sq_int_t : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at X.BM t ω - X.stoch_integral t ω) ^ 2) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (hadapt n) (hbdd_ex n) (htimes_nn n)
      (X.stoch_integral t) (X.stoch_integral_integrable t ht_nn)
      (X.stoch_integral_sq_integrable t ht_nn) t ht_nn
  have hSI_sub_sq_int_s : ∀ n, Integrable (fun ω =>
      ((approx n).stochasticIntegral_at X.BM s ω - X.stoch_integral s ω) ^ 2) μ :=
    fun n => SimpleProcess.stochasticIntegral_at_sub_sq_integrable (approx n) X.BM
      (hadapt n) (hbdd_ex n) (htimes_nn n)
      (X.stoch_integral s) (X.stoch_integral_integrable s hs)
      (X.stoch_integral_sq_integrable s hs) s hs
  have hL2_incr : Filter.Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂μ)
      atTop (nhds 0) := by
    -- (f_n - g)² = ((SI_n(t)-SI(t)) - (SI_n(s)-SI(s)))² ≤ 2·err(t)² + 2·err(s)²
    apply squeeze_zero
    · exact fun n => integral_nonneg fun ω => sq_nonneg _
    · intro n
      -- Pointwise: (a-b)² ≤ 2a² + 2b² where a = SI_n(t)-SI(t), b = SI_n(s)-SI(s)
      calc ∫ ω, (f n ω - g ω) ^ 2 ∂μ
          ≤ ∫ ω, (2 * ((approx n).stochasticIntegral_at X.BM t ω -
                      X.stoch_integral t ω) ^ 2 +
                  2 * ((approx n).stochasticIntegral_at X.BM s ω -
                      X.stoch_integral s ω) ^ 2) ∂μ := by
            apply integral_mono_of_nonneg
            · exact ae_of_all _ fun ω => sq_nonneg _
            · exact ((hSI_sub_sq_int_t n).const_mul 2).add
                ((hSI_sub_sq_int_s n).const_mul 2)
            · exact ae_of_all _ fun ω => by
                show (f n ω - g ω) ^ 2 ≤ _
                simp only [f, g]
                nlinarith [sq_nonneg ((approx n).stochasticIntegral_at X.BM t ω -
                    X.stoch_integral t ω +
                    ((approx n).stochasticIntegral_at X.BM s ω -
                    X.stoch_integral s ω))]
        _ = 2 * ∫ ω, ((approx n).stochasticIntegral_at X.BM t ω -
                      X.stoch_integral t ω) ^ 2 ∂μ +
            2 * ∫ ω, ((approx n).stochasticIntegral_at X.BM s ω -
                      X.stoch_integral s ω) ^ 2 ∂μ := by
            rw [integral_add ((hSI_sub_sq_int_t n).const_mul 2)
                ((hSI_sub_sq_int_s n).const_mul 2),
              integral_const_mul, integral_const_mul]
    · -- 2·E[err(t)²] + 2·E[err(s)²] → 2·0 + 2·0 = 0
      have h_sum := hL2_t.add hL2_s
      simp only [add_zero] at h_sum
      have h2 := h_sum.const_mul 2
      rw [mul_zero] at h2
      exact h2.congr (fun n => by ring)
  -- Step 5: Apply Fatou transfer
  exact integral_pow4_le_of_L2_convergence
    (fun n => -- AEStronglyMeasurable f_n
      (SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
        (hadapt n) (hbdd_ex n) (htimes_nn n) t ht_nn).aestronglyMeasurable.sub
      (SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
        (hadapt n) (hbdd_ex n) (htimes_nn n) s hs).aestronglyMeasurable)
    ((X.stoch_integral_integrable t ht_nn).aestronglyMeasurable.sub
      (X.stoch_integral_integrable s hs).aestronglyMeasurable)
    hL2_incr
    (fun n => by -- Integrable (f n - g)²: bound by 2·err_t² + 2·err_s²
      apply Integrable.mono'
        (((hSI_sub_sq_int_t n).const_mul 2).add ((hSI_sub_sq_int_s n).const_mul 2))
      · exact (continuous_pow 2).comp_aestronglyMeasurable
          (((SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
              (hadapt n) (hbdd_ex n) (htimes_nn n) t ht_nn).sub
            (SimpleProcess.stochasticIntegral_at_integrable (approx n) X.BM
              (hadapt n) (hbdd_ex n) (htimes_nn n) s hs)).sub
          ((X.stoch_integral_integrable t ht_nn).sub
            (X.stoch_integral_integrable s hs))).aestronglyMeasurable
      · filter_upwards with ω
        simp only [Pi.add_apply, Pi.sub_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg ((approx n).stochasticIntegral_at X.BM t ω -
            X.stoch_integral t ω +
            ((approx n).stochasticIntegral_at X.BM s ω -
            X.stoch_integral s ω))])
    (by positivity)
    (fun n => (hf4_data n).2)
    (fun n => (hf4_data n).1)

end SPDE
