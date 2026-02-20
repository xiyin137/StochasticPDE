/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.BrownianMotion
import StochasticPDE.ItoCalculus.Probability.Pythagoras
import StochasticPDE.ItoCalculus.Probability.IndependenceHelpers
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Itô Formula Infrastructure

Infrastructure for proving the Itô formula martingale property.
This file provides the analytical estimates (Gaussian moments, BM quadratic variation
convergence) that feed into the partition-based Itô formula proof.
The martingale property itself follows from the L² limit infrastructure
in `ItoIntegralProperties.lean`.

## Main results

- `fourth_moment_gaussianReal`: ∫ x⁴ d(gaussianReal 0 v) = 3v²
- `IsGaussian.fourth_moment`: E[X⁴] = 3σ⁴ for X ~ N(0, σ²)
- `BrownianMotion.increment_fourth_moment`: E[(ΔW)⁴] = 3(Δt)²
- `BrownianMotion.increment_sq_minus_dt_variance`: E[((ΔW)²-Δt)²] = 2(Δt)²
-/

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal

noncomputable section

namespace SPDE

/-! ## Derivative computations for exp(v·t²/2)

We compute the first four derivatives of `fun t ↦ rexp (v * t ^ 2 / 2)` step by step.
Each function in the chain has the form `p(t) * rexp(v * t² / 2)` where p is a polynomial.

- f₀(t) = 1 · exp(v·t²/2)
- f₁(t) = (v·t) · exp(v·t²/2)
- f₂(t) = (v + v²·t²) · exp(v·t²/2)
- f₃(t) = (3v²·t + v³·t³) · exp(v·t²/2)
- f₄(t) = (3v² + 6v³·t² + v⁴·t⁴) · exp(v·t²/2)

and f₄(0) = 3v².
-/

variable (v : ℝ)

/-- The Gaussian MGF-type function exp(v·t²/2) has derivative v·t·exp(v·t²/2). -/
private lemma hasDerivAt_gauss_exp (t : ℝ) :
    HasDerivAt (fun t => rexp (v * t ^ 2 / 2)) (v * t * rexp (v * t ^ 2 / 2)) t := by
  have hg : HasDerivAt (fun t => v * t ^ 2 / 2) (v * t) t := by
    have h := (hasDerivAt_pow 2 t).const_mul v |>.div_const 2
    convert h using 1; ring
  convert hg.exp using 1; ring

/-- General derivative lemma: if f(t) = p(t) · exp(v·t²/2) and HasDerivAt p p' t,
    then HasDerivAt f ((p' + v·t·p(t)) · exp(v·t²/2)) t. -/
private lemma hasDerivAt_poly_mul_gauss (p : ℝ → ℝ) (p'_val : ℝ) (t : ℝ)
    (hp : HasDerivAt p p'_val t) :
    HasDerivAt (fun t => p t * rexp (v * t ^ 2 / 2))
      ((p'_val + v * t * p t) * rexp (v * t ^ 2 / 2)) t := by
  have hexp := hasDerivAt_gauss_exp v t
  convert hp.mul hexp using 1; ring

/-- Step 0→1: deriv exp(v·t²/2) = v·t · exp(v·t²/2) -/
private lemma deriv_f0 :
    deriv (fun t => rexp (v * t ^ 2 / 2)) =
      fun t => v * t * rexp (v * t ^ 2 / 2) := by
  ext t; exact (hasDerivAt_gauss_exp v t).deriv

/-- Step 1→2: deriv (v·t · exp(v·t²/2)) t = (v + v²·t²) · exp(v·t²/2) -/
private lemma deriv_f1 (t : ℝ) :
    deriv (fun t => v * t * rexp (v * t ^ 2 / 2)) t =
      (v + v ^ 2 * t ^ 2) * rexp (v * t ^ 2 / 2) := by
  have hp : HasDerivAt (fun t => v * t) v t := by
    simpa [Function.id_def, mul_one] using (hasDerivAt_id t).const_mul v
  have := (hasDerivAt_poly_mul_gauss v (fun t => v * t) v t hp).deriv
  convert this using 1; ring

/-- Step 2→3: deriv ((v + v²·t²) · exp(v·t²/2)) t = (3v²·t + v³·t³) · exp(v·t²/2) -/
private lemma deriv_f2 (t : ℝ) :
    deriv (fun t => (v + v ^ 2 * t ^ 2) * rexp (v * t ^ 2 / 2)) t =
      (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * rexp (v * t ^ 2 / 2) := by
  have hp : HasDerivAt (fun t => v + v ^ 2 * t ^ 2) (2 * v ^ 2 * t) t := by
    have h1 := (hasDerivAt_pow 2 t).const_mul (v ^ 2)
    have h2 := (hasDerivAt_const t v).add h1
    convert h2 using 1; ring
  have := (hasDerivAt_poly_mul_gauss v (fun t => v + v ^ 2 * t ^ 2) (2 * v ^ 2 * t) t hp).deriv
  convert this using 1; ring

/-- Step 3→4: deriv ((3v²·t + v³·t³) · exp(v·t²/2)) t =
    (3v² + 6v³·t² + v⁴·t⁴) · exp(v·t²/2) -/
private lemma deriv_f3 (t : ℝ) :
    deriv (fun t => (3 * v ^ 2 * t + v ^ 3 * t ^ 3) * rexp (v * t ^ 2 / 2)) t =
      (3 * v ^ 2 + 6 * v ^ 3 * t ^ 2 + v ^ 4 * t ^ 4) * rexp (v * t ^ 2 / 2) := by
  have hp : HasDerivAt (fun t => 3 * v ^ 2 * t + v ^ 3 * t ^ 3)
      (3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t := by
    have h1 := (hasDerivAt_id t).const_mul (3 * v ^ 2)
    have h2 := (hasDerivAt_pow 3 t).const_mul (v ^ 3)
    convert h1.add h2 using 1; ring
  have := (hasDerivAt_poly_mul_gauss v (fun t => 3 * v ^ 2 * t + v ^ 3 * t ^ 3)
    (3 * v ^ 2 + 3 * v ^ 3 * t ^ 2) t hp).deriv
  convert this using 1; ring

/-- The fourth derivative of exp(v·t²/2) at 0 is 3v².
    This combines the four derivative steps and evaluates at 0. -/
private lemma fourth_deriv_gauss_at_zero :
    deriv (fun t => deriv (fun t => deriv (fun t => deriv
      (fun t => rexp (v * t ^ 2 / 2)) t) t) t) 0 = 3 * v ^ 2 := by
  -- Replace each deriv layer with the explicit formula
  conv_lhs =>
    arg 1; ext t; arg 1; ext t; arg 1; ext t
    rw [(hasDerivAt_gauss_exp v t).deriv]
  conv_lhs =>
    arg 1; ext t; arg 1; ext t
    rw [deriv_f1 v t]
  conv_lhs =>
    arg 1; ext t
    rw [deriv_f2 v t]
  rw [deriv_f3 v 0]
  simp [exp_zero]

/-! ## Gaussian Third Moment -/

/-- The third derivative of exp(v·t²/2) at 0 is 0.
    Since exp(v·t²/2) is an even function of t, all odd derivatives at 0 vanish. -/
private lemma third_deriv_gauss_at_zero :
    deriv (fun t => deriv (fun t => deriv
      (fun t => rexp (v * t ^ 2 / 2)) t) t) 0 = 0 := by
  conv_lhs =>
    arg 1; ext t; arg 1; ext t
    rw [(hasDerivAt_gauss_exp v t).deriv]
  conv_lhs =>
    arg 1; ext t
    rw [deriv_f1 v t]
  rw [deriv_f2 v 0]
  simp [exp_zero]

/-- The third central moment of a Gaussian is zero: E[(X-μ)³] = 0.
    Follows from the MGF approach: the third derivative of exp(v·t²/2) at 0 is 0. -/
theorem third_moment_gaussianReal (μ_val : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ_val) ^ 3 ∂gaussianReal μ_val v = 0 := by
  calc ∫ x, (x - μ_val) ^ 3 ∂gaussianReal μ_val v
  _ = ∫ x, x ^ 3 ∂(gaussianReal μ_val v).map (fun x => x - μ_val) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ x, x ^ 3 ∂gaussianReal 0 v := by
    simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 3 (mgf (fun x => x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = 0 := by
    rw [mgf_fun_id_gaussianReal]
    simp only [zero_mul, zero_add]
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    exact third_deriv_gauss_at_zero ↑v

/-! ## Gaussian Fourth Moment -/

/-- The fourth central moment of a Gaussian distribution: E[(X-μ)⁴] = 3v².

Proof: Use the MGF approach (following the Mathlib `variance_fun_id_gaussianReal` pattern).
- Shift to zero mean via `gaussianReal_map_sub_const`
- MGF of N(0, v) is M(t) = exp(v·t²/2)  (from `mgf_fun_id_gaussianReal`)
- E[X⁴] = iteratedDeriv 4 M 0  (from `iteratedDeriv_mgf_zero`)
- Evaluate via `fourth_deriv_gauss_at_zero`
-/
theorem fourth_moment_gaussianReal (μ_val : ℝ) (v : ℝ≥0) :
    ∫ x, (x - μ_val) ^ 4 ∂gaussianReal μ_val v = 3 * (↑v : ℝ) ^ 2 := by
  calc ∫ x, (x - μ_val) ^ 4 ∂gaussianReal μ_val v
  _ = ∫ x, x ^ 4 ∂(gaussianReal μ_val v).map (fun x => x - μ_val) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ x, x ^ 4 ∂gaussianReal 0 v := by
    simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 4 (mgf (fun x => x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = 3 * ↑v ^ 2 := by
    rw [mgf_fun_id_gaussianReal]
    simp only [zero_mul, zero_add]
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
    exact fourth_deriv_gauss_at_zero ↑v

/-! ## IsGaussian Third and Fourth Moments -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The third moment of a zero-mean Gaussian random variable is zero: E[X³] = 0.
    Uses the pushforward to `gaussianReal` and the third moment computation. -/
theorem Probability.IsGaussian.third_moment {X : Ω → ℝ} {μ : Measure Ω} {variance : ℝ}
    (h : IsGaussian X μ 0 variance) :
    ∫ ω, (X ω) ^ 3 ∂μ = 0 := by
  have hX_am : AEMeasurable X μ := h.integrable.aemeasurable
  have hmap := h.map_eq_gaussianReal
  have htransfer : ∫ ω, (X ω) ^ 3 ∂μ = ∫ x, x ^ 3 ∂(μ.map X) :=
    (integral_map hX_am (by fun_prop : AEStronglyMeasurable (fun x => x ^ 3) (μ.map X))).symm
  rw [htransfer, hmap]
  have h0 := third_moment_gaussianReal 0 ⟨variance, h.variance_nonneg⟩
  simpa [sub_zero] using h0

/-- The fourth moment of a zero-mean Gaussian random variable: E[X⁴] = 3σ⁴.
    Uses the pushforward to `gaussianReal` and the fourth moment computation. -/
theorem Probability.IsGaussian.fourth_moment {X : Ω → ℝ} {μ : Measure Ω} {variance : ℝ}
    (h : IsGaussian X μ 0 variance) :
    ∫ ω, (X ω) ^ 4 ∂μ = 3 * variance ^ 2 := by
  have hX_am : AEMeasurable X μ := h.integrable.aemeasurable
  have hmap := h.map_eq_gaussianReal
  -- Transfer: ∫ (X ω)⁴ dμ = ∫ x⁴ d(μ.map X)
  have htransfer : ∫ ω, (X ω) ^ 4 ∂μ = ∫ x, x ^ 4 ∂(μ.map X) :=
    (integral_map hX_am (by fun_prop : AEStronglyMeasurable (fun x => x ^ 4) (μ.map X))).symm
  rw [htransfer, hmap]
  -- ∫ x⁴ d(gaussianReal 0 ⟨variance, _⟩) = 3 * variance²
  have h0 := fourth_moment_gaussianReal 0 ⟨variance, h.variance_nonneg⟩
  simpa [sub_zero] using h0

/-! ## BM Increment Third and Fourth Moments -/

variable {μ : Measure Ω}

/-- Third moment of BM increments: E[(W_t - W_s)³] = 0.
    Follows directly from the Gaussian third moment since W_t - W_s ~ N(0, t-s). -/
theorem BrownianMotion.increment_third_moment (W : BrownianMotion Ω μ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 3 ∂μ = 0 :=
  (W.gaussian_increments s t hs hst).third_moment

/-- Fourth moment of BM increments: E[(W_t - W_s)⁴] = 3(t-s)².
    Follows directly from the Gaussian fourth moment since W_t - W_s ~ N(0, t-s). -/
theorem BrownianMotion.increment_fourth_moment (W : BrownianMotion Ω μ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 4 ∂μ =
      3 * (t - s) ^ 2 :=
  (W.gaussian_increments s t hs hst).fourth_moment

/-- Variance of (ΔW)² - Δt: E[((W_t - W_s)² - (t-s))²] = 2(t-s)².
    This is the key estimate for BM quadratic variation L² convergence.

    Proof: Expand (X² - c)² = X⁴ - 2c·X² + c² and use E[X⁴] = 3c², E[X²] = c
    where c = t-s and X = W_t - W_s ~ N(0, c). -/
theorem BrownianMotion.increment_sq_minus_dt_variance (W : BrownianMotion Ω μ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫ ω, ((W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 - (t - s)) ^ 2 ∂μ =
      2 * (t - s) ^ 2 := by
  -- Derive probability measure from Gaussian increments
  haveI : IsProbabilityMeasure μ := (W.gaussian_increments s t hs hst).isProbabilityMeasure
  -- Known moments
  have hX4 := W.increment_fourth_moment s t hs hst
  have hX2 := W.increment_variance s t hs hst
  have hX4_int := W.increment_all_moments s t hs hst 4
  have hX2_int := W.increment_sq_integrable s t hs hst
  -- Rewrite (X² - c)² = X⁴ + (-2c)·X² + c²  (using + throughout for integral_add)
  have hexp : ∀ ω, ((W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 -
      (t - s)) ^ 2 =
    (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 4 +
    ((-2 * (t - s)) * (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 +
    (t - s) ^ 2) := fun ω => by ring
  simp_rw [hexp]
  -- Explicitly typed integrability proofs so integral_add can match pointwise
  have hint_bc : Integrable (fun ω =>
      (-2 * (t - s)) * (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2 +
      (t - s) ^ 2) μ :=
    (hX2_int.const_mul _).add (integrable_const _)
  have hint_b : Integrable (fun ω =>
      (-2 * (t - s)) * (W.toAdapted.process t ω - W.toAdapted.process s ω) ^ 2) μ :=
    hX2_int.const_mul _
  -- Split ∫(A + (B + C)) = ∫ A + (∫ B + ∫ C)
  rw [integral_add hX4_int hint_bc]
  rw [integral_add hint_b (integrable_const _)]
  rw [integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  rw [hX4, hX2]; ring

/-! ## BM Quadratic Variation L² Convergence -/

/-- Sum of squared BM increments along a uniform partition of [0, T] with n subintervals.
    QV_n(ω) = Σᵢ₌₀ⁿ⁻¹ (W((i+1)T/n) - W(iT/n))² -/
def bmQVSum (W : BrownianMotion Ω μ) (T : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n,
    (W.toAdapted.process ((↑i + 1) * T / ↑n) ω -
     W.toAdapted.process (↑i * T / ↑n) ω) ^ 2

/-- The L² distance of the QV sum from T is bounded by 2T²/n for uniform partitions.
    E[|QV_n - T|²] ≤ 2T²/n.

    Proof strategy: By independence of BM increments on disjoint intervals,
    the variance of the sum equals the sum of variances.
    Each Yᵢ = (ΔWᵢ)² - T/n has E[Yᵢ] = 0 and E[Yᵢ²] = 2(T/n)² by
    `increment_sq_minus_dt_variance`. By independence, E[(ΣYᵢ)²] = ΣE[Yᵢ²] = n·2(T/n)² = 2T²/n. -/
theorem bm_qv_sum_L2_bound (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (hn : 0 < n) :
    ∫ ω, (bmQVSum W T n ω - T) ^ 2 ∂μ ≤ 2 * T ^ 2 / ↑n := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- Partition increment ΔWᵢ
  let incr : Fin n → Ω → ℝ := fun i ω =>
    W.toAdapted.process ((↑(i : ℕ) + 1) * T / ↑n) ω -
    W.toAdapted.process (↑(i : ℕ) * T / ↑n) ω
  -- Centered squared increment Yᵢ = (ΔWᵢ)² - T/n
  let Y : Fin n → Ω → ℝ := fun i ω => (incr i ω) ^ 2 - T / ↑n
  -- Partition point arithmetic
  have hpt_nonneg : ∀ i : Fin n, 0 ≤ (↑(i : ℕ) : ℝ) * T / ↑n := fun i => by positivity
  have hpt_mono : ∀ i : Fin n,
      (↑(i : ℕ) : ℝ) * T / ↑n ≤ (↑(i : ℕ) + 1) * T / ↑n := by
    intro i; apply div_le_div_of_nonneg_right _ hn_pos.le; nlinarith
  -- Step 1: bmQVSum - T = ∑ Yᵢ
  have hrewrite : ∀ ω, bmQVSum W T n ω - T = ∑ i : Fin n, Y i ω := by
    intro ω
    have h1 : bmQVSum W T n ω = ∑ i : Fin n, (incr i ω) ^ 2 := by
      unfold bmQVSum; exact (Fin.sum_univ_eq_sum_range _ n).symm
    have h2 : T = ∑ _i : Fin n, (T / (↑n : ℝ)) := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; field_simp
    rw [h1, h2, ← Finset.sum_sub_distrib]
  simp_rw [hrewrite]
  -- Yᵢ integrability
  have hY_int : ∀ i : Fin n, Integrable (Y i) μ := fun i =>
    (W.increment_sq_integrable _ _ (hpt_nonneg i) (hpt_mono i)).sub (integrable_const _)
  -- Independence of increments on disjoint partition intervals
  have hindep_incr : ∀ i j : Fin n, i.val < j.val →
      IndepFun (incr i) (incr j) μ := by
    intro i j hij
    have hdisjoint : (↑(i : ℕ) + 1) * T / ↑n ≤ ↑(j : ℕ) * T / ↑n := by
      apply div_le_div_of_nonneg_right _ hn_pos.le
      have : (↑(i : ℕ) + 1 : ℝ) ≤ ↑(j : ℕ) := by exact_mod_cast hij
      nlinarith [hT]
    exact W.disjoint_independent _ _ _ _
      (hpt_nonneg i) (hpt_mono i) hdisjoint (hpt_mono j)
  -- Measurability of φ(x) = x² - c (needed for IndepFun.comp)
  have hφ : Measurable (fun x : ℝ => x ^ 2 - T / ↑n) :=
    (measurable_id.pow_const 2).sub measurable_const
  -- Independence of Yᵢ and Yⱼ (compose independent increments with measurable φ)
  have hindep_Y : ∀ i j : Fin n, i ≠ j → IndepFun (Y i) (Y j) μ := by
    intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hindep_incr i j h).comp hφ hφ
    · exact ((hindep_incr j i h).comp hφ hφ).symm
  -- Yᵢ² integrability (expand as polynomial of Gaussian moments)
  have hY_sq_int : ∀ i : Fin n, Integrable (fun ω => (Y i ω) ^ 2) μ := by
    intro i
    have hfun : ∀ ω, (Y i ω) ^ 2 =
        (incr i ω) ^ 4 + ((-2 * (T / ↑n)) * (incr i ω) ^ 2 + (T / ↑n) ^ 2) := by
      intro ω; ring
    simp_rw [hfun]
    have h4 : Integrable (fun ω => (incr i ω) ^ 4) μ :=
      W.increment_all_moments _ _ (hpt_nonneg i) (hpt_mono i) 4
    have h2c : Integrable (fun ω => (-2 * (T / ↑n)) * (incr i ω) ^ 2) μ :=
      (W.increment_sq_integrable _ _ (hpt_nonneg i) (hpt_mono i)).const_mul _
    exact (h4.add (h2c.add (integrable_const _)))
  -- Cross-integrability (needed for Pythagoras)
  have hcross_int : ∀ i j : Fin n, Integrable (fun ω => Y i ω * Y j ω) μ := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact (hY_sq_int i).congr (ae_of_all _ fun ω => by ring)
    · exact (hindep_Y i j hij).integrable_mul (hY_int i) (hY_int j)
  -- E[Yⱼ] = E[(ΔWⱼ)²] - T/n = (t-s) - T/n = 0
  have hY_mean : ∀ j : Fin n, ∫ ω, Y j ω ∂μ = 0 := by
    intro j
    show ∫ ω, ((incr j ω) ^ 2 - T / ↑n) ∂μ = 0
    rw [integral_sub (W.increment_sq_integrable _ _ (hpt_nonneg j) (hpt_mono j))
        (integrable_const _)]
    rw [W.increment_variance _ _ (hpt_nonneg j) (hpt_mono j)]
    rw [integral_const]; simp only [probReal_univ, one_smul]
    show (↑(j : ℕ) + 1) * T / ↑n - ↑(j : ℕ) * T / ↑n - T / ↑n = 0
    field_simp; ring
  -- Orthogonality: E[Yᵢ·Yⱼ] = E[Yᵢ]·E[Yⱼ] = 0 (by independence and zero mean)
  have horthog : ∀ i j : Fin n, i ≠ j → ∫ ω, Y i ω * Y j ω ∂μ = 0 := by
    intro i j hij
    have hind := (hindep_Y i j hij).integral_mul_eq_mul_integral
      (hY_int i).aestronglyMeasurable (hY_int j).aestronglyMeasurable
    change ∫ ω, (Y i * Y j) ω ∂μ = 0
    rw [hind, hY_mean j, mul_zero]
  -- Apply L² Pythagoras: E[(∑Yᵢ)²] = ∑E[Yᵢ²]
  have hpythag := SPDE.Probability.sum_sq_integral_eq_sum_integral_sq Y hcross_int horthog
  -- E[Yᵢ²] = 2(T/n)² by increment_sq_minus_dt_variance
  have hvar_each : ∀ i : Fin n, ∫ ω, (Y i ω) ^ 2 ∂μ = 2 * (T / ↑n) ^ 2 := by
    intro i
    have h := W.increment_sq_minus_dt_variance _ _ (hpt_nonneg i) (hpt_mono i)
    have hts : (↑(i : ℕ) + 1) * T / ↑n - ↑(i : ℕ) * T / ↑n = T / ↑n := by
      field_simp; ring
    simp_rw [hts] at h; exact h
  -- Combine: ∑ 2(T/n)² = n·2(T/n)² = 2T²/n
  suffices heq : ∫ ω, (∑ i : Fin n, Y i ω) ^ 2 ∂μ = 2 * T ^ 2 / ↑n by linarith
  calc ∫ ω, (∑ i : Fin n, Y i ω) ^ 2 ∂μ
    _ = ∑ i : Fin n, ∫ ω, (Y i ω) ^ 2 ∂μ := hpythag
    _ = ∑ _i : Fin n, (2 * (T / ↑n) ^ 2) := by simp_rw [hvar_each]
    _ = ↑n * (2 * (T / ↑n) ^ 2) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = 2 * T ^ 2 / ↑n := by field_simp

/-- The QV sum converges to T in L² as n → ∞.
    E[|QV_n - T|²] → 0. -/
theorem bm_qv_L2_convergence (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n => ∫ ω, (bmQVSum W T (n + 1) ω - T) ^ 2 ∂μ)
      atTop (nhds 0) := by
  -- Squeeze between 0 and 2T²/(n+1) → 0
  apply squeeze_zero
  · intro n; positivity
  · intro n; exact bm_qv_sum_L2_bound W T hT (n + 1) (Nat.succ_pos n)
  · -- 2T²/(n+1) → 0
    have h : (fun n : ℕ => 2 * T ^ 2 / (↑(n + 1) : ℝ)) =
        (fun n : ℕ => (2 * T ^ 2) * (1 / ((↑n : ℝ) + 1))) := by
      ext n; rw [Nat.cast_succ]; ring
    rw [h, show (0 : ℝ) = (2 * T ^ 2) * 0 from by ring]
    exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## Weighted BM Quadratic Variation

For the Itô formula, we need the weighted version of the QV L² bound:
  E[(Σᵢ gᵢ · ((ΔWᵢ)² - Δtᵢ))²] ≤ C² · 2T²/n
where gᵢ are F_{tᵢ}-measurable and |gᵢ| ≤ C.

The proof uses:
1. Orthogonality: E[gᵢYᵢ · gⱼYⱼ] = 0 for i ≠ j
   (from: gᵢYᵢgⱼ is F_{tⱼ}-measurable, Yⱼ independent of F_{tⱼ} with E[Yⱼ]=0)
2. L² Pythagoras: E[(Σ aᵢ)²] = Σ E[aᵢ²]
3. Pointwise bound: E[gᵢ²Yᵢ²] ≤ C²·E[Yᵢ²] = C²·2(T/n)²
-/

/-- σ-algebra of a composed random variable is coarser than the original.
    If φ is measurable, then comap(φ ∘ f) ≤ comap(f). -/
lemma comap_comp_le {Ω' : Type*} {f : Ω' → ℝ} {φ : ℝ → ℝ} (hφ : Measurable φ) :
    MeasurableSpace.comap (fun ω => φ (f ω)) inferInstance ≤
    MeasurableSpace.comap f inferInstance := by
  intro S hS
  obtain ⟨T, hT, rfl⟩ := hS
  exact ⟨φ ⁻¹' T, hφ hT, rfl⟩

/-- If ΔW is independent of a σ-algebra m, then any measurable function of ΔW is too. -/
private lemma indep_of_comp {m : MeasurableSpace Ω} {f : Ω → ℝ} {φ : ℝ → ℝ}
    (hφ : Measurable φ)
    (hindep : Indep m (MeasurableSpace.comap f inferInstance) μ) :
    Indep m (MeasurableSpace.comap (fun ω => φ (f ω)) inferInstance) μ :=
  ProbabilityTheory.indep_of_indep_of_le_right hindep (comap_comp_le hφ)

/-- Measurability of BM process at a time: W(t) is F_t-measurable. -/
private lemma bm_adapted (W : BrownianMotion Ω μ) (t : ℝ) :
    @Measurable Ω ℝ (W.F.σ_algebra t) _ (W.toAdapted.process t) :=
  W.toAdapted.adapted t

/-- Weighted L² bound for BM quadratic variation sums.

    If gᵢ are F_{tᵢ}-measurable and |gᵢ| ≤ C, then
    E[(Σ gᵢ · ((ΔWᵢ)² - T/n))²] ≤ C² · 2T²/n.

    This extends `bm_qv_sum_L2_bound` to adapted weights. Key for the Itô formula:
    controls the error from replacing (ΔWᵢ)² by Δtᵢ in expressions like
    Σ f''(tᵢ, Xᵢ) · σᵢ² · ((ΔWᵢ)² - Δtᵢ). -/
theorem weighted_qv_sum_L2_bound (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (hn : 0 < n)
    (g : Fin n → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg_adapted : ∀ i : Fin n,
      @Measurable Ω ℝ (W.F.σ_algebra (↑(i : ℕ) * T / ↑n)) _ (g i))
    (hg_bdd : ∀ i : Fin n, ∀ ω, |g i ω| ≤ C) :
    ∫ ω, (∑ i : Fin n, g i ω *
      ((W.toAdapted.process ((↑(i : ℕ) + 1) * T / ↑n) ω -
        W.toAdapted.process (↑(i : ℕ) * T / ↑n) ω) ^ 2 - T / ↑n))^2 ∂μ ≤
    C^2 * (2 * T^2 / ↑n) := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- Define incr, Y, a = g * Y
  let incr : Fin n → Ω → ℝ := fun i ω =>
    W.toAdapted.process ((↑(i : ℕ) + 1) * T / ↑n) ω -
    W.toAdapted.process (↑(i : ℕ) * T / ↑n) ω
  let Y : Fin n → Ω → ℝ := fun i ω => (incr i ω) ^ 2 - T / ↑n
  let a : Fin n → Ω → ℝ := fun i ω => g i ω * Y i ω
  -- Partition point arithmetic
  have hpt_nonneg : ∀ i : Fin n, 0 ≤ (↑(i : ℕ) : ℝ) * T / ↑n := fun i => by positivity
  have hpt_mono : ∀ i : Fin n,
      (↑(i : ℕ) : ℝ) * T / ↑n ≤ (↑(i : ℕ) + 1) * T / ↑n := by
    intro i; apply div_le_div_of_nonneg_right _ hn_pos.le; nlinarith
  -- Key measurability: φ(x) = x² - c is measurable
  have hφ : Measurable (fun x : ℝ => x ^ 2 - T / ↑n) :=
    (measurable_id.pow_const 2).sub measurable_const
  -- g is ambient-measurable (for AEStronglyMeasurable)
  have hg_meas_ambient : ∀ i : Fin n, Measurable (g i) :=
    fun i => (hg_adapted i).mono (W.F.le_ambient _) le_rfl
  -- Y integrability
  have hY_int : ∀ i : Fin n, Integrable (Y i) μ := fun i =>
    (W.increment_sq_integrable _ _ (hpt_nonneg i) (hpt_mono i)).sub (integrable_const _)
  -- a integrability (bounded · integrable)
  have ha_int : ∀ i : Fin n, Integrable (a i) μ := by
    intro i
    exact (hY_int i).bdd_mul (hg_meas_ambient i).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg_bdd i ω)
  -- E[Yⱼ] = 0
  have hY_mean : ∀ j : Fin n, ∫ ω, Y j ω ∂μ = 0 := by
    intro j
    show ∫ ω, ((incr j ω) ^ 2 - T / ↑n) ∂μ = 0
    rw [integral_sub (W.increment_sq_integrable _ _ (hpt_nonneg j) (hpt_mono j))
        (integrable_const _)]
    rw [W.increment_variance _ _ (hpt_nonneg j) (hpt_mono j)]
    rw [integral_const]; simp only [probReal_univ, one_smul]
    show (↑(j : ℕ) + 1) * T / ↑n - ↑(j : ℕ) * T / ↑n - T / ↑n = 0
    field_simp; ring
  -- Independence: ΔWᵢ independent of F_{tᵢ} → Yᵢ = φ(ΔWᵢ) independent of F_{tᵢ}
  have hY_indep : ∀ i : Fin n,
      Indep (W.F.σ_algebra (↑(i : ℕ) * T / ↑n))
        (MeasurableSpace.comap (Y i) inferInstance) μ := by
    intro i
    exact indep_of_comp hφ (W.independent_increments _ _ (hpt_nonneg i) (hpt_mono i))
  -- Yᵢ is F_{tᵢ₊₁}-measurable (W_{tᵢ₊₁} and W_{tᵢ} are adapted)
  have hY_adapted : ∀ i : Fin n,
      @Measurable Ω ℝ (W.F.σ_algebra ((↑(i : ℕ) + 1) * T / ↑n)) _ (Y i) := by
    intro i
    show @Measurable Ω ℝ (W.F.σ_algebra ((↑(i : ℕ) + 1) * T / ↑n)) _
      (fun ω => (incr i ω) ^ 2 - T / ↑n)
    apply Measurable.sub _ measurable_const
    apply Measurable.pow_const
    exact (bm_adapted W _).sub
      ((bm_adapted W _).mono (W.F.mono _ _ (hpt_mono i)) le_rfl)
  -- Orthogonality: E[aᵢ · aⱼ] = 0 for i ≠ j
  have horthog : ∀ i j : Fin n, i ≠ j → ∫ ω, a i ω * a j ω ∂μ = 0 := by
    intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    -- Suffices to prove for i < j (symmetric by mul_comm)
    suffices key : ∀ i' j' : Fin n, i'.val < j'.val →
        ∫ ω, a i' ω * a j' ω ∂μ = 0 by
      rcases lt_or_gt_of_ne hne with h | h
      · exact key i j h
      · rw [show (fun ω => a i ω * a j ω) = (fun ω => a j ω * a i ω) from by ext ω; ring]
        exact key j i h
    intro i j h
    -- Case i < j: rewrite aᵢaⱼ = (gᵢYᵢgⱼ) · Yⱼ
    have hregroup : ∀ ω, a i ω * a j ω =
        (g i ω * Y i ω * g j ω) * Y j ω := by intro ω; ring
    simp_rw [hregroup]
    -- gᵢYᵢgⱼ is F_{tⱼ}-measurable
    have hgi_at_j : @Measurable Ω ℝ (W.F.σ_algebra (↑(j : ℕ) * T / ↑n)) _ (g i) := by
      exact (hg_adapted i).mono (W.F.mono _ _ (by
        apply div_le_div_of_nonneg_right _ hn_pos.le
        have : (↑(i : ℕ) : ℝ) ≤ (↑(j : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_lt h
        nlinarith [hT])) le_rfl
    have hYi_at_j : @Measurable Ω ℝ (W.F.σ_algebra (↑(j : ℕ) * T / ↑n)) _ (Y i) := by
      exact (hY_adapted i).mono (W.F.mono _ _ (by
        apply div_le_div_of_nonneg_right _ hn_pos.le
        have : (↑(i : ℕ) : ℝ) + 1 ≤ (↑(j : ℕ) : ℝ) := by exact_mod_cast h
        nlinarith [hT])) le_rfl
    have hX_meas : @Measurable Ω ℝ (W.F.σ_algebra (↑(j : ℕ) * T / ↑n)) _
        (fun ω => g i ω * Y i ω * g j ω) := (hgi_at_j.mul hYi_at_j).mul (hg_adapted j)
    -- Integrability of gᵢYᵢgⱼ (product of bounded functions and integrable Y)
    have hX_int : Integrable (fun ω => g i ω * Y i ω * g j ω) μ := by
      have : Integrable (fun ω => g j ω * (g i ω * Y i ω)) μ :=
        (ha_int i).bdd_mul (hg_meas_ambient j).aestronglyMeasurable
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hg_bdd j ω)
      exact this.congr (ae_of_all _ fun ω => by ring)
    -- Apply integral_mul_zero_of_indep_zero_mean
    exact SPDE.Probability.integral_mul_zero_of_indep_zero_mean
      (W.F.le_ambient _) hX_meas hX_int (hY_int j) (hY_indep j) (hY_mean j)
  -- Y² integrability
  have hY_sq_int : ∀ i : Fin n, Integrable (fun ω => (Y i ω) ^ 2) μ := by
    intro i
    have hfun : ∀ ω, (Y i ω) ^ 2 =
        (incr i ω) ^ 4 + ((-2 * (T / ↑n)) * (incr i ω) ^ 2 + (T / ↑n) ^ 2) := by
      intro ω; ring
    simp_rw [hfun]
    have h4 : Integrable (fun ω => (incr i ω) ^ 4) μ :=
      W.increment_all_moments _ _ (hpt_nonneg i) (hpt_mono i) 4
    have h2c : Integrable (fun ω => (-2 * (T / ↑n)) * (incr i ω) ^ 2) μ :=
      (W.increment_sq_integrable _ _ (hpt_nonneg i) (hpt_mono i)).const_mul _
    have hbc : Integrable (fun ω =>
        (-2 * (T / ↑n)) * (incr i ω) ^ 2 + (T / ↑n) ^ 2) μ :=
      h2c.add (integrable_const _)
    exact h4.add hbc
  -- Independence of increments (IndepFun version, for cross-integrability)
  have hindep_incr : ∀ i j : Fin n, i.val < j.val →
      IndepFun (incr i) (incr j) μ := by
    intro i j hij
    have hdisjoint : (↑(i : ℕ) + 1) * T / ↑n ≤ ↑(j : ℕ) * T / ↑n := by
      apply div_le_div_of_nonneg_right _ hn_pos.le
      have : (↑(i : ℕ) + 1 : ℝ) ≤ ↑(j : ℕ) := by exact_mod_cast hij
      nlinarith [hT]
    exact W.disjoint_independent _ _ _ _
      (hpt_nonneg i) (hpt_mono i) hdisjoint (hpt_mono j)
  have hindep_Y_fun : ∀ i j : Fin n, i ≠ j → IndepFun (Y i) (Y j) μ := by
    intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hindep_incr i j h).comp hφ hφ
    · exact ((hindep_incr j i h).comp hφ hφ).symm
  -- a² integrability
  have ha_sq_int : ∀ i : Fin n, Integrable (fun ω => (a i ω) ^ 2) μ := by
    intro i
    have hsq : ∀ ω, (a i ω) ^ 2 = (g i ω) ^ 2 * (Y i ω) ^ 2 := fun ω => by ring
    simp_rw [hsq]
    exact (hY_sq_int i).bdd_mul
      ((hg_meas_ambient i).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (abs_le.mp (hg_bdd i ω)).1 (abs_le.mp (hg_bdd i ω)).2)
  -- Cross-integrability for Pythagoras
  have hcross_int : ∀ i j : Fin n, Integrable (fun ω => a i ω * a j ω) μ := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact (ha_sq_int i).congr (ae_of_all _ fun ω => by ring)
    · -- Rewrite a i * a j = (g i * g j) * (Y i * Y j)
      have hrewrite : (fun ω => a i ω * a j ω) =
          fun ω => (g i ω * g j ω) * (Y i ω * Y j ω) := by ext ω; ring
      rw [hrewrite]
      exact ((hindep_Y_fun i j hij).integrable_mul (hY_int i) (hY_int j)).bdd_mul
        ((hg_meas_ambient i).mul (hg_meas_ambient j)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          simp only [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hg_bdd i ω) (hg_bdd j ω) (abs_nonneg _) hC)
  -- Apply Pythagoras
  have hpythag := SPDE.Probability.sum_sq_integral_eq_sum_integral_sq a hcross_int horthog
  -- Bound each E[aᵢ²] ≤ C² · 2(T/n)²
  have hvar_bound : ∀ i : Fin n, ∫ ω, (a i ω) ^ 2 ∂μ ≤ C ^ 2 * (2 * (T / ↑n) ^ 2) := by
    intro i
    have hsq : ∀ ω, (a i ω) ^ 2 = (g i ω) ^ 2 * (Y i ω) ^ 2 := fun ω => by ring
    calc ∫ ω, (a i ω) ^ 2 ∂μ
        = ∫ ω, (g i ω) ^ 2 * (Y i ω) ^ 2 ∂μ :=
          integral_congr_ae (ae_of_all _ fun ω => hsq ω)
      _ ≤ ∫ ω, C ^ 2 * (Y i ω) ^ 2 ∂μ := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ fun ω => mul_nonneg (sq_nonneg _) (sq_nonneg _)
          · exact (hY_sq_int i).const_mul _
          · exact ae_of_all _ fun ω => by
              exact mul_le_mul_of_nonneg_right
                (sq_le_sq' (abs_le.mp (hg_bdd i ω)).1 (abs_le.mp (hg_bdd i ω)).2) (sq_nonneg _)
      _ = C ^ 2 * ∫ ω, (Y i ω) ^ 2 ∂μ := integral_const_mul _ _
      _ = C ^ 2 * (2 * (T / ↑n) ^ 2) := by
          congr 1
          have h := W.increment_sq_minus_dt_variance _ _ (hpt_nonneg i) (hpt_mono i)
          have hts : (↑(i : ℕ) + 1) * T / ↑n - ↑(i : ℕ) * T / ↑n = T / ↑n := by
            field_simp; ring
          simp_rw [hts] at h; exact h
  -- Combine: Σ E[aᵢ²] ≤ n · C²·2(T/n)² = 2C²T²/n
  suffices heq : ∫ ω, (∑ i : Fin n, a i ω) ^ 2 ∂μ ≤ C ^ 2 * (2 * T ^ 2 / ↑n) by
    exact heq
  calc ∫ ω, (∑ i : Fin n, a i ω) ^ 2 ∂μ
      = ∑ i : Fin n, ∫ ω, (a i ω) ^ 2 ∂μ := hpythag
    _ ≤ ∑ _i : Fin n, C ^ 2 * (2 * (T / ↑n) ^ 2) := Finset.sum_le_sum fun i _ => hvar_bound i
    _ = ↑n * (C ^ 2 * (2 * (T / ↑n) ^ 2)) := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ = C ^ 2 * (2 * T ^ 2 / ↑n) := by field_simp

/-- The square of the weighted QV sum is integrable.
    Used for the integrability step in `ito_formula_L2_convergence`. -/
theorem weighted_qv_sq_integrable (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (hn : 0 < n)
    (g : Fin n → Ω → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hg_adapted : ∀ i : Fin n,
      @Measurable Ω ℝ (W.F.σ_algebra (↑(i : ℕ) * T / ↑n)) _ (g i))
    (hg_bdd : ∀ i : Fin n, ∀ ω, |g i ω| ≤ C) :
    Integrable (fun ω => (∑ i : Fin n, g i ω *
      ((W.toAdapted.process ((↑(i : ℕ) + 1) * T / ↑n) ω -
        W.toAdapted.process (↑(i : ℕ) * T / ↑n) ω) ^ 2 - T / ↑n))^2) μ := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  -- Define incr, Y, a (same as in weighted_qv_sum_L2_bound)
  let incr : Fin n → Ω → ℝ := fun i ω =>
    W.toAdapted.process ((↑(i : ℕ) + 1) * T / ↑n) ω -
    W.toAdapted.process (↑(i : ℕ) * T / ↑n) ω
  let Y : Fin n → Ω → ℝ := fun i ω => (incr i ω) ^ 2 - T / ↑n
  let a : Fin n → Ω → ℝ := fun i ω => g i ω * Y i ω
  -- Partition time arithmetic
  have hpt_nonneg : ∀ i : Fin n, 0 ≤ (↑(i : ℕ) : ℝ) * T / ↑n := fun i => by positivity
  have hpt_mono : ∀ i : Fin n,
      (↑(i : ℕ) : ℝ) * T / ↑n ≤ (↑(i : ℕ) + 1) * T / ↑n := by
    intro i; apply div_le_div_of_nonneg_right _ hn_pos.le; nlinarith
  -- Ambient measurability of g
  have hg_meas_ambient : ∀ i : Fin n, Measurable (g i) :=
    fun i => (hg_adapted i).mono (W.F.le_ambient _) le_rfl
  -- Y i² integrable (expand as BM moments)
  have hY_sq_int : ∀ i : Fin n, Integrable (fun ω => (Y i ω) ^ 2) μ := by
    intro i
    have hfun : ∀ ω, (Y i ω) ^ 2 =
        (incr i ω) ^ 4 + ((-2 * (T / ↑n)) * (incr i ω) ^ 2 + (T / ↑n) ^ 2) := by
      intro ω; ring
    simp_rw [hfun]
    exact (W.increment_all_moments _ _ (hpt_nonneg i) (hpt_mono i) 4).add
      ((W.increment_sq_integrable _ _ (hpt_nonneg i) (hpt_mono i)).const_mul _ |>.add
        (integrable_const _))
  -- (a i)² integrable: bounded g² times integrable Y²
  have ha_sq_int : ∀ i : Fin n, Integrable (fun ω => (a i ω) ^ 2) μ := by
    intro i
    have hsq : ∀ ω, (a i ω) ^ 2 = (g i ω) ^ 2 * (Y i ω) ^ 2 := fun ω => by ring
    simp_rw [hsq]
    exact (hY_sq_int i).bdd_mul
      ((hg_meas_ambient i).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (abs_le.mp (hg_bdd i ω)).1 (abs_le.mp (hg_bdd i ω)).2)
  -- ∑ (a i)² integrable
  have hsum_sq_int : Integrable (fun ω => ∑ i : Fin n, (a i ω) ^ 2) μ :=
    integrable_finset_sum _ (fun i _ => ha_sq_int i)
  -- Cauchy-Schwarz bound: (∑ a i)² ≤ n * ∑ (a i)²
  have hdom : ∀ ω, (∑ i : Fin n, a i ω) ^ 2 ≤ ↑n * ∑ i : Fin n, (a i ω) ^ 2 := by
    intro ω
    have h := @sq_sum_le_card_mul_sum_sq (Fin n) ℝ _ _ _ _ Finset.univ (fun i => a i ω)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact h
  -- Measurability of (∑ a i)²
  have hincr_meas : ∀ i : Fin n, Measurable (incr i) := fun i =>
    ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl).sub
      ((W.toAdapted.adapted _).mono (W.F.le_ambient _) le_rfl)
  have ha_meas : ∀ i : Fin n, Measurable (a i) := fun i =>
    (hg_meas_ambient i).mul ((hincr_meas i).pow_const 2 |>.sub measurable_const)
  -- Apply domination
  exact (hsum_sq_int.const_mul (↑n : ℝ)).mono'
    ((Finset.measurable_sum _ (fun i _ => ha_meas i)).pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom ω)

/-- The weighted QV sum converges to 0 in L² as n → ∞.
    E[|Σ gᵢ · ((ΔWᵢ)² - Δtᵢ)|²] → 0 for adapted bounded weights. -/
theorem weighted_qv_L2_convergence (W : BrownianMotion Ω μ) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : 0 ≤ T) (C : ℝ) (hC : 0 ≤ C)
    (g : ∀ n : ℕ, Fin (n + 1) → Ω → ℝ)
    (hg_adapted : ∀ n : ℕ, ∀ i : Fin (n + 1),
      @Measurable Ω ℝ (W.F.σ_algebra (↑(i : ℕ) * T / ↑(n + 1))) _ (g n i))
    (hg_bdd : ∀ n : ℕ, ∀ i : Fin (n + 1), ∀ ω, |g n i ω| ≤ C) :
    Tendsto (fun n => ∫ ω, (∑ i : Fin (n + 1), g n i ω *
      ((W.toAdapted.process ((↑(i : ℕ) + 1) * T / ↑(n + 1)) ω -
        W.toAdapted.process (↑(i : ℕ) * T / ↑(n + 1)) ω) ^ 2 -
        T / ↑(n + 1)))^2 ∂μ)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n; positivity
  · intro n
    exact weighted_qv_sum_L2_bound W T hT (n + 1) (Nat.succ_pos n)
      (g n) C hC (hg_adapted n) (hg_bdd n)
  · have h : (fun n : ℕ => C ^ 2 * (2 * T ^ 2 / (↑(n + 1) : ℝ))) =
        (fun n : ℕ => (C ^ 2 * (2 * T ^ 2)) * (1 / ((↑n : ℝ) + 1))) := by
      ext n; rw [Nat.cast_succ]; ring
    rw [h, show (0 : ℝ) = (C ^ 2 * (2 * T ^ 2)) * 0 from by ring]
    exact tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat

end SPDE