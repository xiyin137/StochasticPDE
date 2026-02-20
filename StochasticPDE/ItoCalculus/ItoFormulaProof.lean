/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.StochasticIntegration
import StochasticPDE.ItoCalculus.ItoFormulaInfrastructure
import StochasticPDE.ItoCalculus.ItoFormulaDecomposition
import StochasticPDE.ItoCalculus.ItoIntegralProperties
import StochasticPDE.ItoCalculus.QVConvergence
import StochasticPDE.ItoCalculus.WeightedQVBound
import Mathlib.Analysis.Calculus.Taylor

/-!
# Itô Formula Proof Infrastructure

This file provides the proof of the Itô formula martingale property (part ii).

## Strategy

The key theorem `ito_formula_martingale` shows that the stochastic integral remainder
M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [generalized drift] ds is a martingale.

**Proof approach**: Show M_t is an L² limit of simple stochastic integrals,
then apply `ito_integral_martingale_setIntegral`.

For partition 0 = t₀ < t₁ < ... < tₙ = T, construct simple process:
  H_n(s) = ∂_x f(tᵢ, X_{tᵢ}) · σ_{tᵢ}  on [tᵢ, tᵢ₊₁)

Then: stoch_int(T) - ∫ H_n dW_T = error terms → 0 in L².

Error decomposition:
- Taylor remainder: controlled by ‖f''‖_∞ · |ΔX|³
- Weighted QV: Σ f''·σ² · [(ΔW)² - Δt] → 0 (weighted_qv_L2_convergence)
- Riemann sum error: Σ g(tᵢ)Δt - ∫ g ds → 0
- Cross terms: (Δt)·(ΔW) terms are O(Δt^{3/2})

## Main results

- `itoPartitionProcess`: construction of approximating simple process
- `ito_formula_L2_convergence`: the L² convergence estimate
- `ito_formula_martingale`: the martingale property
-/

open MeasureTheory ProbabilityTheory Real Filter Finset
open scoped NNReal

noncomputable section

namespace SPDE

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Taylor expansion bound for C² functions

Second-order Taylor: f(x) = f(a) + f'(a)(x-a) + ½f''(ξ)(x-a)² for some ξ.
We use the Lagrange form remainder bound from Mathlib. -/

/-- Second-order Taylor bound: for C² function f on [a, b],
    |f(b) - f(a) - f'(a)(b-a)| ≤ M · (b-a)² where M bounds |f''|.

    This is `taylor_mean_remainder_bound` from Mathlib with n=1. -/
theorem taylor_second_order_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b)) {M : ℝ}
    (hM : ∀ y ∈ Set.Icc a b, ‖iteratedDerivWithin 2 f (Set.Icc a b) y‖ ≤ M) :
    ‖f b - taylorWithinEval f 1 (Set.Icc a b) a b‖ ≤ M * (b - a) ^ 2 := by
  have h := taylor_mean_remainder_bound hab hf (Set.right_mem_Icc.mpr hab) hM
  simp only [show (1 : ℕ) + 1 = 2 from rfl, Nat.factorial_one, Nat.cast_one, div_one] at h
  exact h

/-- The 1st-order Taylor polynomial of f at a evaluated at b equals f(a) + f'(a)(b-a). -/
theorem taylorWithinEval_one {f : ℝ → ℝ} {a b : ℝ} {s : Set ℝ} :
    taylorWithinEval f 1 s a b = f a + derivWithin f s a * (b - a) := by
  rw [taylor_within_apply]
  simp [Finset.sum_range_succ]
  ring

/-- Derivative of a C² function is continuous. -/
theorem contDiff_two_deriv_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (deriv f) :=
  ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2.continuous

/-- Bound on integral of bounded function over [0, u] ⊂ [0, T]. -/
private lemma integral_abs_le_of_bdd (g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ s, ‖g s‖ ≤ C) (u T : ℝ) (hu : 0 ≤ u) (huT : u ≤ T) :
    ‖∫ s in Set.Icc 0 u, g s ∂volume‖ ≤ C * T := by
  have h_meas : volume (Set.Icc (0 : ℝ) u) < ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  calc ‖∫ s in Set.Icc 0 u, g s ∂volume‖
      ≤ C * (volume (Set.Icc (0 : ℝ) u)).toReal :=
        norm_setIntegral_le_of_norm_le_const h_meas (fun s _ => hg s)
    _ = C * u := by
        rw [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hu]
    _ ≤ C * T := by nlinarith

/-- Bound on |Σ cᵢ · dᵢ| when |cᵢ| ≤ C and dᵢ ≥ 0: |Σ cᵢ dᵢ| ≤ C · Σ dᵢ.
    Used for sums like |Σ ½f'' · ΔX²| ≤ ½Mf'' · Sk. -/
private lemma abs_sum_mul_le_of_abs_le_nonneg {ι : Type*} {s : Finset ι}
    {c : ι → ℝ} {d : ι → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hc : ∀ i ∈ s, |c i| ≤ C) (hd : ∀ i ∈ s, 0 ≤ d i) :
    |∑ i ∈ s, c i * d i| ≤ C * ∑ i ∈ s, d i := by
  have h1 : |∑ i ∈ s, c i * d i| ≤ ∑ i ∈ s, |c i * d i| :=
    Finset.abs_sum_le_sum_abs (fun i => c i * d i) s
  have h2 : ∀ i ∈ s, |c i * d i| ≤ C * d i := fun i hi => by
    rw [abs_mul, abs_of_nonneg (hd i hi)]
    exact mul_le_mul_of_nonneg_right (hc i hi) (hd i hi)
  have h3 : ∑ i ∈ s, |c i * d i| ≤ ∑ i ∈ s, C * d i :=
    Finset.sum_le_sum h2
  have h4 : ∑ i ∈ s, C * d i = C * ∑ i ∈ s, d i :=
    (Finset.mul_sum s (fun i => d i) C).symm
  linarith

/-- min(·, c) is non-expansive: min b c - min a c ≤ b - a when a ≤ b -/
private lemma min_sub_min_le_sub {a b c : ℝ} (h : a ≤ b) :
    min b c - min a c ≤ b - a := by
  simp only [min_def]; split_ifs <;> linarith

/-- MVT bound: f Lipschitz in time direction -/
private lemma time_lipschitz {f : ℝ → ℝ → ℝ} {Mft : ℝ}
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hMft : ∀ t x, |deriv (fun s => f s x) t| ≤ Mft) (a b y : ℝ) :
    |f a y - f b y| ≤ Mft * |a - b| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hf_t y) t)
    (fun t _ => by rw [Real.norm_eq_abs]; exact hMft t y)
    convex_univ (Set.mem_univ a) (Set.mem_univ b)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  rwa [abs_sub_comm (f b y), abs_sub_comm b] at this

/-! ## Integral infrastructure for Riemann sum convergence -/

/-- Convert a Fin sum of f(↑i) to a Finset.range sum of f(i). -/
private lemma fin_sum_eq_range_sum {n : ℕ} (f : ℕ → ℝ) :
    ∑ i : Fin n, f ↑i = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Finset.sum_range_succ]

/-- Integral splitting for capped partition: ∫₀ᵘ g = Σᵢ ∫_{τᵢ}^{τᵢ₊₁} g
    where τᵢ = min(i·T/(n+1), u).
    Uses `sum_integral_adjacent_intervals` from Mathlib with Icc↔interval conversion. -/
private lemma integral_eq_sum_capped_intervals {g : ℝ → ℝ} {n : ℕ} {T u : ℝ}
    (hg : IntegrableOn g (Set.Icc 0 u) volume)
    (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) :
    ∫ s in Set.Icc 0 u, g s ∂volume =
    ∑ i : Fin (n + 1), ∫ s in Set.Icc
      (min (↑(i : ℕ) * T / ↑(n + 1)) u)
      (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u), g s ∂volume := by
  -- Define τ(i) = min(i * T / (n+1), u)
  let τ : ℕ → ℝ := fun i => min (↑i * T / ↑(n + 1)) u
  -- τ is monotone
  have hτ_mono : Monotone τ := by
    intro i j hij
    apply min_le_min _ le_rfl
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < ↑(n + 1)).le
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hT.le
  -- τ(0) = 0
  have hτ0 : τ 0 = 0 := by simp [τ, min_eq_left hu]
  -- τ(n+1) = u
  have hτn : τ (n + 1) = u := by
    simp only [τ]
    rw [show (↑(n + 1) : ℝ) * T / ↑(n + 1) = T from by field_simp]
    exact min_eq_right huT
  -- Icc ↔ interval integral conversion
  have hicc_eq : ∀ {a b : ℝ}, a ≤ b →
      ∫ s in Set.Icc a b, g s ∂volume = ∫ s in a..b, g s := by
    intro a b hab
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab]
  -- Sub-interval integrability
  have hint : ∀ k < n + 1, IntervalIntegrable g volume (τ k) (τ (k + 1)) := by
    intro k hk
    apply IntegrableOn.intervalIntegrable
    rw [Set.uIcc_of_le (hτ_mono (Nat.le_succ k))]
    exact hg.mono_set (Set.Icc_subset_Icc
      (by rw [← hτ0]; exact hτ_mono (Nat.zero_le _))
      (by rw [← hτn]; exact hτ_mono (by omega)))
  -- Main proof chain
  calc ∫ s in Set.Icc 0 u, g s ∂volume
      = ∫ s in (0 : ℝ)..u, g s := hicc_eq hu
    _ = ∫ s in (τ 0)..(τ (n + 1)), g s := by rw [hτ0, hτn]
    _ = ∑ k ∈ Finset.range (n + 1), ∫ x in (τ k)..(τ (k + 1)), g x := by
          rw [intervalIntegral.sum_integral_adjacent_intervals hint]
    _ = ∑ i : Fin (n + 1), (fun j => ∫ x in (τ j)..(τ (j + 1)), g x) ↑i := by
          rw [← fin_sum_eq_range_sum]
    _ = ∑ i : Fin (n + 1), ∫ x in (τ ↑i)..(τ (↑i + 1)), g x := by
          congr
    _ = ∑ i : Fin (n + 1), ∫ s in Set.Icc (τ ↑i) (τ (↑i + 1)), g s ∂volume := by
          congr 1; ext ⟨i, hi⟩
          exact (hicc_eq (hτ_mono (Nat.le_succ i))).symm
    _ = ∑ i : Fin (n + 1), ∫ s in Set.Icc
          (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u), g s ∂volume := by
          congr 1; ext ⟨i, hi⟩; dsimp only [τ]; push_cast; ring_nf

/-- FTC on closed interval: g(b) - g(a) = ∫ s in Icc a b, deriv g s
    for differentiable g with continuous derivative.
    Follows from `intervalIntegral.integral_eq_sub_of_hasDerivAt`
    with conversion between interval and set integral. -/
private lemma ftc_set_integral {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    (hg' : Continuous (deriv g)) {a b : ℝ} (hab : a ≤ b) :
    g b - g a = ∫ s in Set.Icc a b, deriv g s ∂volume := by
  symm
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hg x)
    (hg'.intervalIntegrable a b)

/-- Telescoping sum for Fin: Σᵢ (f(i+1) - f(i)) = f(n) - f(0). -/
private lemma fin_sum_telescoping (f : ℕ → ℝ) (n : ℕ) :
    ∑ i : Fin n, (f (↑i + 1) - f ↑i) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]; ring

/-- Telescoping: Σ (τᵢ₊₁ - τᵢ) = u for capped partition.
    Proof: Σᵢ₌₀ⁿ (τᵢ₊₁ - τᵢ) = τₙ₊₁ - τ₀ = min(T,u) - min(0,u) = u - 0 = u. -/
private lemma sum_capped_partition_widths {n : ℕ} {T u : ℝ}
    (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T) :
    ∑ i : Fin (n + 1), (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
      min (↑(i : ℕ) * T / ↑(n + 1)) u) = u := by
  -- Define τ(i) = min(i * T / (n+1), u)
  let τ : ℕ → ℝ := fun i => min (↑i * T / ↑(n + 1)) u
  -- Rewrite summand to match τ(i+1) - τ(i)
  have hsummand : ∀ i : Fin (n + 1),
      min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u - min (↑(i : ℕ) * T / ↑(n + 1)) u =
      τ ((i : ℕ) + 1) - τ (i : ℕ) := by
    intro i; simp only [τ, Nat.cast_add, Nat.cast_one]
  simp_rw [hsummand]
  -- Apply telescoping
  rw [fin_sum_telescoping τ (n + 1)]
  -- τ(n+1) - τ(0) = u - 0 = u
  simp only [τ]
  have h0 : min (↑(0 : ℕ) * T / ↑(n + 1)) u = 0 := by
    simp [min_eq_left hu]
  have hn : min (↑(n + 1) * T / ↑(n + 1)) u = u := by
    have hpos : (↑(n + 1) : ℝ) ≠ 0 := ne_of_gt (by positivity)
    rw [show (↑(n + 1) : ℝ) * T / ↑(n + 1) = T from by field_simp]
    exact min_eq_right huT
  rw [h0, hn, sub_zero]

/-- Partition error bound: if each sub-integral is within C·Δτᵢ of the corresponding cᵢ,
    then the total error |∫g - Σcᵢ| ≤ C·u. Abstracts the common pattern in E1 and E2. -/
private lemma partition_error_bound {g : ℝ → ℝ} {n : ℕ} {T u C : ℝ}
    {c : Fin (n + 1) → ℝ}
    (hg_int : IntegrableOn g (Set.Icc 0 u) volume)
    (_hC : 0 ≤ C) (hT : 0 < T) (hu : 0 ≤ u) (huT : u ≤ T)
    (hbound : ∀ i : Fin (n + 1),
        |∫ s in Set.Icc
          (min (↑(i : ℕ) * T / ↑(n + 1)) u) (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          g s ∂volume - c i| ≤
        C * (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u - min (↑(i : ℕ) * T / ↑(n + 1)) u)) :
    |∫ s in Set.Icc 0 u, g s ∂volume - ∑ i : Fin (n + 1), c i| ≤ C * u := by
  rw [integral_eq_sum_capped_intervals hg_int hT hu huT, ← Finset.sum_sub_distrib]
  calc |∑ i : Fin (n + 1), _|
      ≤ ∑ i : Fin (n + 1), |∫ s in Set.Icc
          (min (↑(i : ℕ) * T / ↑(n + 1)) u) (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          g s ∂volume - c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n + 1),
          C * (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
            min (↑(i : ℕ) * T / ↑(n + 1)) u) :=
        Finset.sum_le_sum fun i _ => hbound i
    _ = C * u := by
        rw [← Finset.mul_sum]
        exact congrArg (C * ·) (sum_capped_partition_widths hT hu huT)

/-! ## Construction of partition simple process -/

/-- For a partition of [0, T] into n equal parts, the partition time for index i. -/
def partitionTime (T : ℝ) (n : ℕ) (i : ℕ) : ℝ := ↑i * T / ↑n

/-- Partition times are nonneg when T ≥ 0. -/
theorem partitionTime_nonneg {T : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n) (i : ℕ) :
    0 ≤ partitionTime T n i := by
  unfold partitionTime; positivity

/-- Partition times are monotone when T ≥ 0. -/
theorem partitionTime_mono {T : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n) {i j : ℕ} (hij : i ≤ j) :
    partitionTime T n i ≤ partitionTime T n j := by
  unfold partitionTime
  apply div_le_div_of_nonneg_right _ (Nat.cast_pos.mpr hn).le
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hT

/-- Partition times are strictly monotone when T > 0. -/
theorem partitionTime_strictMono {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n)
    {i j : ℕ} (hij : i < j) :
    partitionTime T n i < partitionTime T n j := by
  unfold partitionTime
  apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr hn)
  exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij) hT

/-- Partition time at n equals T. -/
theorem partitionTime_n {T : ℝ} {n : ℕ} (hn : 0 < n) :
    partitionTime T n n = T := by
  unfold partitionTime; field_simp

/-- The time step T/n. -/
theorem partitionTime_step {T : ℝ} {n : ℕ} (_hn : 0 < n) (i : ℕ) :
    partitionTime T n (i + 1) - partitionTime T n i = T / ↑n := by
  unfold partitionTime
  rw [Nat.cast_succ, add_mul, one_mul, add_div, add_sub_cancel_left]

/-- Construct the approximating simple process for the Itô formula.

    For a uniform partition of [0, T] with n intervals, the simple process
    has values ∂_x f(tᵢ, X_{tᵢ}) · σ_{tᵢ} on [tᵢ, tᵢ₊₁).

    We need n+1 partition points for n intervals. -/
def itoPartitionProcess {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) : SimpleProcess F where
  n := n + 1
  times i := partitionTime T n (i : ℕ)
  values i ω :=
    deriv (fun x => f (partitionTime T n (i : ℕ)) x) (X.process (partitionTime T n (i : ℕ)) ω) *
    X.diffusion (partitionTime T n (i : ℕ)) ω
  increasing := by
    intro i j hij
    exact partitionTime_strictMono hT hn (by exact hij)
  adapted := by
    intro i
    have hderiv_cont : Continuous (deriv (fun x => f (partitionTime T n (i : ℕ)) x)) :=
      contDiff_two_deriv_continuous (hf_x _)
    have hX_meas : Measurable (X.process (partitionTime T n (i : ℕ))) :=
      (X.process_adapted _).mono (F.le_ambient _) le_rfl
    exact (hderiv_cont.measurable.comp hX_meas).mul (hdiff_meas _)

/-! ## Adapted properties of the partition process

These lemmas verify that the partition simple process satisfies the hypotheses
needed for `ito_integral_martingale_setIntegral`. -/

/-- The partition process values are BM.F-adapted.
    This is the adaptedness condition needed for the martingale theorem. -/
theorem itoPartitionProcess_adapted {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ) (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t)) :
    ∀ i : Fin (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).n,
      @Measurable Ω ℝ (X.BM.F.σ_algebra
        ((itoPartitionProcess X f hf_x hdiff_meas T hT n hn).times i)) _
        ((itoPartitionProcess X f hf_x hdiff_meas T hT n hn).values i) := by
  intro i
  show @Measurable Ω ℝ (X.BM.F.σ_algebra (partitionTime T n (i : ℕ))) _
    (fun ω => deriv (fun x => f (partitionTime T n (i : ℕ)) x)
      (X.process (partitionTime T n (i : ℕ)) ω) *
      X.diffusion (partitionTime T n (i : ℕ)) ω)
  have hderiv_cont : Continuous (deriv (fun x => f (partitionTime T n (i : ℕ)) x)) :=
    contDiff_two_deriv_continuous (hf_x _)
  -- X.process is F-adapted, and F ≤ BM.F
  have hX_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (partitionTime T n (i : ℕ))) _
      (X.process (partitionTime T n (i : ℕ))) :=
    (X.process_adapted _).mono (X.F_le_BM_F _) le_rfl
  have hdiff_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (partitionTime T n (i : ℕ))) _
      (X.diffusion (partitionTime T n (i : ℕ))) :=
    (hdiff_adapted _).mono (X.F_le_BM_F _) le_rfl
  exact (hderiv_cont.measurable.comp hX_BM).mul hdiff_BM

/-- The partition process values are bounded when f' and σ are bounded. -/
theorem itoPartitionProcess_bounded {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M) :
    ∀ i : Fin (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).n,
      ∃ C : ℝ, ∀ ω, |(itoPartitionProcess X f hf_x hdiff_meas T hT n hn).values i ω| ≤ C := by
  intro i
  obtain ⟨M₁, hM₁⟩ := hf_x_bdd
  obtain ⟨M₂, hM₂⟩ := hdiff_bdd
  refine ⟨|M₁| * |M₂|, fun ω => ?_⟩
  show |deriv (fun x => f _ x) _ * X.diffusion _ ω| ≤ _
  rw [abs_mul]
  exact mul_le_mul
    (le_trans (hM₁ _ _) (le_abs_self M₁))
    (le_trans (hM₂ _ _) (le_abs_self M₂))
    (abs_nonneg _) (abs_nonneg _)

/-- The partition process times are nonneg. -/
theorem itoPartitionProcess_times_nonneg {F : Filtration Ω ℝ}
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 0 < n) :
    ∀ i : Fin (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).n,
      0 ≤ (itoPartitionProcess X f hf_x hdiff_meas T hT n hn).times i := by
  intro i
  show 0 ≤ partitionTime T n _
  exact partitionTime_nonneg hT.le hn _

/-! ## Itô formula remainder definition -/

/-- The Itô formula remainder (stochastic integral part):
    M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds

    This is the process that the Itô formula asserts is a martingale. -/
def itoRemainder {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  f t (X.process t ω) - f 0 (X.process 0 ω) -
  ∫ s in Set.Icc 0 t,
    (deriv (fun u => f u (X.process s ω)) s +
     deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
     (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2) ∂volume

/-! ## Second derivative continuity -/

/-- The second derivative of a C² function is continuous. -/
theorem contDiff_two_snd_deriv_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (deriv (deriv f)) :=
  ((contDiff_succ_iff_deriv (n := 0)).mp
    ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).2.2.continuous

/-! ## Weighted QV convergence for Itô formula

The key analytical estimate: the weighted quadratic variation term
  Σᵢ ½f''(tᵢ, Xᵢ) · σ²ᵢ · [(ΔWᵢ)² - Δtᵢ]
converges to 0 in L² as the partition mesh → 0.

This is the mathematical core of the Itô formula proof, using
`weighted_qv_L2_convergence` from ItoFormulaInfrastructure.lean. -/

/-- The QV weights ½f''(tᵢ, Xᵢ)σ²ᵢ are BM.F-adapted at partition times.
    This is needed to apply `weighted_qv_L2_convergence`. -/
theorem ito_qv_weights_adapted {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (t : ℝ) (n : ℕ) :
    ∀ i : Fin (n + 1),
    @Measurable Ω ℝ (X.BM.F.σ_algebra (↑(i : ℕ) * t / ↑(n + 1))) _
      (fun ω => (1 : ℝ) / 2 *
        deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
          (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
        (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) := by
  intro i
  -- f'' is continuous (from C² regularity)
  have hf''_cont : Continuous (deriv (deriv (fun x =>
      f (↑(i : ℕ) * t / ↑(n + 1)) x))) :=
    contDiff_two_snd_deriv_continuous (hf_x _)
  -- X.process is BM.F-adapted (from process_adapted + F_le_BM_F)
  have hX_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (↑(i : ℕ) * t / ↑(n + 1))) _
      (X.process (↑(i : ℕ) * t / ↑(n + 1))) :=
    (X.process_adapted _).mono (X.F_le_BM_F _) le_rfl
  -- σ is BM.F-adapted
  have hσ_BM : @Measurable Ω ℝ (X.BM.F.σ_algebra (↑(i : ℕ) * t / ↑(n + 1))) _
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1))) :=
    (hdiff_adapted _).mono (X.F_le_BM_F _) le_rfl
  -- f''(X(·)) is BM.F-measurable (composition of continuous and measurable)
  have hf''_comp := hf''_cont.measurable.comp hX_BM
  -- Full weight: (1/2 * f''(X)) * σ² is BM.F-measurable
  -- Uses: const is measurable, f''∘X is measurable, σ² is measurable
  apply Measurable.mul
  · exact Measurable.mul measurable_const hf''_comp
  · exact hσ_BM.pow_const 2

/-- The QV weights ½f''(tᵢ, Xᵢ)σ²ᵢ are uniformly bounded.
    Bound: |g| ≤ ½ · |Mf| · Mσ² where Mf bounds |f''| and Mσ bounds |σ|. -/
theorem ito_qv_weights_bounded {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    {Mf : ℝ} (hMf : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mf)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (t : ℝ) (n : ℕ) :
    ∀ i : Fin (n + 1), ∀ ω,
    |(1 : ℝ) / 2 *
      deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2| ≤
    1 / 2 * |Mf| * Mσ ^ 2 := by
  intro i ω
  have h1 : |deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
      (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω)| ≤ |Mf| :=
    le_trans (hMf _ _) (le_abs_self _)
  have h2 : |(X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2| ≤ Mσ ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (abs_le.mp (hMσ _ ω)).1 (abs_le.mp (hMσ _ ω)).2
  calc |(1 : ℝ) / 2 *
      deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2|
      = |(1 : ℝ) / 2| *
        |deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
          (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω)| *
        |(X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 / 2 * |Mf| * Mσ ^ 2 := by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
          (abs_nonneg _) (by positivity)

/-- The weighted QV term in the Itô formula converges to 0 in L².

    For partition 0 = t₀ < t₁ < ... < tₙ = t with uniform mesh t/n:
    E[(Σᵢ ½f''(tᵢ, X_{tᵢ}) · σ²_{tᵢ} · ((ΔWᵢ)² - Δtᵢ))²] → 0.

    This is the primary analytical content of the Itô formula. -/
theorem ito_weighted_qv_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    Filter.Tendsto
      (fun n => ∫ ω,
        (∑ i : Fin (n + 1),
          ((1 : ℝ) / 2 *
            deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
              (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
            (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2) *
          ((X.BM.toAdapted.process ((↑(i : ℕ) + 1) * t / ↑(n + 1)) ω -
            X.BM.toAdapted.process (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2 -
           t / ↑(n + 1)))^2 ∂μ)
      atTop (nhds 0) := by
  -- Extract explicit bounds from hypotheses
  obtain ⟨Mf, hMf⟩ := hf_xx_bdd
  obtain ⟨Mσ, hMσ⟩ := hdiff_bdd
  -- Apply weighted_qv_L2_convergence with bound C = ½|Mf|Mσ²
  exact weighted_qv_L2_convergence X.BM t ht (1 / 2 * |Mf| * Mσ ^ 2) (by positivity)
    (fun n i => fun ω => (1 : ℝ) / 2 *
      deriv (deriv (fun x => f (↑(i : ℕ) * t / ↑(n + 1)) x))
        (X.process (↑(i : ℕ) * t / ↑(n + 1)) ω) *
      (X.diffusion (↑(i : ℕ) * t / ↑(n + 1)) ω) ^ 2)
    (fun n => ito_qv_weights_adapted X f hf_x hdiff_adapted t n)
    (fun n i ω => ito_qv_weights_bounded X f hMf hMσ t n i ω)

/-! ## SI-increment martingale approach

Instead of approximating the Itô formula remainder via simple stochastic integrals
of the partition process f'(tᵢ)·σ(tᵢ) (which requires σ-continuity in time to
converge in L²), we directly use the stochastic integral increments
ΔSIᵢ = SI(tᵢ₊₁) - SI(tᵢ).

Define: M_n(u) = Σᵢ f'ₓ(tᵢ, X_{tᵢ}) · [SI(min(tᵢ₊₁, u)) - SI(min(tᵢ, u))]

**Martingale property**: For 0 ≤ v ≤ u and A ∈ F_v,
  ∫_A M_n(u) = ∫_A M_n(v)
follows term-by-term from SI being a martingale and f'(X_{tᵢ}) being F_{tᵢ}-adapted,
via `stoch_integral_martingale` + `integral_mul_eq_zero_of_setIntegral_eq_zero`.

**L² convergence**: M_n(u) → itoRemainder(u) in L² as mesh → 0.
The error decomposes as:
- Riemann sum errors for ∂_t f and f'·μ (bounded integrands, mesh → 0)
- Weighted QV error: Σ ½f''·(ΔX)² → ∫ ½f''·σ² ds (QV convergence)
- Taylor remainders: Σ Rᵢ → 0 (proved in `taylor_remainder_L2_convergence`)

None of these require σ-continuity in time. -/

/-- The SI-increment approximation to the Itô formula remainder.
    For uniform partition 0 = t₀ < t₁ < ... < t_{n+1} = T, at time u:
    M_n(u, ω) = Σᵢ f'ₓ(tᵢ, X_{tᵢ}(ω)) · [SI(min(tᵢ₊₁, u), ω) - SI(min(tᵢ, u), ω)]
    where tᵢ = i · T / (n+1). -/
def siIncrementApprox {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (T : ℝ) (n : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin (n + 1),
    deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
      (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω) *
    (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
     X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω)

/-- The SI-increment approximation is integrable at each time u ≥ 0.
    Each term is bounded f'(X_{tᵢ}) (bounded by Mf') times an SI increment
    (L²-integrable hence L¹ on probability space). The finite sum is integrable. -/
theorem si_increment_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (T : ℝ) (_hT : 0 ≤ T) (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (siIncrementApprox X f T n u) μ := by
  -- Each term: bounded × integrable = integrable
  -- f'(X_{t_i}) is bounded by Mf', SI increments are L¹ (from L²)
  unfold siIncrementApprox
  apply integrable_finset_sum
  intro i _
  obtain ⟨Mf', hMf'⟩ := hf_x_bdd
  -- The SI values are integrable at nonneg times
  have h_nn1 : 0 ≤ min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u :=
    le_min (by positivity) hu
  have h_nn2 : 0 ≤ min (↑(i : ℕ) * T / ↑(n + 1)) u :=
    le_min (by positivity) hu
  have hSI_int := (X.stoch_integral_integrable _ h_nn1).sub
    (X.stoch_integral_integrable _ h_nn2)
  -- f'(X_{t_i}) is bounded and measurable
  have hf'_meas : Measurable (fun ω =>
      deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
        (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω)) :=
    (contDiff_two_deriv_continuous (hf_x _)).measurable.comp
      ((X.process_adapted _).mono (F.le_ambient _) le_rfl)
  exact hSI_int.bdd_mul hf'_meas.aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hMf' _ _)

/-- The squared difference (M_n(u) - itoRemainder(u))² is integrable.
    Follows from (a-b)² ≤ 2a²+2b², both terms being integrable. -/
theorem si_increment_diff_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hrem_int : Integrable (itoRemainder X f u) μ)
    (hrem_sq_int : Integrable (fun ω => (itoRemainder X f u ω)^2) μ) :
    Integrable (fun ω => (siIncrementApprox X f T n u ω - itoRemainder X f u ω) ^ 2) μ := by
  -- (a - b)² ≤ 2a² + 2b²
  have hM_int := si_increment_integrable X f hf_x hf_x_bdd T hT n u hu
  have hdiff_int := hM_int.sub hrem_int
  -- Need AEStronglyMeasurable for the square
  have hasm : AEStronglyMeasurable
      (fun ω => (siIncrementApprox X f T n u ω - itoRemainder X f u ω) ^ 2) μ :=
    (hdiff_int.aestronglyMeasurable.mul hdiff_int.aestronglyMeasurable).congr
      (ae_of_all _ fun ω => by
        show (siIncrementApprox X f T n u ω - itoRemainder X f u ω) *
          (siIncrementApprox X f T n u ω - itoRemainder X f u ω) =
          (siIncrementApprox X f T n u ω - itoRemainder X f u ω) ^ 2
        ring)
  -- Use MemLp 2 approach: show M_n ∈ L² and R ∈ L², then difference ∈ L²
  -- itoRemainder ∈ L²
  have hR_memLp : MemLp (itoRemainder X f u) 2 μ :=
    (memLp_two_iff_integrable_sq hrem_int.aestronglyMeasurable).mpr hrem_sq_int
  -- Suffices to show siIncrementApprox ∈ L²
  suffices hM_memLp : MemLp (siIncrementApprox X f T n u) 2 μ by
    have hdiff_memLp := hM_memLp.sub hR_memLp
    exact (memLp_two_iff_integrable_sq hdiff_memLp.1).mp hdiff_memLp
  -- siIncrementApprox = Σᵢ f'(X_{tᵢ}) · ΔSI_i, each term ∈ L²
  unfold siIncrementApprox
  apply memLp_finset_sum
  intro i _
  -- f'(X_{tᵢ}) is bounded, SI increment is L²
  obtain ⟨Mf', hMf'⟩ := hf_x_bdd
  have h_nn1 : 0 ≤ min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u :=
    le_min (by positivity) hu
  have h_nn2 : 0 ≤ min (↑(i : ℕ) * T / ↑(n + 1)) u :=
    le_min (by positivity) hu
  -- SI increment is L²
  have hSI_memLp : MemLp (fun ω =>
      X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
      X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) 2 μ :=
    ((memLp_two_iff_integrable_sq
        (X.stoch_integral_integrable _ h_nn1).aestronglyMeasurable).mpr
      (X.stoch_integral_sq_integrable _ h_nn1)).sub
    ((memLp_two_iff_integrable_sq
        (X.stoch_integral_integrable _ h_nn2).aestronglyMeasurable).mpr
      (X.stoch_integral_sq_integrable _ h_nn2))
  -- f'(X_{tᵢ}) · ΔSI ∈ L²: bounded × L² → L²
  have hf'_meas : AEStronglyMeasurable (fun ω =>
      deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
        (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω)) μ :=
    ((contDiff_two_deriv_continuous (hf_x _)).measurable.comp
      ((X.process_adapted _).mono (F.le_ambient _) le_rfl)).aestronglyMeasurable
  -- Use: if g is bounded and h ∈ L², then g·h ∈ L²
  -- Proof: ∫|g·h|² = ∫ g²·h² ≤ M²·∫|h|², hence MemLp 2
  have hprod_asm : AEStronglyMeasurable (fun ω =>
      deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
        (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω) *
      (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω)) μ :=
    hf'_meas.mul hSI_memLp.1
  rw [memLp_two_iff_integrable_sq hprod_asm]
  have hsq_eq : (fun ω => (deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
        (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω) *
      (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω)) ^ 2) =
    (fun ω => (deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
        (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω)) ^ 2 *
      (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) := by
    ext ω; ring
  rw [hsq_eq]
  -- ΔSI² is integrable (from MemLp 2)
  have hSI_sq_int : Integrable (fun ω =>
      (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hSI_memLp.1).mp hSI_memLp
  have hf'_sq_asm : AEStronglyMeasurable (fun ω =>
      (deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
        (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω)) ^ 2) μ :=
    (hf'_meas.mul hf'_meas).congr (ae_of_all _ fun ω => by simp [Pi.mul_apply, sq])
  exact hSI_sq_int.bdd_mul (c := Mf' ^ 2)
    hf'_sq_asm
    (ae_of_all _ fun ω => by
      simp only [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hMf' _ _) 2)

/-- Helper: For bounded F_τ-measurable g, A ∈ F_τ, and 0 ≤ τ ≤ s ≤ t:
    ∫_A g · [SI(t) - SI(s)] = 0.
    Core tool for proving the martingale property of SI-increment approximations.
    Proof converts ∫_A g·Y to ∫ (1_A·g)·Y and applies
    `integral_mul_eq_zero_of_setIntegral_eq_zero`. -/
private lemma setIntegral_adapted_mul_si_increment_eq_zero
    {F : Filtration Ω ℝ} [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (g : Ω → ℝ) (τ s t : ℝ) (hτ : 0 ≤ τ) (hτs : τ ≤ s) (hst : s ≤ t)
    (hg_meas : @Measurable Ω ℝ (F.σ_algebra τ) _ g)
    (hg_bdd : ∃ C : ℝ, ∀ ω, |g ω| ≤ C)
    {A : Set Ω} (hA : @MeasurableSet Ω (F.σ_algebra τ) A) :
    ∫ ω in A, g ω * (X.stoch_integral t ω - X.stoch_integral s ω) ∂μ = 0 := by
  have hA' : MeasurableSet A := F.le_ambient τ A hA
  -- Convert: ∫_A g·Y = ∫ (1_A · g) · Y
  rw [← integral_indicator hA']
  simp_rw [Set.indicator_mul_left]
  -- Apply integral_mul_eq_zero_of_setIntegral_eq_zero
  have hs : 0 ≤ s := le_trans hτ hτs
  have ht' : 0 ≤ t := le_trans hs hst
  apply integral_mul_eq_zero_of_setIntegral_eq_zero (F.le_ambient τ)
  · -- A.indicator g is F_τ-measurable
    exact hg_meas.indicator hA
  · -- SI(t) - SI(s) is integrable
    exact (X.stoch_integral_integrable t ht').sub (X.stoch_integral_integrable s hs)
  · -- (A.indicator g) · (SI(t) - SI(s)) is integrable (bounded × integrable)
    obtain ⟨C, hC⟩ := hg_bdd
    exact ((X.stoch_integral_integrable t ht').sub
      (X.stoch_integral_integrable s hs)).bdd_mul (c := C)
      ((hg_meas.indicator hA).mono (F.le_ambient τ) le_rfl).aestronglyMeasurable
      (ae_of_all μ fun ω => by
        rw [Real.norm_eq_abs]
        simp only [Set.indicator]
        split_ifs
        · exact hC ω
        · simp [le_trans (abs_nonneg _) (hC ω)])
  · -- ∀ B ∈ F_τ, ∫_B [SI(t) - SI(s)] = 0 (by stoch_integral_martingale)
    intro B hB
    rw [integral_sub
      (X.stoch_integral_integrable t ht').integrableOn
      (X.stoch_integral_integrable s hs).integrableOn]
    exact sub_eq_zero.mpr (X.stoch_integral_martingale s t hs hst B (F.mono τ s hτs B hB))

/-- The SI-increment approximation satisfies the martingale set-integral property.
    For 0 ≤ v ≤ u ≤ T and A ∈ F_v:
      ∫_A M_n(u) = ∫_A M_n(v)

    **Proof**: The sum is pushed through the integral, and each term is handled by
    case analysis on the partition time tᵢ relative to v:
    - tᵢ₊₁ ≤ v: SI increments at u and v both equal SI(tᵢ₊₁) - SI(tᵢ), terms equal.
    - tᵢ ≤ v < tᵢ₊₁: difference is f'·[SI(min(tᵢ₊₁,u)) - SI(v)], use helper with F_v.
    - v < tᵢ and u < tᵢ: both terms are 0.
    - v < tᵢ ≤ u: use helper with F_{tᵢ} and A promoted via F.mono. -/
theorem si_increment_martingale_property {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (T : ℝ) (_hT : 0 < T) (n : ℕ)
    (v u : ℝ) (hv : 0 ≤ v) (hvu : v ≤ u) (_hu : u ≤ T)
    (A : Set Ω) (hA : @MeasurableSet Ω (F.σ_algebra v) A) :
    ∫ ω in A, siIncrementApprox X f T n u ω ∂μ =
    ∫ ω in A, siIncrementApprox X f T n v ω ∂μ := by
  -- Unfold siIncrementApprox and push integral through finite sum
  simp only [siIncrementApprox]
  -- Abbreviations for partition times
  set t_ : Fin (n + 1) → ℝ := fun i => ↑(i : ℕ) * T / ↑(n + 1) with ht_def
  -- f' at partition time tᵢ
  set f'_ : Fin (n + 1) → Ω → ℝ := fun i ω =>
    deriv (fun x => f (t_ i) x) (X.process (t_ i) ω) with hf'_def
  -- Each summand is integrable (for integral_finset_sum)
  have h_term_int : ∀ (t' : ℝ), 0 ≤ t' → ∀ i : Fin (n + 1),
      Integrable (fun ω => f'_ i ω *
        (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) t') ω -
         X.stoch_integral (min (t_ i) t') ω)) μ := by
    intro t' ht' i
    obtain ⟨Mf', hMf'⟩ := hf_x_bdd
    exact ((X.stoch_integral_integrable _ (le_min (by positivity) ht')).sub
      (X.stoch_integral_integrable _ (le_min (by positivity) ht'))).bdd_mul (c := Mf')
      ((contDiff_two_deriv_continuous (hf_x _)).measurable.comp
        ((X.process_adapted _).mono (F.le_ambient _) le_rfl)).aestronglyMeasurable
      (ae_of_all μ fun ω => by rw [Real.norm_eq_abs]; exact hMf' _ _)
  rw [integral_finset_sum _ (fun i _ => (h_term_int u (le_trans hv hvu) i).integrableOn),
      integral_finset_sum _ (fun i _ => (h_term_int v hv i).integrableOn)]
  -- Show sums equal term by term
  congr 1; ext i
  -- Per-term: show ∫_A f'ᵢ · ΔSI_i(u) = ∫_A f'ᵢ · ΔSI_i(v)
  -- f'ᵢ properties
  obtain ⟨Mf', hMf'⟩ := hf_x_bdd
  have hf'_meas : @Measurable Ω ℝ (F.σ_algebra (t_ i)) _ (f'_ i) :=
    (contDiff_two_deriv_continuous (hf_x _)).measurable.comp (X.process_adapted (t_ i))
  have hf'_bdd : ∃ C : ℝ, ∀ ω, |f'_ i ω| ≤ C := ⟨Mf', fun ω => hMf' _ _⟩
  -- Partition time nonneg
  have ht_nn : 0 ≤ t_ i := by positivity
  have ht1_nn : 0 ≤ (↑(i : ℕ) + 1) * T / ↑(n + 1) := by positivity
  -- t_ i ≤ t_{i+1} (used in Cases 3a, 3b)
  have hti_le_t1 : t_ i ≤ (↑(i : ℕ) + 1) * T / ↑(n + 1) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : (↑(i : ℕ) : ℝ) ≤ ↑(i : ℕ) + 1) _hT.le)
      (Nat.cast_nonneg _)
  -- Case analysis on t_ i vs v
  by_cases hcase1 : (↑(i : ℕ) + 1) * T / ↑(n + 1) ≤ v
  · -- Case 1: tᵢ₊₁ ≤ v (hence tᵢ ≤ v too). Both min's collapse.
    have hti_le_v : t_ i ≤ v := le_trans hti_le_t1 hcase1
    simp only [min_eq_left (le_trans hcase1 hvu), min_eq_left hcase1,
               min_eq_left (le_trans hti_le_v hvu), min_eq_left hti_le_v]
  · push_neg at hcase1
    by_cases hcase2 : t_ i ≤ v
    · -- Case 2: tᵢ ≤ v < tᵢ₊₁. ΔSI_i(v) = SI(v) - SI(tᵢ).
      -- ΔSI_i(u) = SI(min(tᵢ₊₁, u)) - SI(tᵢ).
      -- Difference = f'ᵢ · [SI(min(tᵢ₊₁, u)) - SI(v)].
      have hti_le_u : t_ i ≤ u := le_trans hcase2 hvu
      simp only [min_eq_left hti_le_u, min_eq_left hcase2, min_eq_right hcase1.le]
      -- Goal: ∫_A f'·(SI(min(tᵢ₊₁,u)) - SI(tᵢ)) = ∫_A f'·(SI(v) - SI(tᵢ))
      -- Key: ∫_A f' · [SI(min(tᵢ₊₁,u)) - SI(v)] = 0
      have key := setIntegral_adapted_mul_si_increment_eq_zero X (f'_ i)
        v v (min ((↑↑i + 1) * T / ↑(n + 1)) u)
        hv le_rfl (le_min hcase1.le hvu)
        (hf'_meas.mono (F.mono _ v hcase2) le_rfl)
        hf'_bdd hA
      -- Split: f'·(SI(min(t₁,u)) - SI(tᵢ)) = f'·(SI(min(t₁,u)) - SI(v)) + f'·(SI(v) - SI(tᵢ))
      have hsplit : ∀ ω, f'_ i ω *
          (X.stoch_integral (min ((↑↑i + 1) * T / ↑(n + 1)) u) ω -
            X.stoch_integral (t_ i) ω) =
          f'_ i ω * (X.stoch_integral (min ((↑↑i + 1) * T / ↑(n + 1)) u) ω -
            X.stoch_integral v ω) +
          f'_ i ω * (X.stoch_integral v ω - X.stoch_integral (t_ i) ω) := by
        intro ω; ring
      simp_rw [hsplit]
      -- Integrability of each summand (with explicit pointwise types)
      have hint1 : IntegrableOn (fun ω => f'_ i ω *
          (X.stoch_integral (min ((↑↑i + 1) * T / ↑(n + 1)) u) ω -
           X.stoch_integral v ω)) A μ :=
        (Integrable.bdd_mul (c := Mf')
          ((X.stoch_integral_integrable _ (le_min ht1_nn (le_trans hv hvu))).sub
            (X.stoch_integral_integrable v hv))
          ((hf'_meas.mono (F.le_ambient _) le_rfl).aestronglyMeasurable)
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hMf' _ _)).integrableOn
      have hint2 : IntegrableOn (fun ω => f'_ i ω *
          (X.stoch_integral v ω - X.stoch_integral (t_ i) ω)) A μ :=
        (Integrable.bdd_mul (c := Mf')
          ((X.stoch_integral_integrable v hv).sub
            (X.stoch_integral_integrable _ ht_nn))
          ((hf'_meas.mono (F.le_ambient _) le_rfl).aestronglyMeasurable)
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hMf' _ _)).integrableOn
      -- Split integral: ∫(g₁+g₂) = ∫g₁ + ∫g₂, then ∫g₁ = 0 by key
      have h_add : ∫ ω in A, (f'_ i ω *
          (X.stoch_integral (min ((↑↑i + 1) * T / ↑(n + 1)) u) ω -
           X.stoch_integral v ω) +
          f'_ i ω * (X.stoch_integral v ω - X.stoch_integral (t_ i) ω)) ∂μ =
        ∫ ω in A, f'_ i ω *
          (X.stoch_integral (min ((↑↑i + 1) * T / ↑(n + 1)) u) ω -
           X.stoch_integral v ω) ∂μ +
        ∫ ω in A, f'_ i ω *
          (X.stoch_integral v ω - X.stoch_integral (t_ i) ω) ∂μ :=
        integral_add hint1 hint2
      rw [h_add, key, zero_add]
    · -- Case 3: v < tᵢ. Both min(tᵢ, v) = v and min(tᵢ₊₁, v) = v.
      push_neg at hcase2
      have hmin_ti_v : min (t_ i) v = v := min_eq_right hcase2.le
      have hmin_t1_v : min ((↑↑i + 1) * T / ↑(n + 1)) v = v :=
        min_eq_right (le_trans hcase2.le hti_le_t1)
      by_cases hcase3 : u < t_ i
      · -- Case 3a: u < tᵢ. Both ΔSI_i(u) = 0 and ΔSI_i(v) = 0.
        have hmin_ti_u : min (t_ i) u = u := min_eq_right hcase3.le
        have hmin_t1_u : min ((↑↑i + 1) * T / ↑(n + 1)) u = u :=
          min_eq_right (le_trans hcase3.le hti_le_t1)
        simp only [hmin_ti_v, hmin_t1_v, hmin_ti_u, hmin_t1_u, sub_self, mul_zero]
      · -- Case 3b: u ≥ tᵢ. ΔSI_i(v) = 0, ΔSI_i(u) = SI(min(tᵢ₊₁,u)) - SI(tᵢ).
        push_neg at hcase3
        have hmin_ti_u : min (t_ i) u = t_ i := min_eq_left hcase3
        simp only [hmin_ti_v, hmin_t1_v, hmin_ti_u, sub_self, mul_zero,
                   integral_zero]
        -- Need: ∫_A f'ᵢ · [SI(min(tᵢ₊₁,u)) - SI(tᵢ)] = 0
        -- Use helper with τ = tᵢ, s = tᵢ, t = min(tᵢ₊₁,u)
        -- A ∈ F_v ⊆ F_{tᵢ} (by mono, v < tᵢ)
        have hA_ti : @MeasurableSet Ω (F.σ_algebra (t_ i)) A :=
          F.mono v (t_ i) hcase2.le A hA
        exact setIntegral_adapted_mul_si_increment_eq_zero X (f'_ i)
          (t_ i) (t_ i) (min ((↑↑i + 1) * T / ↑(n + 1)) u)
          ht_nn le_rfl (le_min hti_le_t1 hcase3)
          hf'_meas hf'_bdd hA_ti

/-- Four-term Cauchy-Schwarz: (a+b+c-d)² ≤ 4(a²+b²+c²+d²).
    Follows from the identity (a+b+c-d)² + (a-b)² + ... = 4(a²+b²+c²+d²)
    minus the nonnegative terms. -/
private lemma four_sq_sub_bound (a b c d : ℝ) :
    (a + b + c - d)^2 ≤ 4 * (a^2 + b^2 + c^2 + d^2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a + d),
             sq_nonneg (b - c), sq_nonneg (b + d), sq_nonneg (c + d)]

/-! ### Process L² increment bounds

The Itô process has L² continuous sample paths in the sense that
E[(X_t - X_s)²] ≤ C·|t - s| for bounded coefficients.

This follows from the integral form X_t - X_s = ∫_s^t μ du + [SI(t) - SI(s)]
plus Cauchy-Schwarz for the drift and Itô isometry for the stochastic integral. -/

/-- L² bound on process increments: E[(X_t - X_s)²] ≤ (2Mμ²T + 2Mσ²)(t-s).
    From integral form: X_t - X_s = ∫_s^t μ du + (SI_t - SI_s) a.e.
    Then: (a+b)² ≤ 2a² + 2b², with Cauchy-Schwarz for drift and Itô isometry for SI. -/
theorem process_L2_increment_bound {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    {T : ℝ} (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht_le : t ≤ T) :
    ∫ ω, (X.process t ω - X.process s ω) ^ 2 ∂μ ≤
    (2 * Mμ ^ 2 * T + 2 * Mσ ^ 2) * (t - s) := by
  have ht : 0 ≤ t := le_trans hs hst
  have h_ts : 0 ≤ t - s := sub_nonneg.mpr hst
  -- Step 1: Bound the drift integral difference: |∫_0^t μ - ∫_0^s μ| ≤ Mμ*(t-s)
  have h_drift_bdd : ∀ ω, (∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
      ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) ^ 2 ≤ Mμ ^ 2 * (t - s) ^ 2 := by
    intro ω
    have h_split : ∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
        ∫ u in Set.Icc 0 s, X.drift u ω ∂volume =
        ∫ u in Set.Icc s t, X.drift u ω ∂volume := by
      linarith [setIntegral_Icc_split hs hst (X.drift_time_integrable ω t ht)]
    rw [h_split]
    have h_abs : |∫ u in Set.Icc s t, X.drift u ω ∂volume| ≤ Mμ * (t - s) := by
      have h_norm := norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Icc s t)) (f := fun u => X.drift u ω)
      simp only [Real.norm_eq_abs] at h_norm
      calc |∫ u in Set.Icc s t, X.drift u ω ∂volume| ≤
            ∫ u in Set.Icc s t, |X.drift u ω| ∂volume := h_norm
        _ ≤ ∫ u in Set.Icc s t, Mμ ∂volume := by
            apply setIntegral_mono_on
            · exact ((X.drift_time_integrable ω t ht).mono_set
                (Set.Icc_subset_Icc hs le_rfl)).norm
            · exact integrableOn_const (show volume (Set.Icc s t) ≠ ⊤ from by
                rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
            · exact measurableSet_Icc
            · intro u _; exact hMμ u ω
        _ = Mμ * (t - s) := by simp [h_ts]; ring
    calc (∫ u in Set.Icc s t, X.drift u ω ∂volume) ^ 2
        = |∫ u in Set.Icc s t, X.drift u ω ∂volume| ^ 2 := by rw [sq_abs]
      _ ≤ (Mμ * (t - s)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h_abs 2
      _ = Mμ ^ 2 * (t - s) ^ 2 := by ring
  -- Step 2: SI increment L² bound via isometry
  have h_SI_iso := X.stoch_integral_isometry s t hs hst
  -- Helper: ∫_s^t σ² ≤ Mσ² * (t-s) for each ω
  have h_inner_bdd : ∀ ω, ∫ u in Set.Icc s t, (X.diffusion u ω) ^ 2 ∂volume ≤
      Mσ ^ 2 * (t - s) := by
    intro ω
    have h1 : ∫ u in Set.Icc s t, (X.diffusion u ω) ^ 2 ∂volume ≤
        ∫ u in Set.Icc s t, Mσ ^ 2 ∂volume :=
      setIntegral_mono_on
        ((X.diffusion_sq_time_integrable ω t ht).mono_set
          (Set.Icc_subset_Icc hs le_rfl))
        (integrableOn_const (show volume (Set.Icc s t) ≠ ⊤ from by
          rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        measurableSet_Icc
        (fun u _ => by
          calc (X.diffusion u ω) ^ 2 = |X.diffusion u ω| ^ 2 := by rw [sq_abs]
            _ ≤ Mσ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hMσ u ω) 2)
    linarith [show ∫ u in Set.Icc s t, Mσ ^ 2 ∂volume = Mσ ^ 2 * (t - s) by
      simp [h_ts]; ring]
  have h_SI_bdd : ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ ≤
      Mσ ^ 2 * (t - s) := by
    rw [h_SI_iso]
    calc ∫ ω, (∫ u in Set.Icc s t, (X.diffusion u ω) ^ 2 ∂volume) ∂μ
        ≤ ∫ _ : Ω, Mσ ^ 2 * (t - s) ∂μ := by
          apply integral_mono_of_nonneg
          · exact ae_of_all _ (fun ω => setIntegral_nonneg measurableSet_Icc
              (fun u _ => sq_nonneg _))
          · exact integrable_const _
          · exact ae_of_all _ h_inner_bdd
      _ = Mσ ^ 2 * (t - s) := by rw [integral_const]; simp
  -- Step 3: SI increment squared integrable
  have h_SI_sq_int : Integrable (fun ω =>
      (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) μ := by
    have h1 := X.stoch_integral_sq_integrable t ht
    have h2 := X.stoch_integral_sq_integrable s hs
    -- Dominate by 2(SI_t² + SI_s²) via (a-b)² ≤ 2(a²+b²)
    apply Integrable.mono' ((h1.const_mul 2).add (h2.const_mul 2))
    · exact (((X.stoch_integral_adapted t).mono (F.le_ambient t) le_rfl).sub
        ((X.stoch_integral_adapted s).mono (F.le_ambient s) le_rfl)).pow_const 2
        |>.aestronglyMeasurable
    · filter_upwards with ω
      simp only [Real.norm_eq_abs, Pi.add_apply]
      rw [abs_of_nonneg (sq_nonneg _)]
      -- (a-b)² ≤ 2a² + 2b² from (a+b)² ≥ 0
      nlinarith [sq_nonneg (X.stoch_integral t ω + X.stoch_integral s ω)]
  -- Step 4: Drift diff squared is integrable (bounded by constant)
  have h_drift_sq_int : Integrable (fun ω =>
      (∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
       ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) ^ 2) μ := by
    apply Integrable.mono' (integrable_const (Mμ ^ 2 * (t - s) ^ 2))
    · -- AEStronglyMeasurable: derive from integral_form
      -- ∫_0^r drift(u, ω) du =ᵐ X_r - X_0 - SI_r, all three measurable from adaptedness
      have h_proc_meas : ∀ r, AEStronglyMeasurable (X.process r) μ :=
        fun r => ((X.process_adapted r).mono (F.le_ambient r) le_rfl).aestronglyMeasurable
      have h_SI_meas : ∀ r, AEStronglyMeasurable (X.stoch_integral r) μ :=
        fun r => ((X.stoch_integral_adapted r).mono (F.le_ambient r) le_rfl).aestronglyMeasurable
      have h_drift_int_meas : ∀ r, 0 ≤ r →
          AEStronglyMeasurable (fun ω => ∫ u in Set.Icc 0 r, X.drift u ω ∂volume) μ :=
        fun r hr => (((h_proc_meas r).sub (h_proc_meas 0)).sub (h_SI_meas r)).congr
          (by filter_upwards [X.integral_form r hr] with ω h_form
              show X.process r ω - X.process 0 ω - X.stoch_integral r ω =
                ∫ u in Set.Icc 0 r, X.drift u ω ∂volume
              linarith)
      have h_diff := (h_drift_int_meas t ht).sub (h_drift_int_meas s hs)
      exact (h_diff.mul h_diff).congr (ae_of_all _ fun ω => by
        simp only [Pi.sub_apply, Pi.mul_apply]; ring)
    · exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact h_drift_bdd ω
  -- Step 5: From a.e. equality, bound ∫(X_t - X_s)² ≤ 2∫drift² + 2∫SI²
  have h_eq : ∫ ω, (X.process t ω - X.process s ω) ^ 2 ∂μ =
      ∫ ω, ((∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
             ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) +
            (X.stoch_integral t ω - X.stoch_integral s ω)) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [X.integral_form t ht, X.integral_form s hs] with ω ht_eq hs_eq
    congr 1; rw [ht_eq, hs_eq]; ring
  rw [h_eq]
  -- Step 5: Use (a+b)² ≤ 2a² + 2b² pointwise, then split and bound integrals
  calc ∫ ω, ((∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
       ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) +
      (X.stoch_integral t ω - X.stoch_integral s ω)) ^ 2 ∂μ
      ≤ ∫ ω, (2 * (∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
           ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) ^ 2 +
          2 * (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun ω => sq_nonneg _)
        · exact (h_drift_sq_int.const_mul 2).add (h_SI_sq_int.const_mul 2)
        · exact ae_of_all _ (fun ω => by
            nlinarith [sq_nonneg ((∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
              ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) -
              (X.stoch_integral t ω - X.stoch_integral s ω))])
    _ = 2 * ∫ ω, (∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
         ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) ^ 2 ∂μ +
        2 * ∫ ω, (X.stoch_integral t ω - X.stoch_integral s ω) ^ 2 ∂μ := by
        rw [integral_add (h_drift_sq_int.const_mul 2) (h_SI_sq_int.const_mul 2),
            integral_const_mul, integral_const_mul]
    _ ≤ 2 * (Mμ ^ 2 * (t - s) ^ 2) + 2 * (Mσ ^ 2 * (t - s)) := by
        have h1 : ∫ ω, (∫ u in Set.Icc 0 t, X.drift u ω ∂volume -
            ∫ u in Set.Icc 0 s, X.drift u ω ∂volume) ^ 2 ∂μ ≤
            Mμ ^ 2 * (t - s) ^ 2 := by
          calc ∫ ω, _ ∂μ ≤ ∫ _ : Ω, Mμ ^ 2 * (t - s) ^ 2 ∂μ :=
                integral_mono h_drift_sq_int (integrable_const _) h_drift_bdd
            _ = Mμ ^ 2 * (t - s) ^ 2 := by
                rw [integral_const]; simp
        linarith [h_SI_bdd]
    _ ≤ (2 * Mμ ^ 2 * T + 2 * Mσ ^ 2) * (t - s) := by
        have h_ts_le_T : t - s ≤ T := le_trans (sub_le_self t hs) ht_le
        nlinarith [sq_nonneg Mμ, sq_nonneg Mσ, mul_le_mul_of_nonneg_left h_ts_le_T
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Mμ ^ 2) h_ts)]

/-! ### Error decomposition for L² convergence

The error siIncrementApprox(u) - itoRemainder(u) decomposes via the telescope
identity f(u,X_u) - f(0,X_0) = Σ [spatial + time changes], combined with Taylor
expansion of the spatial changes into:

  error = E₁ + E₂ + E₃ - E₄

where:
- E₁ = ∫₀ᵘ ∂_t f(s,X_s) ds - Σ [f(τᵢ₊₁,X(τᵢ₊₁)) - f(τᵢ,X(τᵢ₊₁))]   (time Riemann)
- E₂ = ∫₀ᵘ f'(s,X_s)μ(s) ds - Σ f'(τᵢ,X(τᵢ))·ΔDᵢ                       (drift Riemann)
- E₃ = ∫₀ᵘ ½f''(s,X_s)σ²(s) ds - Σ ½f''(τᵢ,X(τᵢ))·(ΔXᵢ)²               (QV error)
- E₄ = Σ Rᵢ  (Taylor remainders)

with τᵢ = min(tᵢ, u), ΔXᵢ = X(τᵢ₊₁) - X(τᵢ), ΔDᵢ = ∫_{τᵢ}^{τᵢ₊₁} μ ds.

Each E[Eₖ²] → 0 as mesh → 0. We bound E[error²] ≤ 4Σ E[Eₖ²] via (a+b+c+d)² ≤ 4(a²+b²+c²+d²). -/

/-- Per-summand telescope algebra: S1 + S2 + S3 + S4 + f'·ΔSI = g_{i+1} - g_i,
    given ΔSI = ΔX - ΔD (from integral form). -/
private lemma summand_telescope_algebra
    (ftu_xu ft_xu ft_xi fprime_xi dx dd dsi half_fpp_xi : ℝ)
    (h_si : dsi = dx - dd) :
    -- S1          + S2              + S3                  + S4 (= spatial Taylor remainder)           + SI
    (ftu_xu - ft_xu) + (fprime_xi * dd) + (half_fpp_xi * dx ^ 2) +
    (ft_xu - ft_xi - fprime_xi * dx - half_fpp_xi * dx ^ 2) +
    (fprime_xi * dsi) = ftu_xu - ft_xi := by
  rw [h_si]; ring

/-- When t_i ≤ u, min(t_i, u) = t_i so unclamped = clamped.
    When t_i > u, both min endpoints equal u so ΔSI = 0.
    In both cases: f'(unclamped) * ΔSI = f'(clamped) * ΔSI. -/
private lemma fprime_unclamped_clamped_si
    {t_i : ℝ} {u : ℝ} (fprime_uc fprime_c dsi : ℝ)
    (h_eq : t_i ≤ u → fprime_uc = fprime_c)
    (h_zero : u < t_i → dsi = 0) :
    fprime_uc * dsi = fprime_c * dsi := by
  by_cases h : t_i ≤ u
  · rw [h_eq h]
  · push_neg at h; rw [h_zero h, mul_zero, mul_zero]

/-- Telescope lemma for sums over Fin: ∑ᵢ (g(i+1) - g(i)) = g(n) - g(0). -/
private lemma fin_sum_sub_telescope (g : ℕ → ℝ) (n : ℕ) :
    ∑ i : Fin n, (g (↑i + 1) - g ↑i) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    linarith

/-- If four sequences each tend to 0, then 4·(f₁²+f₂²+f₃²+f₄²) → 0.
    Used to decompose the Itô error bound into individual error term convergences. -/
private lemma tendsto_four_sq_sum {f1 f2 f3 f4 : ℕ → ℝ}
    (h1 : Tendsto f1 atTop (nhds 0))
    (h2 : Tendsto f2 atTop (nhds 0))
    (h3 : Tendsto f3 atTop (nhds 0))
    (h4 : Tendsto f4 atTop (nhds 0)) :
    Tendsto (fun k => 4 * ((f1 k) ^ 2 + (f2 k) ^ 2 + (f3 k) ^ 2 + (f4 k) ^ 2))
      atTop (nhds 0) := by
  have zpow : (0 : ℝ) ^ 2 = 0 := by norm_num
  have h1' : Tendsto (fun k => (f1 k) ^ 2) atTop (nhds 0) := by
    have := h1.pow 2; rw [zpow] at this; exact this
  have h2' : Tendsto (fun k => (f2 k) ^ 2) atTop (nhds 0) := by
    have := h2.pow 2; rw [zpow] at this; exact this
  have h3' : Tendsto (fun k => (f3 k) ^ 2) atTop (nhds 0) := by
    have := h3.pow 2; rw [zpow] at this; exact this
  have h4' : Tendsto (fun k => (f4 k) ^ 2) atTop (nhds 0) := by
    have := h4.pow 2; rw [zpow] at this; exact this
  have hsum := ((h1'.add h2').add h3').add h4'
  simp only [add_zero] at hsum
  simpa only [mul_zero] using Tendsto.mul (tendsto_const_nhds (x := (4 : ℝ))) hsum

/-- Algebraic identity for Itô error decomposition.
    Given: integral splitting, remainder definition, and sum decomposition,
    concludes SI - Rem = (∫a - S1) + (∫b - S2) + (∫c - S3) - S4. -/
private lemma error_decomp_algebra
    (SI Rem int_abc int_a int_b int_c S1 S2 S3 S4 gu g0 : ℝ)
    (h_split : int_abc = int_a + int_b + int_c)
    (h_rem : Rem = gu - g0 - int_abc)
    (h_sum : S1 + S2 + S3 + S4 + SI = gu - g0) :
    SI - Rem = (int_a - S1) + (int_b - S2) + (int_c - S3) - S4 := by
  linarith

/-- The error identity: siIncrementApprox(u) - itoRemainder(u) equals
    the sum of time-Riemann + drift-Riemann + QV errors minus the Taylor remainder.

    This follows from the telescope identity
    f(u,X_u) - f(0,X_0) = Σᵢ [f(τᵢ₊₁,X(τᵢ₊₁)) - f(τᵢ,X(τᵢ))]
    split into spatial and time changes, with Taylor expansion of the spatial part.

    The bound is a.e. because the proof uses `integral_form` (X = X₀ + ∫drift + SI)
    which holds a.e. in ω. -/
private lemma ito_error_decomposition {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (_hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (T : ℝ) (hT : 0 < T) (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (huT : u ≤ T)
    (hint_t : ∀ᵐ ω ∂μ, IntegrableOn
      (fun s => deriv (fun t => f t (X.process s ω)) s) (Set.Icc 0 u) volume)
    (hint_d : ∀ᵐ ω ∂μ, IntegrableOn
      (fun s => deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
      (Set.Icc 0 u) volume)
    (hint_σ : ∀ᵐ ω ∂μ, IntegrableOn
      (fun s => (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
        (X.diffusion s ω) ^ 2) (Set.Icc 0 u) volume) :
    ∀ᵐ ω ∂μ,
    (siIncrementApprox X f T n u ω - itoRemainder X f u ω)^2 ≤
    4 * ((∫ s in Set.Icc 0 u,
        deriv (fun t => f t (X.process s ω)) s ∂volume -
      ∑ i : Fin (n + 1),
        (f (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u)
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω) -
         f (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω)))^2 +
    (∫ s in Set.Icc 0 u,
        deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume -
      ∑ i : Fin (n + 1),
        deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x)
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          X.drift s ω ∂volume))^2 +
    (∫ s in Set.Icc 0 u,
        (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
        (X.diffusion s ω) ^ 2 ∂volume -
      ∑ i : Fin (n + 1),
        (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)^2 +
    (∑ i : Fin (n + 1),
        (f (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω) -
         f (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) -
         deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x)
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) -
         (1 : ℝ) / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2))^2) := by
  -- Step 0: Get integral_form at all partition times (a.e.)
  -- For each partition time τᵢ = min(i·T/(n+1), u), we need X(τᵢ) = X₀ + ∫drift + SI(τᵢ)
  have h_ae : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 2),
      X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω =
      X.process 0 ω +
      (∫ s in Set.Icc 0 (min (↑(i : ℕ) * T / ↑(n + 1)) u), X.drift s ω ∂volume) +
      X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω := by
    rw [ae_all_iff]; intro i
    exact X.integral_form _ (le_min (by positivity) hu)
  filter_upwards [h_ae, hint_t, hint_d, hint_σ] with ω hω hint_t hint_d hint_σ
  -- Name the four error terms
  set E1 := ∫ s in Set.Icc 0 u,
      deriv (fun t => f t (X.process s ω)) s ∂volume -
    ∑ i : Fin (n + 1),
      (f (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u)
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω) -
       f (min (↑(i : ℕ) * T / ↑(n + 1)) u)
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω)) with hE1_def
  set E2 := ∫ s in Set.Icc 0 u,
      deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume -
    ∑ i : Fin (n + 1),
      deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x)
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
      (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
        X.drift s ω ∂volume) with hE2_def
  set E3 := ∫ s in Set.Icc 0 u,
      (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
      (X.diffusion s ω) ^ 2 ∂volume -
    ∑ i : Fin (n + 1),
      (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 with hE3_def
  set E4 := ∑ i : Fin (n + 1),
      (f (min (↑(i : ℕ) * T / ↑(n + 1)) u)
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω) -
       f (min (↑(i : ℕ) * T / ↑(n + 1)) u)
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) -
       deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x)
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) -
       (1 : ℝ) / 2 *
        deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) with hE4_def
  -- Step 1: The error equals E1 + E2 + E3 - E4
  -- (From telescope identity + Taylor expansion + integral_form)
  suffices h_ident : siIncrementApprox X f T n u ω - itoRemainder X f u ω =
      E1 + E2 + E3 - E4 by
    -- Step 2: Apply four-term Cauchy-Schwarz inequality
    rw [h_ident]
    exact four_sq_sub_bound E1 E2 E3 E4
  -- Step 1: From integral form (hω), derive ΔSI_i = ΔX_i - (∫₀^{τ_{i+1}} - ∫₀^{τ_i}) drift
  -- where τ_i = min(i·T/(n+1), u)
  have h_delta_si : ∀ i : Fin (n + 1),
      X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
      X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω =
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) -
      (∫ s in Set.Icc 0 (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u), X.drift s ω ∂volume -
       ∫ s in Set.Icc 0 (min (↑(i : ℕ) * T / ↑(n + 1)) u), X.drift s ω ∂volume) := by
    intro i
    have h1 := hω ⟨i.val + 1, by omega⟩
    have h0 := hω ⟨i.val, by omega⟩
    -- Normalize Nat.cast: ↑(i.val + 1) → ↑i.val + 1, ↑(n + 1) → ↑n + 1
    simp only [Nat.cast_add, Nat.cast_one] at h1 h0 ⊢
    linarith
  -- Step 2: Interval splitting: ∫₀^{τ_{i+1}} - ∫₀^{τ_i} = ∫_{τ_i}^{τ_{i+1}} drift
  have h_drift_split : ∀ i : Fin (n + 1),
      ∫ s in Set.Icc 0 (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u), X.drift s ω ∂volume -
      ∫ s in Set.Icc 0 (min (↑(i : ℕ) * T / ↑(n + 1)) u), X.drift s ω ∂volume =
      ∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u), X.drift s ω ∂volume := by
    intro i
    have h_tau_nn : 0 ≤ min (↑(i : ℕ) * T / ↑(n + 1)) u := le_min (by positivity) hu
    have h_tau_le : min (↑(i : ℕ) * T / ↑(n + 1)) u ≤
        min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u :=
      min_le_min_right u (div_le_div_of_nonneg_right
        (by nlinarith : (↑(i : ℕ) : ℝ) * T ≤ (↑(i : ℕ) + 1) * T) (Nat.cast_nonneg _))
    linarith [setIntegral_Icc_split h_tau_nn h_tau_le
      (X.drift_time_integrable ω _ (le_min (by positivity) hu))]
  -- Step 3: Combined: ΔSI = ΔX - ΔD (drift over [τ_i, τ_{i+1}])
  have h_si_xd : ∀ i : Fin (n + 1),
      X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
      X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω =
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) -
      ∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u), X.drift s ω ∂volume := by
    intro i; linarith [h_delta_si i, h_drift_split i]
  -- Step 4: Integral splitting ∫(a+b+c) = ∫a + ∫b + ∫c
  have h_split : ∫ s in Set.Icc 0 u,
      (deriv (fun t => f t (X.process s ω)) s +
       deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
       (1 / 2) * deriv (deriv (fun x => f s x)) (X.process s ω) *
         (X.diffusion s ω) ^ 2) ∂volume =
    (∫ s in Set.Icc 0 u, deriv (fun t => f t (X.process s ω)) s ∂volume) +
    (∫ s in Set.Icc 0 u, deriv (fun x => f s x) (X.process s ω) *
       X.drift s ω ∂volume) +
    (∫ s in Set.Icc 0 u, (1 / 2) * deriv (deriv (fun x => f s x)) (X.process s ω) *
       (X.diffusion s ω) ^ 2 ∂volume) := by
    have h12 := integral_add hint_t hint_d
    have h123 := integral_add (hint_t.add hint_d) hint_σ
    simp only [Pi.add_apply] at h12 h123
    linarith
  -- Step 5: The identity follows from error_decomp_algebra
  -- We need: h_rem (itoRemainder unfolds) and h_sum (combined sum telescopes)
  have h_rem : itoRemainder X f u ω = f u (X.process u ω) - f 0 (X.process 0 ω) -
    ∫ s in Set.Icc 0 u,
      (deriv (fun t => f t (X.process s ω)) s +
       deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
       (1 / 2) * deriv (deriv (fun x => f s x)) (X.process s ω) *
         (X.diffusion s ω) ^ 2) ∂volume := rfl
  -- Prove h_ident via telescope identity + linarith
  -- Step A: Define telescope function g and prove endpoints
  let g : ℕ → ℝ := fun j => f (min (↑j * T / ↑(n + 1)) u)
    (X.process (min (↑j * T / ↑(n + 1)) u) ω)
  have hg0 : g 0 = f 0 (X.process 0 ω) := by
    show f (min (↑(0 : ℕ) * T / ↑(n + 1)) u) _ = _
    simp [zero_mul, zero_div, min_eq_left hu]
  have hgn : g (n + 1) = f u (X.process u ω) := by
    show f (min (↑(n + 1) * T / ↑(n + 1)) u) _ = _
    rw [mul_div_cancel_left₀ T (Nat.cast_ne_zero.mpr (by omega : n + 1 ≠ 0)),
        min_eq_right huT]
  -- Step B: Telescope ∑(g(i+1) - g(i)) = f(u,X_u) - f(0,X_0)
  have h_tele : ∑ i : Fin (n + 1), (g (↑i + 1) - g ↑i) =
      f u (X.process u ω) - f 0 (X.process 0 ω) := by
    rw [fin_sum_sub_telescope, hgn, hg0]
  -- Step C: Per-summand identity (unclamped→clamped + algebra = g(i+1) - g(i))
  -- After combining all 5 per-summand contributions and rewriting the unclamped f'
  -- to clamped f', summand_telescope_algebra closes each summand.
  -- We prove h_sum: the 5 sums combined = f(u,X_u) - f(0,X_0)
  -- by unfolding E4 and siIncrementApprox, combining, and telescoping.
  have h_sum : (∑ i : Fin (n + 1),
      (f (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u)
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω) -
       f (min (↑(i : ℕ) * T / ↑(n + 1)) u)
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω))) +
    (∑ i : Fin (n + 1),
      deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x)
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
      (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
        X.drift s ω ∂volume)) +
    (∑ i : Fin (n + 1),
      (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) +
    E4 + siIncrementApprox X f T n u ω =
    f u (X.process u ω) - f 0 (X.process 0 ω) := by
    -- Unfold E4 and siIncrementApprox to expose their sums
    rw [hE4_def, siIncrementApprox]
    -- Combine all 5 sums into one
    simp only [← Finset.sum_add_distrib]
    -- Per-summand identity: rewrite unclamped→clamped, then algebra
    rw [show ∑ i : Fin (n + 1), _ = ∑ i : Fin (n + 1), (g (↑i + 1) - g ↑i) from
      Finset.sum_congr rfl fun i _ => by
        -- Step i: rewrite SI from unclamped to clamped f'
        have h_fprime : deriv (fun x => f (↑(i : ℕ) * T / ↑(n + 1)) x)
            (X.process (↑(i : ℕ) * T / ↑(n + 1)) ω) *
            (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
             X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) =
          deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x)
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
            (X.stoch_integral (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
             X.stoch_integral (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) :=
          fprime_unclamped_clamped_si _ _ _
            (fun h => by rw [min_eq_left h])
            (fun h => by
              rw [min_eq_right (le_of_lt h),
                  show min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u = u from
                    min_eq_right (by
                      have : (↑(i : ℕ) + 1) * T / ↑(n + 1) =
                        ↑(i : ℕ) * T / ↑(n + 1) + T / ↑(n + 1) := by ring
                      linarith [div_nonneg hT.le (Nat.cast_nonneg (n + 1))]),
                  sub_self])
        rw [h_fprime, h_si_xd i]
        -- Step ii: expand f'*(dx-dd) in SI term to f'*dx - f'*dd, then linarith
        conv_lhs => arg 2; rw [mul_sub]
        -- Unfold g at the endpoints so linarith can see the atoms
        have hgi : g ↑i = f (min (↑↑i * T / ↑(n + 1)) u)
            (X.process (min (↑↑i * T / ↑(n + 1)) u) ω) := rfl
        have hgi1 : g (↑i + 1) = f (min ((↑↑i + 1) * T / ↑(n + 1)) u)
            (X.process (min ((↑↑i + 1) * T / ↑(n + 1)) u) ω) := by
          change f (min ((↑((i : ℕ) + 1) : ℝ) * T / ↑(n + 1)) u)
              (X.process (min ((↑((i : ℕ) + 1) : ℝ) * T / ↑(n + 1)) u) ω) = _
          simp only [Nat.cast_add, Nat.cast_one]
        linarith]
    exact h_tele
  -- Step D: Close h_ident via linarith
  -- E1 = ∫a - ∑S1, E2 = ∫b - ∑S2, E3 = ∫c - ∑S3 (by definition)
  -- h_rem: Rem = f_u - f_0 - ∫abc
  -- h_split: ∫abc = ∫a + ∫b + ∫c
  -- h_sum: ∑S1 + ∑S2 + ∑S3 + E4 + SI = f_u - f_0
  -- Goal: SI - Rem = E1 + E2 + E3 - E4
  linarith [hE1_def, hE2_def, hE3_def, h_rem, h_split, h_sum]

/-- Capped partition QV ≤ uncapped partition QV + boundary increment².
    The capped partition `min(iΔ, u)` sums match uncapped for `i < j*`,
    the `j*`-th term gives `(X(u) - X(bdy_pt))²`, and terms beyond vanish. -/
private lemma capped_qv_le_uncapped {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (T : ℝ) (hT : 0 < T) (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (_huT : u ≤ T)
    (ω : Ω) :
    ∑ i : Fin (n + 1),
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 ≤
    (∑ i : Fin (n + 1),
      (X.process ((↑(i : ℕ) + 1) * T / ↑(n + 1)) ω -
       X.process (↑(i : ℕ) * T / ↑(n + 1)) ω) ^ 2) +
    (X.process u ω -
     X.process (↑(Nat.floor (u * ↑(n + 1) / T)) * T / ↑(n + 1)) ω) ^ 2 := by
  set N := n
  have hN_pos : (0 : ℝ) < ↑(N + 1) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hΔ_pos : (0 : ℝ) < T / ↑(N + 1) := div_pos hT hN_pos
  set j := Nat.floor (u * ↑(N + 1) / T)
  -- j * Δ ≤ u
  have hj_le : ↑j * T / ↑(N + 1) ≤ u := by
    have h_floor := Nat.floor_le (show 0 ≤ u * ↑(N + 1) / T from by positivity)
    calc ↑j * T / ↑(N + 1) = ↑j * (T / ↑(N + 1)) := by ring
      _ ≤ (u * ↑(N + 1) / T) * (T / ↑(N + 1)) :=
          mul_le_mul_of_nonneg_right h_floor hΔ_pos.le
      _ = u := by field_simp
  -- (j+1) * Δ > u
  have hj1_gt : u < (↑j + 1) * T / ↑(N + 1) := by
    have h_floor : u * ↑(N + 1) / T < (↑j : ℝ) + 1 :=
      Nat.lt_floor_add_one (u * ↑(N + 1) / T)
    calc u = (u * ↑(N + 1) / T) * (T / ↑(N + 1)) := by field_simp
      _ < ((↑j : ℝ) + 1) * (T / ↑(N + 1)) :=
          mul_lt_mul_of_pos_right h_floor hΔ_pos
      _ = (↑j + 1) * T / ↑(N + 1) := by ring
  -- Helper: (i+1)*T/(N+1) ≤ u when i+1 ≤ j
  have h_le_u : ∀ (i : ℕ), i + 1 ≤ j → (↑i + 1 : ℝ) * T / ↑(N + 1) ≤ u := by
    intro i hi
    calc (↑i + 1 : ℝ) * T / ↑(N + 1) ≤ ↑j * T / ↑(N + 1) := by
          apply div_le_div_of_nonneg_right _ hN_pos.le
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hT.le
      _ ≤ u := hj_le
  -- Helper: u ≤ i*T/(N+1) when i ≥ j+1
  have h_ge_u : ∀ (i : ℕ), j + 1 ≤ i → u ≤ (↑i : ℝ) * T / ↑(N + 1) := by
    intro i hi
    calc u ≤ (↑j + 1) * T / ↑(N + 1) := le_of_lt hj1_gt
      _ ≤ (↑i : ℝ) * T / ↑(N + 1) := by
          apply div_le_div_of_nonneg_right _ hN_pos.le
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hT.le
  -- Term-by-term bound
  suffices h_tw : ∀ i : Fin (N + 1),
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(N + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(N + 1)) u) ω) ^ 2 ≤
      (X.process ((↑(i : ℕ) + 1) * T / ↑(N + 1)) ω -
       X.process (↑(i : ℕ) * T / ↑(N + 1)) ω) ^ 2 +
      if i.val = j then (X.process u ω -
        X.process (↑j * T / ↑(N + 1)) ω) ^ 2 else 0 by
    -- Sum both sides and bound indicator sum
    have h1 : ∑ i : Fin (N + 1), _ ≤
        ∑ i : Fin (N + 1),
        ((X.process ((↑(i : ℕ) + 1) * T / ↑(N + 1)) ω -
         X.process (↑(i : ℕ) * T / ↑(N + 1)) ω) ^ 2 +
        if i.val = j then (X.process u ω -
          X.process (↑j * T / ↑(N + 1)) ω) ^ 2 else 0) :=
      Finset.sum_le_sum fun i _ => h_tw i
    have h2 : ∑ i : Fin (N + 1),
        ((X.process ((↑(i : ℕ) + 1) * T / ↑(N + 1)) ω -
         X.process (↑(i : ℕ) * T / ↑(N + 1)) ω) ^ 2 +
        if i.val = j then (X.process u ω -
          X.process (↑j * T / ↑(N + 1)) ω) ^ 2 else 0) =
        (∑ i : Fin (N + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(N + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(N + 1)) ω) ^ 2) +
        ∑ i : Fin (N + 1),
          if i.val = j then (X.process u ω -
            X.process (↑j * T / ↑(N + 1)) ω) ^ 2 else 0 :=
      Finset.sum_add_distrib
    -- Indicator sum ≤ boundary²
    have h3 : ∑ i : Fin (N + 1),
        (if i.val = j then (X.process u ω -
          X.process (↑j * T / ↑(N + 1)) ω) ^ 2 else 0) ≤
        (X.process u ω - X.process (↑j * T / ↑(N + 1)) ω) ^ 2 := by
      by_cases hj_lt : j < N + 1
      · have : ∀ i : Fin (N + 1), (i.val = j) = (i = ⟨j, hj_lt⟩) := fun i =>
          propext ⟨fun h => Fin.ext h, fun h => congr_arg Fin.val h⟩
        simp_rw [this]
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      · have : ∀ i : Fin (N + 1), i.val ≠ j := fun i => by omega
        simp only [this, ite_false, Finset.sum_const_zero]
        exact sq_nonneg _
    linarith
  -- Prove term-by-term bound
  intro i
  by_cases hi_lt : i.val + 1 ≤ j
  · -- Case i < j: both endpoints ≤ u, so capped = uncapped
    have h1 := h_le_u i.val hi_lt
    have h2 : (↑(i : ℕ) : ℝ) * T / ↑(N + 1) ≤ u := by
      calc (↑(i : ℕ) : ℝ) * T / ↑(N + 1) ≤ (↑(i : ℕ) + 1) * T / ↑(N + 1) := by
            apply div_le_div_of_nonneg_right _ hN_pos.le
            nlinarith
        _ ≤ u := h1
    rw [min_eq_left h1, min_eq_left h2, if_neg (by omega)]
    linarith
  · push_neg at hi_lt
    by_cases hi_eq : i.val = j
    · -- Case i = j: top endpoint ≥ u so min = u, bottom ≤ u so min = left
      have h_i_eq_j : (↑(i : ℕ) : ℝ) = (↑j : ℝ) := by exact_mod_cast hi_eq
      have h_top : u ≤ (↑(i : ℕ) + 1) * T / ↑(N + 1) := by
        rw [h_i_eq_j]; exact le_of_lt hj1_gt
      have h_bot : ↑(i : ℕ) * T / ↑(N + 1) ≤ u := by
        rw [h_i_eq_j]; exact hj_le
      rw [min_eq_right h_top, min_eq_left h_bot, if_pos hi_eq]
      conv_rhs => rw [show (↑j : ℝ) = ↑(i : ℕ) from h_i_eq_j.symm]
      linarith [sq_nonneg (X.process ((↑(i : ℕ) + 1) * T / ↑(N + 1)) ω -
                            X.process (↑(i : ℕ) * T / ↑(N + 1)) ω)]
    · -- Case i > j: both endpoints ≥ u, so min = u, capped = 0
      have hi_ge : j + 1 ≤ i.val := by omega
      have h1 : u ≤ (↑(i : ℕ) + 1) * T / ↑(N + 1) := by
        convert h_ge_u (i.val + 1) (by omega) using 2
        push_cast; ring
      have h2 : u ≤ ↑(i : ℕ) * T / ↑(N + 1) := h_ge_u i.val hi_ge
      rw [min_eq_right h1, min_eq_right h2, sub_self,
          zero_pow (by norm_num : 2 ≠ 0), if_neg (by omega)]
      exact add_nonneg (sq_nonneg _) le_rfl

/-- Capped discrete QV sum is AEStronglyMeasurable. -/
lemma capped_discrete_qv_aesm {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (T : ℝ) (n : ℕ) (u : ℝ) :
    AEStronglyMeasurable (fun ω =>
      ∑ i : Fin (n + 1),
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) μ := by
  exact (aestronglyMeasurable_sum (μ := μ) Finset.univ
    (f := fun (i : Fin (n + 1)) (ω : Ω) =>
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)
    (fun i _ => ((process_aesm X _).sub (process_aesm X _)).pow 2)).congr
    (ae_of_all _ fun ω => Finset.sum_apply ω Finset.univ _)

/-- (Capped discrete QV - QV(u))² is integrable.
    Proof: (a-b)² ≤ 2a²+2b², Cauchy-Schwarz for sum², quartic bounds. -/
lemma capped_qv_diff_sq_integrable {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mμ : ℝ} (hMμ : ∀ t ω, |X.drift t ω| ≤ Mμ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T : ℝ) (hT : 0 < T) (n : ℕ)
    (u : ℝ) (hu : 0 ≤ u) (_huT : u ≤ T) :
    Integrable (fun ω =>
      (∑ i : Fin (n + 1),
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 -
       X.quadraticVariation u ω) ^ 2) μ := by
  set Sk := fun ω => ∑ i : Fin (n + 1),
    (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
     X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2
  set QVu := fun ω => X.quadraticVariation u ω
  -- (capped QV sum)² integrable via Cauchy-Schwarz + quartic bounds
  have hSk_sq_int : Integrable (fun ω => Sk ω ^ 2) μ := by
    have hn_pos : (0 : ℝ) < ↑(n + 1) := by positivity
    have hCS : ∀ ω, Sk ω ^ 2 ≤ ↑(n + 1) * ∑ i : Fin (n + 1),
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 4 := by
      intro ω
      have h := @sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ Finset.univ
        (fun i : Fin (n + 1) =>
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      calc Sk ω ^ 2 ≤ ↑(n + 1) * ∑ i,
            ((X.process _ ω - X.process _ ω) ^ 2) ^ 2 := h
        _ = ↑(n + 1) * ∑ i,
            (X.process _ ω - X.process _ ω) ^ 4 := by
          congr 1; exact Finset.sum_congr rfl fun i _ => by ring
    have hΔX4_int : ∀ i : Fin (n + 1),
        Integrable (fun ω => (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
          X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 4) μ := fun i =>
      process_increment_fourth_integrable X hMμ hMσ _ _
        (le_min (by positivity) hu)
        (min_le_min_right u (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : (↑(i : ℕ) : ℝ) ≤ ↑(i : ℕ) + 1) hT.le)
          hn_pos.le))
    exact ((integrable_finset_sum _ fun i _ => hΔX4_int i).const_mul _).mono'
      ((capped_discrete_qv_aesm X T n u).pow 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hCS ω)
  -- QV(u)² integrable
  have hQVu_sq_int : Integrable (fun ω => QVu ω ^ 2) μ := qv_sq_integrable X hMσ u hu
  -- (Sk - QVu)² ≤ 2·Sk² + 2·QVu², both integrable
  have h_bound : ∀ ω, (Sk ω - QVu ω) ^ 2 ≤ 2 * Sk ω ^ 2 + 2 * QVu ω ^ 2 := by
    intro ω; nlinarith [sq_nonneg (Sk ω + QVu ω)]
  exact ((hSk_sq_int.const_mul 2).add (hQVu_sq_int.const_mul 2)).mono'
    ((capped_discrete_qv_aesm X T n u).sub (qv_aesm X u hu) |>.pow 2)
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_bound ω)

/-- If f = g + h pointwise a.e., then ∫f² ≤ 2∫g² + 2∫h²
    (from the pointwise inequality (a+b)² ≤ 2a²+2b²). -/
private lemma integral_sq_le_of_eq_add
    {f g h : Ω → ℝ}
    (hfgh : ∀ ω, f ω = g ω + h ω)
    (hg_sq : Integrable (fun ω => (g ω) ^ 2) μ)
    (hh_sq : Integrable (fun ω => (h ω) ^ 2) μ) :
    ∫ ω, (f ω) ^ 2 ∂μ ≤ 2 * ∫ ω, (g ω) ^ 2 ∂μ + 2 * ∫ ω, (h ω) ^ 2 ∂μ := by
  calc ∫ ω, (f ω) ^ 2 ∂μ
      = ∫ ω, (g ω + h ω) ^ 2 ∂μ := by
        congr 1; ext ω; rw [hfgh]
    _ ≤ ∫ ω, (2 * (g ω) ^ 2 + 2 * (h ω) ^ 2) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all μ (fun ω => by positivity)
        · exact (hg_sq.const_mul 2).add (hh_sq.const_mul 2)
        · exact ae_of_all μ (fun ω => by nlinarith [sq_nonneg (g ω - h ω)])
    _ = 2 * ∫ ω, (g ω) ^ 2 ∂μ + 2 * ∫ ω, (h ω) ^ 2 ∂μ := by
        rw [integral_add (hg_sq.const_mul 2) (hh_sq.const_mul 2),
            integral_const_mul, integral_const_mul]

set_option maxHeartbeats 3200000 in
/-- The SI-increment approximation converges to the Itô formula remainder in L².
    Error decomposition: M_n(u) - itoRemainder(u) consists of:
    1. [∫ ∂_t f ds - Σ time_terms] (time Riemann error)
    2. [∫ f'·μ ds - Σ f'·ΔD] (drift Riemann error)
    3. [∫ ½f''σ² ds - Σ ½f''·(ΔX)²] (weighted QV error)
    4. [-Σ Rᵢ] (Taylor remainders)

    **Proof**: `tendsto_of_subseq_tendsto` + `fatou_squeeze_tendsto_zero`.
    Extract QV-a.e.-convergent subsequence, show error² → 0 a.e. (from
    path continuity + joint continuity of derivatives + QV convergence),
    bound by integrable dominator, apply Fatou squeeze. -/
theorem si_increment_L2_convergence {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (hf_t_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (T : ℝ) (hT : 0 < T)
    (u : ℝ) (hu : 0 ≤ u) (huT : u ≤ T)
    (hrem_int : Integrable (itoRemainder X f u) μ)
    (hrem_sq_int : Integrable (fun ω => (itoRemainder X f u ω)^2) μ) :
    Filter.Tendsto
      (fun n => ∫ ω, (siIncrementApprox X f T n u ω - itoRemainder X f u ω)^2 ∂μ)
      atTop (nhds 0) := by
  -- Extract explicit bounds
  obtain ⟨Mσ, hMσ⟩ := hdiff_bdd
  obtain ⟨Mμ, hMμ⟩ := hdrift_bdd
  obtain ⟨Mf', hMf'⟩ := hf_x_bdd
  obtain ⟨Mf'', hMf''⟩ := hf_xx_bdd
  obtain ⟨Mft, hMft⟩ := hf_t_bdd
  -- Non-negativity of bounds
  have hMf''_nn : 0 ≤ Mf'' := by linarith [abs_nonneg (deriv (deriv (fun x => f 0 x)) 0), hMf'' 0 0]
  have hMft_nn : 0 ≤ Mft := by linarith [abs_nonneg (deriv (fun s => f s 0) 0), hMft 0 0]
  have hMf'_nn : 0 ≤ Mf' := by linarith [abs_nonneg (deriv (fun x => f 0 x) 0), hMf' 0 0]
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  have hMμ_nn : 0 ≤ Mμ := by
    have ω₀ : Ω := Classical.arbitrary Ω
    linarith [abs_nonneg (X.drift 0 ω₀), hMμ 0 ω₀]
  have hMσ_nn : 0 ≤ Mσ := by
    have ω₀ : Ω := Classical.arbitrary Ω
    linarith [abs_nonneg (X.diffusion 0 ω₀), hMσ 0 ω₀]
  -- Step 1: Apply tendsto_of_subseq_tendsto
  apply tendsto_of_subseq_tendsto
  intro ns hns
  -- Step 2: QV L² convergence along ns
  have h_qv_L2_ns := (ito_process_discrete_qv_L2_convergence X hMμ hMσ T hT).comp hns
  -- Step 3: Double extraction for a.e. convergence (uncapped + capped QV)
  -- Step 3a: Extract uncapped QV a.e.-convergent subsequence via L2_to_ae_subseq
  obtain ⟨ms₁, hms₁, h_qv_ae₁⟩ := L2_to_ae_subseq h_qv_L2_ns
    (fun n => qv_diff_sq_integrable X hMμ hMσ T hT (ns n))
    (fun n => discrete_qv_aesm X T (ns n))
    (qv_aesm X T hT.le)
  -- Step 3b: Capped QV L² convergence along ns ∘ ms₁
  have h_capped_L2 := (capped_discrete_qv_L2_convergence X hMμ hMσ T u hT hu huT).comp
    (hns.comp hms₁.tendsto_atTop)
  -- Step 3c: Extract capped QV a.e.-convergent subsequence along ns ∘ ms₁
  obtain ⟨ms₂, hms₂, h_capped_qv_ae⟩ := L2_to_ae_subseq h_capped_L2
    (fun n => capped_qv_diff_sq_integrable X hMμ hMσ T hT (ns (ms₁ n)) u hu huT)
    (fun n => capped_discrete_qv_aesm X T (ns (ms₁ n)) u)
    (qv_aesm X u hu)
  -- Step 3e: E3 weighted QV error converges in L²
  -- E3(n,ω) = ∫ (1/2)f''(s,X(s))σ² ds - Σ (1/2)f''(τᵢ,X(τᵢ))(ΔXᵢ)²
  -- Proved via: E3 = (Riemann error A) + (weighted QV discrepancy B)
  --   E[A²] → 0 by DCT (A bounded, A → 0 a.e. by UC of f'')
  --   E[B²] → 0 by conditional isometry (cross terms vanish) + drift bounds
  -- Decompose E3 = A + B where:
  --   A = ∫½f″σ²ds − Σ½f″ᵢ·QVᵢ  (Riemann error, bounded, → 0 a.e.)
  --   B = Σ½f″ᵢ·(QVᵢ − (ΔXᵢ)²)  (QV discrepancy, E[B²] ≤ C/n)
  -- Notation: τ_i = min(i·T/(n+1), u), QVᵢ = ∫_{τᵢ}^{τᵢ₊₁} σ²
  -- Define A(n) and B(n) and the bound constant
  set C_A := (1 : ℝ) / 2 * Mf'' * Mσ ^ 2 * u with hCA_def
  -- C_B bounds E[B²]: E[B²] ≤ C_B · T / (n+1)
  -- C_B = (3/4)·(Mf''²·8Mσ⁴·u + 4Mf''²Mμ²Mσ²·u·T + Mf''²Mμ⁴u²·T)
  set C_B := 3 / 4 * (Mf'' ^ 2 * 8 * Mσ ^ 4 * u +
    4 * Mf'' ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T +
    Mf'' ^ 2 * Mμ ^ 4 * u ^ 2 * T) with hCB_def
  have hCA_nn : 0 ≤ C_A := by simp only [hCA_def]; positivity
  have hCB_nn : 0 ≤ C_B := by simp only [hCB_def]; positivity
  -- Shared infrastructure for E3 convergence (needed by h_A_L2 and later steps)
  have hIcc_finite : volume (Set.Icc (0 : ℝ) u) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- Integrability of the integrand s ↦ ½f''(s,X(s,ω))σ²(s,ω) on [0,u] (a.e. ω)
  have h_gω_int : ∀ᵐ ω ∂μ, IntegrableOn (fun s =>
      (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
      (X.diffusion s ω) ^ 2) (Set.Icc 0 u) volume := by
    filter_upwards [X.process_continuous] with ω hω
    have h_half_f'' : Continuous (fun s =>
        (1:ℝ)/2 * deriv (deriv (fun x => f s x)) (X.process s ω)) :=
      continuous_const.mul (hf''_cont.comp (continuous_id.prodMk hω))
    exact Integrable.mono'
      (show IntegrableOn (fun _ => 1/2 * Mf'' * Mσ ^ 2) _ _ from
        integrableOn_const hIcc_finite)
      (h_half_f''.aestronglyMeasurable.restrict.mul
        (X.diffusion_sq_time_integrable ω u hu).aestronglyMeasurable)
      (ae_of_all _ fun s => by
        have h_abs1 : |1/2 * deriv (deriv (fun x => f s x)) (X.process s ω)| =
            1/2 * |deriv (deriv (fun x => f s x)) (X.process s ω)| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
        have h_abs2 : |(X.diffusion s ω) ^ 2| = (X.diffusion s ω) ^ 2 :=
          abs_of_nonneg (sq_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, h_abs1, h_abs2]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hMf'' s _) (by norm_num))
          (sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2)
          (sq_nonneg _)
          (mul_nonneg (by norm_num) hMf''_nn))
  -- Bound: |A(n,ω)| ≤ Mf''·Mσ²·u by triangle inequality (works for ALL ω)
  -- Uses: if g not integrable, ∫g = 0 (Mathlib convention); |Σcᵢ| ≤ ½Mf''Mσ²u always
  have h_A_bdd : ∀ n (ω : Ω),
      |∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume)| ≤ Mf'' * Mσ ^ 2 * u := by
    intro n ω
    -- Triangle inequality: |a - b| ≤ ‖a‖ + ‖b‖
    have hIcc_vol : volume (Set.Icc (0 : ℝ) u) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    -- Bound 1: ‖∫g‖ ≤ ½Mf''Mσ²u (works even if not integrable)
    have h1 : ‖∫ s in Set.Icc 0 u,
        (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
        (X.diffusion s ω) ^ 2 ∂volume‖ ≤ 1 / 2 * Mf'' * Mσ ^ 2 * u := by
      have h_pw : ∀ s ∈ Set.Icc (0 : ℝ) u,
          ‖(1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2‖ ≤ 1 / 2 * Mf'' * Mσ ^ 2 := by
        intro s _
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (X.diffusion s ω)),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hMf'' s _) (by norm_num))
          (sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2)
          (sq_nonneg _) (mul_nonneg (by norm_num) hMf''_nn)
      calc ‖∫ s in Set.Icc 0 u, _ ∂volume‖
          ≤ (1 / 2 * Mf'' * Mσ ^ 2) * volume.real (Set.Icc (0 : ℝ) u) :=
            norm_setIntegral_le_of_norm_le_const hIcc_vol h_pw
        _ = 1 / 2 * Mf'' * Mσ ^ 2 * u := by
            rw [Measure.real, Real.volume_Icc,
                ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ u - 0), sub_zero]
    -- Bound 2: ‖Σcᵢ‖ ≤ ½Mf''Mσ²u
    have h2 : ‖∑ i : Fin (n + 1),
        (1 : ℝ) / 2 * deriv (deriv (fun x =>
            f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          (X.diffusion s ω) ^ 2 ∂volume)‖ ≤
        1 / 2 * Mf'' * Mσ ^ 2 * u := by
      rw [Real.norm_eq_abs]
      calc |∑ i : Fin (n + 1), _|
          ≤ ∑ i : Fin (n + 1), |(1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
            (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
              (X.diffusion s ω) ^ 2 ∂volume)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin (n + 1), (1 / 2 * Mf'' * Mσ ^ 2 *
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
              min (↑(i : ℕ) * T / ↑(n + 1)) u)) :=
          Finset.sum_le_sum fun i _ => by
            -- |½f''ᵢ · ∫σ²| ≤ ½Mf'' · Mσ² · Δτ
            have hi_le : (↑(i : ℕ) : ℝ) * T / ↑(n + 1) ≤
                (↑(i : ℕ) + 1) * T / ↑(n + 1) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by linarith) hT.le) (by positivity)
            have hτ_le : min (↑(i : ℕ) * T / ↑(n + 1)) u ≤
                min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u :=
              min_le_min hi_le le_rfl
            have hτ_lo_nn : 0 ≤ min (↑(i : ℕ) * T / ↑(n + 1)) u :=
              le_min (by positivity) hu
            have hτ_hi_le_u : min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u ≤ u :=
              min_le_right _ _
            have hτ_sub : Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ⊆ Set.Icc 0 u :=
              Set.Icc_subset_Icc hτ_lo_nn hτ_hi_le_u
            rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            -- |∫σ²| = ∫σ² (non-negative integrand)
            have hσ_int_nn : 0 ≤ ∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
                (X.diffusion s ω) ^ 2 ∂volume :=
              setIntegral_nonneg measurableSet_Icc fun s _ => sq_nonneg _
            rw [abs_of_nonneg hσ_int_nn]
            -- ∫σ² ≤ Mσ² · Δτ
            have hσ_int_bdd : ∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
                (X.diffusion s ω) ^ 2 ∂volume ≤
                Mσ ^ 2 * (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
                  min (↑(i : ℕ) * T / ↑(n + 1)) u) := by
              have := norm_setIntegral_le_of_norm_le_const
                (show volume (Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
                    (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u)) < ⊤ from by
                  rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
                (fun s _ => by
                  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X.diffusion s ω))]
                  exact sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2)
              rw [Measure.real, Real.volume_Icc,
                  ENNReal.toReal_ofReal (sub_nonneg.mpr hτ_le)] at this
              rwa [Real.norm_eq_abs, abs_of_nonneg hσ_int_nn] at this
            -- |f''ᵢ| ≤ Mf''
            calc 1 / 2 * |deriv (deriv (fun x =>
                    f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
                  (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω)| *
                  (∫ s in Set.Icc _ _, (X.diffusion s ω) ^ 2 ∂volume)
                ≤ 1 / 2 * Mf'' * (Mσ ^ 2 * (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
                    min (↑(i : ℕ) * T / ↑(n + 1)) u)) := by
                  apply mul_le_mul
                  · exact mul_le_mul_of_nonneg_left (hMf'' _ _) (by norm_num)
                  · exact hσ_int_bdd
                  · exact hσ_int_nn
                  · exact mul_nonneg (by norm_num) hMf''_nn
              _ = 1 / 2 * Mf'' * Mσ ^ 2 * (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
                  min (↑(i : ℕ) * T / ↑(n + 1)) u) := by ring
        _ = 1 / 2 * Mf'' * Mσ ^ 2 * u := by
            rw [← Finset.mul_sum]
            exact congrArg (1 / 2 * Mf'' * Mσ ^ 2 * ·)
              (sum_capped_partition_widths hT hu huT)
    -- Combine: |a - b| ≤ ‖a‖ + ‖b‖ ≤ Mf''Mσ²u
    calc |∫ s in Set.Icc 0 u, _ ∂volume - ∑ i : Fin (n + 1), _|
        ≤ ‖∫ s in Set.Icc 0 u, _ ∂volume‖ + ‖∑ i : Fin (n + 1), _‖ := by
          rw [← Real.norm_eq_abs]; exact norm_sub_le _ _
      _ ≤ 1 / 2 * Mf'' * Mσ ^ 2 * u + 1 / 2 * Mf'' * Mσ ^ 2 * u :=
          add_le_add h1 h2
      _ = Mf'' * Mσ ^ 2 * u := by ring
  -- Measurability: process at each fixed time is measurable w.r.t. ambient σ-algebra
  have h_proc_meas : ∀ t, Measurable (X.process t) :=
    fun t => (X.process_adapted t).mono (F.le_ambient t) le_rfl
  -- Each Riemann sum Sₙ(ω) = Σ ½f″(τᵢ,X(τᵢ,ω))·∫σ² is StronglyMeasurable in ω
  have h_sum_sm : ∀ n, StronglyMeasurable (fun ω =>
      ∑ i : Fin (n + 1),
        (1 : ℝ) / 2 * deriv (deriv (fun x =>
            f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          (X.diffusion s ω) ^ 2 ∂volume)) := by
    intro n; apply Measurable.stronglyMeasurable; apply Finset.measurable_sum; intro i _
    apply Measurable.mul
    · -- ½ * f″(τᵢ,X(τᵢ,ω)): continuous f″ composed with adapted process
      exact measurable_const.mul
        ((contDiff_two_snd_deriv_continuous (hf_x _)).measurable.comp (h_proc_meas _))
    · -- ∫σ²: jointly measurable diffusion via integral_prod_left'
      exact ((X.diffusion_jointly_measurable.pow_const 2).stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Set.Icc _ _))).measurable
  -- A(n,ω) → 0 for a.e. ω (UC of f″ on compact path range)
  have h_A_ptwise_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n =>
      ∫ s in Set.Icc 0 u,
        (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
        (X.diffusion s ω) ^ 2 ∂volume -
      ∑ i : Fin (n + 1),
        (1 : ℝ) / 2 * deriv (deriv (fun x =>
            f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          (X.diffusion s ω) ^ 2 ∂volume))
      atTop (nhds 0) := by
    filter_upwards [X.process_continuous, h_gω_int] with ω hcont h_gω_int_ω
    rw [Metric.tendsto_atTop]; intro ε hε
    -- UC of X on [0,u]
    have hXω_uc : UniformContinuousOn (fun s => X.process s ω) (Set.Icc 0 u) :=
      isCompact_Icc.uniformContinuousOn_of_continuous
        (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
    -- Path range bound R
    obtain ⟨R, hR_pos, hR⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ s ∈ Set.Icc (0 : ℝ) u, |X.process s ω| ≤ R := by
      obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := u)).image_of_continuousOn
        (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
        |>.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, by positivity, fun s hs => by
        have := hR₀ ⟨s, hs, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right] at this
        exact (Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _)⟩
    -- Compact K and UC of f'' on K
    set K := Set.Icc (0 : ℝ) u ×ˢ Metric.closedBall (0 : ℝ) R
    have hK_cpt : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 R)
    have hf''_uc : UniformContinuousOn
        (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2) K :=
      hK_cpt.uniformContinuousOn_of_continuous hf''_cont.continuousOn
    -- Choose η from ε
    set η := 2 * ε / (Mσ ^ 2 * u + 1) with hη_def
    have h_denom_pos : 0 < Mσ ^ 2 * u + 1 := by positivity
    have hη_pos : 0 < η := div_pos (mul_pos two_pos hε) h_denom_pos
    obtain ⟨δ_f, hδ_f_pos, hδ_f⟩ :=
      (Metric.uniformContinuousOn_iff.mp hf''_uc) η hη_pos
    -- Get δ_X from UC of X for δ_f/2
    obtain ⟨δ_X, hδ_X_pos, hδ_X⟩ :=
      (Metric.uniformContinuousOn_iff.mp hXω_uc) (δ_f / 2) (by positivity)
    -- Find N from mesh → 0: T/(N+1) < min(δ_X, δ_f/2)
    have h_mesh_tend : Filter.Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun _ : ℕ => T) atTop (nhds T) := tendsto_const_nhds
      have h2 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h3 := Filter.Tendsto.mul h1 h2
      simp only [mul_zero] at h3
      exact h3.congr fun n => by simp [mul_comm T, div_eq_mul_inv]
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h_mesh_tend)
      (min δ_X (δ_f / 2)) (lt_min hδ_X_pos (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero]
    -- For n ≥ N, mesh = T/(n+1) < min(δ_X, δ_f/2)
    have hmesh : T / (↑n + 1) < min δ_X (δ_f / 2) := by
      have := hN n hn; rwa [Real.dist_eq, sub_zero,
        abs_of_nonneg (div_nonneg hT.le (by positivity))] at this
    -- Apply partition_error_bound with C = η/2 · Mσ²
    have h_peb := partition_error_bound (n := n)
      (c := fun i => (1 : ℝ) / 2 * deriv (deriv (fun x =>
          f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          (X.diffusion s ω) ^ 2 ∂volume))
      h_gω_int_ω (by positivity : 0 ≤ η / 2 * Mσ ^ 2)
      hT hu huT (fun i => by
      -- Per-interval: |∫(½(f''(s)-f''ᵢ))σ²| ≤ η/2·Mσ²·Δτ
      -- Beta-reduce (fun i => ...) i in the goal
      simp only []
      -- Interval setup
      have hi_le : (↑(i : ℕ) : ℝ) * T / ↑(n + 1) ≤
          (↑(i : ℕ) + 1) * T / ↑(n + 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hT.le) (by positivity)
      have hτ_le : min (↑(i : ℕ) * T / ↑(n + 1)) u ≤
          min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u :=
        min_le_min hi_le le_rfl
      have hτ_lo_nn : 0 ≤ min (↑(i : ℕ) * T / ↑(n + 1)) u :=
        le_min (by positivity) hu
      have hτ_hi_le_u : min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u ≤ u :=
        min_le_right _ _
      have hwidth : min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
          min (↑(i : ℕ) * T / ↑(n + 1)) u ≤ T / ↑(n + 1) :=
        (min_sub_min_le_sub hi_le).trans (le_of_eq (by ring))
      have hτ_sub : Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ⊆ Set.Icc 0 u :=
        Set.Icc_subset_Icc hτ_lo_nn hτ_hi_le_u
      -- Abbreviate f''ᵢ value
      set f''_val := deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω)
      -- Factor constant: ½f''ᵢ * ∫σ² = ∫ ½f''ᵢ * σ²
      rw [show (1 : ℝ) / 2 * f''_val * (∫ s in Set.Icc
          (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          (X.diffusion s ω) ^ 2 ∂volume) =
          ∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          (1 : ℝ) / 2 * f''_val * (X.diffusion s ω) ^ 2 ∂volume from
        (integral_const_mul ((1 : ℝ) / 2 * f''_val) _).symm]
      -- Integrability on sub-interval
      have hg_sub : IntegrableOn (fun s =>
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2)
          (Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u)) volume :=
        h_gω_int_ω.mono_set hτ_sub
      have hh_sub : IntegrableOn (fun s =>
          (1 : ℝ) / 2 * f''_val * (X.diffusion s ω) ^ 2)
          (Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
            (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u)) volume :=
        ((X.diffusion_sq_time_integrable ω u hu).mono_set hτ_sub).const_mul
          ((1 : ℝ) / 2 * f''_val)
      -- ∫g - ∫h = ∫(g-h)
      rw [(integral_sub hg_sub hh_sub).symm]
      -- Pointwise bound: ‖g(s) - h(s)‖ ≤ η/2 * Mσ²
      have hpw : ∀ s ∈ Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
          (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
          ‖(1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2 -
           (1 : ℝ) / 2 * f''_val * (X.diffusion s ω) ^ 2‖ ≤
          η / 2 * Mσ ^ 2 := by
        intro s hs
        rw [show (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2 -
           (1 : ℝ) / 2 * f''_val * (X.diffusion s ω) ^ 2 =
            (1 : ℝ) / 2 *
            (deriv (deriv (fun x => f s x)) (X.process s ω) - f''_val) *
            (X.diffusion s ω) ^ 2 from by ring]
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_nonneg (sq_nonneg (X.diffusion s ω)),
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have hs_mem : s ∈ Set.Icc 0 u := hτ_sub hs
        have hτ_mem : min (↑(i : ℕ) * T / ↑(n + 1)) u ∈ Set.Icc (0 : ℝ) u :=
          ⟨hτ_lo_nn, hτ_le.trans hτ_hi_le_u⟩
        -- Normalize Nat.cast: ↑(n+1) = ↑n + 1 for linarith compatibility
        have hmesh_X : T / ↑(n + 1) < δ_X := by
          rw [show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring]
          exact (lt_min_iff.mp hmesh).1
        have hmesh_f : T / ↑(n + 1) < δ_f / 2 := by
          rw [show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring]
          exact (lt_min_iff.mp hmesh).2
        -- Time distance: |s - τᵢ| < δ_f/2
        have hdist_time : dist s (min (↑(i : ℕ) * T / ↑(n + 1)) u) <
            δ_f / 2 := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
          linarith [hs.2, hwidth, hmesh_f]
        -- Space distance: |X(s) - X(τᵢ)| < δ_f/2
        have hdist_X : dist (X.process s ω)
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) < δ_f / 2 := by
          apply hδ_X s hs_mem _ hτ_mem
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
          linarith [hs.2, hwidth, hmesh_X]
        -- K membership
        have h1 : (s, X.process s ω) ∈ K :=
          ⟨hs_mem, Metric.mem_closedBall.mpr (by
            rw [dist_zero_right, Real.norm_eq_abs]; exact hR s hs_mem)⟩
        have h2 : (min (↑(i : ℕ) * T / ↑(n + 1)) u,
            X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ∈ K :=
          ⟨hτ_mem, Metric.mem_closedBall.mpr (by
            rw [dist_zero_right, Real.norm_eq_abs]; exact hR _ hτ_mem)⟩
        -- Product distance < δ_f
        have hdist_prod : dist (s, X.process s ω)
            (min (↑(i : ℕ) * T / ↑(n + 1)) u,
             X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) < δ_f := by
          simp only [Prod.dist_eq]
          exact max_lt (by linarith [hdist_time]) (by linarith [hdist_X])
        -- UC of f'' gives |f''(s,X(s)) - f''ᵢ| < η
        have huc := hδ_f _ h1 _ h2 hdist_prod
        rw [Real.dist_eq] at huc
        -- Final: ½ * |f''-f''ᵢ| * σ² ≤ ½ * η * Mσ² = η/2 * Mσ²
        calc 1 / 2 * |deriv (deriv (fun x => f s x)) (X.process s ω) - f''_val| *
            (X.diffusion s ω) ^ 2
            ≤ 1 / 2 * η * Mσ ^ 2 := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left (le_of_lt huc) (by norm_num)
              · exact sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2
              · exact sq_nonneg _
              · exact mul_nonneg (by norm_num) hη_pos.le
          _ = η / 2 * Mσ ^ 2 := by ring
      -- |∫(g-h)| ≤ (η/2·Mσ²) · Δτ
      calc |∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            ((1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
              (X.diffusion s ω) ^ 2 -
             (1 : ℝ) / 2 * f''_val * (X.diffusion s ω) ^ 2) ∂volume|
          ≤ (η / 2 * Mσ ^ 2) * volume.real (Set.Icc
              (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u)) := by
            rw [← Real.norm_eq_abs]
            exact norm_setIntegral_le_of_norm_le_const
              (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hpw
        _ = (η / 2 * Mσ ^ 2) * (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u -
            min (↑(i : ℕ) * T / ↑(n + 1)) u) := by
            rw [Measure.real, Real.volume_Icc,
                ENNReal.toReal_ofReal (sub_nonneg.mpr hτ_le)])
    calc |_| ≤ η / 2 * Mσ ^ 2 * u := h_peb
      _ < ε := by
          have h1 : η / 2 * Mσ ^ 2 * u < η / 2 * (Mσ ^ 2 * u + 1) := by nlinarith [hη_pos]
          have h2 : η / 2 * (Mσ ^ 2 * u + 1) = ε := by
            rw [hη_def]; field_simp
          linarith
  -- Integral ω ↦ ∫½f″σ² is AEStronglyMeasurable (a.e. limit of SM Riemann sums)
  have h_int_aesm : AEStronglyMeasurable (fun ω => ∫ s in Set.Icc 0 u,
      (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
      (X.diffusion s ω) ^ 2 ∂volume) μ :=
    aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun n ω => ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume))
      (fun n => (h_sum_sm n).aestronglyMeasurable)
      (by -- S_n → integral a.e. (since A = integral - S_n → 0 a.e.)
        filter_upwards [h_A_ptwise_ae] with ω hω
        have := (tendsto_const_nhds (x := ∫ s in Set.Icc 0 u,
            (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2 ∂volume)).sub hω
        simp only [sub_zero] at this
        exact this.congr fun n => by ring)
  -- A(n)² is Integrable for all n (bounded + AEStronglyMeasurable)
  have h_A_sq_int : ∀ n, Integrable (fun ω =>
      (∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume)) ^ 2) μ := fun n =>
    (integrable_const ((Mf'' * Mσ ^ 2 * u) ^ 2)).mono'
      ((h_int_aesm.sub (h_sum_sm n).aestronglyMeasurable).pow 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h := h_A_bdd n ω
        exact sq_le_sq' (neg_le_of_abs_le h) (abs_le.mp h).2)
  -- Step 1: Riemann error A → 0 in L² (by DCT with constant dominator)
  have h_A_L2 : Filter.Tendsto (fun n =>
      ∫ ω, (∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume)) ^ 2 ∂μ)
      atTop (nhds 0) := by
    -- Fatou squeeze with constant dominator (Mf''·Mσ²·u)²
    -- |A(n,ω)| ≤ Mf''·Mσ²·u and A(n,ω) → 0 a.e. by UC of f'' on compact path range
    -- Apply fatou_squeeze_tendsto_zero
    refine fatou_squeeze_tendsto_zero
      (g := fun _ _ => (Mf'' * Mσ ^ 2 * u) ^ 2)
      (G := fun _ => (Mf'' * Mσ ^ 2 * u) ^ 2)
      (fun n ω => sq_nonneg _) (fun n ω => ?_) ?_
      (ae_of_all _ fun _ => tendsto_const_nhds) (fun n => h_A_sq_int n)
      (fun _ => integrable_const _) (integrable_const _) tendsto_const_nhds
    · -- A²(n,ω) ≤ (Mf''Mσ²u)²
      have h := h_A_bdd n ω
      exact sq_le_sq' (neg_le_of_abs_le h) (abs_le.mp h).2
    · -- A² → 0 a.e. (from h_A_ptwise_ae)
      filter_upwards [h_A_ptwise_ae] with ω hω
      have := hω.pow 2; simpa [zero_pow] using this
  -- Step 2: QV discrepancy B satisfies E[B²] ≤ C_B · T / (n+1)
  have h_B_bound : ∀ n : ℕ,
      ∫ ω, (∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          ((∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume) -
           (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
            X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) ^ 2 ∂μ ≤
      C_B * T / ↑(n + 1) := by
    -- Apply weighted_capped_qv_L2_bound with weight = ½f''(τᵢ, X(τᵢ,ω)), C_w = Mf''/2
    intro n
    have h := weighted_capped_qv_L2_bound X hMμ hMσ T u hT hu huT n
      (fun i ω => (1 : ℝ) / 2 * deriv (deriv (fun x =>
          f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
        (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω))
      (C_w := Mf'' / 2) (div_nonneg hMf''_nn (by norm_num))
      (fun i ω => by
        rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1/2 from by norm_num)]
        calc 1 / 2 * |deriv (deriv (fun x => f _ x)) (X.process _ ω)|
            ≤ 1 / 2 * Mf'' :=
              mul_le_mul_of_nonneg_left (hMf'' _ _) (by norm_num)
          _ = Mf'' / 2 := by ring)
      (fun i => measurable_const.mul
        ((contDiff_two_snd_deriv_continuous (hf_x _)).measurable.comp
          (X.process_adapted _)))
    -- Algebraic identity: 3·((Mf''/2)²·8Mσ⁴u + ...) = C_B
    have h_eq : 3 * ((Mf'' / 2) ^ 2 * 8 * Mσ ^ 4 * u +
        4 * (Mf'' / 2) ^ 2 * Mμ ^ 2 * Mσ ^ 2 * u * T +
        (Mf'' / 2) ^ 2 * Mμ ^ 4 * u ^ 2 * T) * T / ↑(n + 1) =
        C_B * T / ↑(n + 1) := by rw [hCB_def]; ring
    linarith
  -- Step 3: B L² convergence from quantitative bound
  have h_B_L2 : Filter.Tendsto (fun n =>
      ∫ ω, (∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          ((∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume) -
           (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
            X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) ^ 2 ∂μ)
      atTop (nhds 0) := by
    apply squeeze_zero
    · intro n; exact integral_nonneg fun ω => sq_nonneg _
    · exact h_B_bound
    · rw [show (0 : ℝ) = C_B * T * 0 from by ring]
      exact (tendsto_const_nhds (x := C_B * T)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by
          rw [Nat.cast_succ]; ring)
  -- Measurability of sum with ΔX² (process increments, not QV)
  have h_sum_ΔX_sm : ∀ n, StronglyMeasurable (fun ω =>
      ∑ i : Fin (n + 1),
        (1 : ℝ) / 2 * deriv (deriv (fun x =>
            f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) := by
    intro n; apply Measurable.stronglyMeasurable; apply Finset.measurable_sum; intro i _
    apply Measurable.mul
    · exact measurable_const.mul
        ((contDiff_two_snd_deriv_continuous (hf_x _)).measurable.comp (h_proc_meas _))
    · exact ((h_proc_meas _).sub (h_proc_meas _)).pow_const 2
  -- E3 is AEStronglyMeasurable (integral - sum with ΔX²)
  have h_E3_aesm : ∀ n, AEStronglyMeasurable (fun ω =>
      ∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) μ :=
    fun n => h_int_aesm.sub (h_sum_ΔX_sm n).aestronglyMeasurable
  -- E3² is integrable (from L4 stochastic integral bounds + bounded drift)
  -- |E3| ≤ ½Mf''Mσ²u + ½Mf''·Σ ΔXᵢ², and Σ ΔXᵢ² ≤ 2Σ ΔSIᵢ² + C a.e.
  -- (Σ ΔSIᵢ²)² ≤ (n+1)·Σ ΔSIᵢ⁴ (Cauchy-Schwarz), each ΔSIᵢ⁴ integrable
  have h_E3_sq_int : ∀ n, Integrable (fun ω =>
      (∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) ^ 2) μ := by
    intro n
    -- Time points
    set τ := fun (i : Fin (n + 1)) => min (↑(i : ℕ) * T / ↑(n + 1)) u
    set τ' := fun (i : Fin (n + 1)) => min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u
    have hτ_nn : ∀ i, 0 ≤ τ i := fun i => le_min
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hT.le) (Nat.cast_nonneg _)) hu
    have hτ'_nn : ∀ i, 0 ≤ τ' i := fun i => le_min
      (div_nonneg (mul_nonneg (by positivity) hT.le) (Nat.cast_nonneg _)) hu
    have hττ' : ∀ i, τ i ≤ τ' i := fun i => min_le_min_right u
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) hT.le)
        (Nat.cast_nonneg _))
    have hτ_le_T : ∀ i, τ i ≤ T := fun i => le_trans (min_le_right _ _) huT
    have hτ'_le_T : ∀ i, τ' i ≤ T := fun i => le_trans (min_le_right _ _) huT
    -- L4 integrability of stochastic integral increments
    have h_SI4 : ∀ i : Fin (n + 1),
        Integrable (fun ω =>
          (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 4) μ :=
      fun i => stoch_integral_increment_L4_integrable_proof X hMσ
        (τ i) (τ' i) (hτ_nn i) (hττ' i)
    -- Dominator: const + const · Σ ΔSI⁴
    set K := 2 * (1 / 2 * Mf'' * Mσ ^ 2 * u) ^ 2 +
      Mf'' ^ 2 * (2 * (↑(n + 1) : ℝ) * (2 * Mμ * T) ^ 2) ^ 2
    have h_dom_int : Integrable (fun ω =>
        K + 4 * Mf'' ^ 2 * (↑(n + 1) : ℝ) *
          ∑ i : Fin (n + 1),
            (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 4) μ :=
      (integrable_const K).add ((integrable_finset_sum _ fun i _ => h_SI4 i).const_mul _)
    -- integral_form: for a.e. ω, ΔX = ΔSI + ΔDI for all intervals
    have h_if_ae : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
        X.process (τ' i) ω - X.process (τ i) ω =
        (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) +
        ((∫ r in Set.Icc 0 (τ' i), X.drift r ω ∂volume) -
         (∫ r in Set.Icc 0 (τ i), X.drift r ω ∂volume)) := by
      rw [ae_all_iff]; intro i
      filter_upwards [X.integral_form (τ' i) (hτ'_nn i),
                       X.integral_form (τ i) (hτ_nn i)] with ω h2 h1
      linarith
    -- Apply Integrable.mono'
    exact h_dom_int.mono' ((h_E3_aesm n).pow 2) (by
      filter_upwards [h_if_ae, h_gω_int] with ω hif hgω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      -- |E3(ω)| ≤ ½Mf''·Mσ²·u + ½Mf''·Σ ΔXᵢ²
      have hIcc_vol : volume (Set.Icc (0 : ℝ) u) < ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      have h_int_bdd : ‖∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume‖ ≤ 1 / 2 * Mf'' * Mσ ^ 2 * u := by
        calc _ ≤ (1 / 2 * Mf'' * Mσ ^ 2) * volume.real (Set.Icc (0 : ℝ) u) :=
              norm_setIntegral_le_of_norm_le_const hIcc_vol (fun s _ => by
                rw [Real.norm_eq_abs, abs_mul, abs_mul,
                    abs_of_nonneg (sq_nonneg (X.diffusion s ω)),
                    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
                exact mul_le_mul (mul_le_mul_of_nonneg_left (hMf'' s _) (by norm_num))
                  (sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2)
                  (sq_nonneg _) (mul_nonneg (by norm_num) hMf''_nn))
          _ = 1 / 2 * Mf'' * Mσ ^ 2 * u := by
              rw [Measure.real, Real.volume_Icc,
                  ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ u - 0), sub_zero]
      -- For a.e. ω: each ΔXᵢ² ≤ 2·ΔSIᵢ² + 2·(2MμT)² (from integral_form + drift bound)
      have h_DX_bdd : ∀ i : Fin (n + 1),
          (X.process (τ' i) ω - X.process (τ i) ω) ^ 2 ≤
          2 * (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2 +
          2 * (2 * Mμ * T) ^ 2 := by
        intro i
        have h_decomp := hif i
        -- Drift integral difference bounded
        have hDI_each : ∀ (t' : ℝ), 0 ≤ t' → t' ≤ T →
            ‖∫ r in Set.Icc 0 t', X.drift r ω ∂volume‖ ≤ Mμ * T := by
          intro t' ht'_nn ht'_le
          calc _ ≤ Mμ * volume.real (Set.Icc 0 t') :=
                norm_setIntegral_le_of_norm_le_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
                  (fun s _ => by exact_mod_cast hMμ s ω)
            _ ≤ Mμ * T := by
                rw [Measure.real, Real.volume_Icc,
                    ENNReal.toReal_ofReal (by linarith), sub_zero]
                exact mul_le_mul_of_nonneg_left ht'_le hMμ_nn
        have hDI : ‖(∫ r in Set.Icc 0 (τ' i), X.drift r ω ∂volume) -
            (∫ r in Set.Icc 0 (τ i), X.drift r ω ∂volume)‖ ≤ 2 * Mμ * T := by
          calc _ ≤ ‖∫ r in Set.Icc 0 (τ' i), X.drift r ω ∂volume‖ +
                    ‖∫ r in Set.Icc 0 (τ i), X.drift r ω ∂volume‖ := norm_sub_le _ _
            _ ≤ Mμ * T + Mμ * T :=
                add_le_add (hDI_each _ (hτ'_nn i) (hτ'_le_T i))
                  (hDI_each _ (hτ_nn i) (hτ_le_T i))
            _ = 2 * Mμ * T := by ring
        -- (a + b)² ≤ 2a² + 2b²
        rw [h_decomp]
        have hDI_abs := (Real.norm_eq_abs _).symm ▸ hDI
        have hDI_sq := sq_le_sq' (abs_le.mp hDI_abs).1 (abs_le.mp hDI_abs).2
        nlinarith [sq_nonneg ((X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) -
            ((∫ r in Set.Icc 0 (τ' i), X.drift r ω ∂volume) -
             (∫ r in Set.Icc 0 (τ i), X.drift r ω ∂volume)))]
      -- Bound: Σ ΔXᵢ² ≤ 2·Σ ΔSIᵢ² + C
      have h_sum_bdd : ∑ i : Fin (n + 1),
          (X.process (τ' i) ω - X.process (τ i) ω) ^ 2 ≤
          2 * ∑ i : Fin (n + 1),
            (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2 +
          2 * (↑(n + 1) : ℝ) * (2 * Mμ * T) ^ 2 := by
        calc ∑ i : Fin (n + 1), (X.process (τ' i) ω - X.process (τ i) ω) ^ 2
            ≤ ∑ i : Fin (n + 1),
              (2 * (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2 +
               2 * (2 * Mμ * T) ^ 2) :=
              Finset.sum_le_sum fun i _ => h_DX_bdd i
          _ = 2 * ∑ i : Fin (n + 1),
                (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2 +
              2 * (↑(n + 1) : ℝ) * (2 * Mμ * T) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
                  Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      -- Cauchy-Schwarz for ΔSI sum: (Σ ΔSIᵢ²)² ≤ (n+1)·Σ ΔSIᵢ⁴
      have h_CS : (∑ i : Fin (n + 1),
          (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2) ^ 2 ≤
          ↑(n + 1) * ∑ i : Fin (n + 1),
            (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 4 := by
        have h := @sq_sum_le_card_mul_sum_sq (Fin (n + 1)) ℝ _ _ _ _
          (s := Finset.univ)
          (f := fun i => (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        calc _ ≤ ↑(n + 1) * ∑ i : Fin (n + 1),
              ((X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2) ^ 2 := h
          _ = _ := by congr 1; apply Finset.sum_congr rfl; intro i _; ring
      -- Abbreviations for clean nlinarith
      set S_SI := ∑ i : Fin (n + 1),
          (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 2
      set S_X := ∑ i : Fin (n + 1),
          (X.process (τ' i) ω - X.process (τ i) ω) ^ 2
      set C' := 2 * (↑(n + 1) : ℝ) * (2 * Mμ * T) ^ 2
      have hC'_nn : 0 ≤ C' := by positivity
      have h_SX_bdd : S_X ≤ 2 * S_SI + C' := h_sum_bdd
      have h_sum_nn : 0 ≤ S_X := Finset.sum_nonneg fun i _ => sq_nonneg _
      -- S_X² ≤ 8(n+1)·Σ ΔSI⁴ + 2C'²
      have h_SX_sq : S_X ^ 2 ≤ 8 * (↑(n + 1) : ℝ) *
          ∑ i : Fin (n + 1),
            (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 4 +
          2 * C' ^ 2 := by
        calc S_X ^ 2 ≤ (2 * S_SI + C') ^ 2 :=
              pow_le_pow_left₀ h_sum_nn h_SX_bdd 2
          _ ≤ 8 * S_SI ^ 2 + 2 * C' ^ 2 := by nlinarith [sq_nonneg (2 * S_SI - C')]
          _ ≤ 8 * (↑(n + 1) : ℝ) *
                ∑ i : Fin (n + 1),
                  (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 4 +
              2 * C' ^ 2 := by nlinarith [h_CS]
      -- |Σ wᵢ·ΔXᵢ²| ≤ ½Mf''·S_X
      have h_sum_abs : |∑ i : Fin (n + 1), 1 / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (τ' i) ω - X.process (τ i) ω) ^ 2| ≤
          1 / 2 * Mf'' * S_X := by
        calc _ ≤ ∑ i : Fin (n + 1), |1 / 2 *
            deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
            (X.process (τ' i) ω - X.process (τ i) ω) ^ 2| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin (n + 1), 1 / 2 * Mf'' *
              (X.process (τ' i) ω - X.process (τ i) ω) ^ 2 := by
              apply Finset.sum_le_sum; intro i _
              have h_sq_nn : (0 : ℝ) ≤
                  (X.process (τ' i) ω - X.process (τ i) ω) ^ 2 := sq_nonneg _
              rw [abs_mul, abs_of_nonneg h_sq_nn, abs_mul,
                  abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/2)]
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hMf'' _ _) (by positivity)) (sq_nonneg _)
          _ = 1 / 2 * Mf'' * S_X := by rw [Finset.mul_sum]
      -- Final bound: E3² ≤ K + 4·Mf''²·(n+1)·Σ ΔSI⁴
      have h_int_abs := (Real.norm_eq_abs _).symm ▸ h_int_bdd
      -- Convert absolute value bounds to squared bounds
      have h_int_sq := sq_le_sq' (abs_le.mp h_int_abs).1 (abs_le.mp h_int_abs).2
      have h_sum_sq := sq_le_sq' (abs_le.mp h_sum_abs).1 (abs_le.mp h_sum_abs).2
      -- Step 1: (a-b)² ≤ 2a² + 2b²
      set DI := ∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume
      set SUM := ∑ i : Fin (n + 1), 1 / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (τ' i) ω - X.process (τ i) ω) ^ 2
      have h_ab : (DI - SUM) ^ 2 ≤ 2 * DI ^ 2 + 2 * SUM ^ 2 := by
        nlinarith [sq_nonneg (DI + SUM)]
      -- Step 2: bound each squared term
      have h_DI_bdd : 2 * DI ^ 2 ≤ 2 * (1 / 2 * Mf'' * Mσ ^ 2 * u) ^ 2 := by
        linarith [h_int_sq]
      have h_SUM_bdd : 2 * SUM ^ 2 ≤ Mf'' ^ 2 / 2 * S_X ^ 2 := by
        have : (1 / 2 * Mf'' * S_X) ^ 2 = Mf'' ^ 2 / 4 * S_X ^ 2 := by ring
        nlinarith [h_sum_sq]
      -- Step 3: bound S_X² using h_SX_sq
      have h_SX_final : Mf'' ^ 2 / 2 * S_X ^ 2 ≤
          4 * Mf'' ^ 2 * (↑(n + 1) : ℝ) *
            ∑ i : Fin (n + 1),
              (X.stoch_integral (τ' i) ω - X.stoch_integral (τ i) ω) ^ 4 +
          Mf'' ^ 2 * C' ^ 2 := by
        nlinarith [h_SX_sq, sq_nonneg Mf'']
      -- Combine: E3² ≤ 2C₁² + Mf''²C'² + 4Mf''²(n+1)Σ ΔSI⁴ = K + 4Mf''²(n+1)Σ ΔSI⁴
      have hK_eq : 2 * (1 / 2 * Mf'' * Mσ ^ 2 * u) ^ 2 + Mf'' ^ 2 * C' ^ 2 = K := by
        simp only [C', K]
      linarith [h_ab, h_DI_bdd, h_SUM_bdd, h_SX_final, hK_eq])
  -- B² integrable: B = E3 - A, so B² ≤ 2E3² + 2A²
  have h_B_sq_int : ∀ n, Integrable (fun ω =>
      (∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          ((∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume) -
           (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
            X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) ^ 2) μ := by
    intro n
    -- B(ω) = E3(ω) - A(ω) pointwise, where E3 uses ΔX² and A uses QV
    have h_dom := ((h_E3_sq_int n).const_mul 2).add ((h_A_sq_int n).const_mul 2)
    refine h_dom.mono' ?_ ?_
    · -- B = (Σ wᵢ·QVᵢ) - (Σ wᵢ·ΔXᵢ²), use h_sum_sm and h_sum_ΔX_sm
      apply AEStronglyMeasurable.pow
      have h_eq : (fun ω => ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          ((∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume) -
           (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
            X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) =
        (fun ω => (∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume)) -
        (∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) := by
        ext ω; simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [h_eq]
      exact ((h_sum_sm n).sub (h_sum_ΔX_sm n)).aestronglyMeasurable
    · refine ae_of_all _ fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      -- B = E3 - A: (Σ w·(QV-ΔX²)) = (integral - Σ w·ΔX²) - (integral - Σ w·QV)
      have hBA : ∑ i : Fin (n + 1), 1 / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          ((∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume) -
           (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
            X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) =
        (∫ s in Set.Icc 0 u, 1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
         ∑ i : Fin (n + 1), 1 / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) -
        (∫ s in Set.Icc 0 u, 1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
         ∑ i : Fin (n + 1), 1 / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume)) := by
        simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]; ring
      rw [hBA]; simp only [Pi.add_apply]
      nlinarith [sq_nonneg (∫ s in Set.Icc 0 u,
          1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1), 1 / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2 +
        (∫ s in Set.Icc 0 u,
          1 / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1), 1 / 2 *
          deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume)))]
  -- Step 4: E[E3²] ≤ 2E[A²] + 2E[B²] from E3 = A + B, (a+b)² ≤ 2a²+2b²
  have h_le : ∀ n : ℕ, ∫ ω, (∫ s in Set.Icc 0 u,
        (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
        (X.diffusion s ω) ^ 2 ∂volume -
      ∑ i : Fin (n + 1),
        (1 : ℝ) / 2 * deriv (deriv (fun x =>
            f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
          (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) ^ 2 ∂μ ≤
    2 * ∫ ω, (∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume)) ^ 2 ∂μ +
    2 * ∫ ω, (∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          ((∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
            (X.diffusion s ω) ^ 2 ∂volume) -
           (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
            X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) ^ 2 ∂μ := by
    intro n
    apply integral_sq_le_of_eq_add
    · -- E3(ω) = A(ω) + B(ω) by adding/subtracting Σ wᵢ · QVᵢ
      intro ω
      -- mul_sub rewrites w*(QV-ΔX²) → w*QV - w*ΔX², then sum_sub_distrib
      simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]; linarith
    · -- A² integrable: |A| ≤ Mf''·Mσ²·u (bounded), hence A² bounded on prob space
      exact h_A_sq_int n
    · -- B² integrable: B is finite sum of L² terms
      exact h_B_sq_int n
  -- Step 5: Combine
  have h_upper : Filter.Tendsto (fun n =>
      2 * ∫ ω, (∫ s in Set.Icc 0 u,
            (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2 ∂volume -
          ∑ i : Fin (n + 1),
            (1 : ℝ) / 2 * deriv (deriv (fun x =>
                f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
            (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
              (X.diffusion s ω) ^ 2 ∂volume)) ^ 2 ∂μ +
      2 * ∫ ω, (∑ i : Fin (n + 1),
            (1 : ℝ) / 2 * deriv (deriv (fun x =>
                f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
            ((∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u),
              (X.diffusion s ω) ^ 2 ∂volume) -
             (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
              X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2)) ^ 2 ∂μ)
      atTop (nhds 0) := by
    have := (h_A_L2.const_mul 2).add (h_B_L2.const_mul 2)
    rwa [mul_zero, zero_add] at this
  have h_E3_L2 : Filter.Tendsto (fun n =>
      ∫ ω, (∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x =>
              f (min (↑(i : ℕ) * T / ↑(n + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n + 1)) u) ω) ^ 2) ^ 2 ∂μ)
      atTop (nhds 0) := by
    exact squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) h_le h_upper
  -- Step 3f: Extract E3 a.e.-convergent subsequence ms₃
  -- First compose with ns ∘ ms₁ ∘ ms₂ to get L² convergence along the subsequence
  obtain ⟨ms₃, hms₃, h_E3_ae_raw⟩ := L2_zero_ae_subseq
    (h_E3_L2.comp ((hns.comp hms₁.tendsto_atTop).comp hms₂.tendsto_atTop))
    (fun k => h_E3_sq_int (ns (ms₁ (ms₂ k))))
    (fun k => h_E3_aesm (ns (ms₁ (ms₂ k))))
  -- Step 3d: Compose ms = ms₁ ∘ ms₂ ∘ ms₃
  let ms := fun k => ms₁ (ms₂ (ms₃ k))
  have hms : StrictMono ms := (hms₁.comp hms₂).comp hms₃
  -- Transfer uncapped QV a.e. convergence to composed subsequence
  have h_qv_ae : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k =>
      ∑ i : Fin (ns (ms k) + 1),
        (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
         X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2)
      atTop (nhds (X.quadraticVariation T ω)) := by
    filter_upwards [h_qv_ae₁] with ω hω
    exact hω.comp (hms₂.comp hms₃).tendsto_atTop
  -- Transfer capped QV a.e. convergence through ms₃
  have h_capped_qv_ae' : ∀ᵐ ω ∂μ, Filter.Tendsto (fun k =>
      ∑ i : Fin (ns (ms₁ (ms₂ (ms₃ k))) + 1),
        (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms₁ (ms₂ (ms₃ k))) + 1)) u) ω -
         X.process (min (↑(i : ℕ) * T / ↑(ns (ms₁ (ms₂ (ms₃ k))) + 1)) u) ω) ^ 2)
      atTop (nhds (X.quadraticVariation u ω)) := by
    filter_upwards [h_capped_qv_ae] with ω hω
    exact hω.comp hms₃.tendsto_atTop
  -- Step 4: L² convergence along ns ∘ ms via Fatou squeeze
  have h_qv_L2_nsms := h_qv_L2_ns.comp hms.tendsto_atTop
  refine ⟨ms, ?_⟩
  -- Define the dominator constant (from crude error bounds)
  -- error² ≤ 4(E1² + E2² + E3² + E4²) ≤ C_det + C_rand · Sk_capped²
  -- where C_det bounds deterministic terms and C_rand bounds Sk-dependent terms
  -- Sk_capped ≤ Sk_uncapped + boundary², so Sk_capped² ≤ 2Sk_uncapped² + 2boundary⁴
  -- Sk_uncapped² ≤ 2(Sk_uncapped-QV(T))² + 2QV(T)²
  -- Combined: C_rand·Sk_capped² ≤ 4C_rand·(Sk-QV)² + 4C_rand·QV² + 2C_rand·boundary⁴
  set C_det : ℝ := 4 * (2 * Mft * T) ^ 2 + 4 * (2 * Mf' * Mμ * T) ^ 2 +
    2 * Mf'' ^ 2 * (Mσ ^ 2 * T) ^ 2
  set C_rand : ℝ := 4 * (Mf'' ^ 2 / 2 + 4 * Mf'' ^ 2) -- ≈ 18 Mf''²
  -- Boundary partition index: j = ⌊u·(n+1)/T⌋, τ_j = j·T/(n+1)
  -- For the boundary correction: X(u) - X(τ_j) is the increment over [τ_j, u]
  -- with u - τ_j ≤ T/(n+1) → 0
  let bdy_pt (k : ℕ) : ℝ :=
    ↑(Nat.floor (u * ↑(ns (ms k) + 1) / T)) * T / ↑(ns (ms k) + 1)
  -- Properties of boundary partition point
  have h_bdy_nn : ∀ k, 0 ≤ bdy_pt k := fun k => by
    simp only [bdy_pt]; positivity
  have h_bdy_le : ∀ k, bdy_pt k ≤ u := by
    intro k; simp only [bdy_pt]
    have hN : (0 : ℝ) < ↑(ns (ms k) + 1) := Nat.cast_pos.mpr (Nat.succ_pos _)
    have hr_nn : 0 ≤ u * ↑(ns (ms k) + 1) / T := by positivity
    calc (↑⌊u * ↑(ns (ms k) + 1) / T⌋₊ : ℝ) * T / ↑(ns (ms k) + 1)
        ≤ (u * ↑(ns (ms k) + 1) / T) * T / ↑(ns (ms k) + 1) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (Nat.floor_le hr_nn) hT.le) hN.le
      _ = u := by field_simp
  -- Lower bound: u - T/(N+1) ≤ bdy_pt k
  have h_lower : ∀ k, u - T / ↑(ns (ms k) + 1) ≤ bdy_pt k := by
    intro k; simp only [bdy_pt]
    have hN : (0 : ℝ) < ↑(ns (ms k) + 1) := Nat.cast_pos.mpr (Nat.succ_pos _)
    have hr_nn : 0 ≤ u * ↑(ns (ms k) + 1) / T := by positivity
    have h1 : (↑⌊u * ↑(ns (ms k) + 1) / T⌋₊ : ℝ) ≥
        u * ↑(ns (ms k) + 1) / T - 1 := by
      have h_fl := Nat.lt_floor_add_one (u * ↑(ns (ms k) + 1) / T)
      push_cast at h_fl ⊢; linarith
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 hT.le) hN.le
    have h3 : (u * ↑(ns (ms k) + 1) / T - 1) * T / ↑(ns (ms k) + 1) =
        u - T / ↑(ns (ms k) + 1) := by field_simp
    linarith
  -- Width T/(N+1) → 0
  have h_width : Filter.Tendsto (fun k => T / ↑(ns (ms k) + 1)) atTop (nhds 0) := by
    have h_nsms_nat : Filter.Tendsto (fun k => ns (ms k) + 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp
        (hns.comp hms.tendsto_atTop) b
      exact ⟨N, fun k hk => le_trans (hN k hk) (Nat.le_add_right _ 1)⟩
    have h_cast : Filter.Tendsto (fun k => (↑(ns (ms k) + 1) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp h_nsms_nat
    exact tendsto_const_nhds.div_atTop h_cast
  -- bdy_pt k → u (squeeze theorem)
  have h_bdy_conv : Filter.Tendsto (fun k => bdy_pt k) atTop (nhds u) := by
    have h_lower_tend : Filter.Tendsto (fun k => u - T / ↑(ns (ms k) + 1))
        atTop (nhds u) := by
      have := tendsto_const_nhds (x := u) |>.sub h_width
      rwa [sub_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h_lower_tend tendsto_const_nhds
      h_lower (h_bdy_le ·)
  -- Apply fatou_squeeze_tendsto_zero_ae (a.e. domination version)
  apply fatou_squeeze_tendsto_zero_ae
    (g := fun k ω => C_det + 4 * C_rand *
      (∑ i : Fin (ns (ms k) + 1),
        (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
         X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
       X.quadraticVariation T ω) ^ 2 +
      4 * C_rand * (X.quadraticVariation T ω) ^ 2 +
      2 * C_rand * (X.process u ω - X.process (bdy_pt k) ω) ^ 4)
    (G := fun ω => C_det + 4 * C_rand * (X.quadraticVariation T ω) ^ 2)
  -- (1) f_k ≥ 0
  · intro k ω; exact sq_nonneg _
  -- (2) g_k ≥ 0
  · intro k ω
    apply add_nonneg (add_nonneg (add_nonneg _ _) _) _
    · positivity
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact mul_nonneg (by positivity) (by positivity)
  -- (3) f_k ≤ g_k a.e. (uniform in k)
  · rw [ae_all_iff]; intro k
    -- Provide a.e. integrability hypotheses for ito_error_decomposition
    have hIcc_finite : volume (Set.Icc (0 : ℝ) u) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hint_t_k : ∀ᵐ ω ∂μ, IntegrableOn
        (fun s => deriv (fun t => f t (X.process s ω)) s) (Set.Icc 0 u) volume := by
      filter_upwards [X.process_continuous] with ω hω
      exact (hf_t_cont.comp (continuous_id.prodMk hω)).continuousOn.integrableOn_compact
        isCompact_Icc
    have hint_d_k : ∀ᵐ ω ∂μ, IntegrableOn
        (fun s => deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
        (Set.Icc 0 u) volume := by
      filter_upwards [X.process_continuous] with ω hω
      exact Integrable.mono'
        (show IntegrableOn (fun _ => Mf' * Mμ) _ _ from integrableOn_const hIcc_finite)
        ((hf'_cont.comp (continuous_id.prodMk hω)).aestronglyMeasurable.restrict.mul
          (X.drift_time_integrable ω u hu).aestronglyMeasurable)
        (ae_of_all _ fun s => le_trans (norm_mul_le _ _) (by
          simp only [Real.norm_eq_abs]
          exact mul_le_mul (hMf' s _) (hMμ s ω) (abs_nonneg _) hMf'_nn))
    have hint_σ_k : ∀ᵐ ω ∂μ, IntegrableOn
        (fun s => (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2) (Set.Icc 0 u) volume := by
      filter_upwards [X.process_continuous] with ω hω
      have h_half_f'' : Continuous (fun s =>
          (1:ℝ)/2 * deriv (deriv (fun x => f s x)) (X.process s ω)) :=
        continuous_const.mul (hf''_cont.comp (continuous_id.prodMk hω))
      exact Integrable.mono'
        (show IntegrableOn (fun _ => 1/2 * Mf'' * Mσ ^ 2) _ _ from
          integrableOn_const hIcc_finite)
        (h_half_f''.aestronglyMeasurable.restrict.mul
          (X.diffusion_sq_time_integrable ω u hu).aestronglyMeasurable)
        (ae_of_all _ fun s => by
          have h_abs1 : |1/2 * deriv (deriv (fun x => f s x)) (X.process s ω)| =
              1/2 * |deriv (deriv (fun x => f s x)) (X.process s ω)| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
          have h_abs2 : |(X.diffusion s ω) ^ 2| = (X.diffusion s ω) ^ 2 :=
            abs_of_nonneg (sq_nonneg _)
          rw [Real.norm_eq_abs, abs_mul, h_abs1, h_abs2]
          -- Goal: 1/2 * |f''(X_s)| * σ² ≤ 1/2 * Mf'' * Mσ²
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hMf'' s _) (by norm_num))
            (sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2)
            (sq_nonneg _)
            (mul_nonneg (by norm_num) hMf''_nn))
    -- Error decomposition: error² ≤ 4(E1² + E2² + E3² + E4²)
    have h_decomp := ito_error_decomposition X f hf_x T hT (ns (ms k)) u hu huT
      hint_t_k hint_d_k hint_σ_k
    filter_upwards [h_decomp] with ω hω
    -- hω: error² ≤ 4 * (E1² + E2² + E3² + E4²)
    -- Strategy: bound 4(E1²+E2²+E3²+E4²) ≤ C_det + 18Mf''²·Sk_capped²
    --           then Sk_capped² ≤ 4(Sk_unc-QV)²+4QV²+2bdy⁴
    --           then ≤ g_k
    set n_k := ns (ms k)
    -- Define Sk_capped (partition sum over capped times min(iΔ, u))
    set Sk_cap := ∑ i : Fin (n_k + 1),
      (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
       X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2
    -- Sk_uncapped (full partition sum without capping)
    set Sk_unc := ∑ i : Fin (n_k + 1),
      (X.process ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) ω -
       X.process (↑(i : ℕ) * T / ↑(n_k + 1)) ω) ^ 2
    set QV := X.quadraticVariation T ω
    set bdy := X.process u ω - X.process (bdy_pt k) ω
    -- Step A: 4*(E1²+E2²+E3²+E4²) ≤ C_det + 18·Mf''²·Sk_cap²
    -- This uses: |E1| ≤ 2Mft·T, |E2| ≤ 2Mf'·Mμ·T,
    --            |E3| ≤ ½Mf''·(Mσ²·T+Sk_cap), |E4| ≤ 2Mf''·Sk_cap
    have hA : 4 * ((∫ s in Set.Icc 0 u,
          deriv (fun t => f t (X.process s ω)) s ∂volume -
        ∑ i : Fin (n_k + 1),
          (f (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u)
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
           f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω)))^2 +
        (∫ s in Set.Icc 0 u,
          deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume -
        ∑ i : Fin (n_k + 1),
          deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u),
            X.drift s ω ∂volume))^2 +
        (∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n_k + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2)^2 +
        (∑ i : Fin (n_k + 1),
          (f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
           f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
           deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
           (1 : ℝ) / 2 *
            deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2))^2) ≤
      C_det + 18 * Mf'' ^ 2 * Sk_cap ^ 2 := by
      -- Name the 4 error terms for clarity
      set E1 := ∫ s in Set.Icc 0 u,
          deriv (fun t => f t (X.process s ω)) s ∂volume -
        ∑ i : Fin (n_k + 1),
          (f (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u)
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
           f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω))
      set E2 := ∫ s in Set.Icc 0 u,
          deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume -
        ∑ i : Fin (n_k + 1),
          deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
          (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
              (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u),
            X.drift s ω ∂volume)
      set E3 := ∫ s in Set.Icc 0 u,
          (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
          (X.diffusion s ω) ^ 2 ∂volume -
        ∑ i : Fin (n_k + 1),
          (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2
      set E4 := ∑ i : Fin (n_k + 1),
          (f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
           f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
           deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
            (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
           (1 : ℝ) / 2 *
            deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2)
      -- Absolute value bounds on each error term
      -- E1: time Riemann error |∫∂_tf - Σ Δf| ≤ |∫∂_tf| + |Σ Δf| ≤ Mft·T + Mft·T
      have hE1_abs : |E1| ≤ 2 * Mft * T := by
        -- Triangle: |int - sum| ≤ |int| + |sum|
        have h_tri : |E1| ≤
            |∫ s in Set.Icc 0 u,
              deriv (fun t => f t (X.process s ω)) s ∂volume| +
            |∑ i : Fin (n_k + 1),
              (f (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u)
                (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
               f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω))| := by
          simp only [E1, ← Real.norm_eq_abs]; exact norm_sub_le _ _
        -- Integral bound: |∫ ∂_tf| ≤ Mft · T
        have h_int : |∫ s in Set.Icc 0 u,
            deriv (fun t => f t (X.process s ω)) s ∂volume| ≤ Mft * T := by
          rw [← Real.norm_eq_abs]
          exact integral_abs_le_of_bdd _ Mft hMft_nn
            (fun s => by rw [Real.norm_eq_abs]; exact hMft s _) u T hu huT
        -- Sum bound: |Σ Δf| ≤ Mft · T via MVT + mesh
        have h_sum : |∑ i : Fin (n_k + 1),
            (f (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
             f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω))| ≤
            Mft * T := by
          have hN : (0 : ℝ) < ↑(n_k + 1) := Nat.cast_pos.mpr (Nat.succ_pos _)
          -- Each |Δf_i| ≤ Mft * T/(n+1) by MVT + mesh bound
          calc |∑ i : Fin (n_k + 1), _|
              ≤ ∑ i : Fin (n_k + 1),
                |f (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u)
                  (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
                 f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                  (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin (n_k + 1), Mft * (T / ↑(n_k + 1)) :=
                Finset.sum_le_sum fun i _ => by
                  -- MVT: |f(a,y) - f(b,y)| ≤ Mft * |a - b|
                  have h_mvt := time_lipschitz hf_t hMft
                    (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u)
                    (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                    (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω)
                  -- Mesh: |t_{i+1}' - t_i'| ≤ T/(n+1)
                  have h_mesh : |min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u -
                      min (↑(i : ℕ) * T / ↑(n_k + 1)) u| ≤ T / ↑(n_k + 1) := by
                    have h_step : (↑(i : ℕ) : ℝ) * T / ↑(n_k + 1) ≤
                        (↑(i : ℕ) + 1) * T / ↑(n_k + 1) := by
                      apply div_le_div_of_nonneg_right _ hN.le
                      exact mul_le_mul_of_nonneg_right (by linarith) hT.le
                    rw [abs_le]; constructor
                    · linarith [min_le_min_right u h_step, div_nonneg hT.le hN.le]
                    · have := min_sub_min_le_sub h_step (c := u)
                      have : (↑(i : ℕ) + 1) * T / ↑(n_k + 1) - ↑(i : ℕ) * T / ↑(n_k + 1) =
                        T / ↑(n_k + 1) := by ring
                      linarith
                  calc |f _ _ - f _ _| ≤ Mft * |_ - _| := h_mvt
                    _ ≤ Mft * (T / ↑(n_k + 1)) :=
                        mul_le_mul_of_nonneg_left h_mesh hMft_nn
            _ = ↑(n_k + 1) * (Mft * (T / ↑(n_k + 1))) := by
                rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            _ = Mft * T := by field_simp
        linarith
      -- E2: drift Riemann error |∫f'μ - Σ f'·∫μ| ≤ Mf'·Mμ·T + Mf'·Mμ·T
      have hE2_abs : |E2| ≤ 2 * Mf' * Mμ * T := by
        -- Triangle: |int - sum| ≤ |int| + |sum|
        have h_tri : |E2| ≤
            |∫ s in Set.Icc 0 u,
              deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume| +
            |∑ i : Fin (n_k + 1),
              deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
                (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
              (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                  (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u),
                X.drift s ω ∂volume)| := by
          simp only [E2, ← Real.norm_eq_abs]; exact norm_sub_le _ _
        -- Integral bound: |∫ f'·μ| ≤ Mf'·Mμ·T
        have h_int : |∫ s in Set.Icc 0 u,
            deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume| ≤
            Mf' * Mμ * T := by
          rw [← Real.norm_eq_abs]
          exact integral_abs_le_of_bdd _ (Mf' * Mμ) (by positivity)
            (fun s => by
              rw [Real.norm_eq_abs]
              calc |deriv (fun x => f s x) (X.process s ω) * X.drift s ω|
                  ≤ |deriv (fun x => f s x) (X.process s ω)| * |X.drift s ω| := (abs_mul _ _).le
                _ ≤ Mf' * Mμ := mul_le_mul (hMf' s _) (hMμ s ω)
                    (abs_nonneg _) hMf'_nn) u T hu huT
        -- Sum bound: |Σ f'·∫μ| ≤ Mf'·Mμ·T via mesh bound
        have h_sum : |∑ i : Fin (n_k + 1),
            deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
            (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u),
              X.drift s ω ∂volume)| ≤ Mf' * Mμ * T := by
          have hN : (0 : ℝ) < ↑(n_k + 1) := Nat.cast_pos.mpr (Nat.succ_pos _)
          calc |∑ i : Fin (n_k + 1), _|
              ≤ ∑ i : Fin (n_k + 1), |deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
                  (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
                (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                    (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u),
                  X.drift s ω ∂volume)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin (n_k + 1), Mf' * Mμ * (T / ↑(n_k + 1)) :=
                Finset.sum_le_sum fun i _ => by
                  -- |f'| ≤ Mf', |∫μ| ≤ Mμ·mesh
                  have h_f' := hMf' (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                    (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω)
                  -- mesh bound on sub-interval length
                  have h_step : (↑(i : ℕ) : ℝ) * T / ↑(n_k + 1) ≤
                      (↑(i : ℕ) + 1) * T / ↑(n_k + 1) := by
                    apply div_le_div_of_nonneg_right _ hN.le
                    exact mul_le_mul_of_nonneg_right (by linarith) hT.le
                  have h_mesh_nn : 0 ≤ min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u -
                      min (↑(i : ℕ) * T / ↑(n_k + 1)) u :=
                    sub_nonneg.mpr (min_le_min_right u h_step)
                  have h_mesh_le : min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u -
                      min (↑(i : ℕ) * T / ↑(n_k + 1)) u ≤ T / ↑(n_k + 1) := by
                    have h1 := min_sub_min_le_sub h_step (c := u)
                    have h2 : (↑(i : ℕ) + 1) * T / ↑(n_k + 1) - ↑(i : ℕ) * T / ↑(n_k + 1) =
                      T / ↑(n_k + 1) := by ring
                    linarith
                  -- bound on integral: |∫ μ| ≤ Mμ * mesh
                  have h_int_mu : |∫ s in Set.Icc
                      (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                      (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u),
                      X.drift s ω ∂volume| ≤ Mμ * (T / ↑(n_k + 1)) := by
                    rw [← Real.norm_eq_abs]
                    calc ‖∫ s in Set.Icc _ _, X.drift s ω ∂volume‖
                        ≤ Mμ * (volume (Set.Icc
                          (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
                          (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u))).toReal :=
                          norm_setIntegral_le_of_norm_le_const
                            (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
                            (fun s _ => by rw [Real.norm_eq_abs]; exact hMμ s ω)
                      _ ≤ Mμ * (T / ↑(n_k + 1)) := by
                          rw [Real.volume_Icc, ENNReal.toReal_ofReal h_mesh_nn]
                          exact mul_le_mul_of_nonneg_left h_mesh_le hMμ_nn
                  calc |_ * _| ≤ |_| * |_| := (abs_mul _ _).le
                    _ ≤ Mf' * (Mμ * (T / ↑(n_k + 1))) :=
                        mul_le_mul h_f' h_int_mu (abs_nonneg _) hMf'_nn
                    _ = Mf' * Mμ * (T / ↑(n_k + 1)) := by ring
            _ = ↑(n_k + 1) * (Mf' * Mμ * (T / ↑(n_k + 1))) := by
                rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            _ = Mf' * Mμ * T := by field_simp
        linarith
      -- E3: QV weighted error |∫½f''σ² - Σ½f''ΔX²| ≤ ½Mf''·Mσ²·T + ½Mf''·Sk
      have hE3_abs : |E3| ≤ 1 / 2 * Mf'' * (Mσ ^ 2 * T + Sk_cap) := by
        -- Integral absolute value bound: |∫½f''σ²| ≤ ½Mf''·Mσ²·T
        have h_int_bnd : |∫ s in Set.Icc 0 u,
            (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2 ∂volume| ≤ 1 / 2 * Mf'' * Mσ ^ 2 * T := by
          rw [← Real.norm_eq_abs]
          exact integral_abs_le_of_bdd _ (1 / 2 * Mf'' * Mσ ^ 2) (by positivity)
            (fun s => by
              rw [Real.norm_eq_abs, abs_mul, abs_mul]
              have hab1 : |((1 : ℝ) / 2)| = 1 / 2 :=
                abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
              have hab2 : |(X.diffusion s ω) ^ 2| = (X.diffusion s ω) ^ 2 :=
                abs_of_nonneg (sq_nonneg (X.diffusion s ω))
              rw [hab1, hab2]
              have h1 := hMf'' s (X.process s ω)
              have h3 : (X.diffusion s ω) ^ 2 ≤ Mσ ^ 2 :=
                sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2
              nlinarith [abs_nonneg (deriv (deriv (fun x => f s x)) (X.process s ω))])
            u T hu huT
        -- Sum absolute value bound: |Σ½f''ΔX²| ≤ ½Mf''·Sk_cap
        have h_sum_bnd : |∑ i : Fin (n_k + 1),
            (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2| ≤
            1 / 2 * Mf'' * Sk_cap := by
          exact abs_sum_mul_le_of_abs_le_nonneg (s := Finset.univ)
            (c := fun i : Fin (n_k + 1) => (1 : ℝ) / 2 *
              deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
                (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω))
            (d := fun i : Fin (n_k + 1) =>
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2)
            (C := 1 / 2 * Mf'') (by positivity)
            (fun i _ => by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
              exact mul_le_mul_of_nonneg_left (hMf'' _ _) (by norm_num))
            (fun i _ => sq_nonneg _)
        -- Triangle: |E3| = |int - sum| ≤ |int| + |sum|
        have h_tri : |E3| ≤ |∫ s in Set.Icc 0 u,
            (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2 ∂volume| +
          |∑ i : Fin (n_k + 1),
            (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2| := by
          simp only [E3, ← Real.norm_eq_abs]
          exact norm_sub_le _ _
        linarith
      -- E4: Taylor remainder |Σ R_i| ≤ 2·Mf''·Sk_cap
      -- Uses c2_taylor_remainder_bound with oscillation bound 2·Mf''
      have hE4_abs : |E4| ≤ 2 * Mf'' * Sk_cap := by
        -- Triangle inequality on sum: |Σ a_i| ≤ Σ |a_i|
        have h_tri : |E4| ≤ ∑ i : Fin (n_k + 1),
            |f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
             f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
             deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
             (1 : ℝ) / 2 *
              deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
                (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2| := by
          simp only [E4]; exact Finset.abs_sum_le_sum_abs _ _
        -- Each |E4_i| ≤ 2·Mf''·ΔX_i² via c2_taylor_remainder_bound
        have h_each : ∀ i : Fin (n_k + 1),
            |f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω) -
             f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u)
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
             deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x)
              (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) -
             (1 : ℝ) / 2 *
              deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) x))
                (X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2| ≤
            2 * Mf'' *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2 := by
          intro i
          set t_i := min (↑(i : ℕ) * T / ↑(n_k + 1)) u
          set x_i := X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω
          set x_i1 := X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω
          set Δx := x_i1 - x_i with hΔx_def
          -- Oscillation bound: |f''(t_i, y) - f''(t_i, x_i)| ≤ 2·Mf'' for all y
          have h_osc : ∀ y ∈ Set.uIcc x_i (x_i + Δx),
              |deriv (deriv (fun x => f t_i x)) y -
               deriv (deriv (fun x => f t_i x)) x_i| ≤ 2 * Mf'' := by
            intro y _
            calc |deriv (deriv (fun x => f t_i x)) y -
                  deriv (deriv (fun x => f t_i x)) x_i|
                ≤ |deriv (deriv (fun x => f t_i x)) y| +
                  |deriv (deriv (fun x => f t_i x)) x_i| := by
                    simp only [← Real.norm_eq_abs]; exact norm_sub_le _ _
              _ ≤ Mf'' + Mf'' := add_le_add (hMf'' t_i y) (hMf'' t_i x_i)
              _ = 2 * Mf'' := by ring
          -- Apply c2_taylor_remainder_bound
          have h_taylor := c2_taylor_remainder_bound (hf_x t_i) x_i Δx
            (by positivity) h_osc
          -- Rewrite x_i + Δx = x_i1 in the Taylor bound
          have hx_eq : x_i + Δx = x_i1 := by rw [hΔx_def]; ring
          rw [hx_eq] at h_taylor
          exact h_taylor
        -- Sum the bounds: Σ |E4_i| ≤ 2Mf'' · Σ ΔX_i² = 2Mf'' · Sk_cap
        calc |E4| ≤ ∑ i : Fin (n_k + 1), _ := h_tri
          _ ≤ ∑ i : Fin (n_k + 1), (2 * Mf'' *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(n_k + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(n_k + 1)) u) ω) ^ 2) :=
            Finset.sum_le_sum fun i _ => h_each i
          _ = 2 * Mf'' * Sk_cap := by rw [← Finset.mul_sum]
      -- Combine: sq ≤ sq of bound, then arithmetic
      have hE1_sq : E1 ^ 2 ≤ (2 * Mft * T) ^ 2 :=
        sq_le_sq' (abs_le.mp hE1_abs).1 (abs_le.mp hE1_abs).2
      have hE2_sq : E2 ^ 2 ≤ (2 * Mf' * Mμ * T) ^ 2 :=
        sq_le_sq' (abs_le.mp hE2_abs).1 (abs_le.mp hE2_abs).2
      have hE3_sq : E3 ^ 2 ≤ (1 / 2 * Mf'' * (Mσ ^ 2 * T + Sk_cap)) ^ 2 :=
        sq_le_sq' (abs_le.mp hE3_abs).1 (abs_le.mp hE3_abs).2
      have hE4_sq : E4 ^ 2 ≤ (2 * Mf'' * Sk_cap) ^ 2 :=
        sq_le_sq' (abs_le.mp hE4_abs).1 (abs_le.mp hE4_abs).2
      -- (a+b)² ≤ 2a²+2b² for E3
      have hE3_expand : (1 / 2 * Mf'' * (Mσ ^ 2 * T + Sk_cap)) ^ 2 ≤
          1 / 2 * Mf'' ^ 2 * (Mσ ^ 2 * T) ^ 2 + 1 / 2 * Mf'' ^ 2 * Sk_cap ^ 2 := by
        nlinarith [sq_nonneg (Mσ ^ 2 * T - Sk_cap)]
      -- Non-negativity for Sk_cap
      have hSk_nn : 0 ≤ Sk_cap := Finset.sum_nonneg fun i _ => sq_nonneg _
      -- Final arithmetic
      nlinarith [sq_nonneg Mf'', sq_nonneg Sk_cap, sq_nonneg (Mft * T),
                  sq_nonneg (Mf' * Mμ * T), sq_nonneg (Mσ ^ 2 * T)]
    -- Step B: Sk_cap ≤ Sk_unc + bdy²
    have hSk_le : Sk_cap ≤ Sk_unc + bdy ^ 2 :=
      capped_qv_le_uncapped X T hT n_k u hu huT ω
    -- Step C: Sk_cap² ≤ 4(Sk_unc-QV)² + 4·QV² + 2·bdy⁴
    have hSk_sq : Sk_cap ^ 2 ≤ 4 * (Sk_unc - QV) ^ 2 +
        4 * QV ^ 2 + 2 * bdy ^ 4 := by
      have h_Sk_cap_nn : 0 ≤ Sk_cap := Finset.sum_nonneg fun i _ => sq_nonneg _
      -- Sk² ≤ (Sk_unc + bdy²)² ≤ 2·Sk_unc²+2·bdy⁴
      have h1 : Sk_cap ^ 2 ≤ 2 * Sk_unc ^ 2 + 2 * bdy ^ 4 := by
        nlinarith [hSk_le, h_Sk_cap_nn, sq_nonneg (Sk_unc - bdy ^ 2)]
      -- Sk_unc² ≤ 2(Sk_unc-QV)²+2QV²
      have h2 : Sk_unc ^ 2 ≤ 2 * (Sk_unc - QV) ^ 2 + 2 * QV ^ 2 := by
        nlinarith [sq_nonneg (Sk_unc - 2 * QV)]
      nlinarith
    -- Step D: 18Mf''²·Sk_cap² ≤ 4C_rand·(Sk-QV)² + 4C_rand·QV² + 2C_rand·bdy⁴
    -- since C_rand = 18Mf''² and 72Mf''² = 4*18Mf''², 36Mf''² = 2*18Mf''²
    have hD : C_det + 18 * Mf'' ^ 2 * Sk_cap ^ 2 ≤
        C_det + 4 * C_rand * (Sk_unc - QV) ^ 2 +
        4 * C_rand * QV ^ 2 + 2 * C_rand * bdy ^ 4 := by
      have hSk_expand := hSk_sq
      -- 18Mf''² = C_rand since C_rand = 4*(Mf''²/2+4Mf''²) = 18Mf''²
      have hC_rand_eq : 18 * Mf'' ^ 2 ≤ C_rand := by
        simp only [C_rand]; nlinarith [sq_nonneg Mf'']
      nlinarith [sq_nonneg (Sk_unc - QV), sq_nonneg QV, sq_nonneg bdy,
                  sq_nonneg (bdy ^ 2), hSk_expand, sq_nonneg Mf'']
    -- Combine: le_trans hω (le_trans hA hD)
    linarith [hω, hA, hD]
  -- (4) f_k → 0 a.e.: error² → 0 along the sub-subsequence
  · -- Step 1: Get error decomposition for ALL k simultaneously
    have h_decomp_all : ∀ᵐ ω ∂μ, ∀ k,
        (siIncrementApprox X f T (ns (ms k)) u ω - itoRemainder X f u ω)^2 ≤
        4 * ((∫ s in Set.Icc 0 u,
            deriv (fun t => f t (X.process s ω)) s ∂volume -
          ∑ i : Fin (ns (ms k) + 1),
            (f (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u) ω) -
             f (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u) ω)))^2 +
        (∫ s in Set.Icc 0 u,
            deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume -
          ∑ i : Fin (ns (ms k) + 1),
            deriv (fun x => f (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) x)
              (X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) *
            (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u)
                (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u),
              X.drift s ω ∂volume))^2 +
        (∫ s in Set.Icc 0 u,
            (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2 ∂volume -
          ∑ i : Fin (ns (ms k) + 1),
            (1 : ℝ) / 2 * deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) x))
              (X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) *
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) ^ 2)^2 +
        (∑ i : Fin (ns (ms k) + 1),
            (f (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u) ω) -
             f (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u)
              (X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) -
             deriv (fun x => f (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) x)
              (X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) -
             (1 : ℝ) / 2 *
              deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) x))
                (X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) *
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u) ω -
               X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) ^ 2))^2) := by
      rw [ae_all_iff]; intro k
      have hIcc_finite : volume (Set.Icc (0 : ℝ) u) ≠ ⊤ := by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      have hint_t_k : ∀ᵐ ω ∂μ, IntegrableOn
          (fun s => deriv (fun t => f t (X.process s ω)) s) (Set.Icc 0 u) volume := by
        filter_upwards [X.process_continuous] with ω hω
        exact (hf_t_cont.comp (continuous_id.prodMk hω)).continuousOn.integrableOn_compact
          isCompact_Icc
      have hint_d_k : ∀ᵐ ω ∂μ, IntegrableOn
          (fun s => deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
          (Set.Icc 0 u) volume := by
        filter_upwards [X.process_continuous] with ω hω
        exact Integrable.mono'
          (show IntegrableOn (fun _ => Mf' * Mμ) _ _ from
            integrableOn_const hIcc_finite)
          ((hf'_cont.comp (continuous_id.prodMk hω)).aestronglyMeasurable.restrict.mul
            (X.drift_time_integrable ω u hu).aestronglyMeasurable)
          (ae_of_all _ fun s => le_trans (norm_mul_le _ _) (by
            simp only [Real.norm_eq_abs]
            exact mul_le_mul (hMf' s _) (hMμ s ω) (abs_nonneg _) hMf'_nn))
      have hint_σ_k : ∀ᵐ ω ∂μ, IntegrableOn
          (fun s => (1 : ℝ) / 2 * deriv (deriv (fun x => f s x)) (X.process s ω) *
            (X.diffusion s ω) ^ 2) (Set.Icc 0 u) volume := by
        filter_upwards [X.process_continuous] with ω hω
        have h_half_f'' : Continuous (fun s =>
            (1:ℝ)/2 * deriv (deriv (fun x => f s x)) (X.process s ω)) :=
          continuous_const.mul (hf''_cont.comp (continuous_id.prodMk hω))
        exact Integrable.mono'
          (show IntegrableOn (fun _ => 1/2 * Mf'' * Mσ ^ 2) _ _ from
            integrableOn_const hIcc_finite)
          (h_half_f''.aestronglyMeasurable.restrict.mul
            (X.diffusion_sq_time_integrable ω u hu).aestronglyMeasurable)
          (ae_of_all _ fun s => by
            have h_abs1 : |1/2 * deriv (deriv (fun x => f s x)) (X.process s ω)| =
                1/2 * |deriv (deriv (fun x => f s x)) (X.process s ω)| := by
              rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
            have h_abs2 : |(X.diffusion s ω) ^ 2| = (X.diffusion s ω) ^ 2 :=
              abs_of_nonneg (sq_nonneg _)
            rw [Real.norm_eq_abs, abs_mul, h_abs1, h_abs2]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (hMf'' s _) (by norm_num))
              (sq_le_sq' (abs_le.mp (hMσ s ω)).1 (abs_le.mp (hMσ s ω)).2)
              (sq_nonneg _)
              (mul_nonneg (by norm_num) hMf''_nn))
      exact ito_error_decomposition X f hf_x T hT (ns (ms k)) u hu huT
        hint_t_k hint_d_k hint_σ_k
    -- Step 2: Squeeze: 0 ≤ error² ≤ 4*(E1²+E2²+E3²+E4²) → 0
    filter_upwards [h_decomp_all, h_capped_qv_ae', h_E3_ae_raw, X.process_continuous]
      with ω hdecomp hcqv h_e3 hcont
    apply squeeze_zero (fun k => sq_nonneg _) hdecomp
    -- Goal: Tendsto (fun k => 4*(E1²+E2²+E3²+E4²)) atTop (nhds 0)
    -- Decompose into 4 individual convergences using tendsto_four_sq_sum
    apply tendsto_four_sq_sum
    · -- E1 (time-Riemann error) → 0: ∫∂ₜf ds - Σ[f(τ_{i+1},X_{i+1}) - f(τᵢ,X_{i+1})] → 0
      -- By FTC: f(τᵢ₊₁,x) - f(τᵢ,x) = ∫_{τᵢ}^{τᵢ₊₁} ∂ₜf(s,x) ds
      -- By integral splitting + subtraction: E1 = Σ ∫_{Iᵢ} [∂ₜf(s,X(s)) - ∂ₜf(s,X(τᵢ₊₁))] ds
      -- Per-interval UC bound: |∂ₜf(s,X(s)) - ∂ₜf(s,X(τᵢ₊₁))| < η
      -- Sum bound: Σ η·Δτᵢ = η·u < ε
      rw [Metric.tendsto_atTop]; intro ε hε
      have hXω_uc : UniformContinuousOn (fun s => X.process s ω) (Set.Icc 0 u) :=
        isCompact_Icc.uniformContinuousOn_of_continuous
          (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
      obtain ⟨R, hR_pos, hR⟩ : ∃ R : ℝ, 0 < R ∧
          ∀ s ∈ Set.Icc (0 : ℝ) u, |X.process s ω| ≤ R := by
        obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := u)).image_of_continuousOn
          (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
          |>.isBounded.subset_closedBall 0
        exact ⟨max R₀ 1, by positivity, fun s hs => by
          have := hR₀ ⟨s, hs, rfl⟩
          rw [Metric.mem_closedBall, dist_zero_right] at this
          exact (Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _)⟩
      set K_e1 := Set.Icc (0 : ℝ) u ×ˢ Metric.closedBall (0 : ℝ) R
      have hK_cpt : IsCompact K_e1 := isCompact_Icc.prod (isCompact_closedBall 0 R)
      have hft_uc : UniformContinuousOn
          (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1) K_e1 :=
        hK_cpt.uniformContinuousOn_of_continuous hf_t_cont.continuousOn
      set η := ε / (u + 1) with hη_def
      have h_denom_pos : 0 < u + 1 := by linarith
      have hη_pos : 0 < η := div_pos hε h_denom_pos
      obtain ⟨δ_f, hδ_f_pos, hδ_f⟩ := (Metric.uniformContinuousOn_iff.mp hft_uc) η hη_pos
      obtain ⟨δ_X, hδ_X_pos, hδ_X⟩ :=
        (Metric.uniformContinuousOn_iff.mp hXω_uc) δ_f hδ_f_pos
      obtain ⟨N_m, hN_m⟩ := (Metric.tendsto_atTop.mp h_width) δ_X hδ_X_pos
      refine ⟨N_m, fun k hk => ?_⟩
      rw [Real.dist_eq, sub_zero]
      set nk := ns (ms k) + 1 with hnk_def
      have hnk_pos : (0 : ℝ) < ↑nk := Nat.cast_pos.mpr (Nat.succ_pos _)
      have hmesh : T / ↑nk < δ_X := by
        have := hN_m k hk
        rwa [Real.dist_eq, sub_zero,
          abs_of_nonneg (div_nonneg hT.le (Nat.cast_nonneg _))] at this
      -- |E1_k| ≤ η·u < ε via FTC + integral splitting + UC + telescoping
      -- Uses ftc_set_integral + integral_eq_sum_capped_intervals +
      -- norm_setIntegral_le_of_norm_le_const + sum_capped_partition_widths.
      -- Per-interval: for s ∈ [τᵢ, τᵢ₊₁], |s - τᵢ₊₁| ≤ T/nk < δ_X,
      -- so |X(s) - X(τᵢ₊₁)| < δ_f by UC of X.
      -- Then dist((s,X(s)), (s,X(τᵢ₊₁))) = |X(s)-X(τᵢ₊₁)| < δ_f,
      -- so |∂ₜf(s,X(s)) - ∂ₜf(s,X(τᵢ₊₁))| < η by UC of ∂ₜf on K.
      calc |∫ s in Set.Icc 0 u,
            deriv (fun t => f t (X.process s ω)) s ∂volume -
          ∑ i : Fin nk,
            (f (min ((↑(i : ℕ) + 1) * T / ↑nk) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) -
             f (min (↑(i : ℕ) * T / ↑nk) u)
              (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω))|
          ≤ η * u := by
            -- Integrability of s ↦ ∂ₜf(s, X(s,ω)) on [0,u]
            have hg_int : IntegrableOn
                (fun s => deriv (fun t => f t (X.process s ω)) s)
                (Set.Icc 0 u) volume :=
              (hf_t_cont.comp (continuous_id.prodMk hcont)).continuousOn.integrableOn_compact
                isCompact_Icc
            -- Apply partition error bound with C = η, n = ns (ms k)
            apply partition_error_bound hg_int hη_pos.le hT hu huT
            -- Per-interval bound: |∫_{Iᵢ} ∂ₜf(s,X(s)) - c(i)| ≤ η·Δτ
            intro i
            -- Interval monotonicity
            have hi_le : (↑(i : ℕ) : ℝ) * T / ↑nk ≤
                (↑(i : ℕ) + 1) * T / ↑nk :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by linarith) hT.le) hnk_pos.le
            have hτ_le : min (↑(i : ℕ) * T / ↑nk) u ≤
                min ((↑(i : ℕ) + 1) * T / ↑nk) u :=
              min_le_min hi_le le_rfl
            -- Bounds
            have hτ_lo_nn : 0 ≤ min (↑(i : ℕ) * T / ↑nk) u :=
              le_min (by positivity) hu
            have hτ_hi_le_u : min ((↑(i : ℕ) + 1) * T / ↑nk) u ≤ u :=
              min_le_right _ _
            -- Width ≤ mesh
            have hwidth : min ((↑(i : ℕ) + 1) * T / ↑nk) u -
                min (↑(i : ℕ) * T / ↑nk) u ≤ T / ↑nk :=
              (min_sub_min_le_sub hi_le).trans (le_of_eq (by ring))
            -- [τ_lo, τ_hi] ⊆ [0, u]
            have hτ_sub : Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ⊆ Set.Icc 0 u :=
              Set.Icc_subset_Icc hτ_lo_nn hτ_hi_le_u
            -- FTC: f(τ_{i+1}, x) - f(τ_i, x) = ∫ ∂ₜf(s, x) ds
            have hftc :
                f (min ((↑(i : ℕ) + 1) * T / ↑nk) u)
                  (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) -
                f (min (↑(i : ℕ) * T / ↑nk) u)
                  (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) =
                ∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                    (min ((↑(i : ℕ) + 1) * T / ↑nk) u),
                  deriv (fun t => f t
                    (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω)) s
                  ∂volume :=
              ftc_set_integral
                (hf_t (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω))
                (hf_t_cont.comp (continuous_id.prodMk continuous_const))
                hτ_le
            rw [hftc]
            -- ∫g - ∫h = ∫(g-h)
            have hg_sub : IntegrableOn
                (fun s => deriv (fun t => f t (X.process s ω)) s)
                (Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                  (min ((↑(i : ℕ) + 1) * T / ↑nk) u)) volume :=
              hg_int.mono_set hτ_sub
            have hh_sub : IntegrableOn
                (fun s => deriv (fun t => f t
                  (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω)) s)
                (Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                  (min ((↑(i : ℕ) + 1) * T / ↑nk) u)) volume :=
              (hf_t_cont.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact
                isCompact_Icc
            rw [(MeasureTheory.integral_sub hg_sub hh_sub).symm]
            -- Pointwise bound: |∂ₜf(s,X(s)) - ∂ₜf(s,X(τ_hi))| ≤ η
            have hpw : ∀ s ∈ Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                (min ((↑(i : ℕ) + 1) * T / ↑nk) u),
                ‖deriv (fun t => f t (X.process s ω)) s -
                 deriv (fun t => f t
                  (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω)) s‖
                ≤ η := by
              intro s hs
              rw [Real.norm_eq_abs]
              have hs_mem : s ∈ Set.Icc 0 u := hτ_sub hs
              have hτ_mem : min ((↑(i : ℕ) + 1) * T / ↑nk) u ∈
                  Set.Icc (0 : ℝ) u :=
                ⟨hτ_lo_nn.trans hτ_le, hτ_hi_le_u⟩
              -- |s - τ_hi| < δ_X via mesh bound
              have hdist_s : dist s
                  (min ((↑(i : ℕ) + 1) * T / ↑nk) u) < δ_X := by
                rw [Real.dist_eq, abs_sub_comm,
                    abs_of_nonneg (by linarith [hs.2])]
                linarith [hs.1, hwidth, hmesh]
              -- UC of X gives |X(s) - X(τ_hi)| < δ_f
              have hdist_X : dist (X.process s ω)
                  (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) <
                  δ_f :=
                hδ_X s hs_mem _ hτ_mem hdist_s
              -- K membership
              have h1 : (s, X.process s ω) ∈ K_e1 :=
                ⟨hs_mem, Metric.mem_closedBall.mpr (by
                  rw [dist_zero_right, Real.norm_eq_abs]
                  exact hR s hs_mem)⟩
              have h2 : (s, X.process
                  (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) ∈ K_e1 :=
                ⟨hs_mem, Metric.mem_closedBall.mpr (by
                  rw [dist_zero_right, Real.norm_eq_abs]
                  exact hR _ hτ_mem)⟩
              -- Product distance = X distance (same first component)
              have hdist_prod : dist (s, X.process s ω)
                  (s, X.process
                    (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) < δ_f := by
                rw [dist_prod_same_left]; exact hdist_X
              -- UC of ∂ₜf gives the bound
              have huc := hδ_f _ h1 _ h2 hdist_prod
              rw [Real.dist_eq] at huc; exact le_of_lt huc
            -- |∫(g-h)| ≤ η · Δτ
            calc |∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                    (min ((↑(i : ℕ) + 1) * T / ↑nk) u),
                  (deriv (fun t => f t (X.process s ω)) s -
                   deriv (fun t => f t
                    (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω)) s)
                  ∂volume|
                ≤ η * volume.real (Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                    (min ((↑(i : ℕ) + 1) * T / ↑nk) u)) := by
                  rw [← Real.norm_eq_abs]
                  exact norm_setIntegral_le_of_norm_le_const
                    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hpw
              _ = η * (min ((↑(i : ℕ) + 1) * T / ↑nk) u -
                  min (↑(i : ℕ) * T / ↑nk) u) := by
                  rw [Measure.real, Real.volume_Icc,
                      ENNReal.toReal_ofReal (sub_nonneg.mpr hτ_le)]
        _ < ε := by
            rw [hη_def]
            calc ε / (u + 1) * u = ε * (u / (u + 1)) := by ring
              _ < ε * 1 := by
                  apply mul_lt_mul_of_pos_left _ hε
                  rw [div_lt_one h_denom_pos]; linarith
              _ = ε := mul_one ε
    · -- E2 (drift-Riemann error) → 0: ∫f'μ ds - Σ f'ᵢ·∫μ dsᵢ → 0
      -- By integral splitting: ∫₀ᵘ f'·μ = Σ ∫_{Iᵢ} f'·μ
      -- E2 = Σ [∫_{Iᵢ} f'·μ - f'ᵢ·∫_{Iᵢ} μ] = Σ ∫_{Iᵢ} (f'-f'ᵢ)·μ
      -- Per-interval: |f'(s,X(s)) - f'(τᵢ,X(τᵢ))| < η (UC of f', UC of X)
      -- Sum bound: Σ η·Mμ·Δτᵢ = η·Mμ·u < ε
      rw [Metric.tendsto_atTop]; intro ε hε
      have hXω_uc : UniformContinuousOn (fun s => X.process s ω) (Set.Icc 0 u) :=
        isCompact_Icc.uniformContinuousOn_of_continuous
          (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
      obtain ⟨R, hR_pos, hR⟩ : ∃ R : ℝ, 0 < R ∧
          ∀ s ∈ Set.Icc (0 : ℝ) u, |X.process s ω| ≤ R := by
        obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := u)).image_of_continuousOn
          (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
          |>.isBounded.subset_closedBall 0
        exact ⟨max R₀ 1, by positivity, fun s hs => by
          have := hR₀ ⟨s, hs, rfl⟩
          rw [Metric.mem_closedBall, dist_zero_right] at this
          exact (Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _)⟩
      set K_e2 := Set.Icc (0 : ℝ) u ×ˢ Metric.closedBall (0 : ℝ) R
      have hK_cpt : IsCompact K_e2 := isCompact_Icc.prod (isCompact_closedBall 0 R)
      have hf'_uc_K : UniformContinuousOn
          (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2) K_e2 :=
        hK_cpt.uniformContinuousOn_of_continuous hf'_cont.continuousOn
      set η := ε / (Mμ * u + 1) with hη_def
      have h_denom_pos : 0 < Mμ * u + 1 := by linarith [mul_nonneg hMμ_nn hu]
      have hη_pos : 0 < η := div_pos hε h_denom_pos
      obtain ⟨δ_f, hδ_f_pos, hδ_f⟩ := (Metric.uniformContinuousOn_iff.mp hf'_uc_K) η hη_pos
      obtain ⟨δ_X, hδ_X_pos, hδ_X⟩ :=
        (Metric.uniformContinuousOn_iff.mp hXω_uc) (δ_f / 2) (by linarith)
      obtain ⟨N_m, hN_m⟩ := (Metric.tendsto_atTop.mp h_width)
        (min (δ_f / 2) δ_X) (by positivity)
      refine ⟨N_m, fun k hk => ?_⟩
      rw [Real.dist_eq, sub_zero]
      set nk := ns (ms k) + 1 with hnk_def
      have hnk_pos : (0 : ℝ) < ↑nk := Nat.cast_pos.mpr (Nat.succ_pos _)
      have hmesh : T / ↑nk < min (δ_f / 2) δ_X := by
        have := hN_m k hk
        rwa [Real.dist_eq, sub_zero,
          abs_of_nonneg (div_nonneg hT.le (Nat.cast_nonneg _))] at this
      -- |E2_k| ≤ η·Mμ·u < ε via integral splitting + UC + bounded drift + telescoping
      -- Uses integral_eq_sum_capped_intervals + integral linearity +
      -- norm_setIntegral_le_of_norm_le_const + sum_capped_partition_widths.
      -- Per-interval: for s ∈ [τᵢ, τᵢ₊₁]:
      --   |s - τᵢ| ≤ T/nk < δ_f/2, |X(s) - X(τᵢ)| < δ_f/2 (UC of X)
      --   dist((s,X(s)), (τᵢ,X(τᵢ))) = max(|s-τᵢ|, |X(s)-X(τᵢ)|) < δ_f
      --   |f'(s,X(s)) - f'(τᵢ,X(τᵢ))| < η by UC of f' on K
      --   |∫_{Iᵢ} (f'-f'ᵢ)·μ| ≤ η·Mμ·Δτᵢ
      calc |∫ s in Set.Icc 0 u,
            deriv (fun x => f s x) (X.process s ω) * X.drift s ω ∂volume -
          ∑ i : Fin nk,
            deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x)
              (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) *
            (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                (min ((↑(i : ℕ) + 1) * T / ↑nk) u),
              X.drift s ω ∂volume)|
          ≤ η * Mμ * u := by
            -- Integrability of s ↦ f'(s,X(s))·μ(s) on [0,u]
            have hIcc_fin : volume (Set.Icc (0 : ℝ) u) ≠ ⊤ := by
              rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
            have hg_int : IntegrableOn
                (fun s => deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
                (Set.Icc 0 u) volume :=
              Integrable.mono'
                (show IntegrableOn (fun _ => Mf' * Mμ) _ _ from
                  integrableOn_const hIcc_fin)
                ((hf'_cont.comp (continuous_id.prodMk hcont)).aestronglyMeasurable.restrict.mul
                  (X.drift_time_integrable ω u hu).aestronglyMeasurable)
                (ae_of_all _ fun s => le_trans (norm_mul_le _ _) (by
                  simp only [Real.norm_eq_abs]
                  exact mul_le_mul (hMf' s _) (hMμ s ω) (abs_nonneg _) hMf'_nn))
            -- Apply partition error bound with C = η * Mμ
            apply partition_error_bound hg_int (mul_nonneg hη_pos.le hMμ_nn) hT hu huT
            -- Per-interval bound
            intro i
            -- Interval setup (same as E1)
            have hi_le : (↑(i : ℕ) : ℝ) * T / ↑nk ≤
                (↑(i : ℕ) + 1) * T / ↑nk :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by linarith) hT.le) hnk_pos.le
            have hτ_le : min (↑(i : ℕ) * T / ↑nk) u ≤
                min ((↑(i : ℕ) + 1) * T / ↑nk) u :=
              min_le_min hi_le le_rfl
            have hτ_lo_nn : 0 ≤ min (↑(i : ℕ) * T / ↑nk) u :=
              le_min (by positivity) hu
            have hτ_hi_le_u : min ((↑(i : ℕ) + 1) * T / ↑nk) u ≤ u :=
              min_le_right _ _
            have hwidth : min ((↑(i : ℕ) + 1) * T / ↑nk) u -
                min (↑(i : ℕ) * T / ↑nk) u ≤ T / ↑nk :=
              (min_sub_min_le_sub hi_le).trans (le_of_eq (by ring))
            have hτ_sub : Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ⊆ Set.Icc 0 u :=
              Set.Icc_subset_Icc hτ_lo_nn hτ_hi_le_u
            -- Abbreviate τ_lo = min(i*T/nk, u) for the evaluation point
            -- Note: E2 evaluates f' at τ_lo (not τ_hi as in E1)
            set f'_val := deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x)
              (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω)
            -- Factor constant: f'ᵢ * ∫μ = ∫ f'ᵢ·μ
            rw [show f'_val * (∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                (min ((↑(i : ℕ) + 1) * T / ↑nk) u), X.drift s ω ∂volume) =
                ∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                  (min ((↑(i : ℕ) + 1) * T / ↑nk) u),
                f'_val * X.drift s ω ∂volume from
              (integral_const_mul f'_val _).symm]
            -- Integrability on sub-interval
            have hg_sub : IntegrableOn
                (fun s => deriv (fun x => f s x) (X.process s ω) * X.drift s ω)
                (Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                  (min ((↑(i : ℕ) + 1) * T / ↑nk) u)) volume :=
              hg_int.mono_set hτ_sub
            have hh_sub : IntegrableOn
                (fun s => f'_val * X.drift s ω)
                (Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                  (min ((↑(i : ℕ) + 1) * T / ↑nk) u)) volume :=
              (X.drift_time_integrable ω u hu).mono_set hτ_sub |>.const_mul f'_val
            -- ∫g - ∫h = ∫(g-h)
            rw [(MeasureTheory.integral_sub hg_sub hh_sub).symm]
            -- Pointwise bound: ‖g(s) - h(s)‖ ≤ η*Mμ
            have hpw : ∀ s ∈ Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                (min ((↑(i : ℕ) + 1) * T / ↑nk) u),
                ‖deriv (fun x => f s x) (X.process s ω) * X.drift s ω -
                 f'_val * X.drift s ω‖ ≤ η * Mμ := by
              intro s hs
              -- g(s) - h(s) = (f'(s,X(s)) - f'(τ,X(τ))) * μ(s)
              rw [show deriv (fun x => f s x) (X.process s ω) * X.drift s ω -
                  f'_val * X.drift s ω =
                  (deriv (fun x => f s x) (X.process s ω) - f'_val) *
                  X.drift s ω from by ring]
              rw [Real.norm_eq_abs, abs_mul]
              -- |f'(s,X(s)) - f'(τ,X(τ))| < η and |μ(s)| ≤ Mμ
              have hs_mem : s ∈ Set.Icc 0 u := hτ_sub hs
              have hτ_mem : min (↑(i : ℕ) * T / ↑nk) u ∈ Set.Icc (0 : ℝ) u :=
                ⟨hτ_lo_nn, hτ_le.trans hτ_hi_le_u⟩
              -- Time distance: |s - τᵢ| < δ_f/2
              have hdist_time : dist s (min (↑(i : ℕ) * T / ↑nk) u) <
                  δ_f / 2 := by
                rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
                linarith [hs.2, hwidth, lt_min_iff.mp hmesh]
              -- Space distance: |X(s) - X(τᵢ)| < δ_f/2
              have hdist_X : dist (X.process s ω)
                  (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) < δ_f / 2 := by
                apply hδ_X s hs_mem _ hτ_mem
                rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
                linarith [hs.2, hwidth, (lt_min_iff.mp hmesh).2]
              -- K membership
              have h1 : (s, X.process s ω) ∈ K_e2 :=
                ⟨hs_mem, Metric.mem_closedBall.mpr (by
                  rw [dist_zero_right, Real.norm_eq_abs]; exact hR s hs_mem)⟩
              have h2 : (min (↑(i : ℕ) * T / ↑nk) u,
                  X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) ∈ K_e2 :=
                ⟨hτ_mem, Metric.mem_closedBall.mpr (by
                  rw [dist_zero_right, Real.norm_eq_abs]; exact hR _ hτ_mem)⟩
              -- Product distance < δ_f (both components < δ_f/2)
              have hdist_prod : dist (s, X.process s ω)
                  (min (↑(i : ℕ) * T / ↑nk) u,
                   X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) < δ_f := by
                simp only [Prod.dist_eq]
                exact max_lt (by linarith [hdist_time]) (by linarith [hdist_X])
              -- UC of f' gives |f'(s,X(s)) - f'(τ,X(τ))| < η
              have huc := hδ_f _ h1 _ h2 hdist_prod
              rw [Real.dist_eq] at huc
              -- Final: |f'-f'ᵢ| * |μ| ≤ η * Mμ
              exact mul_le_mul (le_of_lt huc) (hMμ s ω) (abs_nonneg _) hη_pos.le
            -- |∫(g-h)| ≤ (η*Mμ) · Δτ
            calc |∫ s in Set.Icc (min (↑(i : ℕ) * T / ↑nk) u)
                    (min ((↑(i : ℕ) + 1) * T / ↑nk) u),
                  (deriv (fun x => f s x) (X.process s ω) * X.drift s ω -
                   f'_val * X.drift s ω) ∂volume|
                ≤ (η * Mμ) * volume.real (Set.Icc
                    (min (↑(i : ℕ) * T / ↑nk) u)
                    (min ((↑(i : ℕ) + 1) * T / ↑nk) u)) := by
                  rw [← Real.norm_eq_abs]
                  exact norm_setIntegral_le_of_norm_le_const
                    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hpw
              _ = (η * Mμ) * (min ((↑(i : ℕ) + 1) * T / ↑nk) u -
                  min (↑(i : ℕ) * T / ↑nk) u) := by
                  rw [Measure.real, Real.volume_Icc,
                      ENNReal.toReal_ofReal (sub_nonneg.mpr hτ_le)]
        _ < ε := by
            rw [hη_def]
            calc ε / (Mμ * u + 1) * Mμ * u
                = ε * (Mμ * u / (Mμ * u + 1)) := by ring
              _ < ε * 1 := by
                  apply mul_lt_mul_of_pos_left _ hε
                  rw [div_lt_one h_denom_pos]; linarith
              _ = ε := mul_one ε
    · -- E3 (weighted QV error) → 0: ∫½f''σ² ds - Σ ½f''ᵢ·(ΔXᵢ)² → 0
      -- This was proved via L² convergence + subsequence extraction (ms₃).
      -- h_e3 provides E3 → 0 a.e. for this ω from the ms₃ extraction.
      exact h_e3
    · -- E4 (Taylor remainder) → 0: Σ Rᵢ → 0
      -- Follows taylor_remainders_ae_tendsto_zero pattern with capped partitions
      rw [Metric.tendsto_atTop]; intro ε hε
      -- Path UC on [0,u]
      have hXω_uc : UniformContinuousOn (fun s => X.process s ω) (Set.Icc 0 u) :=
        isCompact_Icc.uniformContinuousOn_of_continuous
          (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
      -- Path bounded on [0,u]
      obtain ⟨R, hR_pos, hR⟩ : ∃ R : ℝ, 0 < R ∧
          ∀ s ∈ Set.Icc (0 : ℝ) u, |X.process s ω| ≤ R := by
        obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := u)).image_of_continuousOn
          (hcont.continuousOn.mono (Set.Icc_subset_Icc_right huT))
          |>.isBounded.subset_closedBall 0
        exact ⟨max R₀ 1, by positivity, fun s hs => by
          have := hR₀ ⟨s, hs, rfl⟩
          rw [Metric.mem_closedBall, dist_zero_right] at this
          exact (Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _)⟩
      -- Compact K, f'' UC
      set K_e4 := Set.Icc (0 : ℝ) u ×ˢ Metric.closedBall (0 : ℝ) (R + 1)
      have hK_cpt : IsCompact K_e4 := isCompact_Icc.prod (isCompact_closedBall 0 (R + 1))
      set QV_ω := X.quadraticVariation u ω
      have hQV_nn := X.quadraticVariation_nonneg u ω
      have hf''_uc : UniformContinuousOn
          (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2) K_e4 :=
        hK_cpt.uniformContinuousOn_of_continuous hf''_cont.continuousOn
      -- QV convergence → S_k eventually bounded by QV + 1
      obtain ⟨N_qv, hN_qv⟩ := (Metric.tendsto_atTop.mp hcqv) 1 one_pos
      have hS_bdd : ∀ k ≥ N_qv, ∑ i : Fin (ns (ms k) + 1),
          (X.process (min ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) u) ω) ^ 2 ≤
          QV_ω + 1 := by
        intro k hk; have h := hN_qv k hk
        rw [Real.dist_eq] at h; have := (abs_lt.mp h).2; linarith
      -- Choose η = ε / (QV + 2), get δ_f from f'' UC, δ_X from path UC
      set η := ε / (QV_ω + 2) with hη_def
      have hη_pos : 0 < η := div_pos hε (by linarith)
      obtain ⟨δ_f, hδ_f_pos, hδ_f⟩ := (Metric.uniformContinuousOn_iff.mp hf''_uc) η hη_pos
      have hδ_pos : 0 < min δ_f 1 := lt_min hδ_f_pos one_pos
      obtain ⟨δ_X, hδ_X_pos, hδ_X⟩ :=
        (Metric.uniformContinuousOn_iff.mp hXω_uc) (min δ_f 1) hδ_pos
      -- Get N from mesh → 0
      obtain ⟨N_m, hN_m⟩ := (Metric.tendsto_atTop.mp h_width) δ_X hδ_X_pos
      -- Main bound for k ≥ max(N_qv, N_m)
      refine ⟨max N_qv N_m, fun k hk => ?_⟩
      rw [Real.dist_eq, sub_zero]
      set nk := ns (ms k) + 1 with hnk_def
      have hnk_pos : (0 : ℝ) < ↑nk := Nat.cast_pos.mpr (Nat.succ_pos _)
      -- Mesh bound: T / nk < δ_X
      have hmesh : T / ↑nk < δ_X := by
        have := hN_m k (le_of_max_le_right hk)
        rwa [Real.dist_eq, sub_zero,
          abs_of_nonneg (div_nonneg hT.le (Nat.cast_nonneg _))] at this
      -- All capped increments |ΔXᵢ| < min(δ_f, 1)
      have h_incr : ∀ i : Fin nk,
          |X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
           X.process (min (↑(i : ℕ) * T / ↑nk) u) ω| < min δ_f 1 := by
        intro i
        have htᵢ : min (↑(i : ℕ) * T / ↑nk) u ∈ Set.Icc (0 : ℝ) u :=
          ⟨le_min (by positivity) hu, min_le_right _ _⟩
        have hti1 : min ((↑(i : ℕ) + 1) * T / ↑nk) u ∈ Set.Icc (0 : ℝ) u :=
          ⟨le_min (by positivity) hu, min_le_right _ _⟩
        have h_ab : ↑(i : ℕ) * T / ↑nk ≤ (↑(i : ℕ) + 1) * T / ↑nk :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hT.le)
            (le_of_lt hnk_pos)
        have h_nn : 0 ≤ min ((↑(i : ℕ) + 1) * T / ↑nk) u -
            min (↑(i : ℕ) * T / ↑nk) u :=
          sub_nonneg.mpr (min_le_min_right u h_ab)
        have hdist : dist (min (↑(i : ℕ) * T / ↑nk) u)
            (min ((↑(i : ℕ) + 1) * T / ↑nk) u) < δ_X := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg h_nn]
          calc min ((↑(i : ℕ) + 1) * T / ↑nk) u - min (↑(i : ℕ) * T / ↑nk) u
              ≤ (↑(i : ℕ) + 1) * T / ↑nk - ↑(i : ℕ) * T / ↑nk :=
                min_sub_min_le_sub h_ab
            _ = T / ↑nk := by ring
            _ < δ_X := hmesh
        have := hδ_X _ htᵢ _ hti1 hdist
        rwa [Real.dist_eq, abs_sub_comm] at this
      -- Per-term Taylor bound: |Rᵢ| ≤ η · (ΔXᵢ)²
      have h_per_term : ∀ i : Fin nk,
          |f (min (↑(i : ℕ) * T / ↑nk) u)
             (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) -
           f (min (↑(i : ℕ) * T / ↑nk) u)
             (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) -
           deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x)
             (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) *
             (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
              X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) -
           (1 : ℝ) / 2 *
             deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x))
               (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) *
             (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
              X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) ^ 2|
          ≤ η * (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
                 X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) ^ 2 := by
        intro i
        set tᵢ := min (↑(i : ℕ) * T / ↑nk) u
        set xᵢ := X.process tᵢ ω
        set hᵢ := X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω - xᵢ
        have hg : ContDiff ℝ 2 (fun x => f tᵢ x) := hf_x tᵢ
        have hform : f tᵢ (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) =
            (fun x => f tᵢ x) (xᵢ + hᵢ) := by simp [hᵢ, xᵢ]
        rw [hform]
        apply le_trans (c2_taylor_remainder_bound hg xᵢ hᵢ (le_of_lt hη_pos) ?_)
        · exact le_rfl
        -- Bound oscillation of f''(tᵢ, ·) by η on uIcc(xᵢ, xᵢ + hᵢ)
        intro y hy
        have hy_near := abs_sub_le_of_mem_uIcc hy
        have hhi_small := h_incr i
        have hy_dist : |y - xᵢ| < min δ_f 1 := lt_of_le_of_lt hy_near hhi_small
        -- tᵢ ∈ [0, u]
        have htᵢ_mem : tᵢ ∈ Set.Icc (0 : ℝ) u :=
          ⟨le_min (by positivity) hu, min_le_right _ _⟩
        -- xᵢ bounded, y bounded, both in K_e4
        have hxᵢ_bdd : |xᵢ| ≤ R := hR tᵢ htᵢ_mem
        have hy_bdd : |y| ≤ R + 1 := by
          have h1 : |y| ≤ |y - xᵢ| + |xᵢ| := by linarith [abs_sub_abs_le_abs_sub y xᵢ]
          have h2 : |y - xᵢ| < 1 := lt_of_lt_of_le hy_dist (min_le_right δ_f 1)
          linarith
        have hxᵢ_K : (tᵢ, xᵢ) ∈ K_e4 :=
          ⟨htᵢ_mem, Metric.mem_closedBall.mpr (by
            rw [dist_zero_right, Real.norm_eq_abs]; linarith)⟩
        have hy_K : (tᵢ, y) ∈ K_e4 :=
          ⟨htᵢ_mem, Metric.mem_closedBall.mpr (by
            rw [dist_zero_right, Real.norm_eq_abs]; exact hy_bdd)⟩
        -- dist((tᵢ,y), (tᵢ,xᵢ)) < δ_f
        have hdist_pair : dist (tᵢ, y) (tᵢ, xᵢ) < δ_f := by
          calc dist (tᵢ, y) (tᵢ, xᵢ)
              = max (dist tᵢ tᵢ) (dist y xᵢ) := Prod.dist_eq
            _ = max 0 (dist y xᵢ) := by rw [dist_self]
            _ = dist y xᵢ := max_eq_right dist_nonneg
            _ < min δ_f 1 := by rwa [Real.dist_eq]
            _ ≤ δ_f := min_le_left _ _
        have h_uc := hδ_f (tᵢ, y) hy_K (tᵢ, xᵢ) hxᵢ_K hdist_pair
        rw [Real.dist_eq] at h_uc
        simp only [] at h_uc
        exact le_of_lt h_uc
      -- Triangle inequality: |Σ Rᵢ| ≤ Σ |Rᵢ| ≤ η · Σ(ΔXᵢ)² ≤ η · (QV+1) < ε
      calc |∑ i : Fin nk,
            (f (min (↑(i : ℕ) * T / ↑nk) u)
               (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) -
             f (min (↑(i : ℕ) * T / ↑nk) u)
               (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) -
             deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x)
               (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) *
               (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
                X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) -
             (1 : ℝ) / 2 *
               deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x))
                 (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) *
               (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
                X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) ^ 2)|
          ≤ ∑ i : Fin nk,
            |f (min (↑(i : ℕ) * T / ↑nk) u)
               (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω) -
             f (min (↑(i : ℕ) * T / ↑nk) u)
               (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) -
             deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x)
               (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) *
               (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
                X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) -
             (1 : ℝ) / 2 *
               deriv (deriv (fun x => f (min (↑(i : ℕ) * T / ↑nk) u) x))
                 (X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) *
               (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
                X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) ^ 2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin nk,
            η * (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
                 X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) ^ 2 :=
            Finset.sum_le_sum (fun i _ => h_per_term i)
        _ = η * ∑ i : Fin nk,
            (X.process (min ((↑(i : ℕ) + 1) * T / ↑nk) u) ω -
             X.process (min (↑(i : ℕ) * T / ↑nk) u) ω) ^ 2 :=
            (Finset.mul_sum ..).symm
        _ ≤ η * (QV_ω + 1) := by
            exact mul_le_mul_of_nonneg_left
              (hS_bdd k (le_of_max_le_left hk)) (le_of_lt hη_pos)
        _ < ε := by
            rw [hη_def, div_mul_eq_mul_div]
            have hqv2 : (0 : ℝ) < QV_ω + 2 := by linarith
            rw [div_lt_iff₀ hqv2]
            nlinarith
  -- (5) g_k → G a.e.
  · filter_upwards [h_qv_ae, X.process_continuous] with ω hω hω_cont
    -- Term 1: (Sk - QV)² → 0
    have h_qv_sq : Filter.Tendsto (fun k =>
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2)
        atTop (nhds 0) := by
      have hc : Filter.Tendsto (fun _ : ℕ => X.quadraticVariation T ω) atTop
          (nhds (X.quadraticVariation T ω)) := tendsto_const_nhds
      have h := (hω.sub hc).pow 2
      simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0)] at h; exact h
    -- Term 2: boundary⁴ → 0 (partition point → u, X continuous)
    have h_bdy : Filter.Tendsto (fun k =>
        (X.process u ω - X.process (bdy_pt k) ω) ^ 4) atTop (nhds 0) := by
      have h_xu := hω_cont.continuousAt.tendsto.comp h_bdy_conv
      have h_sub := (tendsto_const_nhds (x := X.process u ω)).sub h_xu
      rw [sub_self] at h_sub
      have := h_sub.pow 4
      rwa [zero_pow (by norm_num : 4 ≠ 0)] at this
    -- Build tendsto matching left-assoc structure: C_det + 4C*(Sk-QV)² + 4C*QV² + 2C*bdy⁴
    have h1 := h_qv_sq.const_mul (4 * C_rand)
    rw [mul_zero] at h1
    -- h1: Tendsto (fun k => 4*C_rand*(Sk-QV)²) → 0
    have h2 := h1.const_add C_det
    rw [add_zero] at h2
    -- h2: Tendsto (fun k => C_det + 4*C_rand*(Sk-QV)²) → C_det
    have h3 := h2.add (tendsto_const_nhds
      (x := 4 * C_rand * (X.quadraticVariation T ω) ^ 2))
    -- h3: Tendsto (fun k => C_det + 4*C_rand*(Sk-QV)² + 4*C_rand*QV²) → C_det + 4*C_rand*QV²
    have h4 := h_bdy.const_mul (2 * C_rand)
    rw [mul_zero] at h4
    -- h4: Tendsto (fun k => 2*C_rand*bdy⁴) → 0
    have h5 := h3.add h4
    rw [add_zero] at h5
    -- h5: Tendsto g_k → G  (left-assoc matches goal)
    exact h5
  -- (5) f_k integrable
  · intro k
    exact si_increment_diff_sq_integrable X f hf_x ⟨Mf', hMf'⟩ T hT.le (ns (ms k)) u hu
      hrem_int hrem_sq_int
  -- (6) g_k integrable
  · intro k
    exact (((integrable_const C_det).add
      ((qv_diff_sq_integrable X hMμ hMσ T hT (ns (ms k))).const_mul (4 * C_rand))).add
      ((qv_sq_integrable X hMσ T hT.le).const_mul (4 * C_rand))).add
      ((process_increment_fourth_integrable X hMμ hMσ (bdy_pt k) u
        (h_bdy_nn k) (h_bdy_le k)).const_mul (2 * C_rand))
  -- (7) G integrable
  · exact (integrable_const C_det).add ((qv_sq_integrable X hMσ T hT.le).const_mul (4 * C_rand))
  -- (8) ∫g_k → ∫G
  · -- g_k = G + 4*C_rand*(Sk-QV)² + 2*C_rand*bdy⁴, where both extra terms → 0 in L¹
    have hG_i : Integrable (fun ω => C_det + 4 * C_rand *
        (X.quadraticVariation T ω) ^ 2) μ :=
      (integrable_const C_det).add
        ((qv_sq_integrable X hMσ T hT.le).const_mul (4 * C_rand))
    have hD1_i : ∀ k, Integrable (fun ω => 4 * C_rand *
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2) μ :=
      fun k => (qv_diff_sq_integrable X hMμ hMσ T hT (ns (ms k))).const_mul (4 * C_rand)
    have hD2_i : ∀ k, Integrable (fun ω => 2 * C_rand *
        (X.process u ω - X.process (bdy_pt k) ω) ^ 4) μ :=
      fun k => (process_increment_fourth_integrable X hMμ hMσ (bdy_pt k) u
        (h_bdy_nn k) (h_bdy_le k)).const_mul (2 * C_rand)
    -- Decompose ∫g_k into 4 additive pieces using integral_add
    -- g_k = (C_det + 4C*(Sk-QV)²) + (4C*QV²) + (2C*bdy⁴)
    --     left-assoc:  ((C_det + A) + B) + D
    -- We split as: ∫((C_det+A)+B+D) = ∫((C_det+A)+B) + ∫D = (∫(C_det+A) + ∫B) + ∫D
    -- Then rearrange to show ∫g_k = ∫G + ∫D1 + ∫D2
    -- ∫C_det = C_det, ∫4C*(Sk-QV)² → 0, ∫4C*QV² = const, ∫2C*bdy⁴ → 0

    -- Integrability of first two addends combined
    have h_first_two_i : ∀ k, Integrable (fun ω => C_det + 4 * C_rand *
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2) μ :=
      fun k => (integrable_const C_det).add (hD1_i k)
    -- Integrability of first three addends combined
    have h_first_three_i : ∀ k, Integrable (fun ω => C_det + 4 * C_rand *
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2 +
        4 * C_rand * (X.quadraticVariation T ω) ^ 2) μ :=
      fun k => (h_first_two_i k).add ((qv_sq_integrable X hMσ T hT.le).const_mul (4 * C_rand))
    -- Decompose: ∫g_k = ∫(first three) + ∫D2
    have h_split1 : ∀ k, ∫ ω, (C_det + 4 * C_rand *
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2 +
        4 * C_rand * (X.quadraticVariation T ω) ^ 2 +
        2 * C_rand * (X.process u ω - X.process (bdy_pt k) ω) ^ 4) ∂μ =
        ∫ ω, (C_det + 4 * C_rand *
          (∑ i : Fin (ns (ms k) + 1),
            (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
             X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
           X.quadraticVariation T ω) ^ 2 +
          4 * C_rand * (X.quadraticVariation T ω) ^ 2) ∂μ +
        ∫ ω, (2 * C_rand *
          (X.process u ω - X.process (bdy_pt k) ω) ^ 4) ∂μ :=
      fun k => integral_add (h_first_three_i k) (hD2_i k)
    -- Decompose further: ∫(first three) = ∫(first two) + ∫(4C*QV²)
    have h_split2 : ∀ k, ∫ ω, (C_det + 4 * C_rand *
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2 +
        4 * C_rand * (X.quadraticVariation T ω) ^ 2) ∂μ =
        ∫ ω, (C_det + 4 * C_rand *
          (∑ i : Fin (ns (ms k) + 1),
            (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
             X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
           X.quadraticVariation T ω) ^ 2) ∂μ +
        ∫ ω, (4 * C_rand * (X.quadraticVariation T ω) ^ 2) ∂μ :=
      fun k => integral_add (h_first_two_i k)
        ((qv_sq_integrable X hMσ T hT.le).const_mul (4 * C_rand))
    -- And: ∫(first two) = ∫C_det + ∫D1
    have h_split3 : ∀ k, ∫ ω, (C_det + 4 * C_rand *
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2) ∂μ =
        ∫ ω, (C_det : ℝ) ∂μ +
        ∫ ω, (4 * C_rand *
          (∑ i : Fin (ns (ms k) + 1),
            (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
             X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
           X.quadraticVariation T ω) ^ 2) ∂μ :=
      fun k => integral_add (integrable_const C_det) (hD1_i k)
    -- ∫D1_k → 0
    have h_D1_tail : Filter.Tendsto (fun k => ∫ ω, (4 * C_rand *
        (∑ i : Fin (ns (ms k) + 1),
          (X.process ((↑(i : ℕ) + 1) * T / ↑(ns (ms k) + 1)) ω -
           X.process (↑(i : ℕ) * T / ↑(ns (ms k) + 1)) ω) ^ 2 -
         X.quadraticVariation T ω) ^ 2) ∂μ) atTop (nhds 0) := by
      have := h_qv_L2_nsms.const_mul (4 * C_rand)
      rw [mul_zero] at this
      exact this.congr (fun k => (integral_const_mul _ _).symm)
    -- ∫D2_k → 0 (from E[boundary⁴] ≤ C·(T/(N+1))² → 0)
    have h_D2_tail : Filter.Tendsto (fun k => ∫ ω, (2 * C_rand *
        (X.process u ω - X.process (bdy_pt k) ω) ^ 4) ∂μ) atTop (nhds 0) := by
      -- Factor out constant: ∫(2C*f) = 2C * ∫f
      simp_rw [integral_const_mul]
      rw [show (0:ℝ) = 2 * C_rand * 0 from (mul_zero _).symm]
      apply Filter.Tendsto.const_mul
      -- Need: ∫(X(u) - X(bdy_pt k))⁴ → 0
      -- Strategy: squeeze with ito_process_increment_L4_bound
      set C₄ := 8 * Mμ ^ 4 + 8 * 3 * Mσ ^ 4
      -- Eventually u - bdy_pt k ≤ 1
      have h_ev_small : ∀ᶠ k in atTop, u - bdy_pt k ≤ 1 := by
        have h_sub : Filter.Tendsto (fun k => u - bdy_pt k) atTop (nhds 0) := by
          have := (tendsto_const_nhds (x := u)).sub h_bdy_conv
          rwa [sub_self] at this
        exact (h_sub.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))).mono
          fun k hk => hk.le
      -- Eventually ‖∫f⁴‖ ≤ C₄*(u-bdy_pt k)²
      have h_ev_bnd : ∀ᶠ k in atTop,
          ‖∫ ω, (X.process u ω - X.process (bdy_pt k) ω) ^ 4 ∂μ‖ ≤
          C₄ * (u - bdy_pt k) ^ 2 := by
        filter_upwards [h_ev_small] with k hk
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω => by positivity)]
        exact ito_process_increment_L4_bound X hMμ hMσ (bdy_pt k) u
          (h_bdy_nn k) (h_bdy_le k) hk
      -- Upper bound → 0
      have h_upper : Filter.Tendsto (fun k => C₄ * (u - bdy_pt k) ^ 2)
          atTop (nhds 0) := by
        have h_sub : Filter.Tendsto (fun k => u - bdy_pt k) atTop (nhds 0) := by
          have := (tendsto_const_nhds (x := u)).sub h_bdy_conv
          rwa [sub_self] at this
        have h_sq := h_sub.pow 2
        rw [zero_pow (by norm_num : 2 ≠ 0)] at h_sq
        have := h_sq.const_mul C₄
        rwa [mul_zero] at this
      exact squeeze_zero_norm' h_ev_bnd h_upper
    -- Build ∫g_k → ∫G using the decomposition
    -- ∫g_k = (∫C_det + ∫D1_k) + ∫(4C*QV²) + ∫D2_k
    -- → (∫C_det + 0) + ∫(4C*QV²) + 0
    -- = ∫C_det + ∫(4C*QV²) = ∫(C_det + 4C*QV²) = ∫G
    simp_rw [h_split1, h_split2, h_split3]
    -- Goal: Tendsto (fun k => (∫C_det + ∫D1_k) + ∫(4C*QV²) + ∫D2_k) → ∫G
    -- ∫G = ∫C_det + ∫(4C*QV²) by integral_add
    have hG_eq : ∫ ω, (C_det + 4 * C_rand * (X.quadraticVariation T ω) ^ 2) ∂μ =
        ∫ ω, (C_det : ℝ) ∂μ + ∫ ω, (4 * C_rand * (X.quadraticVariation T ω) ^ 2) ∂μ :=
      integral_add (integrable_const C_det)
        ((qv_sq_integrable X hMσ T hT.le).const_mul (4 * C_rand))
    rw [hG_eq]
    -- Goal: Tendsto (fun k => (∫C_det + ∫D1_k) + ∫(4C*QV²) + ∫D2_k) → ∫C_det + ∫(4C*QV²)
    -- Build left-assoc: ∫C_det + ∫D1_k → ∫C_det + 0 = ∫C_det
    have h1 := h_D1_tail.const_add (∫ ω, (C_det : ℝ) ∂μ)
    simp only [add_zero] at h1
    -- + ∫(4C*QV²) constant
    have h2 := h1.add (tendsto_const_nhds
      (x := ∫ ω, (4 * C_rand * (X.quadraticVariation T ω) ^ 2) ∂μ))
    -- + ∫D2_k → 0
    have h3 := h2.add h_D2_tail
    rw [add_zero] at h3
    exact h3

/-! ## Main martingale property theorem

Combines SI-increment approximation with L² limit infrastructure via
`martingale_setIntegral_eq_of_L2_limit`. -/

/-- The Itô formula remainder is a martingale.

    This is the key content of the Itô formula: the process
    M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds
    satisfies the martingale set-integral property.

    **Proof**: M_t is the L² limit of SI-increment approximations M_n(t),
    each of which satisfies the martingale set-integral property. By
    `martingale_setIntegral_eq_of_L2_limit`, the property transfers to the limit. -/
theorem ito_formula_martingale {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    -- Regularity of diffusion
    (_hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (_hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    -- Regularity of drift
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    -- Boundedness of derivatives
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (hf_t_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M)
    -- Joint continuity of derivatives (C^{1,2} regularity)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    -- Integrability of the remainder (verified by caller using boundedness of f, drift, etc.)
    (hrem_int : ∀ t', 0 ≤ t' → Integrable (itoRemainder X f t') μ)
    (hrem_sq_int : ∀ t', 0 ≤ t' → Integrable (fun ω => (itoRemainder X f t' ω)^2) μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
      ∫ ω in A, itoRemainder X f t ω ∂μ = ∫ ω in A, itoRemainder X f s ω ∂μ := by
  intro s t hs hst A hA
  -- Handle the trivial case s = t
  by_cases hst_eq : s = t
  · subst hst_eq; rfl
  have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
  have ht_pos : 0 < t := lt_of_le_of_lt hs hst_lt
  -- Apply martingale_setIntegral_eq_of_L2_limit with:
  --   M := itoRemainder X f
  --   M_n n := siIncrementApprox X f t n  (partition of [0, t])
  exact martingale_setIntegral_eq_of_L2_limit
    -- Integrability of itoRemainder at s and t
    (hrem_int s hs)
    (hrem_int t ht_pos.le)
    -- Integrability of M_n at s and t
    (fun n => si_increment_integrable X f hf_x hf_x_bdd t ht_pos.le n s hs)
    (fun n => si_increment_integrable X f hf_x hf_x_bdd t ht_pos.le n t ht_pos.le)
    -- Square-integrability of (M_n - itoRemainder) at s and t
    (fun n => si_increment_diff_sq_integrable X f hf_x hf_x_bdd t ht_pos.le n s hs
      (hrem_int s hs) (hrem_sq_int s hs))
    (fun n => si_increment_diff_sq_integrable X f hf_x hf_x_bdd t ht_pos.le n t ht_pos.le
      (hrem_int t ht_pos.le) (hrem_sq_int t ht_pos.le))
    -- L² convergence at s (partition of [0,t], evaluated at s ≤ t)
    (si_increment_L2_convergence X f hf_t hf_x hdiff_bdd hdrift_bdd hf_x_bdd hf_xx_bdd
      hf_t_bdd hf_t_cont hf'_cont hf''_cont t ht_pos s hs hst
      (hrem_int s hs) (hrem_sq_int s hs))
    -- L² convergence at t (partition of [0,t], evaluated at t)
    (si_increment_L2_convergence X f hf_t hf_x hdiff_bdd hdrift_bdd hf_x_bdd hf_xx_bdd
      hf_t_bdd hf_t_cont hf'_cont hf''_cont t ht_pos t ht_pos.le le_rfl
      (hrem_int t ht_pos.le) (hrem_sq_int t ht_pos.le))
    -- MeasurableSet A in ambient σ-algebra (from F_s ≤ ambient)
    (F.le_ambient s _ hA)
    -- Martingale property of M_n: ∫_A M_n(t) = ∫_A M_n(s) for A ∈ F_s
    (fun n => si_increment_martingale_property X f hf_x hf_x_bdd t ht_pos n
      s t hs hst le_rfl A hA)

/-! ## Itô's Formula (full theorem)

Combines the martingale property (`ito_formula_martingale`) with the trivial
initial condition and identity parts. This is the main entry point. -/

/-- Itô's formula for a C² function f applied to an Itô process.

    f(t, X_t) = f(0, X_0) + ∫₀ᵗ [∂_t f + μ ∂_x f + ½ σ² ∂²_x f](s, X_s) ds
                + stoch_int(t)

    where stoch_int is a martingale. The conclusion asserts the existence of a
    stochastic integral process that:
    (i) starts at 0 a.s.
    (ii) is a martingale (set-integral property for F_s-measurable sets)
    (iii) satisfies the Itô formula equation

    **Hypotheses**: Beyond C² regularity of f, we need boundedness of derivatives
    and coefficients. These ensure integrability of the remainder and convergence
    of the approximation scheme. -/
theorem ito_formula {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    -- Regularity of diffusion
    (hdiff_meas : ∀ t, Measurable (X.diffusion t))
    (hdiff_adapted : ∀ t, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    -- Regularity of drift
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    -- Boundedness of derivatives
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (hf_t_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M)
    -- Joint continuity of derivatives (C^{1,2} regularity)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    -- Integrability of the remainder
    (hrem_int : ∀ t', 0 ≤ t' → Integrable (itoRemainder X f t') μ)
    (hrem_sq_int : ∀ t', 0 ≤ t' → Integrable (fun ω => (itoRemainder X f t' ω)^2) μ) :
    ∃ (stoch_int : ℝ → Ω → ℝ),
    -- (i) Initial condition: the stochastic integral starts at 0
    (∀ᵐ ω ∂μ, stoch_int 0 ω = 0) ∧
    -- (ii) Martingale property: for 0 ≤ s ≤ t and A ∈ F_s, ∫_A M_t = ∫_A M_s
    (∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
      ∫ ω in A, stoch_int t ω ∂μ = ∫ ω in A, stoch_int s ω ∂μ) ∧
    -- (iii) Itô's formula
    (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
      f t (X.process t ω) = f 0 (X.process 0 ω) +
        (∫ (s : ℝ) in Set.Icc 0 t,
          (deriv (fun u => f u (X.process s ω)) s +
           deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
           (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2)
          ∂volume) +
        stoch_int t ω) := by
  -- The stochastic integral is the Itô remainder
  refine ⟨itoRemainder X f, ?_, ?_, ?_⟩
  · -- (i) Initial condition: itoRemainder at t=0 is 0
    filter_upwards with ω
    unfold itoRemainder
    have hmeas_zero : (volume.restrict (Set.Icc (0 : ℝ) 0)) = 0 := by
      rw [Measure.restrict_eq_zero, Set.Icc_self]; simp
    rw [hmeas_zero, integral_zero_measure]
    ring
  · -- (ii) Martingale property: from ito_formula_martingale
    exact ito_formula_martingale X f hf_t hf_x hdiff_meas hdiff_adapted hdiff_bdd
      hdrift_bdd hf_x_bdd hf_xx_bdd hf_t_bdd hf_t_cont hf'_cont hf''_cont
      hrem_int hrem_sq_int
  · -- (iii) Itô's formula: by definition of itoRemainder
    intro t ht
    filter_upwards with ω
    unfold itoRemainder
    ring

end SPDE
