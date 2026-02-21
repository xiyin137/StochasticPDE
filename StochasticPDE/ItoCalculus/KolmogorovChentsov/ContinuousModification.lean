/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Algebra.InfiniteSum.Real
import StochasticPDE.ItoCalculus.KolmogorovChentsov.DyadicPartition
import StochasticPDE.ItoCalculus.KolmogorovChentsov.DyadicIncrement

/-!
# Kolmogorov-Chentsov Continuous Modification

Under the Kolmogorov moment condition `E[|X_t - X_s|^p] ≤ M * |t-s|^q` with `q ≥ 2`,
we construct a modification Y of X with continuous paths a.s. on `[0, T]`.

## Strategy

1. From the Borel-Cantelli result (Phase 3), a.e. eventually all dyadic increments are
   controlled by a threshold sequence `δ`.
2. The dyadic floor approximation `X(d_n(t), ω)` forms a Cauchy sequence for a.e. ω.
3. The pointwise limit defines the modification Y.
4. Y has continuous paths (modulus of continuity from the threshold sequence).
5. Y(t) = X(t) a.e. (from the moment condition).

## Main Results

* `kolmogorov_chentsov` — Existence of continuous modification

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Theorem 2.2.8
-/

namespace KolmogorovChentsov

open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Section 1: Nat.floor doubling -/

/-- For x ≥ 0, the natural floor of 2x is either 2⌊x⌋ or 2⌊x⌋ + 1 -/
theorem Nat.floor_two_mul_eq_or {x : ℝ} (hx : 0 ≤ x) :
    ⌊2 * x⌋₊ = 2 * ⌊x⌋₊ ∨ ⌊2 * x⌋₊ = 2 * ⌊x⌋₊ + 1 := by
  have h_lower : 2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith [Nat.floor_le hx]
  have h_upper : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := by
    rw [Nat.floor_lt (by linarith)]
    push_cast
    linarith [Nat.lt_floor_add_one x]
  omega

/-! ## Section 2: Dyadic floor refinement -/

/-- At level n+1, the dyadic floor index is either 2k or 2k+1 where k is the
    dyadic floor at level n. This is the key refinement property for telescoping. -/
theorem dyadicFloor_succ_eq {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) :
    dyadicFloor T (n + 1) t = 2 * dyadicFloor T n t ∨
    dyadicFloor T (n + 1) t = 2 * dyadicFloor T n t + 1 := by
  unfold dyadicFloor
  rw [if_neg (not_le.mpr hT), if_neg (not_le.mpr hT)]
  set x := t * 2 ^ n / T with hx_def
  have hx_nn : 0 ≤ x := div_nonneg (mul_nonneg ht.1 (two_pow_pos n).le) hT.le
  -- t * 2^{n+1} / T = 2 * x
  have hx2 : t * 2 ^ (n + 1) / T = 2 * x := by
    simp only [hx_def, pow_succ]; ring
  rw [hx2]
  -- x ≤ 2^n (from t ≤ T)
  have hx_le : x ≤ (2 : ℝ) ^ n := by
    simp only [hx_def]
    rw [div_le_iff₀ hT]
    calc t * 2 ^ n ≤ T * 2 ^ n := mul_le_mul_of_nonneg_right ht.2 (two_pow_pos n).le
      _ = 2 ^ n * T := by ring
  have h_floor_le : ⌊x⌋₊ ≤ 2 ^ n :=
    Nat.floor_le_of_le (by exact_mod_cast hx_le)
  rw [min_eq_right h_floor_le]
  -- Use the doubling property
  rcases Nat.floor_two_mul_eq_or hx_nn with h | h
  · left
    have h_le : ⌊2 * x⌋₊ ≤ 2 ^ (n + 1) := by
      rw [h, pow_succ, two_mul]; omega
    rw [min_eq_right h_le, h]
  · right
    -- In the +1 case, ⌊x⌋₊ < 2^n (equality would force the 2k case)
    have h_strict : ⌊x⌋₊ < 2 ^ n := by
      by_contra h_not_lt
      push_neg at h_not_lt
      have h_eq : ⌊x⌋₊ = 2 ^ n := Nat.le_antisymm h_floor_le h_not_lt
      have hx_eq : x = (2 : ℝ) ^ n := by
        have h1 := Nat.floor_le hx_nn
        rw [h_eq, Nat.cast_pow, Nat.cast_ofNat] at h1
        linarith
      -- ⌊2 * (2 : ℝ)^n⌋₊ = 2 * 2^n (since 2 * 2^n is a natural number)
      have h_floor : ⌊2 * x⌋₊ = 2 * ⌊x⌋₊ := by
        rw [hx_eq]
        have h2x : 2 * (2 : ℝ) ^ n = ↑(2 * (2 : ℕ) ^ n) := by push_cast; ring
        have hx' : (2 : ℝ) ^ n = ↑((2 : ℕ) ^ n) := by push_cast; rfl
        rw [h2x, hx', Nat.floor_natCast, Nat.floor_natCast]
      omega
    have h_le : ⌊2 * x⌋₊ ≤ 2 ^ (n + 1) := by
      rw [h, pow_succ, two_mul]; omega
    rw [min_eq_right h_le, h]

/-- When the floor jumps at level n+1, the index 2k is still valid as a
    dyadic interval index at level n+1 -/
theorem dyadicFloor_succ_double_lt {T : ℝ} (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Icc 0 T) (n : ℕ)
    (h : dyadicFloor T (n + 1) t = 2 * dyadicFloor T n t + 1) :
    2 * dyadicFloor T n t < 2 ^ (n + 1) := by
  have hle := dyadicFloor_le_pow T n t
  have : dyadicFloor T n t < 2 ^ n := by
    by_contra h_not
    push_neg at h_not
    have h_eq : dyadicFloor T n t = 2 ^ n := Nat.le_antisymm hle h_not
    rcases dyadicFloor_succ_eq hT ht n with h2k | h2k1
    · rw [h2k] at h; rw [h_eq] at h; omega
    · have := dyadicFloor_le_pow T (n + 1) t
      rw [h2k1, h_eq] at this
      rw [pow_succ, two_mul] at this; omega
  rw [pow_succ, two_mul]; omega

/-! ## Section 3: Dyadic approximation sequence -/

/-- The dyadic approximation sequence: X evaluated at the dyadic floor of t -/
noncomputable def dyadicApprox (X : ℝ → Ω → ℝ) (T : ℝ) (t : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => X (dyadicPoint T n (dyadicFloor T n t)) ω

/-- Each step of the dyadic approximation changes by at most one level-(n+1) increment.
    This is because d_n(t) = dyadicPoint T (n+1) (2k) and d_{n+1}(t) is either the same
    or dyadicPoint T (n+1) (2k+1). -/
theorem dyadicApprox_step_eq {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) (ω : Ω) :
    dyadicApprox X T t (n + 1) ω - dyadicApprox X T t n ω = 0 ∨
    (∃ j, j < 2 ^ (n + 1) ∧
      dyadicApprox X T t (n + 1) ω - dyadicApprox X T t n ω =
      X (dyadicPoint T (n + 1) (j + 1)) ω - X (dyadicPoint T (n + 1) j) ω) := by
  unfold dyadicApprox
  rcases dyadicFloor_succ_eq hT ht n with h_eq | h_inc
  · -- Case: floor at n+1 = 2k. Then d_{n+1}(t) = d_n(t), difference = 0.
    left
    have : dyadicPoint T (n + 1) (dyadicFloor T (n + 1) t) =
           dyadicPoint T n (dyadicFloor T n t) := by
      rw [h_eq, ← dyadicPoint_level_succ]
    simp [this]
  · -- Case: floor at n+1 = 2k+1. This is a single level-(n+1) increment.
    right
    set k := dyadicFloor T n t
    refine ⟨2 * k, dyadicFloor_succ_double_lt hT ht n h_inc, ?_⟩
    rw [h_inc, ← dyadicPoint_level_succ]

/-- The absolute step bound: each dyadic approximation step is controlled by a
    single dyadic increment at the next level -/
theorem dyadicApprox_step_le {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) (ω : Ω) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcontrol : ∀ k, k < 2 ^ (n + 1) →
      |X (dyadicPoint T (n + 1) (k + 1)) ω - X (dyadicPoint T (n + 1) k) ω| ≤ δ) :
    |dyadicApprox X T t (n + 1) ω - dyadicApprox X T t n ω| ≤ δ := by
  rcases dyadicApprox_step_eq hT ht n ω with h_zero | ⟨j, hj_lt, hj_eq⟩
  · rw [h_zero, abs_zero]; exact hδ
  · rw [hj_eq]; exact hcontrol j hj_lt

/-! ## Section 4: Cauchy bounds and convergence -/

/-- Telescoping bound: the difference between level-m and level-n approximations
    is bounded by the sum of thresholds. -/
theorem dyadicApprox_diff_le {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) {δ : ℕ → ℝ} (hδ_nn : ∀ n, 0 ≤ δ n)
    (ω : Ω) {N : ℕ}
    (hcontrol : ∀ n ≥ N, ∀ k, k < 2 ^ n →
      |X (dyadicPoint T n (k + 1)) ω - X (dyadicPoint T n k) ω| ≤ δ n)
    {n m : ℕ} (hn : N ≤ n) (hm : n ≤ m) :
    |dyadicApprox X T t m ω - dyadicApprox X T t n ω| ≤
      ∑ j ∈ Finset.Ico n m, δ (j + 1) := by
  induction m with
  | zero =>
    simp [Nat.le_zero.mp hm]
  | succ m ih =>
    by_cases h_eq : n = m + 1
    · subst h_eq; simp
    · have hm_le : n ≤ m := by omega
      have h_step := dyadicApprox_step_le hT ht m ω (hδ_nn (m + 1))
        (hcontrol (m + 1) (by omega))
      have h_tri : |dyadicApprox X T t (m + 1) ω - dyadicApprox X T t n ω| ≤
          |dyadicApprox X T t (m + 1) ω - dyadicApprox X T t m ω| +
          |dyadicApprox X T t m ω - dyadicApprox X T t n ω| := by
        calc |dyadicApprox X T t (m + 1) ω - dyadicApprox X T t n ω|
            = |(dyadicApprox X T t (m + 1) ω - dyadicApprox X T t m ω) +
               (dyadicApprox X T t m ω - dyadicApprox X T t n ω)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      calc |dyadicApprox X T t (m + 1) ω - dyadicApprox X T t n ω|
          ≤ |dyadicApprox X T t (m + 1) ω - dyadicApprox X T t m ω| +
            |dyadicApprox X T t m ω - dyadicApprox X T t n ω| := h_tri
        _ ≤ δ (m + 1) + ∑ j ∈ Finset.Ico n m, δ (j + 1) := by
            linarith [h_step, ih hm_le]
        _ = ∑ j ∈ Finset.Ico n (m + 1), δ (j + 1) := by
            rw [Finset.sum_Ico_succ_top (by omega : n ≤ m)]
            linarith

/-! ## Section 5: Modification definition -/

/-- The Kolmogorov modification: pointwise limit of dyadic approximations.
    Uses `Filter.limUnder` which returns the limit when it exists, and a
    default value otherwise. On the a.e. good set, this is the actual limit. -/
noncomputable def kolmogorovModification (X : ℝ → Ω → ℝ) (T : ℝ) : ℝ → Ω → ℝ :=
  fun t ω => limUnder atTop (fun n => dyadicApprox X T t n ω)

/-! ## Section 6: Continuity infrastructure -/

/-- Adjacent dyadic floors differ by at most 1 step -/
theorem dyadicFloor_close {T : ℝ} (hT : 0 < T) {n : ℕ}
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc 0 T) (ht₂ : t₂ ∈ Icc 0 T)
    (hclose : |t₁ - t₂| < T / 2 ^ n) :
    dyadicFloor T n t₂ ≤ dyadicFloor T n t₁ + 1 ∧
    dyadicFloor T n t₁ ≤ dyadicFloor T n t₂ + 1 := by
  have hT_pos := hT
  unfold dyadicFloor
  rw [if_neg (not_le.mpr hT), if_neg (not_le.mpr hT)]
  set k₁ := min (2 ^ n) ⌊t₁ * 2 ^ n / T⌋₊
  set k₂ := min (2 ^ n) ⌊t₂ * 2 ^ n / T⌋₊
  -- Key: |t₁ - t₂| < T/2^n implies |t₁·2^n/T - t₂·2^n/T| < 1
  have h_scaled : |t₁ * 2 ^ n / T - t₂ * 2 ^ n / T| < 1 := by
    have h2n_pos : (0 : ℝ) < 2 ^ n := two_pow_pos n
    rw [show t₁ * 2 ^ n / T - t₂ * 2 ^ n / T = (t₁ - t₂) * (2 ^ n / T) from by ring]
    rw [abs_mul, abs_of_pos (div_pos h2n_pos hT_pos)]
    calc |t₁ - t₂| * (2 ^ n / T) < T / 2 ^ n * (2 ^ n / T) :=
          mul_lt_mul_of_pos_right hclose (div_pos h2n_pos hT_pos)
      _ = 1 := by field_simp
  -- Floor values differ by at most 1 when the real values differ by < 1
  have h1 := Nat.floor_le (div_nonneg (mul_nonneg ht₁.1 (two_pow_pos n).le) hT.le)
  have h2 := Nat.floor_le (div_nonneg (mul_nonneg ht₂.1 (two_pow_pos n).le) hT.le)
  have h3 := Nat.lt_floor_add_one (t₁ * 2 ^ n / T)
  have h4 := Nat.lt_floor_add_one (t₂ * 2 ^ n / T)
  have h_diff := abs_sub_lt_iff.mp h_scaled
  have hab : ⌊t₁ * 2 ^ n / T⌋₊ ≤ ⌊t₂ * 2 ^ n / T⌋₊ + 1 := by
    suffices h : (⌊t₁ * 2 ^ n / T⌋₊ : ℝ) < (⌊t₂ * 2 ^ n / T⌋₊ : ℝ) + 2 by
      have h' : ⌊t₁ * 2 ^ n / T⌋₊ < ⌊t₂ * 2 ^ n / T⌋₊ + 2 := by exact_mod_cast h
      omega
    linarith
  have hba : ⌊t₂ * 2 ^ n / T⌋₊ ≤ ⌊t₁ * 2 ^ n / T⌋₊ + 1 := by
    suffices h : (⌊t₂ * 2 ^ n / T⌋₊ : ℝ) < (⌊t₁ * 2 ^ n / T⌋₊ : ℝ) + 2 by
      have h' : ⌊t₂ * 2 ^ n / T⌋₊ < ⌊t₁ * 2 ^ n / T⌋₊ + 2 := by exact_mod_cast h
      omega
    linarith
  exact ⟨by omega, by omega⟩

/-- Dyadic approximation difference bound for nearby points -/
theorem dyadicApprox_close_bound {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc 0 T) (ht₂ : t₂ ∈ Icc 0 T)
    {n : ℕ} (hclose : |t₁ - t₂| < T / 2 ^ n)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ω : Ω)
    (hcontrol : ∀ k, k < 2 ^ n →
      |X (dyadicPoint T n (k + 1)) ω - X (dyadicPoint T n k) ω| ≤ δ) :
    |dyadicApprox X T t₁ n ω - dyadicApprox X T t₂ n ω| ≤ δ := by
  unfold dyadicApprox
  obtain ⟨h₁, h₂⟩ := dyadicFloor_close hT ht₁ ht₂ hclose
  set k₁ := dyadicFloor T n t₁
  set k₂ := dyadicFloor T n t₂
  by_cases heq : k₁ = k₂
  · simp [heq, hδ]
  · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
    · have hk2 : k₂ = k₁ + 1 := by omega
      rw [hk2, abs_sub_comm]
      have hk1_lt : k₁ < 2 ^ n := by
        have := dyadicFloor_le_pow T n t₂; omega
      exact hcontrol k₁ hk1_lt
    · have hk1 : k₁ = k₂ + 1 := by omega
      rw [hk1]
      have hk2_lt : k₂ < 2 ^ n := by
        have := dyadicFloor_le_pow T n t₁; omega
      exact hcontrol k₂ hk2_lt

/-! ## Section 6b: Cauchy convergence of dyadic approximations -/

/-- On the good set (where dyadic increments are controlled), the dyadic
    approximation sequence is Cauchy, hence convergent in ℝ. -/
theorem dyadicApprox_cauchySeq {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) {δ : ℕ → ℝ} (hδ_nn : ∀ n, 0 ≤ δ n)
    (hδ_sum : Summable δ) (ω : Ω) {N : ℕ}
    (hcontrol : ∀ n ≥ N, ∀ k, k < 2 ^ n →
      |X (dyadicPoint T n (k + 1)) ω - X (dyadicPoint T n k) ω| ≤ δ n) :
    CauchySeq (fun n => dyadicApprox X T t n ω) := by
  set a := fun n => dyadicApprox X T t n ω
  -- Step bound for n ≥ N: dist(a(n), a(n+1)) ≤ δ(n+1)
  have h_step : ∀ n, N ≤ n → dist (a n) (a n.succ) ≤ δ (n + 1) := by
    intro n hn
    show dist (dyadicApprox X T t n ω) (dyadicApprox X T t (n + 1) ω) ≤ δ (n + 1)
    rw [Real.dist_eq, abs_sub_comm]
    exact dyadicApprox_step_le hT ht n ω (hδ_nn (n + 1)) (hcontrol (n + 1) (by omega))
  -- The shifted sequence a'(m) := a(N+m) has summable step distances
  have h_step' : ∀ m, dist (a (N + m)) (a (N + m).succ) ≤ δ (N + m + 1) :=
    fun m => h_step (N + m) (le_add_right le_rfl)
  -- The bounding sequence δ(N + · + 1) is summable
  have h_bnd_sum : Summable (fun m => δ (N + m + 1)) := by
    rw [show (fun m => δ (N + m + 1)) = (fun m => δ (m + (N + 1))) from by ext m; congr 1; omega]
    exact (summable_nat_add_iff (N + 1)).mpr hδ_sum
  -- The shifted sequence is Cauchy
  have h_shift_cauchy : CauchySeq (fun m => a (N + m)) :=
    cauchySeq_of_dist_le_of_summable _ h_step' h_bnd_sum
  -- Cauchy of a shift implies Cauchy of the original
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rw [Metric.cauchySeq_iff] at h_shift_cauchy
  obtain ⟨K, hK⟩ := h_shift_cauchy ε hε
  exact ⟨N + K, fun n₁ hn₁ n₂ hn₂ => by
    have := hK (n₁ - N) (by omega) (n₂ - N) (by omega)
    rwa [show N + (n₁ - N) = n₁ from by omega, show N + (n₂ - N) = n₂ from by omega] at this⟩

/-! ## Section 6c: Tail bound for the limit -/

/-- Distance from d_n(t) to the limit Y(t) is bounded by the tail sum of δ.
    This is the key quantitative estimate for the continuity argument. -/
theorem dyadicApprox_limit_dist {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) {δ : ℕ → ℝ} (hδ_nn : ∀ n, 0 ≤ δ n)
    (hδ_sum : Summable δ) (ω : Ω) {N : ℕ}
    (hcontrol : ∀ n ≥ N, ∀ k, k < 2 ^ n →
      |X (dyadicPoint T n (k + 1)) ω - X (dyadicPoint T n k) ω| ≤ δ n)
    {n : ℕ} (hn : N ≤ n) :
    dist (dyadicApprox X T t n ω) (kolmogorovModification X T t ω) ≤
      ∑' j, δ (n + j + 1) := by
  set a := fun m => dyadicApprox X T t m ω
  -- Shifted sequence step bounds
  have h_step' : ∀ m, dist (a (N + m)) (a (N + m).succ) ≤ δ (N + m + 1) := by
    intro m
    show dist (dyadicApprox X T t (N + m) ω) (dyadicApprox X T t (N + m + 1) ω) ≤ _
    rw [Real.dist_eq, abs_sub_comm]
    exact dyadicApprox_step_le hT ht (N + m) ω (hδ_nn (N + m + 1))
      (hcontrol (N + m + 1) (by omega))
  have h_bnd_sum : Summable (fun m => δ (N + m + 1)) := by
    rw [show (fun m => δ (N + m + 1)) = (fun m => δ (m + (N + 1))) from by ext m; congr 1; omega]
    exact (summable_nat_add_iff (N + 1)).mpr hδ_sum
  -- The shifted sequence converges to the limUnder of the original
  have h_cauchy := dyadicApprox_cauchySeq hT ht hδ_nn hδ_sum ω hcontrol
  have h_tendsto := h_cauchy.tendsto_limUnder
  have h_shift_tendsto : Tendsto (fun m => a (N + m)) atTop (nhds (limUnder atTop a)) :=
    h_tendsto.comp (Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn' => by omega⟩))
  -- Apply the tail bound from Mathlib to the shifted sequence
  have h_dist := dist_le_tsum_of_dist_le_of_tendsto _ h_step' h_bnd_sum h_shift_tendsto (n - N)
  -- h_dist : dist (a (N + (n-N))) (limUnder atTop a) ≤ ∑' m, δ(N + ((n-N) + m) + 1)
  -- Convert to goal form: dist (a n) (lim a) ≤ ∑' j, δ(n + j + 1)
  have h1 : a (N + (n - N)) = a n := by congr 1; omega
  rw [h1] at h_dist
  exact h_dist.trans (le_of_eq (tsum_congr (fun m => by congr 1; omega)))

/-! ## Section 7: Main theorem — Kolmogorov-Chentsov -/

/-- **Kolmogorov-Chentsov continuous modification theorem**.

Under the Kolmogorov condition `E[|X_t - X_s|^p] ≤ M * |t-s|^q` with `q ≥ 2`,
for any summable threshold sequence `δ` satisfying the Borel-Cantelli condition,
there exists a modification Y of X with continuous sample paths a.s. on `[0, T]`.

The modification is constructed as the pointwise limit of dyadic floor approximations.
-/
theorem kolmogorov_chentsov [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T) {p q : ℕ} (hp : 0 < p)
    {M : ℝ}
    -- Integrability
    (hint : ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T →
      Integrable (fun ω => |X t ω - X s ω| ^ p) μ)
    -- Kolmogorov moment condition
    (hbound : ∀ s t, s ∈ Icc 0 T → t ∈ Icc 0 T →
      (∫ ω, |X t ω - X s ω| ^ p ∂μ) ≤ M * |t - s| ^ q)
    -- Threshold sequence
    {δ : ℕ → ℝ} (hδ_pos : ∀ n, 0 < δ n)
    (hδ_sum : Summable δ)
    -- Borel-Cantelli summability
    (hterms_nn : ∀ n, 0 ≤ (2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p))
    (hBC_sum : Summable (fun n => (2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p))) :
    ∃ Y : ℝ → Ω → ℝ,
      -- (i) Y has continuous paths a.s. on [0, T]
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Icc 0 T)) ∧
      -- (ii) Y(t) = X(t) a.e. for each t ∈ [0, T]
      (∀ t, t ∈ Icc 0 T → ∀ᵐ ω ∂μ, Y t ω = X t ω) := by
  -- Step 1: Borel-Cantelli gives a.e. control of dyadic increments
  have h_ae_control := ae_eventually_dyadic_controlled hT hp hint hbound hδ_pos hterms_nn hBC_sum
  -- Step 2: Define the modification
  let Y := kolmogorovModification X T
  refine ⟨Y, ?_, ?_⟩
  · -- (i) Continuity: proved on the a.e. good set
    have hδ_nn : ∀ n, 0 ≤ δ n := fun n => (hδ_pos n).le
    have h_tail_zero : Tendsto (fun i => ∑' k, δ (k + i)) atTop (nhds 0) :=
      tendsto_sum_nat_add δ
    have h_term_zero : Tendsto δ atTop (nhds 0) := hδ_sum.tendsto_atTop_zero
    filter_upwards [h_ae_control] with ω ⟨N, hN⟩
    rw [Metric.continuousOn_iff]
    intro t₁ ht₁ ε hε
    have hε3 : (0 : ℝ) < ε / 3 := by linarith
    -- Eventually: tail sum < ε/3
    have h_ev_n1 : ∀ᶠ n in atTop, ∑' k, δ (k + (n + 1)) < ε / 3 := by
      have h1 : ∀ᶠ i in atTop, ∑' k, δ (k + i) < ε / 3 :=
        h_tail_zero.eventually (gt_mem_nhds hε3)
      exact (tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩) :
        Tendsto (· + 1 : ℕ → ℕ) atTop atTop).eventually h1
    -- Eventually: δ(n) < ε/3
    have h_ev_term : ∀ᶠ n in atTop, δ n < ε / 3 :=
      h_term_zero.eventually (gt_mem_nhds hε3)
    -- Eventually: n ≥ N
    have h_ev_N : ∀ᶠ n in atTop, N ≤ n := eventually_atTop.mpr ⟨N, fun _ h => h⟩
    -- Extract witness n satisfying all three
    obtain ⟨n, hn_N, hn_tail, hn_term⟩ :=
      (h_ev_N.and (h_ev_n1.and h_ev_term)).exists
    -- Set spatial threshold = T / 2^n
    refine ⟨T / 2 ^ n, div_pos hT (two_pow_pos n), fun t₂ ht₂ hclose => ?_⟩
    have h_lim1 := dyadicApprox_limit_dist hT ht₁ hδ_nn hδ_sum ω hN hn_N
    have h_lim2 := dyadicApprox_limit_dist hT ht₂ hδ_nn hδ_sum ω hN hn_N
    have h_close : |t₁ - t₂| < T / 2 ^ n := by
      rw [abs_sub_comm]; rwa [Real.dist_eq] at hclose
    have h_mid := dyadicApprox_close_bound hT ht₁ ht₂ h_close (hδ_nn n) ω (hN n hn_N)
    -- Convert tail bound: ∑' j, δ(n+j+1) = ∑' k, δ(k+(n+1)) < ε/3
    have h_tail_bound : ∑' j, δ (n + j + 1) < ε / 3 := by
      convert hn_tail using 1; exact tsum_congr (fun j => by congr 1; omega)
    -- Triangle inequality: dist(Y t₂, Y t₁) ≤ tail + δ(n) + tail < ε
    rw [dist_comm]
    calc dist (Y t₁ ω) (Y t₂ ω)
        ≤ dist (Y t₁ ω) (dyadicApprox X T t₁ n ω) +
          dist (dyadicApprox X T t₁ n ω) (Y t₂ ω) := dist_triangle _ _ _
      _ ≤ dist (Y t₁ ω) (dyadicApprox X T t₁ n ω) +
          (dist (dyadicApprox X T t₁ n ω) (dyadicApprox X T t₂ n ω) +
           dist (dyadicApprox X T t₂ n ω) (Y t₂ ω)) := by
          linarith [dist_triangle (dyadicApprox X T t₁ n ω)
            (dyadicApprox X T t₂ n ω) (Y t₂ ω)]
      _ ≤ (∑' j, δ (n + j + 1)) + (δ n + (∑' j, δ (n + j + 1))) := by
          rw [dist_comm (Y t₁ ω) (dyadicApprox X T t₁ n ω)]
          have hmid : dist (dyadicApprox X T t₁ n ω) (dyadicApprox X T t₂ n ω) ≤ δ n := by
            rw [Real.dist_eq]; exact h_mid
          linarith [h_lim1, h_lim2, hmid]
      _ < ε := by linarith
  · -- (ii) Modification property: Y(t) = X(t) a.e. for each t
    have hδ_nn : ∀ n, 0 ≤ δ n := fun n => (hδ_pos n).le
    intro t ht
    -- Strategy: Show d_n(t) → X(t) a.e. via Borel-Cantelli, then use uniqueness
    -- of limits with d_n(t) → Y(t) a.e. from the good set.
    set s := fun n => dyadicPoint T n (dyadicFloor T n t)
    have hs_mem : ∀ n, s n ∈ Icc 0 T :=
      fun n => dyadicPoint_mem_Icc hT.le (dyadicFloor_le_pow T n t)
    -- Key: each bc term is nonneg, so M*(T/2^n)^q/(δ n)^p ≥ 0
    have h_bc_nn : ∀ n, 0 ≤ M * (T / 2 ^ n) ^ q / (δ n) ^ p :=
      fun n => nonneg_of_mul_nonneg_right (hterms_nn n) (two_pow_pos n)
    -- |s_n - t| ≤ T/2^n
    have h_st_le : ∀ n, |s n - t| ≤ T / 2 ^ n := by
      intro n
      have h1 := dyadicPoint_floor_le hT ht n   -- s n ≤ t
      have h2 := dyadicFloor_dist_le hT ht n     -- t - s n ≤ T / 2^n
      rw [abs_of_nonpos (by linarith)]
      linarith
    -- Markov + comparison: μ{|X(s_n)-X(t)| > δ(n)} ≤ bc_term(n)
    have h_bad_le : ∀ n, μ {ω | δ n < |X (s n) ω - X t ω|} ≤
        ENNReal.ofReal ((2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p)) := by
      intro n
      have h_dp := pow_pos (hδ_pos n) p
      -- Derive M ≥ 0 from the nonnegativity of the BC terms
      have hM : 0 ≤ M := by
        by_contra hM_neg; push_neg at hM_neg
        linarith [h_bc_nn n, div_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos hM_neg (pow_pos (div_pos hT (two_pow_pos n)) q)) h_dp]
      calc μ {ω | δ n < |X (s n) ω - X t ω|}
          ≤ ENNReal.ofReal (M * |s n - t| ^ q / (δ n) ^ p) :=
            moment_tail_bound_strict hp (hδ_pos n) (hint t (s n) ht (hs_mem n))
              (hbound t (s n) ht (hs_mem n))
        _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p)) := by
            apply ENNReal.ofReal_le_ofReal
            -- Step 1: numerator bound M*|s_n - t|^q ≤ M*(T/2^n)^q
            have h_num : M * |s n - t| ^ q ≤ M * (T / 2 ^ n) ^ q :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (abs_nonneg _) (h_st_le n) q) hM
            -- Step 2: divide both sides by (δ n)^p
            have h1 : M * |s n - t| ^ q / (δ n) ^ p ≤ M * (T / 2 ^ n) ^ q / (δ n) ^ p :=
              (div_le_div_iff_of_pos_right h_dp).mpr h_num
            -- Step 3: x ≤ 2^n * x for nonneg x
            have h2 : M * (T / 2 ^ n) ^ q / (δ n) ^ p ≤
                2 ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p) :=
              le_mul_of_one_le_left (h_bc_nn n)
                (by exact_mod_cast Nat.one_le_two_pow : (1 : ℝ) ≤ 2 ^ n)
            linarith
    -- Sum of bad event measures is finite (by comparison with hBC_sum)
    have h_sum_ne_top : (∑' n, μ {ω | δ n < |X (s n) ω - X t ω|}) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h_bad_le)
      rw [← ENNReal.ofReal_tsum_of_nonneg hterms_nn hBC_sum]
      exact ENNReal.ofReal_ne_top
    -- Borel-Cantelli: a.e. eventually |X(s_n) - X(t)| ≤ δ(n)
    have h_ae_conv : ∀ᵐ ω ∂μ, ∃ N₂, ∀ n ≥ N₂, |X (s n) ω - X t ω| ≤ δ n := by
      have h_bc := ae_eventually_notMem h_sum_ne_top
      exact h_bc.mono (fun ω hω => by
        rw [Filter.eventually_atTop] at hω
        obtain ⟨N₂, hN₂⟩ := hω
        exact ⟨N₂, fun n hn => not_lt.mp (hN₂ n hn)⟩)
    -- Since δ(n) → 0, this means X(s_n, ω) → X(t, ω) a.e.
    -- Combined with X(s_n, ω) → Y(t, ω) on the good set → Y(t) = X(t) a.e.
    filter_upwards [h_ae_control, h_ae_conv] with ω ⟨N₁, hN₁⟩ ⟨N₂, hN₂⟩
    -- On good set: dyadicApprox → Y(t) (Cauchy convergence)
    have h_cauchy := dyadicApprox_cauchySeq hT ht hδ_nn hδ_sum ω hN₁
    have h_lim : Tendsto (fun n => dyadicApprox X T t n ω) atTop
        (nhds (kolmogorovModification X T t ω)) := h_cauchy.tendsto_limUnder
    -- From Borel-Cantelli: X(s_n) → X(t) (pointwise)
    have h_conv_X : Tendsto (fun n => X (s n) ω) atTop (nhds (X t ω)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
        (hδ_sum.tendsto_atTop_zero.eventually (gt_mem_nhds hε))
      exact ⟨max N₂ N₃, fun n hn => by
        rw [Real.dist_eq]
        calc |X (s n) ω - X t ω| ≤ δ n := hN₂ n (by omega)
          _ < ε := hN₃ n (by omega)⟩
    -- h_lim says dyadicApprox → Y(t); but dyadicApprox n = X(s n)
    -- So X(s_n) → Y(t) AND X(s_n) → X(t). By uniqueness: Y(t) = X(t).
    exact tendsto_nhds_unique h_lim h_conv_X

end KolmogorovChentsov
