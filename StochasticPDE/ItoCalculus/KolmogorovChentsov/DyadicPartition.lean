/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Dyadic Partition Infrastructure

This file provides definitions and lemmas for dyadic partitions of an interval [0, T],
used in the proof of the Kolmogorov-Chentsov theorem.

## Main Definitions

* `dyadicPoint T n k` — The k-th dyadic point at level n: k * T / 2^n
* `dyadicFloor T n t` — The largest dyadic point at level n that is ≤ t

## Main Results

* `dyadicPoint_mem_Icc` — Dyadic points lie in [0, T]
* `dyadicPoint_spacing` — Adjacent dyadic points are T / 2^n apart
* `dyadicPoint_level_succ` — Refinement: D_n ⊂ D_{n+1}
* `dyadicFloor_tendsto` — Dyadic floor approximations converge to t

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Theorem 2.2.8
-/

namespace KolmogorovChentsov

open Filter

/-! ## Dyadic Points -/

/-- The k-th dyadic point at level n on [0, T]: k * T / 2^n -/
noncomputable def dyadicPoint (T : ℝ) (n : ℕ) (k : ℕ) : ℝ :=
  k * T / 2 ^ n

theorem two_pow_pos (n : ℕ) : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n

theorem two_pow_ne_zero (n : ℕ) : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (two_pow_pos n)

/-- Dyadic point at k=0 is 0 -/
theorem dyadicPoint_zero (T : ℝ) (n : ℕ) : dyadicPoint T n 0 = 0 := by
  simp [dyadicPoint]

/-- Dyadic point at k=2^n is T -/
theorem dyadicPoint_last (T : ℝ) (n : ℕ) : dyadicPoint T n (2 ^ n) = T := by
  unfold dyadicPoint
  rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm, mul_div_cancel_right₀ T (two_pow_ne_zero n)]

/-- Dyadic point is non-negative when T ≥ 0 -/
theorem dyadicPoint_nonneg {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (k : ℕ) :
    0 ≤ dyadicPoint T n k := by
  unfold dyadicPoint
  exact div_nonneg (mul_nonneg (by positivity) hT) (two_pow_pos n).le

/-- Dyadic point is ≤ T when k ≤ 2^n and T ≥ 0 -/
theorem dyadicPoint_le_T {T : ℝ} (hT : 0 ≤ T) {n : ℕ} {k : ℕ} (hk : k ≤ 2 ^ n) :
    dyadicPoint T n k ≤ T := by
  unfold dyadicPoint
  rw [div_le_iff₀ (two_pow_pos n)]
  calc (k : ℝ) * T ≤ (2 ^ n : ℕ) * T :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hT
    _ = T * 2 ^ n := by rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm]

/-- Dyadic point is in [0, T] when k ≤ 2^n and T ≥ 0 -/
theorem dyadicPoint_mem_Icc {T : ℝ} (hT : 0 ≤ T) {n : ℕ} {k : ℕ} (hk : k ≤ 2 ^ n) :
    dyadicPoint T n k ∈ Set.Icc 0 T :=
  ⟨dyadicPoint_nonneg hT n k, dyadicPoint_le_T hT hk⟩

/-- Monotonicity: k₁ ≤ k₂ implies dyadicPoint k₁ ≤ dyadicPoint k₂ (for T ≥ 0) -/
theorem dyadicPoint_mono {T : ℝ} (hT : 0 ≤ T) (n : ℕ) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) :
    dyadicPoint T n k₁ ≤ dyadicPoint T n k₂ := by
  unfold dyadicPoint
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hT) (two_pow_pos n).le

/-- Strict monotonicity for T > 0 -/
theorem dyadicPoint_strictMono {T : ℝ} (hT : 0 < T) (n : ℕ) {k₁ k₂ : ℕ} (hk : k₁ < k₂) :
    dyadicPoint T n k₁ < dyadicPoint T n k₂ := by
  unfold dyadicPoint
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hk) hT) (two_pow_pos n)

/-- Spacing between adjacent dyadic points -/
theorem dyadicPoint_spacing (T : ℝ) (n : ℕ) (k : ℕ) :
    dyadicPoint T n (k + 1) - dyadicPoint T n k = T / 2 ^ n := by
  unfold dyadicPoint
  rw [Nat.cast_succ]
  ring

/-- Absolute value of spacing -/
theorem dyadicPoint_spacing_abs {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (k : ℕ) :
    |dyadicPoint T n (k + 1) - dyadicPoint T n k| = T / 2 ^ n := by
  rw [dyadicPoint_spacing]
  exact abs_of_nonneg (div_nonneg hT (two_pow_pos n).le)

/-! ## Refinement: Level n embeds into level n+1 -/

/-- A dyadic point at level n equals a dyadic point at level n+1 with doubled index -/
theorem dyadicPoint_level_succ (T : ℝ) (n : ℕ) (k : ℕ) :
    dyadicPoint T n k = dyadicPoint T (n + 1) (2 * k) := by
  unfold dyadicPoint
  rw [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  ring

/-- Between two consecutive dyadic points at level n, there is a midpoint at level n+1 -/
theorem dyadicPoint_midpoint (T : ℝ) (n : ℕ) (k : ℕ) :
    dyadicPoint T (n + 1) (2 * k + 1) =
    (dyadicPoint T n k + dyadicPoint T n (k + 1)) / 2 := by
  unfold dyadicPoint
  push_cast
  rw [pow_succ]
  ring

/-- General level embedding: dyadicPoint at level m equals dyadicPoint at level n
    with scaled index, for m ≤ n -/
theorem dyadicPoint_level_embed (T : ℝ) {m n : ℕ} (hmn : m ≤ n) (k : ℕ) :
    dyadicPoint T m k = dyadicPoint T n (2 ^ (n - m) * k) := by
  unfold dyadicPoint
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ℝ) ^ n = 2 ^ (n - m) * 2 ^ m from by rw [← pow_add, Nat.sub_add_cancel hmn]]
  have h2nm : (2 : ℝ) ^ (n - m) ≠ 0 := two_pow_ne_zero _
  field_simp

/-! ## Dyadic Floor -/

/-- The dyadic floor: the largest k such that dyadicPoint T n k ≤ t.
    Returns ⌊t · 2^n / T⌋ clamped to [0, 2^n]. -/
noncomputable def dyadicFloor (T : ℝ) (n : ℕ) (t : ℝ) : ℕ :=
  if T ≤ 0 then 0
  else min (2 ^ n) (Nat.floor (t * 2 ^ n / T))

/-- The dyadic floor index is at most 2^n -/
theorem dyadicFloor_le_pow (T : ℝ) (n : ℕ) (t : ℝ) :
    dyadicFloor T n t ≤ 2 ^ n := by
  unfold dyadicFloor
  split_ifs
  · exact Nat.zero_le _
  · exact min_le_left _ _

/-- Dyadic floor point is ≤ t (for t ∈ [0, T], T > 0) -/
theorem dyadicPoint_floor_le {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (n : ℕ) :
    dyadicPoint T n (dyadicFloor T n t) ≤ t := by
  unfold dyadicFloor dyadicPoint
  rw [if_neg (not_le.mpr hT)]
  by_cases hcase : Nat.floor (t * 2 ^ n / T) ≤ 2 ^ n
  · rw [min_eq_right hcase]
    rw [div_le_iff₀ (two_pow_pos n)]
    have hx_nn : 0 ≤ t * 2 ^ n / T :=
      div_nonneg (mul_nonneg ht.1 (two_pow_pos n).le) hT.le
    calc ↑(Nat.floor (t * 2 ^ n / T)) * T
        ≤ (t * 2 ^ n / T) * T := by
          exact mul_le_mul_of_nonneg_right (Nat.floor_le hx_nn) hT.le
      _ = t * 2 ^ n := by field_simp
  · -- This case is impossible: t ≤ T implies floor(t·2^n/T) ≤ 2^n
    exfalso; push_neg at hcase
    have hx_nn : 0 ≤ t * 2 ^ n / T :=
      div_nonneg (mul_nonneg ht.1 (two_pow_pos n).le) hT.le
    have h_floor_le_x : (↑(Nat.floor (t * 2 ^ n / T)) : ℝ) ≤ t * 2 ^ n / T :=
      Nat.floor_le hx_nn
    have h_x_le_2n : t * 2 ^ n / T ≤ (2 : ℝ) ^ n := by
      calc t * 2 ^ n / T = (t / T) * 2 ^ n := by ring
        _ ≤ 1 * 2 ^ n := by
            apply mul_le_mul_of_nonneg_right _ (two_pow_pos n).le
            exact (div_le_one (by linarith : (0 : ℝ) < T)).mpr ht.2
        _ = 2 ^ n := one_mul _
    have h_cast_lt : (↑(2 ^ n : ℕ) : ℝ) < ↑(Nat.floor (t * 2 ^ n / T)) :=
      Nat.cast_lt.mpr hcase
    rw [Nat.cast_pow, Nat.cast_ofNat] at h_cast_lt
    linarith

/-- t is less than the next dyadic point after the floor (for t < T, T > 0) -/
theorem lt_dyadicPoint_floor_succ {T : ℝ} (hT : 0 < T) {t : ℝ}
    (ht_nn : 0 ≤ t) (ht_lt : t < T) (n : ℕ) :
    t < dyadicPoint T n (dyadicFloor T n t + 1) := by
  unfold dyadicFloor dyadicPoint
  rw [if_neg (not_le.mpr hT)]
  have h2n_pos := two_pow_pos n
  have hT2n_pos : (0 : ℝ) < T / 2 ^ n := div_pos hT h2n_pos
  set x := t * 2 ^ n / T with hx_def
  have hx_nn : 0 ≤ x := div_nonneg (mul_nonneg ht_nn h2n_pos.le) hT.le
  have ht_eq : t = x * (T / 2 ^ n) := by simp only [hx_def]; field_simp
  by_cases hcase : ⌊x⌋₊ ≤ 2 ^ n
  · rw [min_eq_right hcase, Nat.cast_succ]
    rw [ht_eq, show (↑⌊x⌋₊ + 1) * T / 2 ^ n = (↑⌊x⌋₊ + 1) * (T / 2 ^ n) from by ring]
    exact mul_lt_mul_of_pos_right (Nat.lt_floor_add_one x) hT2n_pos
  · push_neg at hcase
    rw [min_eq_left hcase.le, Nat.cast_succ, Nat.cast_pow, Nat.cast_ofNat]
    have : ((2 : ℝ) ^ n + 1) * T / 2 ^ n = T + T / 2 ^ n := by field_simp
    rw [this]
    linarith

/-- The distance from t to its dyadic floor approximation is at most T / 2^n -/
theorem dyadicFloor_dist_le {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (n : ℕ) :
    t - dyadicPoint T n (dyadicFloor T n t) ≤ T / 2 ^ n := by
  have hle := dyadicPoint_floor_le hT ht n
  by_cases ht_eq : t = T
  · rw [ht_eq]
    have hdf : dyadicFloor T n T = 2 ^ n := by
      unfold dyadicFloor
      rw [if_neg (not_le.mpr hT)]
      have h1 : T * 2 ^ n / T = ↑(2 ^ n : ℕ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]; field_simp
      rw [h1, Nat.floor_natCast, min_self]
    rw [hdf, dyadicPoint_last, sub_self]
    exact div_nonneg hT.le (two_pow_pos n).le
  · push_neg at ht_eq
    have ht_lt : t < T := lt_of_le_of_ne ht.2 ht_eq
    have hlt := lt_dyadicPoint_floor_succ hT ht.1 ht_lt n
    linarith [dyadicPoint_spacing T n (dyadicFloor T n t)]

/-- The distance from t to its dyadic floor is non-negative -/
theorem dyadicFloor_dist_nonneg {T : ℝ} (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) (n : ℕ) :
    0 ≤ t - dyadicPoint T n (dyadicFloor T n t) :=
  sub_nonneg.mpr (dyadicPoint_floor_le hT ht n)

/-- The dyadic floor approximation converges to t from below -/
theorem dyadicFloor_tendsto {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    Tendsto (fun n => dyadicPoint T n (dyadicFloor T n t)) atTop (nhds t) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- For large n, T / 2^n < ε
  have hT_div : Tendsto (fun n => T / 2 ^ n) atTop (nhds 0) := by
    have : Tendsto (fun n => T * (1 / 2) ^ n) atTop (nhds (T * 0)) :=
      tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num))
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [Metric.tendsto_atTop] at hT_div
  obtain ⟨N, hN⟩ := hT_div ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_comm, Real.dist_eq]
  have hle := dyadicPoint_floor_le hT ht n
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  calc t - dyadicPoint T n (dyadicFloor T n t)
      ≤ T / 2 ^ n := dyadicFloor_dist_le hT ht n
    _ = |T / 2 ^ n - 0| := by rw [sub_zero, abs_of_nonneg (div_nonneg hT.le (two_pow_pos n).le)]
    _ = dist (T / 2 ^ n) 0 := (Real.dist_eq _ _).symm
    _ < ε := hN n hn

/-- The number of dyadic intervals at level n -/
theorem dyadicLevel_card (n : ℕ) : Finset.card (Finset.range (2 ^ n)) = 2 ^ n :=
  Finset.card_range _

end KolmogorovChentsov
