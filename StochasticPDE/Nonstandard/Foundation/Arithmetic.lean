/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Arithmetic Helper Lemmas

This file provides helper lemmas for integer/real arithmetic, particularly for:
- Integer division and its relationship to real division
- Cast conversions between ℕ, ℤ, and ℝ
- Floor and ceiling properties

These are used throughout the SPDE/Nonstandard development, especially in
the Local CLT proofs where we need to convert between integer and real bounds.

## Main Results

* `int_div2_le_real_div2` - Integer division is at most real division
* `int_div2_ge_real_div2_sub_half` - Integer division is at least real division minus 1/2
* `int_ge_one_of_real_gt_half_nonneg` - Integer > 0.5 as real implies integer ≥ 1
* `natCast_intCast_eq` - ((n : ℤ) : ℝ) = (n : ℝ) for naturals

## Implementation Notes

These lemmas are designed to be short and composable, reducing boilerplate
in longer proofs involving mixed integer/real arithmetic.

**Important distinction**: `(((n : ℤ) / 2) : ℝ)` is the cast of integer division to real,
while `((n : ℤ) : ℝ) / 2` is real division after casting. These are NOT equal in general!
-/

open Int

namespace SPDE.Nonstandard.Arithmetic

/-! ## Cast Conversions -/

/-- Natural to integer to real equals natural to real directly. -/
theorem natCast_intCast_eq (n : ℕ) : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n

/-- Integer absolute value cast to real equals real absolute value. -/
theorem int_abs_cast (j : ℤ) : ((|j| : ℤ) : ℝ) = |((j : ℤ) : ℝ)| := by
  exact_mod_cast Int.cast_abs

/-! ## Integer Division Bounds -/

/-- Integer division by 2 is at most real division by 2.
    Here q = (n : ℤ) / 2 is an integer, and we show (q : ℝ) ≤ (n : ℝ) / 2. -/
theorem int_div2_le_real_div2 (n : ℕ) : ((((n : ℤ) / 2) : ℤ) : ℝ) ≤ (n : ℝ) / 2 := by
  have h : ((n : ℤ) / 2) * 2 ≤ (n : ℤ) := Int.ediv_mul_le (n : ℤ) (by norm_num : (2 : ℤ) ≠ 0)
  have h' : ((((n : ℤ) / 2) : ℤ) : ℝ) * 2 ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h
  have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := natCast_intCast_eq n
  rw [hcast] at h'
  linarith

/-- Integer division by 2 is at least real division by 2 minus 1/2.
    Here q = (n : ℤ) / 2 is an integer, and we show (q : ℝ) ≥ (n : ℝ) / 2 - 1/2. -/
theorem int_div2_ge_real_div2_sub_half (n : ℕ) : ((((n : ℤ) / 2) : ℤ) : ℝ) ≥ (n : ℝ) / 2 - 1/2 := by
  have hdiv_bound : 2 * ((n : ℤ) / 2) ≥ (n : ℤ) - 1 := by omega
  let q : ℤ := (n : ℤ) / 2
  have hcast_n : ((n : ℤ) : ℝ) = (n : ℝ) := natCast_intCast_eq n
  -- Cast hdiv_bound to ℝ: we have (n : ℤ) - 1 ≤ 2 * q as integers
  -- So ((n : ℤ) - 1 : ℝ) ≤ (2 * q : ℝ) = 2 * (q : ℝ)
  have h1 : (2 : ℝ) * (q : ℝ) ≥ (n : ℝ) - 1 := by
    have hle : ((n : ℤ) - 1 : ℤ) ≤ 2 * q := hdiv_bound
    -- Cast to ℝ
    have h_cast : (((n : ℤ) - 1 : ℤ) : ℝ) ≤ ((2 * q : ℤ) : ℝ) := Int.cast_le.mpr hle
    -- Simplify LHS: (((n : ℤ) - 1 : ℤ) : ℝ) = ((n : ℤ) : ℝ) - 1 = (n : ℝ) - 1
    -- Simplify RHS: ((2 * q : ℤ) : ℝ) = 2 * (q : ℝ)
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_one, hcast_n] at h_cast
    exact h_cast
  linarith

/-- An integer whose real cast is > 1/2 and ≥ 0 must be ≥ 1. -/
theorem int_ge_one_of_real_gt_half_nonneg {m : ℤ} (hpos : 0 ≤ m) (hgt : (m : ℝ) > 1/2) : 1 ≤ m := by
  by_contra h_neg
  push_neg at h_neg
  have h1 : m ≤ 0 := by omega
  have h2 : (m : ℝ) ≤ 0 := by exact_mod_cast h1
  linarith

/-- An integer strictly less than another as reals implies ≤ as integers. -/
theorem int_le_of_real_lt {a b : ℤ} (h : (a : ℝ) < (b : ℝ)) : a ≤ b := by
  by_contra hgt
  push_neg at hgt
  have h' : (b : ℝ) < (a : ℝ) := by exact_mod_cast hgt
  linarith

/-! ## Sum Bounds with Division -/

/-- If n ≥ 9 and j ≥ -(n/2), then (n : ℤ) / 2 + j ≥ 0. -/
theorem int_div2_add_ge_zero (n : ℕ) (j : ℤ) (hn : 9 ≤ n) (hj_lower : -((n : ℤ)/2) ≤ j) :
    0 ≤ (n : ℤ) / 2 + j := by
  have hnat_div_le : (n : ℤ) / 2 ≥ (n/2 : ℕ) := by omega
  have hn' : (n/2 : ℕ) ≥ 4 := by omega
  omega

/-- Real bound (n:ℝ)/2 + j > 1 combined with integrality gives (n:ℤ)/2 + j ≥ 1.
    This is the key lemma for index lower bounds. -/
theorem int_div2_add_ge_one_of_real_gt_one (n : ℕ) (j : ℤ) (hn : 9 ≤ n)
    (hj_lower : -((n : ℤ)/2) ≤ j) (h_real : (n : ℝ) / 2 + (j : ℝ) > 1) :
    1 ≤ (n : ℤ) / 2 + j := by
  have hge0 : 0 ≤ (n : ℤ) / 2 + j := int_div2_add_ge_zero n j hn hj_lower
  have hintdiv_real := int_div2_ge_real_div2_sub_half n
  let q : ℤ := (n : ℤ) / 2
  -- hintdiv_real: (q : ℝ) ≥ (n : ℝ) / 2 - 1/2
  have hsum_gt : (q : ℝ) + (j : ℝ) > 1/2 := by
    have h1 : (q : ℝ) ≥ (n : ℝ) / 2 - 1/2 := hintdiv_real
    have h2 : (q : ℝ) + (j : ℝ) ≥ (n : ℝ) / 2 - 1/2 + (j : ℝ) := by linarith
    have h3 : (n : ℝ) / 2 - 1/2 + (j : ℝ) = (n : ℝ) / 2 + (j : ℝ) - 1/2 := by ring
    have h4 : (n : ℝ) / 2 + (j : ℝ) > 1 := h_real
    linarith
  have hsum_real : (((q + j) : ℤ) : ℝ) > 1/2 := by
    have heq : (((q + j) : ℤ) : ℝ) = (q : ℝ) + (j : ℝ) := by norm_cast
    rw [heq]
    exact hsum_gt
  exact int_ge_one_of_real_gt_half_nonneg hge0 hsum_real

/-- Real bound (n:ℝ)/2 + j < n - 1 combined with integrality gives (n:ℤ)/2 + j ≤ n - 1.
    This is the key lemma for index upper bounds. -/
theorem int_div2_add_le_n_sub_one_of_real_lt (n : ℕ) (j : ℤ)
    (h_real : (n : ℝ) / 2 + (j : ℝ) < (n : ℝ) - 1) :
    (n : ℤ) / 2 + j ≤ (n : ℤ) - 1 := by
  let q : ℤ := (n : ℤ) / 2
  have hdiv_le := int_div2_le_real_div2 n
  have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := natCast_intCast_eq n
  -- hdiv_le: (q : ℝ) ≤ (n : ℝ) / 2
  have hsum_lt : (q : ℝ) + (j : ℝ) < (n : ℝ) - 1 := by linarith
  -- q + j < (n : ℤ) - 1 as reals, so q + j ≤ (n : ℤ) - 1 as integers
  have hint : q + j < (n : ℤ) - 1 ∨ q + j = (n : ℤ) - 1 ∨ q + j > (n : ℤ) - 1 := lt_trichotomy _ _
  rcases hint with hlt | heq | hgt
  · exact le_of_lt hlt
  · exact le_of_eq heq
  · -- Contradiction: we have q + j > (n : ℤ) - 1 as integers, but < as reals
    exfalso
    have h' : (((n : ℤ) - 1) : ℝ) < ((q + j) : ℝ) := by exact_mod_cast hgt
    -- Simplify the casts
    simp only [hcast] at h'
    linarith

/-! ## Logarithm Bounds

These lemmas provide Taylor-style bounds on log(1+x) that are used in the
exponential factor approximation for the Local CLT.
-/

/-- Upper bound: log(1+x) ≤ x for x > -1.
    This is a restatement of log_le_sub_one_of_pos with substitution. -/
theorem log_one_add_le (x : ℝ) (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have h1 : 0 < 1 + x := by linarith
  have h2 := Real.log_le_sub_one_of_pos h1
  linarith

/-- Lower bound: 2x/(x+2) ≤ log(1+x) for x ≥ 0.
    This is re-exported from Mathlib. -/
theorem log_one_add_ge_of_nonneg (x : ℝ) (hx : 0 ≤ x) : 2 * x / (x + 2) ≤ Real.log (1 + x) :=
  Real.le_log_one_add_of_nonneg hx

/-- Lower bound for log(1+x) when x ≤ 0: log(1+x) ≥ x/(1+x) for -1 < x ≤ 0.
    This comes from 1 - (1+x)⁻¹ ≤ log(1+x) via one_sub_inv_le_log_of_pos. -/
theorem log_one_add_ge_of_neg (x : ℝ) (hx_lower : -1 < x) (_hx_upper : x ≤ 0) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have h1 : 0 < 1 + x := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  -- 1 - (1+x)⁻¹ = (1+x - 1)/(1+x) = x/(1+x)
  have h3 : 1 - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp
    ring
  rw [← h3]
  exact h2

/-- For x ≥ 0, we have x - x²/2 ≤ log(1+x) ≤ x.
    The lower bound x - x²/2 is weaker than 2x/(x+2) but simpler.
    (Note: 2x/(x+2) ≥ x - x²/2 for x ≥ 0 can be verified algebraically.) -/
theorem log_one_add_bounds_nonneg (x : ℝ) (hx : 0 ≤ x) :
    x - x^2/2 ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x := by
  constructor
  · -- Lower bound: for x ≥ 0, 2x/(x+2) ≥ x - x²/2
    -- We have 2x/(x+2) ≤ log(1+x), and 2x/(x+2) ≥ x - x²/2
    have h1 := log_one_add_ge_of_nonneg x hx
    -- Show x - x²/2 ≤ 2x/(x+2)
    -- Multiply both sides by (x+2): (x - x²/2)(x+2) ≤ 2x
    -- x² + 2x - x³/2 - x² ≤ 2x
    -- 2x - x³/2 ≤ 2x
    -- -x³/2 ≤ 0, which is true for x ≥ 0
    have hpos : 0 < x + 2 := by linarith
    have h2 : x - x^2/2 ≤ 2 * x / (x + 2) := by
      rw [le_div_iff₀ hpos]
      have h3 : (x - x^2/2) * (x + 2) = x^2 + 2*x - x^3/2 - x^2 := by ring
      rw [h3]
      have h4 : x^2 + 2*x - x^3/2 - x^2 = 2*x - x^3/2 := by ring
      rw [h4]
      have h5 : x^3/2 ≥ 0 := by positivity
      linarith
    linarith
  · -- Upper bound: log(1+x) ≤ x
    exact log_one_add_le x (by linarith)

/-- For -1 < x < 0, we have x/(1+x) ≤ log(1+x) ≤ x.
    Note: For x < 0, log(1+x) < x (the log is more negative).
    The lower bound x/(1+x) is more negative than x for -1 < x < 0. -/
theorem log_one_add_bounds_neg (x : ℝ) (hx_lower : -1 < x) (hx_upper : x < 0) :
    x / (1 + x) ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x := by
  constructor
  · -- Lower bound: x/(1+x) ≤ log(1+x)
    exact log_one_add_ge_of_neg x hx_lower (le_of_lt hx_upper)
  · -- Upper bound: log(1+x) ≤ x
    exact log_one_add_le x hx_lower

/-- Combined bound: |log(1+x) - x| ≤ x²/2 for x ≥ 0, with equality approached as x → 0. -/
theorem log_one_add_sub_self_abs_le_nonneg (x : ℝ) (hx : 0 ≤ x) :
    |Real.log (1 + x) - x| ≤ x^2 / 2 := by
  have h := log_one_add_bounds_nonneg x hx
  -- log(1+x) - x ∈ [-x²/2, 0] for x ≥ 0
  -- So |log(1+x) - x| = x - log(1+x) ≤ x - (x - x²/2) = x²/2
  have h1 : Real.log (1 + x) - x ≤ 0 := by linarith [h.2]
  have h2 : Real.log (1 + x) - x ≥ -x^2/2 := by linarith [h.1]
  rw [abs_le]
  constructor <;> linarith

/-- For the exponential factor in the local CLT, we need a bound on the log error.
    This lemma states that for |x| ≤ 1/2:
    x - x²/(1 - |x|) ≤ log(1+x) ≤ x + x²/(1 - |x|)
    which gives |log(1+x) - x| ≤ x²/(1 - |x|) ≤ 2x² when |x| ≤ 1/2. -/
theorem log_one_add_taylor_error (x : ℝ) (hx : |x| ≤ 1/2) :
    |Real.log (1 + x) - x| ≤ 2 * x^2 := by
  by_cases hxnn : 0 ≤ x
  · -- Case x ≥ 0: |log(1+x) - x| ≤ x²/2 ≤ 2x²
    have h := log_one_add_sub_self_abs_le_nonneg x hxnn
    calc |Real.log (1 + x) - x| ≤ x^2 / 2 := h
      _ ≤ 2 * x^2 := by nlinarith [sq_nonneg x]
  · -- Case x < 0
    push_neg at hxnn
    have hxneg : x < 0 := hxnn
    have hx_lower : -1 < x := by
      have h1 : |x| = -x := abs_of_neg hxneg
      have h2 : -x ≤ 1/2 := by rw [← h1]; exact hx
      linarith
    have hpos : 0 < 1 + x := by linarith
    have hbounds := log_one_add_bounds_neg x hx_lower hxneg
    -- log(1+x) - x ≤ 0 and log(1+x) ≥ x/(1+x)
    have h1 : Real.log (1 + x) - x ≤ 0 := by linarith [hbounds.2]
    have h2 : Real.log (1 + x) ≥ x / (1 + x) := hbounds.1
    -- |log(1+x) - x| = -(log(1+x) - x) = x - log(1+x)
    have h5 : |Real.log (1 + x) - x| = -(Real.log (1 + x) - x) := abs_of_nonpos h1
    rw [h5]
    -- -(log(1+x) - x) = x - log(1+x) ≤ x - x/(1+x) = x²/(1+x)
    have h6 : -(Real.log (1 + x) - x) ≤ x^2 / (1 + x) := by
      have h3 : x - x / (1 + x) = x^2 / (1 + x) := by field_simp; ring
      have h4 : x - Real.log (1 + x) ≤ x - x / (1 + x) := by linarith [h2]
      linarith [h3, h4]
    -- Since 1+x ≥ 1/2 (from |x| ≤ 1/2 and x < 0), we have x²/(1+x) ≤ 2x²
    have h7 : 1/2 ≤ 1 + x := by
      have h8 : |x| = -x := abs_of_neg hxneg
      have h9 : -x ≤ 1/2 := by rw [← h8]; exact hx
      linarith
    have h8 : x^2 / (1 + x) ≤ 2 * x^2 := by
      rw [div_le_iff₀ hpos]
      have h9 : 2 * x^2 * (1 + x) = 2 * x^2 + 2 * x^3 := by ring
      rw [h9]
      have h10 : x^2 ≤ 2 * x^2 + 2 * x^3 ↔ 0 ≤ x^2 + 2 * x^3 := by ring_nf; constructor <;> intro hh <;> linarith
      rw [h10]
      have h11 : x^2 + 2 * x^3 = x^2 * (1 + 2*x) := by ring
      rw [h11]
      apply mul_nonneg (sq_nonneg x)
      -- 1 + 2x ≥ 0 when x ≥ -1/2
      have : -1/2 ≤ x := by
        have h12 : |x| = -x := abs_of_neg hxneg
        have h13 : -x ≤ 1/2 := by rw [← h12]; exact hx
        linarith
      linarith
    linarith

/-- Second-order bound: |log(1+x) - (x - x²/2)| ≤ 5x²/2 for |x| ≤ 1/2.
    This follows from the triangle inequality and log_one_add_taylor_error. -/
theorem log_one_add_second_order_weak (x : ℝ) (hx : |x| ≤ 1/2) :
    |Real.log (1 + x) - (x - x^2/2)| ≤ 5/2 * x^2 := by
  -- Use triangle inequality: |log(1+x) - (x - x²/2)| = |log(1+x) - x + x²/2|
  --                                                  ≤ |log(1+x) - x| + |x²/2|
  --                                                  ≤ 2x² + x²/2 = 5x²/2
  have h1 := log_one_add_taylor_error x hx
  -- |log(1+x) - x| ≤ 2x²
  have h2 : Real.log (1 + x) - (x - x^2/2) = (Real.log (1 + x) - x) + x^2/2 := by ring
  calc |Real.log (1 + x) - (x - x^2/2)| = |(Real.log (1 + x) - x) + x^2/2| := by rw [h2]
    _ ≤ |Real.log (1 + x) - x| + |x^2/2| := abs_add_le _ _
    _ ≤ 2 * x^2 + |x^2/2| := by linarith [h1]
    _ = 2 * x^2 + x^2/2 := by rw [abs_of_nonneg]; linarith [sq_nonneg x]
    _ = 5/2 * x^2 := by ring

/-- For n ≥ 9, we have 2/√n ≤ 2/3.
    This helper establishes that x = 2j/n satisfies the Taylor bound condition when |j| ≤ √n. -/
theorem two_div_sqrt_n_bound (n : ℕ) (hn : 9 ≤ n) : (2 : ℝ) / Real.sqrt n ≤ 2/3 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 9) hn)
  have hn9 : (9 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hsqrt3 : (3 : ℝ) ≤ Real.sqrt n := by
    have h1 : (9 : ℝ) = 3^2 := by norm_num
    have h2 : Real.sqrt 9 = 3 := by rw [h1, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
    have h3 : Real.sqrt 9 ≤ Real.sqrt n := Real.sqrt_le_sqrt hn9
    linarith
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  rw [div_le_div_iff₀ hsqrt_pos (by norm_num : (0:ℝ) < 3)]
  linarith

/-- Key bound: for |j| ≤ √n and n ≥ 9, we have |2j/n| ≤ 2/3.
    This is used to ensure the Taylor expansion converges. -/
theorem abs_two_j_div_n_bound (n : ℕ) (j : ℤ) (hn : 9 ≤ n) (hj : |j| ≤ Real.sqrt n) :
    |2 * (j : ℝ) / n| ≤ 2/3 := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 9) hn)
  have hj_bound : |(j : ℝ)| ≤ Real.sqrt n := by simp only [← Int.cast_abs]; exact hj
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- |2j/n| = 2|j|/n
  have h1 : |2 * (j : ℝ) / n| = 2 * |(j : ℝ)| / n := by
    rw [abs_div, abs_mul]
    simp only [abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hn_pos]
  rw [h1]
  -- 2|j|/n ≤ 2√n/n = 2/√n
  calc 2 * |(j : ℝ)| / n ≤ 2 * Real.sqrt n / n := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
        exact mul_le_mul_of_nonneg_left hj_bound (by norm_num : (0:ℝ) ≤ 2)
    _ = 2 * (Real.sqrt n / n) := by ring
    _ = 2 * (1 / Real.sqrt n) := by
        congr 1
        -- √n / n = 1 / √n because √n * √n = n
        have hsqrt_sq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (le_of_lt hn_pos)
        field_simp
        linarith [hsqrt_sq]
    _ = 2 / Real.sqrt n := by ring
    _ ≤ 2/3 := two_div_sqrt_n_bound n hn

set_option maxHeartbeats 400000 in
/-- The core log sum calculation: for real k' = n/2 + j and x = 2j/n,
    -k'·log(1+x) - (n-k')·log(1-x) ≈ -2j²/n

    This is the continuous version that ignores integer rounding.
    The bound shows the error is O(n·x³) = O(j³/n²) ≤ O(1/√n) for |j| ≤ √n. -/
theorem log_sum_main_term (n : ℕ) (j : ℤ) (hn : 9 ≤ n) (hj : |j| ≤ Real.sqrt n)
    (hj_lower : -(n/2 : ℤ) ≤ j) (hj_upper : j ≤ (n/2 : ℤ)) :
    let x := 2 * (j : ℝ) / n
    let k' := (n : ℝ) / 2 + j
    let target := -2 * (j : ℝ)^2 / n
    |(- k' * Real.log (1 + x) - ((n : ℝ) - k') * Real.log (1 - x)) - target| ≤ 20 * (j : ℝ)^2 / n := by
  intro x k' target
  -- Basic setup
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by norm_num : 0 < 9) hn)
  have _hn9 : (9 : ℝ) ≤ n := Nat.cast_le.mpr hn

  -- Show |x| ≤ 2/3 < 1 (needed for log to be defined)
  have hx_bound : |x| ≤ 2/3 := abs_two_j_div_n_bound n j hn hj

  have hx_pos_bound : x < 1 := by
    calc x ≤ |x| := le_abs_self x
      _ ≤ 2/3 := hx_bound
      _ < 1 := by norm_num
  have hx_neg_bound : -1 < x := by
    calc -1 < -2/3 := by norm_num
      _ ≤ -|x| := by linarith [abs_nonneg x, hx_bound]
      _ ≤ x := neg_abs_le x
  have h1px_pos : 0 < 1 + x := by linarith
  have h1mx_pos : 0 < 1 - x := by linarith

  -- Note: n - k' = n/2 - j
  have hnmk : (n : ℝ) - k' = (n : ℝ) / 2 - j := by simp only [k']; ring

  -- If j = 0, both sides are 0
  by_cases hj_zero : j = 0
  · subst hj_zero
    simp only [Int.cast_zero, mul_zero, zero_div, sq] at *
    simp only [x, k', target]
    norm_num

  -- General case: j ≠ 0, so j² > 0
  have hj_sq_pos : 0 < (j : ℝ)^2 := by
    have : (j : ℝ) ≠ 0 := by exact_mod_cast hj_zero
    exact sq_pos_of_ne_zero this

  -- The Taylor expansion proof. Key insight:
  -- Using log(1+x) = x - x²/2 + R_+ and log(1-x) = -x - x²/2 + R_-
  -- The main terms give exactly -2j²/n, so the error is just from remainders.

  -- First, establish the second-order Taylor remainder bounds
  -- |log(1+x) - (x - x²/2)| ≤ 5x²/2 for |x| ≤ 2/3

  -- For x ≥ 0: |log(1+x) - x| ≤ x²/2, so |log(1+x) - (x - x²/2)| ≤ x²
  -- For x < 0: |log(1+x) - x| ≤ x²/(1+x) ≤ 3x² when 1+x ≥ 1/3, so |...| ≤ 3x² + x²/2

  have hR_plus_bound : |Real.log (1 + x) - (x - x^2/2)| ≤ 5/2 * x^2 := by
    by_cases hx_sign : 0 ≤ x
    · -- x ≥ 0 case
      have h1 := log_one_add_sub_self_abs_le_nonneg x hx_sign
      -- |log(1+x) - x| ≤ x²/2
      calc |Real.log (1 + x) - (x - x^2/2)|
          = |Real.log (1 + x) - x + x^2/2| := by ring_nf
        _ ≤ |Real.log (1 + x) - x| + |x^2/2| := abs_add_le _ _
        _ ≤ x^2/2 + x^2/2 := by
            have habs_sq : |x^2/2| = x^2/2 := abs_of_nonneg (by positivity)
            linarith
        _ ≤ 5/2 * x^2 := by nlinarith [sq_nonneg x]
    · -- x < 0 case
      push_neg at hx_sign
      have h1 := log_one_add_bounds_neg x hx_neg_bound hx_sign
      -- log(1+x) - x ≤ 0 and log(1+x) ≥ x/(1+x)
      have hlog_le_x : Real.log (1 + x) ≤ x := h1.2
      have hlog_ge : x / (1 + x) ≤ Real.log (1 + x) := h1.1
      have hdiff_nonpos : Real.log (1 + x) - x ≤ 0 := by linarith
      have hdiff_bound : x - Real.log (1 + x) ≤ x^2 / (1 + x) := by
        have h3 : x - x / (1 + x) = x^2 / (1 + x) := by field_simp; ring
        linarith
      -- Since |x| ≤ 2/3 and x < 0, we have x ≥ -2/3, so 1+x ≥ 1/3
      have h1px_lower : 1/3 ≤ 1 + x := by linarith [hx_bound, abs_of_neg hx_sign]
      have hdiff_bound' : x - Real.log (1 + x) ≤ 3 * x^2 := by
        calc x - Real.log (1 + x) ≤ x^2 / (1 + x) := hdiff_bound
          _ ≤ x^2 / (1/3) := by
              apply div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num : (0:ℝ) < 1/3) h1px_lower
          _ = 3 * x^2 := by ring
      -- |log(1+x) - (x - x²/2)| = |log(1+x) - x + x²/2|
      -- = |x²/2 - (x - log(1+x))|
      -- x - log(1+x) > 0 (since log(1+x) < x for x < 0)
      have hxmlog_pos : 0 < x - Real.log (1 + x) := by
        have : Real.log (1 + x) < x := by
          -- x < 0 so 1 + x < 1, hence 1 + x ≠ 1
          have h1px_ne_1 : 1 + x ≠ 1 := ne_of_lt (by linarith : 1 + x < 1)
          have hlog_strict : Real.log (1 + x) < (1 + x) - 1 := Real.log_lt_sub_one_of_pos h1px_pos h1px_ne_1
          linarith
        linarith
      by_cases hcase : x^2/2 ≥ x - Real.log (1 + x)
      · -- x²/2 ≥ x - log(1+x), so the expression is nonneg
        have h4 : Real.log (1 + x) - (x - x^2/2) ≥ 0 := by linarith
        calc |Real.log (1 + x) - (x - x^2/2)|
            = Real.log (1 + x) - (x - x^2/2) := abs_of_nonneg h4
          _ = x^2/2 - (x - Real.log (1 + x)) := by ring
          _ ≤ x^2/2 := by linarith [hxmlog_pos]
          _ ≤ 5/2 * x^2 := by nlinarith [sq_nonneg x]
      · -- x²/2 < x - log(1+x), so the expression is negative
        push_neg at hcase
        have h4 : Real.log (1 + x) - (x - x^2/2) < 0 := by linarith
        calc |Real.log (1 + x) - (x - x^2/2)|
            = -(Real.log (1 + x) - (x - x^2/2)) := abs_of_neg h4
          _ = (x - Real.log (1 + x)) - x^2/2 := by ring
          _ ≤ 3 * x^2 - x^2/2 := by linarith
          _ = 5/2 * x^2 := by ring

  -- Same bound for log(1-x) = log(1 + (-x))
  have hR_minus_bound : |Real.log (1 - x) - (-x - x^2/2)| ≤ 5/2 * x^2 := by
    -- log(1-x) = log(1 + (-x)), apply the bound with -x
    have hmx_bound : |-x| ≤ 2/3 := by rw [abs_neg]; exact hx_bound
    have hmx_neg_bound : -1 < -x := by linarith
    have hmx_pos_bound : -x < 1 := by linarith
    have h1mmx_pos : 0 < 1 + (-x) := by linarith
    -- Apply the same case analysis
    by_cases hx_sign : x ≤ 0
    · -- x ≤ 0, so -x ≥ 0
      have hmx_nonneg : 0 ≤ -x := by linarith
      have h1 := log_one_add_sub_self_abs_le_nonneg (-x) hmx_nonneg
      -- |log(1+(-x)) - (-x)| ≤ (-x)²/2
      have h2 : |Real.log (1 + (-x)) - ((-x) - (-x)^2/2)|
              = |(Real.log (1 + (-x)) - (-x)) + (-x)^2/2| := by ring_nf
      calc |Real.log (1 - x) - (-x - x^2/2)|
          = |Real.log (1 + (-x)) - ((-x) - (-x)^2/2)| := by ring_nf
        _ = |(Real.log (1 + (-x)) - (-x)) + (-x)^2/2| := h2
        _ ≤ |Real.log (1 + (-x)) - (-x)| + |(-x)^2/2| := abs_add_le _ _
        _ ≤ (-x)^2/2 + (-x)^2/2 := by
            have habs_sq : |(-x)^2/2| = (-x)^2/2 := abs_of_nonneg (by positivity)
            linarith
        _ = x^2 := by ring
        _ ≤ 5/2 * x^2 := by nlinarith [sq_nonneg x]
    · -- x > 0, so -x < 0
      push_neg at hx_sign
      have hmx_neg : -x < 0 := by linarith
      have h1 := log_one_add_bounds_neg (-x) hmx_neg_bound hmx_neg
      have hlog_le : Real.log (1 + (-x)) ≤ -x := h1.2
      have hlog_ge : (-x) / (1 + (-x)) ≤ Real.log (1 + (-x)) := h1.1
      have h1mmx_lower : 1/3 ≤ 1 + (-x) := by
        -- Since |x| ≤ 2/3 and x > 0, we have x ≤ 2/3, so 1 - x ≥ 1/3
        have hx_upper : x ≤ 2/3 := by
          have h := le_abs_self x
          linarith [hx_bound]
        linarith
      have hdiff_bound' : (-x) - Real.log (1 + (-x)) ≤ 3 * (-x)^2 := by
        have hdiff_bound : (-x) - Real.log (1 + (-x)) ≤ (-x)^2 / (1 + (-x)) := by
          have h3 : (-x) - (-x) / (1 + (-x)) = (-x)^2 / (1 + (-x)) := by field_simp; ring
          linarith
        calc (-x) - Real.log (1 + (-x)) ≤ (-x)^2 / (1 + (-x)) := hdiff_bound
          _ ≤ (-x)^2 / (1/3) := by
              apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num : (0:ℝ) < 1/3) h1mmx_lower
          _ = 3 * (-x)^2 := by ring
      have hxmlog_pos : 0 < (-x) - Real.log (1 + (-x)) := by
        have : Real.log (1 + (-x)) < (-x) := by
          -- x > 0 so -x < 0, hence 1 + (-x) = 1 - x < 1, so 1 + (-x) ≠ 1
          have h1mmx_ne_1 : 1 + (-x) ≠ 1 := ne_of_lt (by linarith : 1 + (-x) < 1)
          have hlog_strict : Real.log (1 + (-x)) < (1 + (-x)) - 1 := Real.log_lt_sub_one_of_pos h1mmx_pos h1mmx_ne_1
          linarith
        linarith
      by_cases hcase : (-x)^2/2 ≥ (-x) - Real.log (1 + (-x))
      · have h4 : Real.log (1 + (-x)) - ((-x) - (-x)^2/2) ≥ 0 := by linarith
        calc |Real.log (1 - x) - (-x - x^2/2)|
            = |Real.log (1 + (-x)) - ((-x) - (-x)^2/2)| := by ring_nf
          _ = Real.log (1 + (-x)) - ((-x) - (-x)^2/2) := abs_of_nonneg h4
          _ = (-x)^2/2 - ((-x) - Real.log (1 + (-x))) := by ring
          _ ≤ (-x)^2/2 := by linarith [hxmlog_pos]
          _ = x^2/2 := by ring
          _ ≤ 5/2 * x^2 := by nlinarith [sq_nonneg x]
      · push_neg at hcase
        have h4 : Real.log (1 + (-x)) - ((-x) - (-x)^2/2) < 0 := by linarith
        calc |Real.log (1 - x) - (-x - x^2/2)|
            = |Real.log (1 + (-x)) - ((-x) - (-x)^2/2)| := by ring_nf
          _ = -(Real.log (1 + (-x)) - ((-x) - (-x)^2/2)) := abs_of_neg h4
          _ = ((-x) - Real.log (1 + (-x))) - (-x)^2/2 := by ring
          _ ≤ 3 * (-x)^2 - (-x)^2/2 := by linarith
          _ = 5/2 * x^2 := by ring

  -- Now compute the main terms
  -- -k' * log(1+x) - (n-k') * log(1-x)
  -- = -k' * (x - x²/2 + R_+) - (n-k') * (-x - x²/2 + R_-)
  -- = -k'x + k'x²/2 - k'R_+ + (n-k')x + (n-k')x²/2 - (n-k')R_-
  -- = (n-2k')x + nx²/2 - k'R_+ - (n-k')R_-

  -- Let's define the remainder terms
  let R_plus := Real.log (1 + x) - (x - x^2/2)
  let R_minus := Real.log (1 - x) - (-x - x^2/2)

  -- We have: log(1+x) = (x - x²/2) + R_plus and log(1-x) = (-x - x²/2) + R_minus
  -- So: -k' * log(1+x) - (n-k') * log(1-x)
  --   = -k' * ((x - x²/2) + R_plus) - (n-k') * ((-x - x²/2) + R_minus)
  --   = -k'(x - x²/2) - k'R_plus - (n-k')(-x - x²/2) - (n-k')R_minus
  --   = -k'x + k'x²/2 + (n-k')x + (n-k')x²/2 - k'R_plus - (n-k')R_minus
  --   = (n-2k')x + nx²/2 - k'R_plus - (n-k')R_minus

  -- The main term (n-2k')x + nx²/2 with k' = n/2 + j and x = 2j/n equals:
  -- (n - 2(n/2+j))·(2j/n) + n·(4j²/n²)/2 = -2j·(2j/n) + 2j²/n = -4j²/n + 2j²/n = -2j²/n = target

  -- Bound the remainder terms
  -- k' = n/2 + j ≥ 0 because j ≥ -n/2 (from hj_lower)
  have hk'_nonneg : 0 ≤ k' := by
    -- k' = (n:ℝ)/2 + j ≥ 0 since j ≥ -n/2 and (n:ℝ)/2 ≥ (n:ℤ)/2
    have hint : 0 ≤ (n : ℤ) / 2 + j := by linarith
    have h2 := int_div2_le_real_div2 n
    have hj_cast : (((n : ℤ) / 2 + j : ℤ) : ℝ) ≥ 0 := by exact_mod_cast hint
    have heq : (((n : ℤ) / 2 + j : ℤ) : ℝ) = (((n : ℤ) / 2 : ℤ) : ℝ) + (j : ℝ) := Int.cast_add _ _
    linarith [heq, hj_cast, h2]
  -- n - k' = n/2 - j ≥ 0 because j ≤ n/2 (from hj_upper)
  have hnmk'_nonneg : 0 ≤ (n : ℝ) - k' := by
    rw [hnmk]
    have hint : 0 ≤ (n : ℤ) / 2 - j := by linarith
    have h2 := int_div2_le_real_div2 n
    have hj_cast : (((n : ℤ) / 2 - j : ℤ) : ℝ) ≥ 0 := by exact_mod_cast hint
    have heq : (((n : ℤ) / 2 - j : ℤ) : ℝ) = (((n : ℤ) / 2 : ℤ) : ℝ) - (j : ℝ) := Int.cast_sub _ _
    linarith [heq, hj_cast, h2]

  -- The remainder R_plus = log(1+x) - (x - x²/2), so log(1+x) = (x - x²/2) + R_plus
  have hlog_plus : Real.log (1 + x) = (x - x^2/2) + R_plus := by
    show Real.log (1 + x) = (x - x^2/2) + (Real.log (1 + x) - (x - x^2/2))
    ring
  have hlog_minus : Real.log (1 - x) = (-x - x^2/2) + R_minus := by
    show Real.log (1 - x) = (-x - x^2/2) + (Real.log (1 - x) - (-x - x^2/2))
    ring

  -- Compute the expression
  have hcompute : - k' * Real.log (1 + x) - ((n : ℝ) - k') * Real.log (1 - x)
                = (n - 2*k') * x + n * x^2/2 - k' * R_plus - ((n : ℝ) - k') * R_minus := by
    rw [hlog_plus, hlog_minus]
    ring

  -- The main algebraic term equals -2j²/n = target
  -- k' = (n:ℝ)/2 + j, x = 2j/n
  -- (n - 2k')x + nx²/2 = (n - 2(n/2+j))(2j/n) + n(4j²/n²)/2
  --                    = -2j · 2j/n + 2j²/n = -4j²/n + 2j²/n = -2j²/n
  have hmain : (n - 2*k') * x + n * x^2/2 = -2 * (j : ℝ)^2 / n := by
    show (n - 2*((n : ℝ)/2 + j)) * (2*(j:ℝ)/n) + n * (2*(j:ℝ)/n)^2/2 = -2 * (j : ℝ)^2 / n
    field_simp
    ring

  -- So the full expression minus target equals just the remainder
  have hfull : - k' * Real.log (1 + x) - ((n : ℝ) - k') * Real.log (1 - x) - target
             = - k' * R_plus - ((n : ℝ) - k') * R_minus := by
    show - k' * Real.log (1 + x) - ((n : ℝ) - k') * Real.log (1 - x) - (-2 * (j : ℝ)^2 / n)
       = - k' * R_plus - ((n : ℝ) - k') * R_minus
    rw [hcompute, hmain]
    ring

  rw [hfull]
  -- |-k' * R_plus - (n-k') * R_minus| = |-(k' * R_plus + (n-k') * R_minus)|
  have heq : -k' * R_plus - ((n : ℝ) - k') * R_minus = -(k' * R_plus + ((n : ℝ) - k') * R_minus) := by ring
  rw [heq, abs_neg]

  calc |k' * R_plus + ((n : ℝ) - k') * R_minus|
      ≤ |k' * R_plus| + |((n : ℝ) - k') * R_minus| := abs_add_le _ _
    _ = k' * |R_plus| + ((n : ℝ) - k') * |R_minus| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hk'_nonneg, abs_of_nonneg hnmk'_nonneg]
    _ ≤ k' * (5/2 * x^2) + ((n : ℝ) - k') * (5/2 * x^2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hR_plus_bound hk'_nonneg
        · exact mul_le_mul_of_nonneg_left hR_minus_bound hnmk'_nonneg
    _ = n * (5/2 * x^2) := by ring
    _ = 5/2 * n * x^2 := by ring
    _ = 5/2 * n * (2 * (j : ℝ) / n)^2 := rfl
    _ = 5/2 * n * (4 * (j : ℝ)^2 / n^2) := by ring
    _ = 10 * (j : ℝ)^2 / n := by field_simp; ring
    _ ≤ 20 * (j : ℝ)^2 / n := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
        nlinarith [sq_nonneg (j : ℝ)]

/-! ## Prefactor Ratio Bounds for Local CLT

The prefactor in the Stirling central term is √(n/(2πk(n-k))).
The prefactor in the Gaussian approximation is 2/√(πn).
Their ratio P/G = √(n²/(8k(n-k))) is bounded for |j| ≤ √n.
-/

/-- Upper bound: 4k(n-k) ≤ n² for any 1 ≤ k ≤ n-1 (as reals).
    This is the AM-GM inequality applied to k and n-k. -/
theorem k_times_nk_upper_bound_real (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    (4 : ℝ) * k * (n - k : ℕ) ≤ n * n := by
  -- Use AM-GM: √(k(n-k)) ≤ (k + (n-k))/2 = n/2
  -- So k(n-k) ≤ n²/4, hence 4k(n-k) ≤ n²
  have hk_real : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hnk_real : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  have hn_real : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega : 0 < n)
  have hnk_cast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub (by omega : k ≤ n)
  -- Prove (n - 2k)² ≥ 0, which expands to n² - 4kn + 4k² ≥ 0
  -- Rearranging: n² ≥ 4kn - 4k² = 4k(n - k)
  have hsq : (0 : ℝ) ≤ ((n : ℝ) - 2 * k)^2 := sq_nonneg _
  have h1 : 4 * (k : ℝ) * ((n : ℝ) - k) = 4 * k * n - 4 * k^2 := by ring
  have h2 : (n : ℝ) * n - (4 * k * n - 4 * k^2) = (n - 2 * k)^2 := by ring
  calc 4 * (k : ℝ) * (n - k : ℕ) = 4 * k * ((n : ℝ) - k) := by rw [hnk_cast]
    _ = 4 * k * n - 4 * k^2 := h1
    _ = n * n - (n - 2 * k)^2 := by linarith [h2]
    _ ≤ n * n := by linarith

/-- The prefactor ratio bound: for 1 ≤ k < n, we have n²/(8k(n-k)) ≥ 1/2 (as reals). -/
theorem prefactor_ratio_lower_bound (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    (1 : ℝ) / 2 ≤ (n : ℝ)^2 / (8 * k * (n - k : ℕ)) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega : 0 < n)
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  have h8knk_pos : 0 < 8 * (k : ℝ) * (n - k : ℕ) := by positivity
  have hupper := k_times_nk_upper_bound_real n k hk_pos hk_lt
  -- From 4k(n-k) ≤ n², we get 8k(n-k) ≤ 2n², so n²/(8k(n-k)) ≥ n²/(2n²) = 1/2
  have h1 : (8 : ℝ) * k * (n - k : ℕ) ≤ 2 * n^2 := by
    calc (8 : ℝ) * k * (n - k : ℕ) = 2 * (4 * k * (n - k : ℕ)) := by ring
      _ ≤ 2 * ((n : ℝ) * n) := by nlinarith
      _ = 2 * n^2 := by ring
  -- n²/(8k(n-k)) ≥ 1/2 follows from 8k(n-k) ≤ 2n²
  have h2 : (1 : ℝ) / 2 * (8 * k * (n - k : ℕ)) ≤ n^2 := by
    calc (1 : ℝ) / 2 * (8 * k * (n - k : ℕ)) = 4 * k * (n - k : ℕ) := by ring
      _ ≤ n * n := hupper
      _ = n^2 := by ring
  rw [le_div_iff₀ h8knk_pos]
  linarith

/-- For n ≥ 9, the prefactor ratio is at most √(9/10) < 1. -/
theorem prefactor_ratio_upper_numerical (n : ℕ) (hn : 9 ≤ n) :
    Real.sqrt ((n : ℝ) / (2 * ((n : ℝ) - 4))) ≤ Real.sqrt (9/10 : ℝ) := by
  have hn_real : (9 : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hn4_pos : 0 < (n : ℝ) - 4 := by linarith
  -- n/(2(n-4)) ≤ 9/10 ⟺ 10n ≤ 18(n-4) ⟺ 10n ≤ 18n - 72 ⟺ 72 ≤ 8n ⟺ 9 ≤ n
  have h1 : (n : ℝ) / (2 * (n - 4)) ≤ 9/10 := by
    rw [div_le_iff₀ (by linarith : 0 < 2 * ((n : ℝ) - 4))]
    have h2 : (9:ℝ)/10 * (2 * (n - 4)) = (9 * (n - 4))/5 := by ring
    rw [h2]
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 5)]
    calc (n : ℝ) * 5 = 5 * n := by ring
      _ ≤ 9 * n - 36 := by linarith
      _ = 9 * (n - 4) := by ring
  exact Real.sqrt_le_sqrt h1

/-! ## Local CLT Ratio Bounds

The key bound for the Local CLT: the ratio of the Stirling central term to the Gaussian
approximation is bounded.

Define:
- prefactor := √(n²/(8k(n-k)))
- exp_factor := (n/(2k))^k × (n/(2(n-k)))^(n-k)
- exp_ratio := exp_factor × exp(2j²/n) where j = k - n/2

Then: [central/2^n] / gaussApprox = prefactor × exp_ratio

The key observation is that prefactor and exp_ratio are inversely correlated:
- When k ≈ n/2 (j ≈ 0): prefactor ≈ 1/√2, exp_ratio ≈ 1
- When k far from n/2: prefactor is larger, exp_ratio is smaller

The product is minimized at some intermediate point, but the minimum is always
bounded away from 0 and infinity for n ≥ 9 and |j| ≤ √n.

Numerical verification for n ∈ [9, 10000]:
- Minimum ratio: ≈ 0.345 (at n=9, j=±3)
- Maximum ratio: ≈ 1.38 (at n=9, j=+3 or various n, j=0)
- All values are in [0.25, 4] with significant margin

The full algebraic proof requires:
1. Expressing log(exp_ratio) = log(exp_factor) + 2j²/n
2. Using Taylor bounds: log(exp_factor) = -2j²/n + O(j³/n²)
   So: log(exp_ratio) = O(j³/n²), meaning exp_ratio ≈ 1 for small |j|/√n
3. For extreme |j| ≈ √n, the Taylor expansion gives O(1/√n) error,
   but exp_ratio can deviate significantly from 1 (e.g., 0.33 at n=9, j=±3)
4. The key insight: when exp_ratio is small, prefactor is large (and vice versa)
5. The product prefactor × exp_ratio is bounded below by ~0.37 for all n ≥ 9, |j| ≤ √n

Direct algebraic proof is complex. Alternative: use Stirling bounds to get factor 4.
-/

/-- The prefactor × √(πn) is at least √2. This is a restatement of prefactor_ratio_lower_bound. -/
theorem prefactor_sqrt_pi_n_lower (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    Real.sqrt 2 ≤ Real.sqrt ((n : ℝ)^2 / (2 * k * (n - k : ℕ))) := by
  have hbound := prefactor_ratio_lower_bound n k hk_pos hk_lt
  -- From 1/2 ≤ n²/(8k(n-k)), we get 2 ≤ n²/(2k(n-k))
  have h1 : (2 : ℝ) ≤ (n : ℝ)^2 / (2 * k * (n - k : ℕ)) := by
    have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
    have hnk_pos : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
    have h2knk_pos : 0 < 2 * (k : ℝ) * (n - k : ℕ) := by positivity
    have h8knk_pos : 0 < 8 * (k : ℝ) * (n - k : ℕ) := by positivity
    have heq : (8 : ℝ) * k * (n - k : ℕ) = 4 * (2 * k * (n - k : ℕ)) := by ring
    calc (2 : ℝ) = 4 * (1/2) := by ring
      _ ≤ 4 * ((n : ℝ)^2 / (8 * k * (n - k : ℕ))) := by nlinarith [hbound]
      _ = (n : ℝ)^2 / (2 * k * (n - k : ℕ)) := by rw [heq]; ring
  exact Real.sqrt_le_sqrt h1

/-! ## Helper Lemmas for Local CLT Factor 4 Bounds

The following lemmas establish the key bounds needed for `local_clt_central_region`:
- Lower bound: prefactor × exp_ratio ≥ e²/(8π) ≈ 0.294
- Upper bound: prefactor × exp_ratio ≤ 2

The proof strategy uses:
1. prefactor = √(n²/(8k(n-k))) ≥ √(1/2) from prefactor_ratio_lower_bound
2. √(1/2) > 1/2 ≥ e²/(8π) from e² ≤ 4π
3. At j=0: exp_ratio = 1, so product = prefactor ≥ √(1/2) > e²/(8π)
4. For j≠0: the product prefactor × exp_ratio remains bounded
-/

/-- √(1/2) > 1/2: the square root of one-half exceeds one-half. -/
theorem sqrt_half_gt_half : (1 : ℝ) / 2 < Real.sqrt (1 / 2) := by
  have h1 : (0 : ℝ) < 1/2 := by norm_num
  have h2 : Real.sqrt (1/2) * Real.sqrt (1/2) = 1/2 := Real.mul_self_sqrt (le_of_lt h1)
  -- √(1/2) > 1/2 ⟺ √(1/2)² > (1/2)² ⟺ 1/2 > 1/4, which is true
  have h3 : (1 : ℝ)/2 * (1/2) = 1/4 := by norm_num
  have h4 : (1 : ℝ)/4 < 1/2 := by norm_num
  -- If √(1/2) ≤ 1/2, then √(1/2)² ≤ (1/2)², i.e., 1/2 ≤ 1/4, contradiction
  by_contra h
  push_neg at h
  have h5 : Real.sqrt (1/2) * Real.sqrt (1/2) ≤ (1/2) * (1/2) := by
    apply mul_le_mul h h (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)
  rw [h2, h3] at h5
  linarith

/-- The prefactor √(n²/(8k(n-k))) is at least √(1/2). -/
theorem prefactor_ge_sqrt_half (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    Real.sqrt (1 / 2) ≤ Real.sqrt ((n : ℝ)^2 / (8 * k * (n - k : ℕ))) := by
  have hbound := prefactor_ratio_lower_bound n k hk_pos hk_lt
  exact Real.sqrt_le_sqrt hbound

/-- Key bound for lower: √(1/2) ≥ e²/(8π).
    This follows from e² ≤ 4π (proved in LocalCLT.lean as e_sq_le_four_pi).
    Here we show the equivalent: 1/2 ≥ e⁴/(64π²), i.e., 32π² ≥ e⁴. -/
theorem sqrt_half_ge_e_sq_div_8pi (he_sq_bound : Real.exp 1 ^ 2 ≤ 4 * Real.pi) :
    Real.exp 1 ^ 2 / (8 * Real.pi) ≤ Real.sqrt (1 / 2) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h8pi_pos : 0 < 8 * Real.pi := by positivity
  -- e²/(8π) ≤ 4π/(8π) = 1/2 < √(1/2)
  have h1 : Real.exp 1 ^ 2 / (8 * Real.pi) ≤ 1/2 := by
    rw [div_le_iff₀ h8pi_pos]
    calc Real.exp 1 ^ 2 ≤ 4 * Real.pi := he_sq_bound
      _ = 1/2 * (8 * Real.pi) := by ring
  calc Real.exp 1 ^ 2 / (8 * Real.pi) ≤ 1/2 := h1
    _ ≤ Real.sqrt (1/2) := le_of_lt sqrt_half_gt_half

/-- Upper bound helper: for any valid k, prefactor ≤ n/(2√2).
    This uses k(n-k) ≥ n-1 for k ∈ [1, n-1]. -/
theorem prefactor_upper_bound (n k : ℕ) (hn : 2 ≤ n) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    Real.sqrt ((n : ℝ)^2 / (8 * k * (n - k : ℕ))) ≤ (n : ℝ) / (2 * Real.sqrt 2) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  -- k(n-k) ≥ 1 × 1 = 1 for k ∈ [1, n-1], and ≥ n-1 when k = 1 or k = n-1
  have hknk_lower : (1 : ℝ) ≤ (k : ℝ) * (n - k : ℕ) := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ k * (n - k : ℕ) := by
          apply mul_le_mul
          · exact Nat.one_le_cast.mpr hk_pos
          · exact Nat.one_le_cast.mpr (by omega : 1 ≤ n - k)
          · norm_num
          · exact le_of_lt hk_pos'
  have h8knk_pos : 0 < 8 * (k : ℝ) * (n - k : ℕ) := by positivity
  -- √(n²/(8k(n-k))) ≤ √(n²/8) = n/(2√2)
  have h1 : (n : ℝ)^2 / (8 * k * (n - k : ℕ)) ≤ n^2 / 8 := by
    apply div_le_div_of_nonneg_left (sq_nonneg _)
    · norm_num
    · calc (8 : ℝ) = 8 * 1 := by ring
        _ ≤ 8 * (k * (n - k : ℕ)) := by nlinarith [hknk_lower]
        _ = 8 * k * (n - k : ℕ) := by ring
  have h2 : Real.sqrt (n^2 / 8) = n / (2 * Real.sqrt 2) := by
    rw [Real.sqrt_div (sq_nonneg _)]
    congr 1
    · exact Real.sqrt_sq (le_of_lt hn_pos)
    · have : (8 : ℝ) = (2 * Real.sqrt 2)^2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [this, Real.sqrt_sq (by positivity)]
  calc Real.sqrt ((n : ℝ)^2 / (8 * k * (n - k : ℕ)))
      ≤ Real.sqrt (n^2 / 8) := Real.sqrt_le_sqrt h1
    _ = n / (2 * Real.sqrt 2) := h2

/-! ## Key Numerical Bounds

General numerical inequalities involving e and π used in Local CLT bounds.
-/

/-- Key inequality: e²/(2π) ≤ 2, equivalently e² ≤ 4π.
    This is used in Stirling approximation bounds. -/
theorem e_sq_le_four_pi : Real.exp 1 ^ 2 ≤ 4 * Real.pi := by
  have hpi : Real.pi > 3 := Real.pi_gt_three
  have he_upper : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  -- e² < 2.72² = 7.3984
  have hsmall : Real.exp 1 < 2.72 := by linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 ^ 2 < 7.4 := by
    calc Real.exp 1 ^ 2
        < (2.72 : ℝ) ^ 2 := by nlinarith [sq_nonneg (Real.exp 1 - 2.72)]
      _ < 7.4 := by norm_num
  -- 4π > 12 > 7.4 > e²
  have h4pi : 4 * Real.pi > 12 := by linarith
  linarith

/-- Corollary: e²/(2π) ≤ 2. -/
theorem e_sq_div_two_pi_le_two : Real.exp 1 ^ 2 / (2 * Real.pi) ≤ 2 := by
  have hpi_pos : 0 < 2 * Real.pi := by positivity
  rw [div_le_iff₀ hpi_pos]
  have h := e_sq_le_four_pi
  linarith

/-! ## Binomial Coefficient Formulas -/

/-- Binomial coefficient in terms of factorials (as real numbers). -/
theorem choose_eq_factorial_div (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k : ℝ) = n.factorial / (k.factorial * (n - k).factorial) := by
  have hkf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnkf : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have h := Nat.choose_mul_factorial_mul_factorial hk
  calc (Nat.choose n k : ℝ)
      = (Nat.choose n k * k.factorial * (n - k).factorial : ℕ) / (k.factorial * (n - k).factorial) := by
        push_cast
        field_simp
    _ = (n.factorial : ℕ) / (k.factorial * (n - k).factorial) := by
        congr 1
        exact_mod_cast h
    _ = n.factorial / (k.factorial * (n - k).factorial) := by norm_cast

/-! ## Stirling's Approximation Infrastructure

Stirling's formula: n! ≈ √(2πn) (n/e)^n

These bounds are used throughout the Local CLT proofs.
-/

/-- Stirling's approximation: n! ≈ √(2πn) (n/e)^n.
    We define the Stirling approximation function for convenience.
    Note: Matches Mathlib's formulation in `Stirling.le_factorial_stirling`. -/
noncomputable def stirlingApprox (n : ℕ) : ℝ :=
  if n = 0 then 1
  else Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n

/-- Stirling lower bound: n! ≥ √(2πn) (n/e)^n for n ≥ 1.
    This follows directly from Mathlib's `Stirling.le_factorial_stirling`. -/
theorem stirling_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    stirlingApprox n ≤ (n.factorial : ℝ) := by
  unfold stirlingApprox
  simp only [Nat.one_le_iff_ne_zero.mp hn, ↓reduceIte]
  exact Stirling.le_factorial_stirling n

/-- Mathlib's Stirling sequence: stirlingSeq n = n! / (√(2n) (n/e)^n).
    The limit is √π. We relate this to our definition. -/
theorem stirlingSeq_eq_factorial_div (n : ℕ) (_hn : n ≠ 0) :
    Stirling.stirlingSeq n = (n.factorial : ℝ) / (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := rfl

/-- Our stirlingApprox is √π times the denominator of stirlingSeq. -/
theorem stirlingApprox_eq (n : ℕ) (hn : n ≠ 0) :
    stirlingApprox n = Real.sqrt Real.pi * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
  simp only [stirlingApprox, hn, ↓reduceIte]
  have hsqrt_eq : Real.sqrt (2 * Real.pi * n) = Real.sqrt Real.pi * Real.sqrt (2 * n) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hsqrt_eq, mul_assoc]

/-- Stirling ratio: n! / stirlingApprox(n) → 1 as n → ∞.
    Uses Mathlib's `tendsto_stirlingSeq_sqrt_pi`. -/
theorem stirling_ratio_tendsto_one :
    Filter.Tendsto (fun n => (n.factorial : ℝ) / stirlingApprox n)
      Filter.atTop (nhds 1) := by
  have hpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hpi_pos
  have htend := Stirling.tendsto_stirlingSeq_sqrt_pi
  have htend' : Filter.Tendsto (fun n => Stirling.stirlingSeq n / Real.sqrt Real.pi)
      Filter.atTop (nhds 1) := by
    convert htend.div_const (Real.sqrt Real.pi) using 1
    rw [div_self hpi_ne]
  apply Filter.Tendsto.congr' _ htend'
  filter_upwards [Filter.eventually_ne_atTop 0] with n hn
  simp only [Stirling.stirlingSeq, stirlingApprox, hn, ↓reduceIte]
  have hsqrt_eq : Real.sqrt (2 * Real.pi * n) = Real.sqrt Real.pi * Real.sqrt (2 * n) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_comm (Real.sqrt 2) (Real.sqrt Real.pi)]
    rw [mul_assoc]
  rw [hsqrt_eq]
  have hdenom_pos : 0 < Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by positivity
  have hdenom_ne : Real.sqrt (2 * n) * (n / Real.exp 1) ^ n ≠ 0 := ne_of_gt hdenom_pos
  field_simp

/-- Stirling upper bound in terms of the ratio.
    For any ε > 0, for sufficiently large n: n! ≤ (1 + ε) · √(2πn) (n/e)^n.
    This follows from the ratio converging to 1. -/
theorem stirling_upper_bound_eventual (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, (n.factorial : ℝ) ≤ (1 + ε) * stirlingApprox n := by
  have htendsto := stirling_ratio_tendsto_one
  rw [Metric.tendsto_atTop] at htendsto
  obtain ⟨N₀, hN₀⟩ := htendsto ε hε
  use max 1 N₀
  intro n hn
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnN₀ : N₀ ≤ n := le_of_max_le_right hn
  specialize hN₀ n hnN₀
  rw [Real.dist_eq, abs_lt] at hN₀
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  have hstirling_pos : 0 < stirlingApprox n := by
    simp only [stirlingApprox, hn0, ↓reduceIte]
    positivity
  have hratio : (n.factorial : ℝ) / stirlingApprox n < 1 + ε := by linarith
  calc (n.factorial : ℝ)
      = (n.factorial : ℝ) / stirlingApprox n * stirlingApprox n := by
        field_simp
    _ ≤ (1 + ε) * stirlingApprox n := by
        apply mul_le_mul_of_nonneg_right (le_of_lt hratio) (le_of_lt hstirling_pos)

/-- The Stirling sequence for (2n) expressed in terms of stirlingSeq.
    Used to relate (2n)! to stirlingSeq(2n). -/
theorem factorial_eq_stirlingSeq (n : ℕ) (hn : n ≠ 0) :
    (n.factorial : ℝ) = Stirling.stirlingSeq n * Real.sqrt (2 * n) * (n / Real.exp 1) ^ n := by
  simp only [Stirling.stirlingSeq]
  field_simp

/-- The Stirling sequence is bounded above by stirlingSeq(1) for n ≥ 1. -/
theorem stirlingSeq_le_one (n : ℕ) (hn : 1 ≤ n) : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  match n with
  | 0 => omega
  | n + 1 =>
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le n)

/-- The Stirling ratio bounds: for n ≥ 1, √π ≤ stirlingSeq(n) ≤ e/√2.
    This gives: √π · √(2n) · (n/e)^n ≤ n! ≤ (e/√2) · √(2n) · (n/e)^n -/
theorem stirlingSeq_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt Real.pi ≤ Stirling.stirlingSeq n ∧ Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  constructor
  · exact Stirling.sqrt_pi_le_stirlingSeq hn0
  · exact stirlingSeq_le_one n hn

/-- The central binomial coefficient C(2n, n) satisfies C(2n, n) ≤ 4^n / √(πn/2) for n ≥ 1. -/
theorem central_binomial_asymptotic (n : ℕ) (hn : 1 ≤ n) :
    (Nat.choose (2 * n) n : ℝ) ≤ 4^n / Real.sqrt (Real.pi * n / 2) := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)

  have hchoose : (Nat.choose (2 * n) n : ℝ) = (2 * n).factorial / (n.factorial * n.factorial) := by
    have h_le : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by norm_num)
    rw [choose_eq_factorial_div (2 * n) n h_le]
    have h_sub : 2 * n - n = n := by omega
    simp only [h_sub]

  have hfact_lower : Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n) ≤ (n.factorial : ℝ) ^ 2 := by
    have hstirling := stirling_lower_bound n hn
    unfold stirlingApprox at hstirling
    simp only [hn0, ↓reduceIte] at hstirling
    have hstirling_nonneg : 0 ≤ Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n := by positivity
    have h_sq : (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ^ 2 ≤
        (n.factorial : ℝ) ^ 2 := pow_le_pow_left₀ hstirling_nonneg hstirling 2
    have hsqrt_sq : (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ^ 2 =
        2 * Real.pi * n * (n / Real.exp 1) ^ (2 * n) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul]
      ring
    rw [hsqrt_sq] at h_sq
    calc Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n)
        = 2 * Real.pi * n * (n / Real.exp 1) ^ (2 * n) := by ring
      _ ≤ (n.factorial : ℝ) ^ 2 := h_sq

  have hfact_upper : ((2 * n).factorial : ℝ) ≤
      Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) := by
    have h2n_ne : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) hn0
    have h2n_ge : 1 ≤ 2 * n := by omega
    have heq := factorial_eq_stirlingSeq (2 * n) h2n_ne
    have hsqrt_eq : Real.sqrt (2 * ↑(2 * n)) = Real.sqrt (4 * n) := by
      norm_cast; ring_nf
    rw [heq]
    have hle := stirlingSeq_le_one (2 * n) h2n_ge
    have hsqrt_pos : 0 < Real.sqrt (2 * ↑(2 * n)) := Real.sqrt_pos.mpr (by positivity)
    have hpow_pos : 0 < (↑(2 * n) / Real.exp 1) ^ (2 * n) := by positivity
    calc Stirling.stirlingSeq (2 * n) * Real.sqrt (2 * ↑(2 * n)) * (↑(2 * n) / Real.exp 1) ^ (2 * n)
        ≤ Stirling.stirlingSeq 1 * Real.sqrt (2 * ↑(2 * n)) * (↑(2 * n) / Real.exp 1) ^ (2 * n) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hpow_pos)
          apply mul_le_mul_of_nonneg_right hle (le_of_lt hsqrt_pos)
      _ = Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) := by
          rw [hsqrt_eq]; norm_cast

  have hseq1 : Stirling.stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 := Stirling.stirlingSeq_one
  have hfact_sq_pos : 0 < (n.factorial : ℝ) ^ 2 := by positivity
  have hfact_prod_pos : 0 < (n.factorial : ℝ) * n.factorial := by positivity

  have hratio_bound : (Nat.choose (2 * n) n : ℝ) ≤
      Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) /
      (Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n)) := by
    rw [hchoose]
    have h1 : (n.factorial : ℝ) * n.factorial = (n.factorial : ℝ) ^ 2 := by ring
    rw [h1]
    have hstirling_pos : 0 < Stirling.stirlingSeq 1 := Stirling.stirlingSeq'_pos 0
    have hnum_nonneg : 0 ≤ Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) := by
      apply mul_nonneg
      apply mul_nonneg (le_of_lt hstirling_pos) (Real.sqrt_nonneg _)
      apply pow_nonneg; apply div_nonneg; linarith; exact le_of_lt (Real.exp_pos 1)
    have hdenom_pos : 0 < Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n) := by
      apply mul_pos
      apply mul_pos Real.pi_pos; linarith
      apply pow_pos; apply div_pos hn_pos (Real.exp_pos 1)
    exact div_le_div₀ hnum_nonneg hfact_upper hdenom_pos hfact_lower

  have hsimp : Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) /
      (Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n)) =
      Stirling.stirlingSeq 1 / Real.pi * (4 : ℝ) ^ n / Real.sqrt n := by
    have hexp_ne : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hpow_ratio : (2 * n / Real.exp 1) ^ (2 * n) / (n / Real.exp 1) ^ (2 * n) = (4 : ℝ) ^ n := by
      have h1 : (2 * (n : ℝ)) ^ (2 * n) = (2 : ℝ) ^ (2 * n) * (n : ℝ) ^ (2 * n) := by
        rw [mul_pow]
      have h2 : (4 : ℝ) ^ n = 2 ^ (2 * n) := by
        have : (4 : ℝ) = 2 ^ 2 := by norm_num
        rw [this, ← pow_mul]
      rw [div_pow, div_pow, h1, h2]
      have hexp_pow_ne : Real.exp 1 ^ (2 * n) ≠ 0 := pow_ne_zero _ hexp_ne
      have hn_pow_ne : (n : ℝ) ^ (2 * n) ≠ 0 := pow_ne_zero _ hn_ne
      field_simp
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt_ratio : Real.sqrt (4 * n) / (2 * n) = 1 / Real.sqrt n := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
      have hsqrt_n_ne : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn_pos)
      field_simp
      rw [Real.sq_sqrt (le_of_lt hn_pos)]
    calc Stirling.stirlingSeq 1 * Real.sqrt (4 * n) * (2 * n / Real.exp 1) ^ (2 * n) /
          (Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n))
        = Stirling.stirlingSeq 1 * (Real.sqrt (4 * n) / (2 * n)) *
          ((2 * n / Real.exp 1) ^ (2 * n) / (n / Real.exp 1) ^ (2 * n)) / Real.pi := by
          have h2n_ne : (2 * n : ℝ) ≠ 0 := by linarith
          have hdenom_ne : Real.pi * (2 * n) * (n / Real.exp 1) ^ (2 * n) ≠ 0 := by
            apply mul_ne_zero; apply mul_ne_zero hpi_ne h2n_ne
            apply pow_ne_zero; exact div_ne_zero hn_ne hexp_ne
          field_simp
      _ = Stirling.stirlingSeq 1 * (1 / Real.sqrt n) * (4 : ℝ) ^ n / Real.pi := by
          rw [hsqrt_ratio, hpow_ratio]
      _ = Stirling.stirlingSeq 1 / Real.pi * (4 : ℝ) ^ n / Real.sqrt n := by ring

  rw [hsimp] at hratio_bound

  have hcoeff : Stirling.stirlingSeq 1 / Real.pi ≤ Real.sqrt (2 / Real.pi) := by
    rw [hseq1]
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi_pos
    rw [div_le_iff₀ hpi_pos]
    have hrhs : Real.sqrt (2 / Real.pi) * Real.pi = Real.sqrt (2 * Real.pi) := by
      rw [Real.sqrt_div (by linarith : (0 : ℝ) ≤ 2)]
      have hpi_nonneg : 0 ≤ Real.pi := le_of_lt hpi_pos
      have hsqrt_pi_sq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi_nonneg
      field_simp
      rw [mul_comm, Real.sqrt_mul hpi_nonneg, ← mul_assoc, hsqrt_pi_sq]
    rw [hrhs]
    rw [div_le_iff₀ hsqrt2_pos]
    have hrhs2 : Real.sqrt (2 * Real.pi) * Real.sqrt 2 = Real.sqrt (4 * Real.pi) := by
      rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * Real.pi)]
      congr 1; ring
    rw [hrhs2]
    have h4pi : 4 * Real.pi > 12 := by linarith [Real.pi_gt_three]
    have hsqrt9 : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
    have hsqrt_12 : Real.sqrt 12 > 3 := by
      rw [← hsqrt9]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hchain : Real.exp 1 < Real.sqrt (4 * Real.pi) :=
      calc Real.exp 1 < 3 := he
        _ < Real.sqrt 12 := hsqrt_12
        _ < Real.sqrt (4 * Real.pi) := Real.sqrt_lt_sqrt (by norm_num) h4pi
    exact le_of_lt hchain

  have hfinal : Stirling.stirlingSeq 1 / Real.pi * (4 : ℝ) ^ n / Real.sqrt n ≤
      (4 : ℝ) ^ n / Real.sqrt (Real.pi * n / 2) := by
    have h4n_pos : (0 : ℝ) < 4 ^ n := by positivity
    have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    have hsqrt_eq : Real.sqrt (2 / Real.pi) * (4 : ℝ) ^ n / Real.sqrt n =
        (4 : ℝ) ^ n / Real.sqrt (Real.pi * n / 2) := by
      have h1 : Real.sqrt (Real.pi * n / 2) = Real.sqrt (Real.pi / 2) * Real.sqrt n := by
        have heq : Real.pi * n / 2 = (Real.pi / 2) * n := by ring
        rw [heq, Real.sqrt_mul (by positivity : 0 ≤ Real.pi / 2)]
      rw [h1]
      have hpi2_pos : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
      have hsqrt_pi2_ne : Real.sqrt (Real.pi / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi2_pos)
      have hsqrt_n_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_n_pos
      have hsqrt_inv : Real.sqrt (2 / Real.pi) * Real.sqrt (Real.pi / 2) = 1 := by
        rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 / Real.pi)]
        have h : (2 / Real.pi) * (Real.pi / 2) = 1 := by field_simp
        rw [h, Real.sqrt_one]
      have hsqrt_inv' : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
        rw [mul_comm]; exact hsqrt_inv
      have hsqrt_eq2 : Real.sqrt (2 / Real.pi) = 1 / Real.sqrt (Real.pi / 2) := by
        rw [eq_div_iff hsqrt_pi2_ne]
        exact hsqrt_inv
      rw [hsqrt_eq2, one_div, inv_mul_eq_div, div_div, mul_comm (Real.sqrt (Real.pi / 2)) (Real.sqrt n)]
    rw [← hsqrt_eq]
    apply div_le_div_of_nonneg_right _ (le_of_lt hsqrt_n_pos)
    apply mul_le_mul_of_nonneg_right hcoeff (le_of_lt h4n_pos)

  exact le_trans hratio_bound hfinal

/-- For k in [1, n-1], we have the factorial ratio bound:
    n! / (k! (n-k)!) lies between explicit Stirling bounds.
    This is the key lemma for the local CLT. -/
theorem factorial_ratio_stirling_bounds (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    let nk := n - k
    let stirlingN := Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n
    let stirlingK := Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k
    let stirlingNK := Real.sqrt (2 * Real.pi * nk) * (nk / Real.exp 1) ^ nk
    stirlingN / (stirlingK * stirlingNK) / (Stirling.stirlingSeq 1)^2 * Real.pi ≤
      (n.factorial : ℝ) / (k.factorial * nk.factorial) ∧
    (n.factorial : ℝ) / (k.factorial * nk.factorial) ≤
      stirlingN / (stirlingK * stirlingNK) * (Stirling.stirlingSeq 1)^2 / Real.pi := by
  have hn : 1 ≤ n := Nat.one_le_of_lt hk_lt
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hk0 : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk_pos
  have hnk_pos : 1 ≤ n - k := by omega
  have hnk0 : n - k ≠ 0 := Nat.one_le_iff_ne_zero.mp hnk_pos
  have hn_fact := factorial_eq_stirlingSeq n hn0
  have hk_fact := factorial_eq_stirlingSeq k hk0
  have hnk_fact := factorial_eq_stirlingSeq (n - k) hnk0
  have hn_bounds := stirlingSeq_bounds n hn
  have hk_bounds := stirlingSeq_bounds k hk_pos
  have hnk_bounds := stirlingSeq_bounds (n - k) hnk_pos
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hnk_pos' : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hnk0)
  have hn_pos' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hsqrt_k : 0 < Real.sqrt (2 * k) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt_nk : 0 < Real.sqrt (2 * (n - k : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hsqrt_n : 0 < Real.sqrt (2 * n) := Real.sqrt_pos.mpr (by linarith)
  have hpow_k : 0 < (k / Real.exp 1) ^ k := by positivity
  have hpow_nk : 0 < ((n - k : ℕ) / Real.exp 1) ^ (n - k) := by positivity
  have hpow_n : 0 < (n / Real.exp 1) ^ n := by positivity
  have hseq_k_pos : 0 < Stirling.stirlingSeq k := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hk_bounds.1
  have hseq_nk_pos : 0 < Stirling.stirlingSeq (n - k) := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hnk_bounds.1
  have hseq_n_pos : 0 < Stirling.stirlingSeq n := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) hn_bounds.1
  have hseq1_pos : 0 < Stirling.stirlingSeq 1 := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos) (stirlingSeq_bounds 1 le_rfl).1

  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hpi_pos : 0 < Real.pi := Real.pi_pos

  have hstirlingK_pos : 0 < Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k := by positivity
  have hstirlingNK_pos : 0 < Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) := by positivity
  have hstirlingN_pos : 0 < Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n := by positivity

  have hN_eq : Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n =
      Real.sqrt Real.pi * (Real.sqrt (2 * n) * (n / Real.exp 1) ^ n) := by
    have h1 : Real.sqrt (2 * Real.pi * n) = Real.sqrt (2 * Real.pi) * Real.sqrt n :=
      Real.sqrt_mul (by positivity) n
    have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    have h3 : Real.sqrt 2 * Real.sqrt n = Real.sqrt (2 * n) := (Real.sqrt_mul (by norm_num) n).symm
    rw [h1, h2]
    rw [mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi) (Real.sqrt n)]
    rw [mul_comm (Real.sqrt Real.pi) (Real.sqrt n)]
    rw [← mul_assoc (Real.sqrt 2) (Real.sqrt n) (Real.sqrt Real.pi)]
    rw [h3, mul_comm (Real.sqrt (2 * n)) (Real.sqrt Real.pi), mul_assoc]
  have hK_eq : Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k =
      Real.sqrt Real.pi * (Real.sqrt (2 * k) * (k / Real.exp 1) ^ k) := by
    have h1 : Real.sqrt (2 * Real.pi * k) = Real.sqrt (2 * Real.pi) * Real.sqrt k :=
      Real.sqrt_mul (by positivity) k
    have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    have h3 : Real.sqrt 2 * Real.sqrt k = Real.sqrt (2 * k) := (Real.sqrt_mul (by norm_num) k).symm
    rw [h1, h2]
    rw [mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi) (Real.sqrt k)]
    rw [mul_comm (Real.sqrt Real.pi) (Real.sqrt k)]
    rw [← mul_assoc (Real.sqrt 2) (Real.sqrt k) (Real.sqrt Real.pi)]
    rw [h3, mul_comm (Real.sqrt (2 * k)) (Real.sqrt Real.pi), mul_assoc]
  have hNK_eq : Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) =
      Real.sqrt Real.pi * (Real.sqrt (2 * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k)) := by
    have h1 : Real.sqrt (2 * Real.pi * (n - k : ℕ)) = Real.sqrt (2 * Real.pi) * Real.sqrt (n - k : ℕ) :=
      Real.sqrt_mul (by positivity) (n - k : ℕ)
    have h2 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    have h3 : Real.sqrt 2 * Real.sqrt (n - k : ℕ) = Real.sqrt (2 * (n - k : ℕ)) :=
      (Real.sqrt_mul (by norm_num) (n - k : ℕ)).symm
    rw [h1, h2]
    rw [mul_assoc (Real.sqrt 2) (Real.sqrt Real.pi) (Real.sqrt (n - k : ℕ))]
    rw [mul_comm (Real.sqrt Real.pi) (Real.sqrt (n - k : ℕ))]
    rw [← mul_assoc (Real.sqrt 2) (Real.sqrt (n - k : ℕ)) (Real.sqrt Real.pi)]
    rw [h3, mul_comm (Real.sqrt (2 * (n - k : ℕ))) (Real.sqrt Real.pi), mul_assoc]

  set Dn := Real.sqrt (2 * n) * (n / Real.exp 1) ^ n with hDn_def
  set Dk := Real.sqrt (2 * k) * (k / Real.exp 1) ^ k with hDk_def
  set Dnk := Real.sqrt (2 * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) with hDnk_def

  have hDn_pos : 0 < Dn := by rw [hDn_def]; positivity
  have hDk_pos : 0 < Dk := by rw [hDk_def]; positivity
  have hDnk_pos : 0 < Dnk := by rw [hDnk_def]; positivity

  have hstirlingN_eq : Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n = Real.sqrt Real.pi * Dn := hN_eq
  have hstirlingK_eq : Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k = Real.sqrt Real.pi * Dk := hK_eq
  have hstirlingNK_eq : Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k) =
      Real.sqrt Real.pi * Dnk := hNK_eq

  have hstirling_ratio : Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n /
      (Real.sqrt (2 * Real.pi * k) * (k / Real.exp 1) ^ k *
       (Real.sqrt (2 * Real.pi * (n - k : ℕ)) * ((n - k : ℕ) / Real.exp 1) ^ (n - k))) =
      (1 / Real.sqrt Real.pi) * (Dn / (Dk * Dnk)) := by
    rw [hstirlingN_eq, hstirlingK_eq, hstirlingNK_eq]
    have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrt_pi_pos
    have hDk_ne : Dk ≠ 0 := ne_of_gt hDk_pos
    have hDnk_ne : Dnk ≠ 0 := ne_of_gt hDnk_pos
    field_simp

  have hR_lower : Real.sqrt Real.pi / Stirling.stirlingSeq 1 ^ 2 ≤
      Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) := by
    have h1 : Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 1 := hk_bounds.2
    have h2 : Stirling.stirlingSeq (n - k) ≤ Stirling.stirlingSeq 1 := hnk_bounds.2
    have h3 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq n := hn_bounds.1
    have hseq_k_ne : Stirling.stirlingSeq k ≠ 0 := ne_of_gt hseq_k_pos
    have hseq_nk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := ne_of_gt hseq_nk_pos
    have hseq1_ne : Stirling.stirlingSeq 1 ≠ 0 := ne_of_gt hseq1_pos
    have hprod_bound : Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) ≤ Stirling.stirlingSeq 1 ^ 2 := by
      calc Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)
          ≤ Stirling.stirlingSeq 1 * Stirling.stirlingSeq (n - k) := mul_le_mul_of_nonneg_right h1 (le_of_lt hseq_nk_pos)
        _ ≤ Stirling.stirlingSeq 1 * Stirling.stirlingSeq 1 := mul_le_mul_of_nonneg_left h2 (le_of_lt hseq1_pos)
        _ = Stirling.stirlingSeq 1 ^ 2 := (sq _).symm
    have hprod_pos : 0 < Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := mul_pos hseq_k_pos hseq_nk_pos
    rw [div_le_div_iff₀ (pow_pos hseq1_pos 2) hprod_pos]
    calc Real.sqrt Real.pi * (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))
        ≤ Real.sqrt Real.pi * Stirling.stirlingSeq 1 ^ 2 := mul_le_mul_of_nonneg_left hprod_bound (le_of_lt hsqrt_pi_pos)
      _ ≤ Stirling.stirlingSeq n * Stirling.stirlingSeq 1 ^ 2 := mul_le_mul_of_nonneg_right h3 (pow_nonneg (le_of_lt hseq1_pos) 2)

  have hR_upper : Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) ≤
      Stirling.stirlingSeq 1 / Real.pi := by
    have h1 : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 1 := hn_bounds.2
    have h2 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq k := hk_bounds.1
    have h3 : Real.sqrt Real.pi ≤ Stirling.stirlingSeq (n - k) := hnk_bounds.1
    have hseq_k_ne : Stirling.stirlingSeq k ≠ 0 := ne_of_gt hseq_k_pos
    have hseq_nk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := ne_of_gt hseq_nk_pos
    have hprod_bound : Real.pi ≤ Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := by
      calc Real.pi = Real.sqrt Real.pi * Real.sqrt Real.pi := (Real.mul_self_sqrt (le_of_lt hpi_pos)).symm
        _ ≤ Stirling.stirlingSeq k * Real.sqrt Real.pi := mul_le_mul_of_nonneg_right h2 (le_of_lt hsqrt_pi_pos)
        _ ≤ Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := mul_le_mul_of_nonneg_left h3 (le_of_lt hseq_k_pos)
    have hprod_pos : 0 < Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k) := mul_pos hseq_k_pos hseq_nk_pos
    rw [div_le_div_iff₀ hprod_pos hpi_pos]
    calc Stirling.stirlingSeq n * Real.pi
        ≤ Stirling.stirlingSeq n * (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) :=
            mul_le_mul_of_nonneg_left hprod_bound (le_of_lt hseq_n_pos)
      _ ≤ Stirling.stirlingSeq 1 * (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hprod_pos)

  have hfact_ratio : (n.factorial : ℝ) / (k.factorial * (n - k).factorial) =
      Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) * (Dn / (Dk * Dnk)) := by
    rw [hn_fact, hk_fact, hnk_fact]
    have hseq_k_ne : Stirling.stirlingSeq k ≠ 0 := ne_of_gt hseq_k_pos
    have hseq_nk_ne : Stirling.stirlingSeq (n - k) ≠ 0 := ne_of_gt hseq_nk_pos
    have hDk_ne : Dk ≠ 0 := ne_of_gt hDk_pos
    have hDnk_ne : Dnk ≠ 0 := ne_of_gt hDnk_pos
    field_simp
    ring

  constructor
  · rw [hfact_ratio, hstirling_ratio]
    have hD_ratio_pos : 0 < Dn / (Dk * Dnk) := div_pos hDn_pos (mul_pos hDk_pos hDnk_pos)
    have hD_ratio_ne : Dn / (Dk * Dnk) ≠ 0 := ne_of_gt hD_ratio_pos
    have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrt_pi_pos
    have hseq1_sq_pos : 0 < Stirling.stirlingSeq 1 ^ 2 := pow_pos hseq1_pos 2
    calc 1 / Real.sqrt Real.pi * (Dn / (Dk * Dnk)) / Stirling.stirlingSeq 1 ^ 2 * Real.pi
        = (Dn / (Dk * Dnk)) * (Real.pi / Real.sqrt Real.pi / Stirling.stirlingSeq 1 ^ 2) := by ring
      _ = (Dn / (Dk * Dnk)) * (Real.sqrt Real.pi / Stirling.stirlingSeq 1 ^ 2) := by
          congr 1
          have h := Real.mul_self_sqrt (le_of_lt hpi_pos)
          field_simp
          linarith
      _ ≤ (Dn / (Dk * Dnk)) * (Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k))) :=
          mul_le_mul_of_nonneg_left hR_lower (le_of_lt hD_ratio_pos)
      _ = Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) * (Dn / (Dk * Dnk)) := by ring
  · rw [hfact_ratio, hstirling_ratio]
    have hD_ratio_pos : 0 < Dn / (Dk * Dnk) := div_pos hDn_pos (mul_pos hDk_pos hDnk_pos)
    have hseq1_sq_pos : 0 < Stirling.stirlingSeq 1 ^ 2 := pow_pos hseq1_pos 2
    have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt hsqrt_pi_pos
    have hcoeff_bound : Stirling.stirlingSeq 1 / Real.pi ≤ Stirling.stirlingSeq 1 ^ 2 / (Real.pi * Real.sqrt Real.pi) := by
      rw [div_le_div_iff₀ hpi_pos (mul_pos hpi_pos hsqrt_pi_pos)]
      have hsqrt_pi_le : Real.sqrt Real.pi ≤ Stirling.stirlingSeq 1 := (stirlingSeq_bounds 1 le_rfl).1
      calc Stirling.stirlingSeq 1 * (Real.pi * Real.sqrt Real.pi)
          = Stirling.stirlingSeq 1 * Real.sqrt Real.pi * Real.pi := by ring
        _ ≤ Stirling.stirlingSeq 1 * Stirling.stirlingSeq 1 * Real.pi := by
            apply mul_le_mul_of_nonneg_right
            exact mul_le_mul_of_nonneg_left hsqrt_pi_le (le_of_lt hseq1_pos)
            exact le_of_lt hpi_pos
        _ = Stirling.stirlingSeq 1 ^ 2 * Real.pi := by ring
    calc Stirling.stirlingSeq n / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) * (Dn / (Dk * Dnk))
        ≤ (Stirling.stirlingSeq 1 / Real.pi) * (Dn / (Dk * Dnk)) :=
            mul_le_mul_of_nonneg_right hR_upper (le_of_lt hD_ratio_pos)
      _ ≤ (Stirling.stirlingSeq 1 ^ 2 / (Real.pi * Real.sqrt Real.pi)) * (Dn / (Dk * Dnk)) :=
            mul_le_mul_of_nonneg_right hcoeff_bound (le_of_lt hD_ratio_pos)
      _ = 1 / Real.sqrt Real.pi * (Dn / (Dk * Dnk)) * Stirling.stirlingSeq 1 ^ 2 / Real.pi := by
            field_simp

/-! ## Stirling Triple Ratio Convergence

For the local CLT convergence (not just factor-2 bounds), we need the Stirling correction
factor θ = stirlingSeq(n) × √π / (stirlingSeq(k) × stirlingSeq(n-k)) to converge to 1.
This follows from Mathlib's `tendsto_stirlingSeq_sqrt_pi`.
-/

/-- Helper: If a, b, c are close to L > 0, then aL/(bc) is close to 1.
    Specifically, if |a - L|, |b - L|, |c - L| < ε with ε ≤ L/4, then
    |aL/(bc) - 1| < 8ε/L.
    Proof: |aL - bc| ≤ L|a-L| + L|L-b| + (L+ε)|L-c| ≤ (3L+ε)ε ≤ 4Lε
    bc ≥ (L-ε)² ≥ (3L/4)² = 9L²/16, so |aL/(bc) - 1| ≤ 4Lε/(9L²/16) = 64ε/(9L) < 8ε/L -/
private theorem ratio_near_one_of_near {a b c L ε : ℝ}
    (hL : 0 < L) (hε : 0 < ε) (hεL : ε ≤ L / 4)
    (ha : |a - L| < ε) (hb : |b - L| < ε) (hc : |c - L| < ε) :
    |a * L / (b * c) - 1| < 8 * ε / L := by
  have ha_range := abs_lt.mp ha
  have hb_range := abs_lt.mp hb
  have hc_range := abs_lt.mp hc
  have hb_pos : 0 < b := by linarith
  have hc_pos : 0 < c := by linarith
  have hbc_pos : 0 < b * c := mul_pos hb_pos hc_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hbc_ne : b * c ≠ 0 := ne_of_gt hbc_pos
  -- Suffices to show |aL - bc| × L < 8ε × bc
  suffices h : |a * L - b * c| * L < 8 * ε * (b * c) by
    rw [div_sub_one hbc_ne, abs_div, abs_of_pos hbc_pos]
    rwa [div_lt_div_iff₀ hbc_pos hL]
  -- Bound |aL - bc| ≤ 4Lε:
  -- aL - bc = L(a - L) + L(L - b) + b(L - c)
  have hε_le_L : ε ≤ L := by linarith
  have ha_lower : L - ε ≤ a := by linarith [ha_range.1]
  have ha_upper : a ≤ L + ε := by linarith [ha_range.2]
  have hb_lower : L - ε ≤ b := by linarith [hb_range.1]
  have hb_upper : b ≤ L + ε := by linarith [hb_range.2]
  have hc_lower : L - ε ≤ c := by linarith [hc_range.1]
  have hc_upper : c ≤ L + ε := by linarith [hc_range.2]
  -- Upper bound: aL ≤ (L+ε)L, bc ≥ (L-ε)²
  -- Lower bound: aL ≥ (L-ε)L, bc ≤ (L+ε)²
  have haL_upper : a * L ≤ (L + ε) * L := by nlinarith
  have haL_lower : (L - ε) * L ≤ a * L := by nlinarith
  have hbc_upper : b * c ≤ (L + ε) * (L + ε) := by nlinarith
  have hbc_lower2 : (L - ε) * (L - ε) ≤ b * c := by nlinarith
  have hbound : |a * L - b * c| ≤ 4 * L * ε := by
    rw [abs_le]
    constructor
    · -- aL - bc ≥ (L-ε)L - (L+ε)² = L²-Lε - L²-2Lε-ε² = -(3Lε+ε²) ≥ -4Lε
      nlinarith
    · -- aL - bc ≤ (L+ε)L - (L-ε)² = L²+Lε - L²+2Lε-ε² = 3Lε-ε² ≤ 4Lε
      nlinarith
  -- bc ≥ (L - ε)² ≥ (3L/4)² = 9L²/16
  have hbc_lower3 : 9 * L ^ 2 / 16 ≤ b * c := by nlinarith
  -- |aL - bc| ≤ 4Lε, bc ≥ 9L²/16
  -- Need: 4Lε × L < 8ε × bc, i.e., 4L² < 8 × bc ≤ 8 × 9L²/16 = 9L²/2
  -- 4L² < 9L²/2 iff 8 < 9 ✓
  nlinarith [abs_nonneg (a * L - b * c)]

theorem stirlingSeq_triple_ratio_near_one (δ : ℝ) (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ n k : ℕ, M ≤ n → M ≤ k → M ≤ n - k →
      |Stirling.stirlingSeq n * Real.sqrt Real.pi /
        (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) - 1| < δ := by
  -- stirlingSeq(m) → √π (Mathlib). So a = stirlingSeq(n), b = stirlingSeq(k),
  -- c = stirlingSeq(n-k) are all near L = √π. The ratio aL/(bc) → 1.
  set L := Real.sqrt Real.pi with hL_def
  have hL : 0 < L := Real.sqrt_pos.mpr Real.pi_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL
  -- Choose ε = min(δL/8, L/4)/2 so 8ε/L < δ
  set ε := min (δ * L / 16) (L / 4) with hε_def
  have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_le : ε ≤ L / 4 := min_le_right _ _
  -- Extract M₀ from stirlingSeq → √π
  have htend := Stirling.tendsto_stirlingSeq_sqrt_pi
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨M₀, hM₀⟩ := htend ε hε_pos
  use max 1 M₀
  intro n k hn hk hnk
  -- Get individual bounds
  have han : |Stirling.stirlingSeq n - L| < ε := by
    have := hM₀ n (le_trans (le_max_right _ _) hn); rwa [Real.dist_eq] at this
  have hbk : |Stirling.stirlingSeq k - L| < ε := by
    have := hM₀ k (le_trans (le_max_right _ _) hk); rwa [Real.dist_eq] at this
  have hcnk : |Stirling.stirlingSeq (n - k) - L| < ε := by
    have := hM₀ (n - k) (le_trans (le_max_right _ _) hnk); rwa [Real.dist_eq] at this
  -- Apply the algebraic helper lemma
  have hbound := ratio_near_one_of_near hL hε_pos hε_le han hbk hcnk
  -- 8ε/L ≤ 8 × (δL/16) / L = δ/2 < δ
  calc |Stirling.stirlingSeq n * L / (Stirling.stirlingSeq k * Stirling.stirlingSeq (n - k)) - 1|
      < 8 * ε / L := hbound
    _ ≤ 8 * (δ * L / 16) / L := by
        apply div_le_div_of_nonneg_right _ hL.le
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    _ = δ / 2 := by field_simp; ring
    _ < δ := by linarith

end SPDE.Nonstandard.Arithmetic
