/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.Anderson.LocalCLTHelpers
import StochasticPDE.Nonstandard.Foundation.Arithmetic

/-!
# Ratio Convergence Helpers

Infrastructure for proving `binomProb_ratio_near_one`.

## Key Results

* `mul_near_one` - product of near-1 factors is near 1
* `sqrt_near_one` - √(1+x) is near 1 when x is small
* `exp_near_one` - exp(x) is near 1 when x is small
* `floor_ratio_near_one` - ⌊r⌋/r is near 1 when r is large
-/

open Real Finset

namespace SPDE.Nonstandard.RatioConvergenceHelpers

/-! ## Product of Near-One Factors -/

/-- If |a - 1| < ε and |b - 1| < ε with ε ≤ 1/2, then |a*b - 1| < 3ε. -/
theorem mul_near_one {a b ε : ℝ} (ha : |a - 1| < ε) (hb : |b - 1| < ε) (hε : ε ≤ 1 / 2) :
    |a * b - 1| < 3 * ε := by
  have hε_pos : 0 < ε := lt_of_le_of_lt (abs_nonneg _) ha
  -- Get interval bounds
  have ha_l : -(ε) ≤ a - 1 := (abs_le.mp (le_of_lt ha)).1
  have ha_u : a - 1 ≤ ε := (abs_le.mp (le_of_lt ha)).2
  have hb_l : -(ε) ≤ b - 1 := (abs_le.mp (le_of_lt hb)).1
  have hb_u : b - 1 ≤ ε := (abs_le.mp (le_of_lt hb)).2
  -- a*b - 1 = (a-1)*(b-1) + (a-1) + (b-1)
  have h_eq : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  -- |a*b - 1| ≤ |a-1|*|b-1| + |a-1| + |b-1| < ε² + 2ε < 3ε
  rw [h_eq, abs_lt]; constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]

/-- Triple product: if each factor is ε-close to 1 with ε ≤ 1/4,
    then the triple product is 10ε-close to 1. -/
theorem mul_three_near_one {a b c ε : ℝ} (ha : |a - 1| < ε) (hb : |b - 1| < ε)
    (hc : |c - 1| < ε) (hε : ε ≤ 1 / 4) :
    |a * b * c - 1| < 10 * ε := by
  have hε_pos : 0 < ε := lt_of_le_of_lt (abs_nonneg _) ha
  have h_ab : |a * b - 1| < 3 * ε := mul_near_one ha hb (by linarith)
  -- Get bounds
  have hab_l : -(3 * ε) < a * b - 1 := (abs_lt.mp h_ab).1
  have hab_u : a * b - 1 < 3 * ε := (abs_lt.mp h_ab).2
  have hc_l : -(ε) ≤ c - 1 := (abs_le.mp (le_of_lt hc)).1
  have hc_u : c - 1 ≤ ε := (abs_le.mp (le_of_lt hc)).2
  have h_eq : a * b * c - 1 = (a * b - 1) * (c - 1) + ((a * b - 1) + (c - 1)) := by ring
  rw [h_eq, abs_lt]
  constructor <;> nlinarith [sq_nonneg (a * b - 1), sq_nonneg (c - 1)]

/-! ## Bounds on sqrt and exp near 1 -/

/-- √(1+x) is near 1: |√(1+x) - 1| ≤ |x| for |x| ≤ 1/2. -/
theorem sqrt_near_one {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.sqrt (1 + x) - 1| ≤ |x| := by
  have hx_l : -(1/2) ≤ x := by linarith [(abs_le.mp hx).1]
  have hx_u : x ≤ 1/2 := by linarith [(abs_le.mp hx).2]
  have h1x_pos : (0 : ℝ) < 1 + x := by linarith
  have h1x_nn : (0 : ℝ) ≤ 1 + x := le_of_lt h1x_pos
  by_cases hx_nn : 0 ≤ x
  · -- Case x ≥ 0: √(1+x) ∈ [1, 1+x], so |√(1+x)-1| = √(1+x)-1 ≤ x
    have hsqrt_ge : 1 ≤ Real.sqrt (1 + x) := by
      calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
        _ ≤ Real.sqrt (1 + x) := Real.sqrt_le_sqrt (by linarith)
    have hsqrt_le : Real.sqrt (1 + x) ≤ 1 + x := by
      -- (1+x)² ≥ 1+x for x ≥ 0, so √(1+x) ≤ √((1+x)²) = 1+x
      calc Real.sqrt (1 + x) ≤ Real.sqrt ((1 + x) ^ 2) := by
              apply Real.sqrt_le_sqrt; nlinarith
        _ = 1 + x := Real.sqrt_sq h1x_nn
    rw [abs_of_nonneg (by linarith), abs_of_nonneg hx_nn]
    linarith
  · -- Case x < 0: √(1+x) ∈ [1+x, 1], so |√(1+x)-1| = 1-√(1+x) ≤ -x = |x|
    push_neg at hx_nn
    have hsqrt_le : Real.sqrt (1 + x) ≤ 1 := by
      calc Real.sqrt (1 + x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hsqrt_ge : 1 + x ≤ Real.sqrt (1 + x) := by
      -- (1+x)² ≤ 1+x for 0 ≤ 1+x ≤ 1, so 1+x = √((1+x)²) ≤ √(1+x)
      calc 1 + x = Real.sqrt ((1 + x) ^ 2) := (Real.sqrt_sq h1x_nn).symm
        _ ≤ Real.sqrt (1 + x) := Real.sqrt_le_sqrt (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_neg hx_nn, neg_sub]
    linarith

/-- |exp(x) - 1| ≤ 2|x| for |x| ≤ 1.
    Uses: convexity of exp for upper bound, 1+x ≤ exp(x) for lower bound. -/
theorem exp_near_one {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1| ≤ 2 * |x| := by
  by_cases hx_nn : 0 ≤ x
  · -- x ≥ 0: exp(x) ≥ 1, |exp(x)-1| = exp(x)-1
    have hle1 : x ≤ 1 := by linarith [(abs_le.mp hx).2]
    rw [abs_of_nonneg (by linarith [Real.one_le_exp hx_nn] : 0 ≤ Real.exp x - 1),
        abs_of_nonneg hx_nn]
    -- By convexity: exp((1-x)*0 + x*1) ≤ (1-x)*exp(0) + x*exp(1)
    -- So exp(x) ≤ 1 - x + x*e, giving exp(x)-1 ≤ x*(e-1) ≤ 2x
    have he_bound : Real.exp 1 - 1 < 2 := by linarith [Real.exp_one_lt_d9]
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
        (show (0:ℝ) ≤ 1 - x by linarith) hx_nn (show (1:ℝ) - x + x = 1 by ring)
    simp only [smul_eq_mul, mul_zero, mul_one, Real.exp_zero, zero_add] at h
    -- h : exp(x) ≤ 1 - x + x * exp(1), i.e. exp(x) - 1 ≤ x*(exp(1)-1)
    -- x*(exp(1)-1) ≤ x*2 since x ≥ 0 and exp(1)-1 < 2
    have h2 : x * (Real.exp 1 - 1) ≤ x * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hx_nn
    linarith
  · -- x < 0: exp(x) ≤ 1, |exp(x)-1| = 1-exp(x)
    push_neg at hx_nn
    -- 1 - exp(x) ≤ -x ≤ -2x for x < 0
    have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have h_exp_le : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonpos (by linarith : Real.exp x - 1 ≤ 0),
        abs_of_neg hx_nn, neg_sub]
    -- Goal: 1 - exp(x) ≤ 2 * (-x) = -(2*x)
    linarith

/-- For r ≥ 2: k = ⌊r⌋ satisfies 0 < k and |r/k - 1| ≤ 1/k. -/
theorem floor_ratio_near_one {r : ℝ} (hr : 2 ≤ r) :
    let k := Nat.floor r
    (0 : ℝ) < k ∧ |r / k - 1| ≤ 1 / k := by
  intro k
  have hr_pos : 0 < r := by linarith
  have hk_pos : 0 < k := Nat.floor_pos.mpr (by linarith)
  have hk_r : (0 : ℝ) < k := Nat.cast_pos.mpr hk_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_r
  have hk_le : (k : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hk_gt : r - 1 < k := by
    have := Nat.lt_floor_add_one r; push_cast at this; linarith
  constructor
  · exact hk_r
  · rw [abs_le]; constructor
    · -- Lower: -(1/k) ≤ r/k - 1
      -- Since k ≤ r, r/k ≥ 1, so r/k - 1 ≥ 0 ≥ -1/k
      have h1 : 1 ≤ r / ↑k := (le_div_iff₀ hk_r).mpr (by linarith : 1 * ↑k ≤ r)
      linarith [div_pos (show (0:ℝ) < 1 by norm_num) hk_r]
    · -- Upper: r/k - 1 ≤ 1/k
      -- r < k+1 so r-k < 1, so (r-k)/k < 1/k
      rw [div_sub_one hk_ne]
      exact div_le_div_of_nonneg_right (by linarith : r - ↑k ≤ 1) (le_of_lt hk_r)

end SPDE.Nonstandard.RatioConvergenceHelpers
