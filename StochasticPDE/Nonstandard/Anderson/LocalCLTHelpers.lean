/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.Foundation.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Helper Lemmas for Local CLT

Infrastructure for proving `local_clt_central_region` factor-2 bounds.

## Main Results

* `binary_pinsker` - (1+v)ln(1+v) + (1-v)ln(1-v) ≥ v² for |v| < 1
* `exp_factor_le_one` - (n/(2k))^k × (n/(2(n-k)))^{n-k} × exp(s²/(2n)) ≤ 1

## Proof Strategy

The binary Pinsker inequality is proved via two applications of the monotone
derivative theorem:
1. h(v) = ln(1+v) - ln(1-v) - 2v satisfies h(0)=0 and h'(v) = 2v²/(1-v²) ≥ 0,
   so h(v) ≥ 0 for v ∈ [0,1).
2. g(v) = (1+v)ln(1+v) + (1-v)ln(1-v) - v² satisfies g(0)=0 and g'(v) = h(v) ≥ 0,
   so g(v) ≥ 0 for v ∈ [0,1).
-/

open Real Set

namespace SPDE.Nonstandard.LocalCLTHelpers

/-! ## Binary Pinsker Inequality -/

/-- Auxiliary: ln(1+v) - ln(1-v) ≥ 2v for 0 ≤ v < 1.
    Proof: The function h(v) = ln(1+v) - ln(1-v) - 2v satisfies h(0)=0 and
    h'(v) = 1/(1+v) + 1/(1-v) - 2 = 2v²/(1-v²) ≥ 0. -/
theorem log_diff_ge_two_v {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    2 * v ≤ Real.log (1 + v) - Real.log (1 - v) := by
  by_cases hv_eq : v = 0
  · simp [hv_eq]
  have hv_pos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv_eq)
  -- Suffices: f(v) ≥ 0 where f(t) = log(1+t) - log(1-t) - 2t
  suffices h : 0 ≤ Real.log (1 + v) - Real.log (1 - v) - 2 * v by linarith
  -- f(0) = 0 and f is monotone on [0,v] since f'(t) = 2t²/((1+t)(1-t)) ≥ 0
  -- Work directly with the explicit function
  have hf0 : Real.log (1 + (0:ℝ)) - Real.log (1 - (0:ℝ)) - 2 * (0:ℝ) = 0 := by
    simp [Real.log_one]
  -- Show the function is monotone on [0, v]
  have hmono : MonotoneOn (fun t => Real.log (1 + t) - Real.log (1 - t) - 2 * t) (Icc 0 v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 v)
    · -- ContinuousOn
      apply ContinuousOn.sub
      · apply ContinuousOn.sub
        · apply ContinuousOn.log
          · exact continuousOn_const.add continuousOn_id
          · intro t ht; exact ne_of_gt (show (0:ℝ) < 1 + t by linarith [ht.1])
        · apply ContinuousOn.log
          · exact continuousOn_const.sub continuousOn_id
          · intro t ht; exact ne_of_gt (show (0:ℝ) < 1 - t by linarith [ht.2])
      · exact continuousOn_const.mul continuousOn_id
    · -- DifferentiableOn on interior
      intro t ht
      rw [interior_Icc] at ht
      have h1pos : (0:ℝ) < 1 + t := by linarith [ht.1]
      have h2pos : (0:ℝ) < 1 - t := by linarith [ht.2]
      apply DifferentiableAt.differentiableWithinAt
      exact ((((differentiableAt_const (1:ℝ)).add differentiableAt_id).log
        (ne_of_gt h1pos)).sub
        (((differentiableAt_const (1:ℝ)).sub differentiableAt_id).log
        (ne_of_gt h2pos))).sub
        ((differentiableAt_const (2:ℝ)).mul differentiableAt_id)
    · -- Derivative nonneg on interior
      intro t ht
      rw [interior_Icc] at ht
      have h1pos : (0:ℝ) < 1 + t := by linarith [ht.1]
      have h2pos : (0:ℝ) < 1 - t := by linarith [ht.2]
      -- Compute derivative via HasDerivAt
      have hd1 : HasDerivAt (fun s => (1:ℝ) + s) 1 t := by
        simpa using (hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)
      have hd2 : HasDerivAt (fun s => (1:ℝ) - s) (-1) t := by
        simpa using (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
      have hd3 : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t :=
        hd1.log (ne_of_gt h1pos)
      have hd4 : HasDerivAt (fun s => Real.log (1 - s)) ((-1) / (1 - t)) t :=
        hd2.log (ne_of_gt h2pos)
      have hd5 : HasDerivAt (fun s => (2:ℝ) * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul (2:ℝ)
      have hd_f : HasDerivAt (fun t => Real.log (1 + t) - Real.log (1 - t) - 2 * t)
          (1 / (1 + t) - (-1) / (1 - t) - 2) t :=
        (hd3.sub hd4).sub hd5
      rw [hd_f.deriv]
      -- Show 1/(1+t) - (-1)/(1-t) - 2 = 2t²/((1+t)(1-t)) ≥ 0
      have hval : 1 / (1 + t) - (-1) / (1 - t) - 2 = 2 * t ^ 2 / ((1 + t) * (1 - t)) := by
        field_simp
        ring
      rw [hval]
      apply div_nonneg
      · positivity
      · exact le_of_lt (mul_pos h1pos h2pos)
  -- Extract f(0) ≤ f(v)
  have h_le := hmono (left_mem_Icc.mpr hv_pos.le) (right_mem_Icc.mpr hv_pos.le) hv_pos.le
  linarith [hf0]

/-- Helper for HasDerivAt of t ↦ (1+t) * log(1+t): derivative is log(1+t) + 1. -/
private lemma hasDerivAt_mul_log_add (t : ℝ) (h1pos : (0:ℝ) < 1 + t) :
    HasDerivAt (fun s => (1 + s) * Real.log (1 + s)) (Real.log (1 + t) + 1) t := by
  have hd_lin : HasDerivAt (fun s => (1:ℝ) + s) 1 t := by
    simpa using (hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)
  have hd_log : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + t)) t :=
    hd_lin.log (ne_of_gt h1pos)
  have hd := hd_lin.mul hd_log
  -- hd : HasDerivAt (fun s => (1+s) * log(1+s)) (1 * log(1+t) + (1+t) * (1/(1+t))) t
  convert hd using 1
  rw [one_mul, mul_one_div_cancel (ne_of_gt h1pos)]

/-- Helper for HasDerivAt of t ↦ (1-t) * log(1-t): derivative is -log(1-t) - 1. -/
private lemma hasDerivAt_mul_log_sub (t : ℝ) (h2pos : (0:ℝ) < 1 - t) :
    HasDerivAt (fun s => (1 - s) * Real.log (1 - s)) (-Real.log (1 - t) - 1) t := by
  have hd_lin : HasDerivAt (fun s => (1:ℝ) - s) (-1) t := by
    simpa using (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
  have hd_log : HasDerivAt (fun s => Real.log (1 - s)) ((-1) / (1 - t)) t :=
    hd_lin.log (ne_of_gt h2pos)
  have hd := hd_lin.mul hd_log
  -- hd : HasDerivAt (fun s => (1-s) * log(1-s)) ((-1) * log(1-t) + (1-t) * ((-1)/(1-t))) t
  convert hd using 1
  rw [neg_one_mul, mul_div_cancel₀ (-1) (ne_of_gt h2pos)]
  ring

/-- Binary Pinsker inequality for v ≥ 0:
    (1+v) ln(1+v) + (1-v) ln(1-v) ≥ v² for 0 ≤ v < 1. -/
private theorem binary_pinsker_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    v ^ 2 ≤ (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) := by
  by_cases hv_eq : v = 0
  · simp [hv_eq, Real.log_one]
  have hv_pos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv_eq)
  -- g(v) = (1+v)log(1+v) + (1-v)log(1-v) - v². Show g(v) ≥ 0.
  suffices h : 0 ≤ (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2 by
    linarith
  have hg0 : (1 + (0:ℝ)) * Real.log (1 + 0) + (1 - (0:ℝ)) * Real.log (1 - 0) - (0:ℝ) ^ 2 = 0 := by
    simp [Real.log_one]
  -- g is monotone on [0, v] since g'(t) = log(1+t) - log(1-t) - 2t ≥ 0
  have hmono : MonotoneOn
      (fun t => (1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t) - t ^ 2) (Icc 0 v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 v)
    · -- ContinuousOn
      apply ContinuousOn.sub
      · apply ContinuousOn.add
        · apply ContinuousOn.mul
          · exact continuousOn_const.add continuousOn_id
          · apply ContinuousOn.log
            · exact continuousOn_const.add continuousOn_id
            · intro t ht; exact ne_of_gt (show (0:ℝ) < 1 + t by linarith [ht.1])
        · apply ContinuousOn.mul
          · exact continuousOn_const.sub continuousOn_id
          · apply ContinuousOn.log
            · exact continuousOn_const.sub continuousOn_id
            · intro t ht; exact ne_of_gt (show (0:ℝ) < 1 - t by linarith [ht.2])
      · exact continuousOn_pow 2
    · -- DifferentiableOn on interior
      intro t ht
      rw [interior_Icc] at ht
      have h1pos : (0:ℝ) < 1 + t := by linarith [ht.1]
      have h2pos : (0:ℝ) < 1 - t := by linarith [ht.2]
      exact (hasDerivAt_mul_log_add t h1pos).differentiableAt.add
        (hasDerivAt_mul_log_sub t h2pos).differentiableAt |>.sub
        (differentiableAt_pow 2) |>.differentiableWithinAt
    · -- Derivative nonneg on interior
      intro t ht
      rw [interior_Icc] at ht
      have h1pos : (0:ℝ) < 1 + t := by linarith [ht.1]
      have h2pos : (0:ℝ) < 1 - t := by linarith [ht.2]
      -- Compute derivative: g'(t) = (log(1+t)+1) + (-log(1-t)-1) - 2t = log(1+t)-log(1-t)-2t
      have hd_g : HasDerivAt
          (fun t => (1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t) - t ^ 2)
          (Real.log (1 + t) - Real.log (1 - t) - 2 * t) t := by
        have hd_sq : HasDerivAt (fun s => s ^ 2) (2 * t) t := by
          simpa [pow_one] using hasDerivAt_pow 2 t
        have hd := (hasDerivAt_mul_log_add t h1pos).add (hasDerivAt_mul_log_sub t h2pos) |>.sub hd_sq
        convert hd using 1; ring
      rw [hd_g.deriv]
      -- log(1+t) - log(1-t) - 2t ≥ 0 by log_diff_ge_two_v
      linarith [log_diff_ge_two_v (le_of_lt ht.1) (lt_trans ht.2 hv1)]
  have h_le := hmono (left_mem_Icc.mpr hv_pos.le) (right_mem_Icc.mpr hv_pos.le) hv_pos.le
  linarith [hg0]

/-- The binary Pinsker inequality:
    (1+v) ln(1+v) + (1-v) ln(1-v) ≥ v² for |v| < 1.

    This is equivalent to D_KL(p || 1/2) ≥ 2(p - 1/2)² where p = (1+v)/2. -/
theorem binary_pinsker {v : ℝ} (hv : |v| < 1) :
    v ^ 2 ≤ (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) := by
  by_cases hv0 : 0 ≤ v
  · -- v ≥ 0: direct
    exact binary_pinsker_nonneg hv0 (abs_lt.mp hv).2
  · -- v < 0: use symmetry g(-v) = g(v)
    push_neg at hv0
    have hv0' : 0 ≤ -v := le_of_lt (neg_pos.mpr hv0)
    have hv1' : -v < 1 := by linarith [(abs_lt.mp hv).1]
    have key := binary_pinsker_nonneg hv0' hv1'
    -- key : (-v)^2 ≤ (1+(-v))*log(1+(-v)) + (1-(-v))*log(1-(-v))
    -- Rewrite: 1+(-v) = 1-v, 1-(-v) = 1+v, (-v)^2 = v^2
    have h1 : (1:ℝ) + (-v) = 1 - v := by ring
    have h2 : (1:ℝ) - (-v) = 1 + v := by ring
    rw [h1, h2, add_comm ((1-v) * _) _] at key
    linarith [neg_sq v]

/-! ## Exponential Factor Bound -/

/-- For a > 0, a ^ k = exp(k * log a). -/
private lemma pow_eq_exp_mul_log {a : ℝ} (ha : 0 < a) (k : ℕ) :
    a ^ k = Real.exp (↑k * Real.log a) := by
  conv_lhs => rw [← Real.exp_log ha]
  rw [← Real.exp_nat_mul]

/-- The exponential factor in the local CLT is ≤ 1 (Pinsker bound).
    (n/(2k))^k × (n/(2(n-k)))^{n-k} × exp((2k-n)²/(2n)) ≤ 1 -/
theorem exp_factor_le_one (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    ((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) *
      Real.exp ((2 * (k : ℝ) - n) ^ 2 / (2 * n)) ≤ 1 := by
  -- Setup: positivity hypotheses
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk_pos' : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0:ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  -- Set v = (2k - n) / n
  set v := (2 * (k : ℝ) - n) / n with hv_def
  -- Show |v| < 1
  have hv_lt : |v| < 1 := by
    simp only [hv_def]
    rw [abs_div, abs_of_pos hn_pos, div_lt_one hn_pos]
    rw [abs_lt]
    have hk_real : (k : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hk_lt
    constructor <;> nlinarith
  -- Key identities: 1+v = 2k/n and 1-v = 2(n-k)/n
  have hv_plus : 1 + v = 2 * ↑k / ↑n := by
    simp only [hv_def]; field_simp; ring
  have hv_minus : 1 - v = 2 * ↑(n - k) / ↑n := by
    simp only [hv_def]; rw [Nat.cast_sub hk_lt.le]; field_simp; ring
  have h1v_pos : 0 < 1 + v := by rw [hv_plus]; positivity
  have h1mv_pos : 0 < 1 - v := by rw [hv_minus]; positivity
  -- n/(2k) = 1/(1+v) and n/(2(n-k)) = 1/(1-v)
  have ha_eq : (n : ℝ) / (2 * k) = 1 / (1 + v) := by
    rw [hv_plus]; field_simp
  have hb_eq : (n : ℝ) / (2 * (n - k : ℕ)) = 1 / (1 - v) := by
    rw [hv_minus]; field_simp
  -- Rewrite LHS as exp(exponent) and show exponent ≤ 0
  rw [ha_eq, hb_eq]
  rw [pow_eq_exp_mul_log (by positivity : (0:ℝ) < 1 / (1 + v)) k]
  rw [pow_eq_exp_mul_log (by positivity : (0:ℝ) < 1 / (1 - v)) (n - k)]
  rw [← Real.exp_add, ← Real.exp_add]
  -- Goal: exp(exponent) ≤ 1, use exp_le_one_iff
  rw [exp_le_one_iff]
  -- Simplify logs: log(1/(1+v)) = -log(1+v)
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt h1v_pos)]
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt h1mv_pos)]
  simp only [Real.log_one, zero_sub]
  -- Express s²/(2n) = n/2 * v²
  have hsq : (2 * (k : ℝ) - n) ^ 2 / (2 * n) = n / 2 * v ^ 2 := by
    simp only [hv_def]; field_simp
  rw [hsq]
  -- Express ↑k = n * (1+v) / 2 and ↑(n-k) = n * (1-v) / 2
  have hk_eq : (k : ℝ) = ↑n * (1 + v) / 2 := by
    rw [hv_plus]; field_simp
  have hnk_eq : ((n - k : ℕ) : ℝ) = ↑n * (1 - v) / 2 := by
    rw [hv_minus]; field_simp
  rw [hk_eq, hnk_eq]
  -- Factor out n/2
  have hfactor : ↑n * (1 + v) / 2 * -Real.log (1 + v) +
      ↑n * (1 - v) / 2 * -Real.log (1 - v) + ↑n / 2 * v ^ 2 =
      ↑n / 2 * (v ^ 2 - ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v))) := by
    ring
  rw [hfactor]
  apply mul_nonpos_of_nonneg_of_nonpos
  · positivity
  · linarith [binary_pinsker hv_lt]

/-! ## Numerical Bounds -/

/-- e⁴ < 16π². -/
theorem e_fourth_lt_sixteen_pi_sq : Real.exp 1 ^ 4 < 16 * Real.pi ^ 2 := by
  have he_bound : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have hpi_bound : 3.14 < Real.pi := pi_gt_d2
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 ^ 4 < 2.72 ^ 4 := by
    have h_sq : Real.exp 1 ^ 2 < 2.72 ^ 2 := by
      nlinarith [sq_nonneg (2.72 - Real.exp 1), Real.exp_pos 1]
    nlinarith [sq_nonneg (2.72 ^ 2 - Real.exp 1 ^ 2), sq_nonneg (Real.exp 1)]
  have h2 : (2.72 : ℝ) ^ 4 < 55 := by norm_num
  have h3 : (55 : ℝ) < 16 * 3.14 ^ 2 := by norm_num
  have h4 : 16 * (3.14 : ℝ) ^ 2 ≤ 16 * Real.pi ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 16)
    exact sq_le_sq' (by linarith) (le_of_lt hpi_bound)
  linarith

/-- 81 × e⁴ < 512 × π². Used for the central region prefactor bound. -/
theorem eighty_one_e4_lt_512_pi_sq : 81 * Real.exp 1 ^ 4 < 512 * Real.pi ^ 2 := by
  have he_bound : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have hpi_bound : 3.14 < Real.pi := pi_gt_d2
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.exp 1 ^ 4 < 55 := by
    have h_sq : Real.exp 1 ^ 2 < 2.72 ^ 2 := by
      nlinarith [sq_nonneg (2.72 - Real.exp 1)]
    nlinarith [sq_nonneg (2.72 ^ 2 - Real.exp 1 ^ 2)]
  have h2 : 81 * (55 : ℝ) = 4455 := by norm_num
  have h3 : (4455 : ℝ) < 512 * 3.14 ^ 2 := by norm_num
  have h4 : 512 * (3.14 : ℝ) ^ 2 ≤ 512 * Real.pi ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 512)
    exact sq_le_sq' (by linarith) (le_of_lt hpi_bound)
  nlinarith

/-! ## Central Region Prefactor Bound -/

/-- For n ≥ 9 and (2k-n)² ≤ 49n/9, we have e⁴n² ≤ 64π²k(n-k).
    This is the key numerical bound for the local CLT factor-2 upper bound. -/
theorem e4n2_le_64pi2_kink (n k : ℕ) (hn : 9 ≤ n) (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (hs : (2 * (k : ℝ) - n)^2 ≤ 49 * (n : ℝ) / 9) :
    Real.exp 1 ^ 4 * (n : ℝ)^2 ≤ 64 * Real.pi ^ 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) := by
  have hn_real : (9 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hpi_sq_pos : 0 < Real.pi ^ 2 := by positivity
  -- Key identity: 4k(n-k) = n² - (2k-n)²
  have hkink : 4 * (k : ℝ) * ((n - k : ℕ) : ℝ) = (n : ℝ)^2 - (2 * (k : ℝ) - n)^2 := by
    rw [Nat.cast_sub hk_lt.le]; ring
  -- From eighty_one_e4_lt_512_pi_sq: 81e⁴ < 512π²
  have he4 := eighty_one_e4_lt_512_pi_sq
  -- Step 1: 16π²(2k-n)² ≤ 784π²n/9 (from hs)
  have h1 : 16 * Real.pi ^ 2 * (2 * (k : ℝ) - n)^2 ≤ 784 * Real.pi ^ 2 * n / 9 := by
    nlinarith [hs, hpi_sq_pos]
  -- Step 2: e⁴n + 784π²/9 ≤ 16π²n
  -- Equivalently: (16π² - e⁴)n ≥ 784π²/9
  -- Since 81(16π² - e⁴) ≥ 784π²  [from 512π² > 81e⁴]
  -- and n ≥ 9: (16π² - e⁴)n ≥ 9(16π² - e⁴) ≥ 784π²/9
  have h2 : Real.exp 1 ^ 4 * (n : ℝ) + 784 * Real.pi ^ 2 / 9 ≤ 16 * Real.pi ^ 2 * n := by
    -- From he4: 81e⁴ < 512π², so 9(16π² - e⁴) > 784π²/9
    -- So (16π² - e⁴) × n ≥ (16π² - e⁴) × 9 ≥ 784π²/9
    nlinarith [he4, hn_real]
  -- Combine: e⁴n² + 16π²(2k-n)² ≤ e⁴n² + 784π²n/9 ≤ 16π²n²
  -- So e⁴n² ≤ 16π²n² - 16π²(2k-n)² = 16π²(n²-(2k-n)²) = 16π²×4k(n-k) = 64π²k(n-k)
  nlinarith [h1, h2, hkink, sq_nonneg (2 * (k : ℝ) - ↑n)]

/-! ## Stirling Ratio Algebraic Identity

The key identity: stirlingN / (stirlingK × stirlingNK) / 2^n
= √(n/(2πk(n-k))) × (n/(2k))^k × (n/(2(n-k)))^{n-k}
-/

/-- Square root factoring: √(2πa) / (√(2πb) × √(2πc)) = √(a/(2πbc)). -/
private lemma sqrt_two_pi_ratio {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) :
    Real.sqrt (2 * Real.pi * a) / (Real.sqrt (2 * Real.pi * b) * Real.sqrt (2 * Real.pi * c)) =
    Real.sqrt (a / (2 * Real.pi * b * c)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pb : 0 < 2 * Real.pi * b := by positivity
  have h2pc : 0 < 2 * Real.pi * c := by positivity
  rw [← Real.sqrt_mul (le_of_lt h2pb), ← Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi * a)]
  congr 1
  have hbc : 0 < 2 * Real.pi * b * (2 * Real.pi * c) := by positivity
  field_simp

/-- Power factoring: (n/e)^n / ((k/e)^k × ((n-k)/e)^(n-k)) / 2^n = (n/(2k))^k × (n/(2(n-k)))^(n-k). -/
private lemma pow_stirling_ratio (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    ((n : ℝ) / Real.exp 1) ^ n /
      (((k : ℝ) / Real.exp 1) ^ k * (((n - k : ℕ) : ℝ) / Real.exp 1) ^ (n - k)) / (2 : ℝ) ^ n =
    ((n : ℝ) / (2 * ↑k)) ^ k * ((n : ℝ) / (2 * ↑(n - k : ℕ))) ^ (n - k) := by
  set nk := n - k with hnk_def
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he_ne : Real.exp 1 ≠ 0 := ne_of_gt he
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0 : ℝ) < (nk : ℕ) := Nat.cast_pos.mpr (by omega)
  -- Rewrite all (a/e)^m as a^m/e^m
  simp only [div_pow]
  -- Cancel e terms: e^k * e^nk = e^n
  have he_split : (Real.exp 1) ^ n = (Real.exp 1) ^ k * (Real.exp 1) ^ nk := by
    rw [← pow_add]; congr 1; omega
  -- Split n^n = n^k * n^{n-k} and 2^n = 2^k * 2^{n-k}
  have hn_split : (n : ℝ) ^ n = (n : ℝ) ^ k * (n : ℝ) ^ nk := by
    rw [← pow_add]; congr 1; omega
  have h2_split : (2 : ℝ) ^ n = (2 : ℝ) ^ k * (2 : ℝ) ^ nk := by
    rw [← pow_add]; congr 1; omega
  -- Now everything is a^m / b^m terms. Clear all denominators.
  have hek_ne : (Real.exp 1) ^ k ≠ 0 := pow_ne_zero _ he_ne
  have henk_ne : (Real.exp 1) ^ nk ≠ 0 := pow_ne_zero _ he_ne
  have hen_ne : (Real.exp 1) ^ n ≠ 0 := pow_ne_zero _ he_ne
  have hkk_ne : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hk_pos')
  have hnknk_ne : ((nk : ℕ) : ℝ) ^ nk ≠ 0 := pow_ne_zero _ (ne_of_gt hnk_pos)
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2k_ne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2nk_ne : (2 : ℝ) ^ nk ≠ 0 := pow_ne_zero _ (by norm_num)
  -- Use field_simp to clear all fractions, then ring
  rw [hn_split, h2_split, he_split]
  have h2k_pos : (0 : ℝ) < 2 * ↑k := by positivity
  have h2nk_pos : (0 : ℝ) < 2 * ↑(nk : ℕ) := by positivity
  field_simp
  ring

/-- The Stirling ratio decomposition:
    stirlingN / (stirlingK × stirlingNK) / 2^n = √(n/(2πk(n-k))) × exp_factor
    where exp_factor = (n/(2k))^k × (n/(2(n-k)))^{n-k}. -/
theorem stirling_ratio_decomp (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    let nk := n - k
    let stirlingN := Real.sqrt (2 * Real.pi * ↑n) * (↑n / Real.exp 1) ^ n
    let stirlingK := Real.sqrt (2 * Real.pi * ↑k) * (↑k / Real.exp 1) ^ k
    let stirlingNK := Real.sqrt (2 * Real.pi * ↑nk) * (↑nk / Real.exp 1) ^ nk
    let exp_factor : ℝ := (↑n / (2 * ↑k)) ^ k * (↑n / (2 * ↑nk)) ^ nk
    stirlingN / (stirlingK * stirlingNK) / (2 : ℝ) ^ n =
    Real.sqrt (↑n / (2 * Real.pi * ↑k * ↑nk)) * exp_factor := by
  intro nk stirlingN stirlingK stirlingNK exp_factor
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0 : ℝ) < (nk : ℕ) := Nat.cast_pos.mpr (by omega)
  have hsqrt := sqrt_two_pi_ratio (le_of_lt hn) hk hnk_pos
  have hpow := pow_stirling_ratio n k hk_pos hk_lt
  simp only [stirlingN, stirlingK, stirlingNK]
  have hsK : 0 < Real.sqrt (2 * Real.pi * ↑k) := Real.sqrt_pos.mpr (by positivity)
  have hsNK : 0 < Real.sqrt (2 * Real.pi * ↑(nk : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hpK : 0 < (↑k / Real.exp 1) ^ k := by positivity
  have hpNK : 0 < (↑(nk : ℕ) / Real.exp 1) ^ nk := by positivity
  have h_rearrange :
      Real.sqrt (2 * Real.pi * ↑n) * (↑n / Real.exp 1) ^ n /
        (Real.sqrt (2 * Real.pi * ↑k) * (↑k / Real.exp 1) ^ k *
         (Real.sqrt (2 * Real.pi * ↑(nk : ℕ)) * (↑(nk : ℕ) / Real.exp 1) ^ nk)) / (2 : ℝ) ^ n =
      (Real.sqrt (2 * Real.pi * ↑n) /
        (Real.sqrt (2 * Real.pi * ↑k) * Real.sqrt (2 * Real.pi * ↑(nk : ℕ)))) *
      ((↑n / Real.exp 1) ^ n /
        ((↑k / Real.exp 1) ^ k * (↑(nk : ℕ) / Real.exp 1) ^ nk) / (2 : ℝ) ^ n) := by
    field_simp
  rw [h_rearrange, hsqrt, hpow]

/-! ## Central Region Combined Bound -/

/-- For n ≥ 9, |j| ≤ √n, and k = ⌊n/2⌋ + j (as integers), we have (2k-n)² ≤ 49n/9.
    This is the integer arithmetic step connecting the central region to the prefactor bound. -/
theorem central_region_s_bound (n : ℕ) (j : ℤ) (k : ℕ)
    (hn : 9 ≤ n) (hk_eq : (k : ℤ) = (n : ℤ) / 2 + j)
    (hj : (↑|j| : ℝ) ≤ Real.sqrt n) :
    (2 * (k : ℝ) - n)^2 ≤ 49 * (n : ℝ) / 9 := by
  -- Direct approach: work with (2k-n)² on reals
  -- Since k = ⌊n/2⌋ + j, we have 2k - n = 2j + (2⌊n/2⌋ - n) where |2⌊n/2⌋ - n| ≤ 1
  -- So (2k-n)² ≤ (1 + 2|j|)² ≤ (1 + 2√n)² ≤ 49n/9

  -- Step 1: Bound (2k - n)² as integers
  -- 2k - n = 2j + r where r = 2⌊n/2⌋ - n ∈ {0, -1}
  have h_r_bound : 2 * ((n : ℤ) / 2) = n ∨ 2 * ((n : ℤ) / 2) = n - 1 := by omega
  -- |2k - n| ≤ 1 + 2|j|
  have h_abs_bound : |2 * (k : ℤ) - n| ≤ 1 + 2 * |j| := by
    rcases h_r_bound with h | h
    · -- n even: 2k - n = 2j, |2j| = 2|j| ≤ 1 + 2|j|
      have h2kn : 2 * (k : ℤ) - n = 2 * j := by omega
      rw [h2kn, abs_mul, abs_of_nonneg (show (0:ℤ) ≤ 2 by norm_num)]
      linarith [abs_nonneg j]
    · -- n odd: 2k - n = 2j - 1, |2j - 1| ≤ 1 + 2|j|
      have h2kn : 2 * (k : ℤ) - n = 2 * j - 1 := by omega
      rw [h2kn]
      -- |2j - 1| ≤ |2j| + |-1| = 2|j| + 1
      have htri : |2 * j + (-1)| ≤ |2 * j| + |-1| := abs_add_le (2 * j) (-1)
      have h_eq : 2 * j + (-1) = 2 * j - 1 := by ring
      rw [h_eq] at htri
      rw [abs_neg, abs_one, abs_mul, abs_of_nonneg (show (0:ℤ) ≤ 2 by norm_num)] at htri
      linarith
  have h_2k_bound : (2 * (k : ℤ) - n)^2 ≤ (1 + 2 * |j|)^2 := by
    have h_nonneg : 0 ≤ 1 + 2 * |j| := by linarith [abs_nonneg j]
    nlinarith [sq_abs (2 * (k : ℤ) - n), abs_nonneg (2 * (k : ℤ) - n),
               sq_nonneg (1 + 2 * |j| - |2 * (k : ℤ) - n|)]

  -- Step 2: Convert to reals
  have h_sq_real : (2 * (k : ℝ) - n)^2 ≤ (1 + 2 * (↑|j| : ℝ))^2 := by
    have h1 : (2 * (k : ℝ) - n)^2 = ((2 * (k : ℤ) - n : ℤ) : ℝ)^2 := by push_cast; ring_nf
    have h2 : (1 + 2 * (↑|j| : ℝ))^2 = ((1 + 2 * |j| : ℤ) : ℝ)^2 := by push_cast; ring
    rw [h1, h2]
    have : ((2 * (k : ℤ) - n)^2 : ℤ) ≤ ((1 + 2 * |j|)^2 : ℤ) := h_2k_bound
    exact_mod_cast this

  -- Step 3: (1 + 2|j|)² ≤ (1 + 2√n)² since |j| ≤ √n
  have h_sq : (2 * (k : ℝ) - n)^2 ≤ (1 + 2 * Real.sqrt n)^2 := by
    have hj_nonneg : (0 : ℝ) ≤ ↑|j| := by positivity
    calc (2 * (k : ℝ) - n)^2 ≤ (1 + 2 * (↑|j| : ℝ))^2 := h_sq_real
      _ ≤ (1 + 2 * Real.sqrt n)^2 := by
          have : 1 + 2 * (↑|j| : ℝ) ≤ 1 + 2 * Real.sqrt n := by linarith [hj]
          have h1 : 0 ≤ 1 + 2 * (↑|j| : ℝ) := by linarith
          nlinarith [sq_nonneg (2 * Real.sqrt n - 2 * (↑|j| : ℝ))]

  -- Step 4: (1 + 2√n)² ≤ 49n/9 for n ≥ 9
  -- Expand: (1 + 2√n)² = 1 + 4√n + 4n
  -- Need: 1 + 4√n + 4n ≤ 49n/9
  -- i.e., 4√n ≤ 49n/9 - 4n - 1 = 13n/9 - 1
  -- For n ≥ 9: √n ≤ n/3 (since n ≤ n²/9 for n ≥ 9)
  -- So 4√n ≤ 4n/3 and 1 + 4n/3 + 4n = 1 + 16n/3
  -- Need 1 + 16n/3 ≤ 49n/9, i.e., 1 ≤ n/9, i.e., n ≥ 9 ✓
  have hn_real : (9 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hsqrt_bound : Real.sqrt n ≤ (n : ℝ) / 3 := by
    have h_le : (n : ℝ) ≤ ((n : ℝ) / 3)^2 := by nlinarith
    have h_nonneg : (0 : ℝ) ≤ (n : ℝ) / 3 := by linarith
    calc Real.sqrt n ≤ Real.sqrt (((n : ℝ) / 3)^2) := Real.sqrt_le_sqrt h_le
      _ = (n : ℝ) / 3 := Real.sqrt_sq h_nonneg
  have h_expand : (1 + 2 * Real.sqrt n)^2 ≤ 49 * (n : ℝ) / 9 := by
    have h1 : (1 + 2 * Real.sqrt n)^2 = 1 + 4 * Real.sqrt n + 4 * (Real.sqrt n)^2 := by ring
    rw [h1, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ n)]
    nlinarith [hsqrt_bound]
  linarith

/-- Combined bound for the central region: for n ≥ 9, |j| ≤ √n, k = ⌊n/2⌋ + j,
    1 ≤ k < n, we have e⁴n² ≤ 64π²k(n-k).
    This combines the integer arithmetic with the numerical bound. -/
theorem central_region_e4_bound (n : ℕ) (j : ℤ) (k : ℕ)
    (hn : 9 ≤ n) (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (hk_eq : (k : ℤ) = (n : ℤ) / 2 + j)
    (hj : (↑|j| : ℝ) ≤ Real.sqrt n) :
    Real.exp 1 ^ 4 * (n : ℝ)^2 ≤ 64 * Real.pi ^ 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) :=
  e4n2_le_64pi2_kink n k hn hk_pos hk_lt (central_region_s_bound n j k hn hk_eq hj)

/-! ## Prefactor Bound: (s₁²/π) × √(n²/(4k(n-k))) ≤ 2

The key step: squaring reduces to e⁴n²/(16π²k(n-k)) ≤ 4,
which is exactly central_region_e4_bound.
-/

/-- (s₁²/π)² × n²/(4k(n-k)) ≤ 4 when e⁴n² ≤ 64π²k(n-k).
    Combines the Stirling sequence formula s₁² = e²/2 with the e⁴ bound. -/
theorem s1_sq_pi_ratio_sq_le_four (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (hkey : Real.exp 1 ^ 4 * (n : ℝ)^2 ≤ 64 * Real.pi ^ 2 * (k : ℝ) * ((n - k : ℕ) : ℝ)) :
    (Stirling.stirlingSeq 1 ^ 2 / Real.pi) ^ 2 * ((n : ℝ)^2 / (4 * k * (n - k : ℕ))) ≤ 4 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  -- s₁² = e²/2
  have hs₁_sq : Stirling.stirlingSeq 1 ^ 2 = Real.exp 1 ^ 2 / 2 := by
    rw [Stirling.stirlingSeq_one, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hs₁_sq]
  -- LHS = (e²/(2π))² × n²/(4k(nk)) = e⁴n²/(16π²k(nk))
  have hlhs : (Real.exp 1 ^ 2 / 2 / Real.pi) ^ 2 * ((n : ℝ) ^ 2 / (4 * ↑k * ↑(n - k))) =
      Real.exp 1 ^ 4 * (n : ℝ) ^ 2 / (16 * Real.pi ^ 2 * ↑k * ↑(n - k)) := by
    field_simp; ring
  rw [hlhs]
  -- Need: e⁴n²/(16π²k(nk)) ≤ 4, i.e., e⁴n² ≤ 64π²k(nk)
  have hdenom_pos : (0 : ℝ) < 16 * Real.pi ^ 2 * ↑k * ↑(n - k) := by positivity
  exact (div_le_iff₀ hdenom_pos).mpr (by linarith)

/-- The prefactor bound: (s₁²/π) × √(n²/(4k(n-k))) ≤ 2.
    Proved by squaring and applying s1_sq_pi_ratio_sq_le_four. -/
theorem s1_prefactor_le_two (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (hkey : Real.exp 1 ^ 4 * (n : ℝ)^2 ≤ 64 * Real.pi ^ 2 * (k : ℝ) * ((n - k : ℕ) : ℝ)) :
    Stirling.stirlingSeq 1 ^ 2 / Real.pi *
      Real.sqrt ((n : ℝ)^2 / (4 * k * (n - k : ℕ))) ≤ 2 := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  -- Both sides are nonneg
  have hlhs_nn : 0 ≤ Stirling.stirlingSeq 1 ^ 2 / Real.pi *
      Real.sqrt ((n : ℝ)^2 / (4 * k * (n - k : ℕ))) := by positivity
  -- Square both sides
  suffices h : (Stirling.stirlingSeq 1 ^ 2 / Real.pi *
      Real.sqrt ((n : ℝ)^2 / (4 * k * (n - k : ℕ))))^2 ≤ 4 by
    nlinarith [sq_nonneg (2 - Stirling.stirlingSeq 1 ^ 2 / Real.pi *
      Real.sqrt ((n : ℝ)^2 / (4 * k * (n - k : ℕ))))]
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)^2 / (4 * k * (n - k : ℕ)))]
  exact s1_sq_pi_ratio_sq_le_four n k hk_pos hk_lt hkey

/-- Square root factoring: √(n/(2πk(nk))) = √(n²/(4k(nk))) × √(2/(πn)).
    This decomposes the Stirling prefactor into a simpler ratio times the Gaussian normalization. -/
theorem sqrt_prefactor_factoring (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    Real.sqrt ((n : ℝ) / (2 * Real.pi * k * (n - k : ℕ))) =
    Real.sqrt ((n : ℝ)^2 / (4 * k * (n - k : ℕ))) * Real.sqrt (2 / (Real.pi * n)) := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (n : ℝ)^2 / (4 * k * (n - k : ℕ)))]
  congr 1
  field_simp
  ring

/-! ## Lower Bound Helpers -/

/-- π/s₁² = 2π/e² ≥ 1/2 when e² ≤ 4π. -/
theorem pi_div_s1_sq_ge_half :
    Real.pi / Stirling.stirlingSeq 1 ^ 2 ≥ 1 / 2 := by
  have hs₁_sq : Stirling.stirlingSeq 1 ^ 2 = Real.exp 1 ^ 2 / 2 := by
    rw [Stirling.stirlingSeq_one, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have he_sq_pos : (0 : ℝ) < Real.exp 1 ^ 2 := by positivity
  have hs₁_sq_pos : (0 : ℝ) < Stirling.stirlingSeq 1 ^ 2 := by rw [hs₁_sq]; positivity
  -- Suffices: s₁² ≤ 2π
  suffices h : Stirling.stirlingSeq 1 ^ 2 ≤ 2 * Real.pi by
    rw [ge_iff_le]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hs₁_sq_pos]
    linarith
  rw [hs₁_sq]
  -- Goal: e²/2 ≤ 2 * π, i.e., e² ≤ 4π
  linarith [Arithmetic.e_sq_le_four_pi]

/-- n² ≥ 4k(n-k) by AM-GM (equivalently (2k-n)² ≥ 0). -/
theorem sq_ge_four_mul (n k : ℕ) (_hk_pos : 1 ≤ k) (hk_lt : k < n) :
    4 * (k : ℝ) * ((n - k : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hkink : 4 * (k : ℝ) * ((n - k : ℕ) : ℝ) = (n : ℝ)^2 - (2 * (k : ℝ) - n)^2 := by
    rw [Nat.cast_sub hk_lt.le]; ring
  linarith [sq_nonneg (2 * (k : ℝ) - n)]

/-- √(n²/(4k(n-k))) ≥ 1 by AM-GM. -/
theorem sqrt_ratio_ge_one (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    1 ≤ Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ))) := by
  have hk_pos' : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  rw [← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  have hdenom_pos : (0 : ℝ) < 4 * k * (n - k : ℕ) := by positivity
  rw [le_div_iff₀ hdenom_pos]
  linarith [sq_ge_four_mul n k hk_pos hk_lt]

/-- (π/s₁²) × √(n²/(4k(n-k))) ≥ 1/2 for the lower bound.
    Combines π/s₁² ≥ 1/2 with √(n²/(4k(n-k))) ≥ 1. -/
theorem pi_s1_prefactor_ge_half (n k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < n) :
    Real.pi / Stirling.stirlingSeq 1 ^ 2 *
      Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ))) ≥ 1 / 2 := by
  have h1 : Real.pi / Stirling.stirlingSeq 1 ^ 2 ≥ 1 / 2 := pi_div_s1_sq_ge_half
  have h2 : 1 ≤ Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ))) :=
    sqrt_ratio_ge_one n k hk_pos hk_lt
  calc Real.pi / Stirling.stirlingSeq 1 ^ 2 *
        Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ)))
      ≥ 1 / 2 * 1 := by
        apply mul_le_mul h1 h2 (by linarith) (by linarith)
    _ = 1 / 2 := mul_one _

/-- exp_factor × exp(s²/(2n)) ≥ exp_factor (since exp(s²/(2n)) ≥ 1). -/
theorem exp_factor_times_exp_ge (n k : ℕ) (s : ℤ) :
    ((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) ≤
    ((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) *
      Real.exp ((s : ℝ) ^ 2 / (2 * n)) := by
  have hexp_ge : 1 ≤ Real.exp ((s : ℝ) ^ 2 / (2 * n)) := by
    apply Real.one_le_exp; positivity
  have hef_nn : 0 ≤ ((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) := by
    positivity
  linarith [mul_le_mul_of_nonneg_left hexp_ge hef_nn]

/-! ## Pinsker Excess Bound Infrastructure

For the lower bound of local_clt_central_region, we need to show that
the "ratio" R = √(1/(1-v²)) × exp(-n(h(v)-v²)/2) ≥ 1/√e.
This requires bounding the Pinsker excess h(v) - v².
-/

/-- e⁵ < 16π². Key numerical bound for the lower bound proof. -/
theorem e_fifth_lt_sixteen_pi_sq : Real.exp 1 ^ 5 < 16 * Real.pi ^ 2 := by
  have he_bound : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
  have hpi_bound : 3.14 < Real.pi := pi_gt_d2
  -- e² < 2.72² = 7.3984
  have he_sq : Real.exp 1 ^ 2 < 7.3985 := by nlinarith [Real.exp_pos 1]
  -- e⁴ < 7.3985² < 54.74
  have he4 : Real.exp 1 ^ 4 < 54.74 := by
    have : Real.exp 1 ^ 4 = (Real.exp 1 ^ 2) ^ 2 := by ring
    rw [this]; nlinarith [Real.exp_pos 1]
  -- e⁵ = e⁴ × e < 54.74 × 2.72 = 148.8928
  have he5 : Real.exp 1 ^ 5 < 148.9 := by
    have : Real.exp 1 ^ 5 = Real.exp 1 ^ 4 * Real.exp 1 := by ring
    rw [this]; nlinarith [Real.exp_pos 1]
  -- 16π² > 16 × 3.14² = 157.7536 > 148.9
  nlinarith

/-- Cubic upper bound on log difference: log(1+t) - log(1-t) - 2t ≤ 2t³/(3(1-t²)).
    Proof: g(t) = 2t³/(3(1-t²)) - (log(1+t) - log(1-t) - 2t) satisfies g(0)=0
    and g'(t) = 4t⁴/(3(1-t²)²) ≥ 0 on [0,1). -/
private theorem log_diff_cubic_bound {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Real.log (1 + t) - Real.log (1 - t) - 2 * t ≤ 2 * t ^ 3 / (3 * (1 - t ^ 2)) := by
  by_cases ht_eq : t = 0
  · simp [ht_eq, Real.log_one]
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_eq)
  have ht_sq : t ^ 2 < 1 := by nlinarith
  have h1mt2 : (0 : ℝ) < 1 - t ^ 2 := by linarith
  suffices h : 0 ≤ 2 * t ^ 3 / (3 * (1 - t ^ 2)) -
      (Real.log (1 + t) - Real.log (1 - t) - 2 * t) by linarith
  have hg0 : 2 * (0 : ℝ) ^ 3 / (3 * (1 - (0 : ℝ) ^ 2)) -
      (Real.log (1 + (0 : ℝ)) - Real.log (1 - (0 : ℝ)) - 2 * (0 : ℝ)) = 0 := by
    simp [Real.log_one]
  have hmono : MonotoneOn
      (fun s => 2 * s ^ 3 / (3 * (1 - s ^ 2)) -
        (Real.log (1 + s) - Real.log (1 - s) - 2 * s)) (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · -- ContinuousOn
      apply ContinuousOn.sub
      · apply ContinuousOn.div (continuousOn_const.mul (continuousOn_pow 3))
          (continuousOn_const.mul (continuousOn_const.sub (continuousOn_pow 2)))
        intro s hs; exact ne_of_gt (by nlinarith [hs.1, hs.2, sq_nonneg s] : (0:ℝ) < 3 * (1 - s ^ 2))
      · apply ContinuousOn.sub
        · apply ContinuousOn.sub
          · exact ContinuousOn.log (continuousOn_const.add continuousOn_id)
              (fun s hs => ne_of_gt (by linarith [hs.1] : (0:ℝ) < 1 + s))
          · exact ContinuousOn.log (continuousOn_const.sub continuousOn_id)
              (fun s hs => ne_of_gt (by linarith [hs.2] : (0:ℝ) < 1 - s))
        · exact continuousOn_const.mul continuousOn_id
    · -- DifferentiableOn on interior
      intro s hs
      rw [interior_Icc] at hs
      have h1pos : (0:ℝ) < 1 + s := by linarith [hs.1]
      have h2pos : (0:ℝ) < 1 - s := by linarith [hs.2]
      have h_den_pos : (0:ℝ) < 3 * (1 - s ^ 2) := by nlinarith
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.sub
      · exact ((differentiableAt_const _).mul (differentiableAt_pow 3)).div
            ((differentiableAt_const _).mul ((differentiableAt_const _).sub (differentiableAt_pow 2)))
            (ne_of_gt h_den_pos)
      · exact (((differentiableAt_const (1:ℝ)).add differentiableAt_id).log (ne_of_gt h1pos)).sub
            (((differentiableAt_const (1:ℝ)).sub differentiableAt_id).log (ne_of_gt h2pos)) |>.sub
            ((differentiableAt_const _).mul differentiableAt_id)
    · -- Derivative nonneg: g'(s) = 4s⁴/(3(1-s²)²) ≥ 0
      intro s hs
      rw [interior_Icc] at hs
      have h1pos : (0:ℝ) < 1 + s := by linarith [hs.1]
      have h2pos : (0:ℝ) < 1 - s := by linarith [hs.2]
      have h_ssq : s ^ 2 < 1 := by nlinarith
      have h_den_pos : (0:ℝ) < 3 * (1 - s ^ 2) := by nlinarith
      -- HasDerivAt for 2s³/(3(1-s²))
      have hd_num : HasDerivAt (fun u => 2 * u ^ 3) (6 * s ^ 2) s := by
        have := (hasDerivAt_pow 3 s).const_mul 2
        convert this using 1; ring
      have hd_den : HasDerivAt (fun u => 3 * (1 - u ^ 2)) (3 * (-(2 * s))) s := by
        have hd_sq : HasDerivAt (fun u => u ^ 2) (2 * s) s := by
          have := hasDerivAt_pow 2 s; simp [pow_one] at this; exact this
        convert (hasDerivAt_const s 3).mul ((hasDerivAt_const s 1).sub hd_sq) using 1; ring
      have hd_quot : HasDerivAt (fun u => 2 * u ^ 3 / (3 * (1 - u ^ 2)))
          ((6 * s ^ 2 * (3 * (1 - s ^ 2)) - 2 * s ^ 3 * (3 * (-(2 * s)))) /
            (3 * (1 - s ^ 2)) ^ 2) s :=
        hd_num.div hd_den (ne_of_gt h_den_pos)
      -- HasDerivAt for log(1+s) - log(1-s) - 2s
      have hd1 : HasDerivAt (fun u => (1:ℝ) + u) 1 s := by
        simpa using (hasDerivAt_const s (1:ℝ)).add (hasDerivAt_id s)
      have hd2 : HasDerivAt (fun u => (1:ℝ) - u) (-1) s := by
        simpa using (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)
      have hd_log1 : HasDerivAt (fun u => Real.log (1 + u)) (1 / (1 + s)) s :=
        hd1.log (ne_of_gt h1pos)
      have hd_log2 : HasDerivAt (fun u => Real.log (1 - u)) ((-1) / (1 - s)) s :=
        hd2.log (ne_of_gt h2pos)
      have hd_lin : HasDerivAt (fun u => (2:ℝ) * u) 2 s := by
        simpa using (hasDerivAt_id s).const_mul (2:ℝ)
      have hd_rhs : HasDerivAt
          (fun u => Real.log (1 + u) - Real.log (1 - u) - 2 * u)
          (1 / (1 + s) - (-1) / (1 - s) - 2) s :=
        (hd_log1.sub hd_log2).sub hd_lin
      have hd_g : HasDerivAt
          (fun s => 2 * s ^ 3 / (3 * (1 - s ^ 2)) -
            (Real.log (1 + s) - Real.log (1 - s) - 2 * s))
          ((6 * s ^ 2 * (3 * (1 - s ^ 2)) - 2 * s ^ 3 * (3 * (-(2 * s)))) /
            (3 * (1 - s ^ 2)) ^ 2 - (1 / (1 + s) - (-1) / (1 - s) - 2)) s :=
        hd_quot.sub hd_rhs
      rw [hd_g.deriv]
      -- Show the derivative value = 4s⁴/(3(1-s²)²)
      have hval : (6 * s ^ 2 * (3 * (1 - s ^ 2)) - 2 * s ^ 3 * (3 * (-(2 * s)))) /
          (3 * (1 - s ^ 2)) ^ 2 - (1 / (1 + s) - (-1) / (1 - s) - 2) =
          4 * s ^ 4 / (3 * (1 - s ^ 2) ^ 2) := by
        have h1s_ne : (1 + s : ℝ) ≠ 0 := ne_of_gt h1pos
        have h2s_ne : (1 - s : ℝ) ≠ 0 := ne_of_gt h2pos
        have h1ms2_ne : (1 - s ^ 2 : ℝ) ≠ 0 := ne_of_gt (by nlinarith)
        field_simp [h1s_ne, h2s_ne, h1ms2_ne]
        ring
      rw [hval]
      exact div_nonneg (by nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)])
        (mul_nonneg (by norm_num) (sq_nonneg _))
  have h_le := hmono (left_mem_Icc.mpr ht_pos.le) (right_mem_Icc.mpr ht_pos.le) ht_pos.le
  linarith [hg0]

/-- Pinsker excess bound: h(v) - v² ≤ v⁴/(6(1-v²)) for 0 ≤ v < 1,
    where h(v) = (1+v)ln(1+v) + (1-v)ln(1-v).
    Proof: f(v) = v⁴/(6(1-v²)) - (h(v)-v²) satisfies f(0)=0 and f'(v) ≥ 0.
    The derivative uses:
    - d/dv[v⁴/(6(1-v²))] = v³(2-v²)/(3(1-v²)²)
    - d/dv[h(v)-v²] = ln(1+v) - ln(1-v) - 2v
    - The bound ln(1+v)-ln(1-v)-2v ≤ 2v³/(3(1-v²)) (from integral of 2s²/(1-s²)). -/
theorem pinsker_excess_crude {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2 ≤
      v ^ 4 / (6 * (1 - v ^ 2)) := by
  by_cases hv_eq : v = 0
  · simp [hv_eq, Real.log_one]
  have hv_pos : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hv_eq)
  -- f(v) = v⁴/(6(1-v²)) - (h(v) - v²) ≥ 0
  suffices h : 0 ≤ v ^ 4 / (6 * (1 - v ^ 2)) -
      ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2) by linarith
  have hf0 : (0:ℝ) ^ 4 / (6 * (1 - (0:ℝ) ^ 2)) -
      ((1 + 0) * Real.log (1 + 0) + (1 - 0) * Real.log (1 - 0) - (0:ℝ) ^ 2) = 0 := by
    simp [Real.log_one]
  have hmono : MonotoneOn
      (fun t => t ^ 4 / (6 * (1 - t ^ 2)) -
        ((1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t) - t ^ 2))
      (Icc 0 v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 v)
    · -- ContinuousOn
      apply ContinuousOn.sub
      · -- t⁴/(6(1-t²)): numerator t⁴, denominator 6*(1-t²)
        apply ContinuousOn.div (continuousOn_pow 4)
          (continuousOn_const.mul (continuousOn_const.sub (continuousOn_pow 2)))
        intro t ht
        have ht1 : t < 1 := lt_of_le_of_lt ht.2 hv1
        have ht0 : 0 ≤ t := ht.1
        have h1mt : 0 ≤ 1 - t := by linarith
        exact ne_of_gt (by nlinarith [mul_nonneg h1mt ht0])
      · apply ContinuousOn.sub
        · apply ContinuousOn.add
          · exact (continuousOn_const.add continuousOn_id).mul
              (ContinuousOn.log (continuousOn_const.add continuousOn_id)
                (fun t ht => ne_of_gt (show (0:ℝ) < 1 + t by linarith [ht.1])))
          · exact (continuousOn_const.sub continuousOn_id).mul
              (ContinuousOn.log (continuousOn_const.sub continuousOn_id)
                (fun t ht => ne_of_gt (show (0:ℝ) < 1 - t by
                  linarith [ht.2, hv1])))
        · exact continuousOn_pow 2
    · -- DifferentiableOn on interior
      intro t ht
      rw [interior_Icc] at ht
      have h1pos : (0:ℝ) < 1 + t := by linarith [ht.1]
      have h2pos : (0:ℝ) < 1 - t := by linarith [ht.2, hv1]
      have h_tsq : t ^ 2 < 1 := by nlinarith
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.sub
      · exact (differentiableAt_pow 4).div
            ((differentiableAt_const _).mul ((differentiableAt_const _).sub (differentiableAt_pow 2)))
            (ne_of_gt (by nlinarith))
      · exact ((hasDerivAt_mul_log_add t h1pos).differentiableAt.add
            (hasDerivAt_mul_log_sub t h2pos).differentiableAt).sub (differentiableAt_pow 2)
    · -- Derivative nonneg on interior
      -- f'(t) = t³(2-t²)/(3(1-t²)²) - (log(1+t)-log(1-t)-2t) ≥ 0
      intro t ht
      rw [interior_Icc] at ht
      have h1pos : (0:ℝ) < 1 + t := by linarith [ht.1]
      have h2pos : (0:ℝ) < 1 - t := by linarith [ht.2, hv1]
      have h_tsq : t ^ 2 < 1 := by nlinarith
      have h_den_pos : (0:ℝ) < 6 * (1 - t ^ 2) := by linarith
      -- HasDerivAt for t⁴/(6(1-t²))
      have hd_num : HasDerivAt (fun s => s ^ 4) (4 * t ^ 3) t := by
        convert hasDerivAt_pow 4 t using 1
      have hd_den : HasDerivAt (fun s => 6 * (1 - s ^ 2)) (6 * (-(2 * t))) t := by
        have hd_sq : HasDerivAt (fun s => s ^ 2) (2 * t) t := by
          convert hasDerivAt_pow 2 t using 1; simp [pow_one]
        convert (hasDerivAt_const t 6).mul ((hasDerivAt_const t 1).sub hd_sq) using 1
        ring
      have hd_quot : HasDerivAt (fun s => s ^ 4 / (6 * (1 - s ^ 2)))
          ((4 * t ^ 3 * (6 * (1 - t ^ 2)) - t ^ 4 * (6 * (-(2 * t)))) /
            (6 * (1 - t ^ 2)) ^ 2) t :=
        hd_num.div hd_den (ne_of_gt h_den_pos)
      -- HasDerivAt for (1+t)log(1+t) + (1-t)log(1-t) - t²
      have hd_sq : HasDerivAt (fun s => s ^ 2) (2 * t) t := by
        have := hasDerivAt_pow 2 t; simp [pow_one] at this; exact this
      have hd_hv : HasDerivAt
          (fun s => (1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s) - s ^ 2)
          (Real.log (1 + t) - Real.log (1 - t) - 2 * t) t := by
        have hd := (hasDerivAt_mul_log_add t h1pos).add
          (hasDerivAt_mul_log_sub t h2pos) |>.sub hd_sq
        convert hd using 1; ring
      -- HasDerivAt for the full f
      have hd_f : HasDerivAt
          (fun s => s ^ 4 / (6 * (1 - s ^ 2)) -
            ((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s) - s ^ 2))
          ((4 * t ^ 3 * (6 * (1 - t ^ 2)) - t ^ 4 * (6 * (-(2 * t)))) /
            (6 * (1 - t ^ 2)) ^ 2 -
            (Real.log (1 + t) - Real.log (1 - t) - 2 * t)) t :=
        hd_quot.sub hd_hv
      rw [hd_f.deriv]
      -- Bound using log_diff_cubic_bound
      have h_cubic := log_diff_cubic_bound (le_of_lt ht.1) (lt_trans ht.2 hv1)
      -- The quotient derivative simplifies to t³(2-t²)/(3(1-t²)²)
      -- We show: t³(2-t²)/(3(1-t²)²) - (log(1+t)-log(1-t)-2t) ≥ 0
      -- Using: log(1+t)-log(1-t)-2t ≤ 2t³/(3(1-t²))
      -- And: t³(2-t²)/(3(1-t²)²) - 2t³/(3(1-t²)) = t⁵/(3(1-t²)²) ≥ 0
      have h_simp : (4 * t ^ 3 * (6 * (1 - t ^ 2)) - t ^ 4 * (6 * (-(2 * t)))) /
          (6 * (1 - t ^ 2)) ^ 2 = t ^ 3 * (2 - t ^ 2) / (3 * (1 - t ^ 2) ^ 2) := by
        field_simp; ring
      rw [h_simp]
      have h_lower : 2 * t ^ 3 / (3 * (1 - t ^ 2)) ≤
          t ^ 3 * (2 - t ^ 2) / (3 * (1 - t ^ 2) ^ 2) := by
        have h_diff : t ^ 3 * (2 - t ^ 2) / (3 * (1 - t ^ 2) ^ 2) -
            2 * t ^ 3 / (3 * (1 - t ^ 2)) = t ^ 5 / (3 * (1 - t ^ 2) ^ 2) := by
          field_simp; ring
        linarith [show 0 ≤ t ^ 5 / (3 * (1 - t ^ 2) ^ 2) from
          div_nonneg (pow_nonneg (le_of_lt ht.1) 5) (mul_nonneg (by norm_num) (sq_nonneg _))]
      linarith
  have h_le := hmono (left_mem_Icc.mpr hv_pos.le) (right_mem_Icc.mpr hv_pos.le) hv_pos.le
  linarith [hf0]

/-- Symmetric version of pinsker_excess_crude for |v| < 1. -/
theorem pinsker_excess_crude_abs {v : ℝ} (hv : |v| < 1) :
    (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2 ≤
      v ^ 4 / (6 * (1 - v ^ 2)) := by
  by_cases hv0 : 0 ≤ v
  · exact pinsker_excess_crude hv0 (abs_lt.mp hv).2
  · push_neg at hv0
    have h := pinsker_excess_crude (neg_nonneg.mpr (le_of_lt hv0)) (by linarith [(abs_lt.mp hv).1])
    simp only [neg_sq] at h ⊢
    convert h using 2 <;> ring_nf

/-! ## Combined Lower Bound for Central Region -/

/-- For v² ≤ 49/(9n) and n ≥ 9: (n+6)v⁴ ≤ 6. Arithmetic step for the combined bound. -/
private theorem nv4_bound_central (n : ℕ) (v : ℝ) (hn : 9 ≤ n)
    (hv_sq : v ^ 2 ≤ 49 / (9 * (n : ℝ))) :
    ((n : ℝ) + 6) * v ^ 4 ≤ 6 := by
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_real : (9:ℝ) ≤ n := Nat.cast_le.mpr hn
  -- v⁴ = (v²)² ≤ (49/(9n))²
  have hv4 : v ^ 4 ≤ (49 / (9 * (n : ℝ))) ^ 2 := by
    have : v ^ 4 = (v ^ 2) ^ 2 := by ring
    rw [this]; exact sq_le_sq' (by linarith [sq_nonneg v]) hv_sq
  -- (n+6) × (49/(9n))² = 2401(n+6)/(81n²)
  -- Need: 2401(n+6)/(81n²) ≤ 6, i.e., 2401(n+6) ≤ 486n²
  -- i.e., 486n² - 2401n - 14406 ≥ 0, which holds for n ≥ 9
  have step1 : ((n : ℝ) + 6) * v ^ 4 ≤ (n + 6) * (49 / (9 * n)) ^ 2 :=
    mul_le_mul_of_nonneg_left hv4 (by linarith)
  have step2 : (n + 6) * (49 / (9 * (n : ℝ))) ^ 2 = 2401 * (n + 6) / (81 * n ^ 2) := by
    field_simp; ring
  have step3 : 2401 * ((n : ℝ) + 6) / (81 * n ^ 2) ≤ 6 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 81 * n ^ 2)]
    nlinarith
  linarith

/-- Combined Pinsker-log bound: (1-v²)exp(n(h(v)-v²)) ≤ e
    for 0 ≤ v < 1, v² ≤ 49/(9n), n ≥ 9.
    Uses: h(v)-v² ≤ v⁴/(6(1-v²)) and ln(1-v²) ≤ -v². -/
theorem combined_exp_bound (n : ℕ) (v : ℝ) (hn : 9 ≤ n)
    (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hv_sq : v ^ 2 ≤ 49 / (9 * (n : ℝ))) :
    (1 - v ^ 2) * Real.exp (↑n * ((1 + v) * Real.log (1 + v) +
      (1 - v) * Real.log (1 - v) - v ^ 2)) ≤ Real.exp 1 := by
  have hv_sq_lt : v ^ 2 < 1 := by nlinarith
  have h1mv2_pos : (0:ℝ) < 1 - v ^ 2 := by linarith
  -- Step 1: Bound h(v)-v² using pinsker_excess_crude
  have h_excess := pinsker_excess_crude hv0 hv1
  -- Step 2: Bound n(h(v)-v²) ≤ nv⁴/(6(1-v²))
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have h_n_excess : ↑n * ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2) ≤
      ↑n * (v ^ 4 / (6 * (1 - v ^ 2))) :=
    mul_le_mul_of_nonneg_left h_excess (Nat.cast_nonneg n)
  -- Step 3: ln(1-v²) ≤ -v² (from Mathlib: log(x) ≤ x - 1 for x > 0)
  have h_log : Real.log (1 - v ^ 2) ≤ -v ^ 2 := by
    have := Real.log_le_sub_one_of_pos h1mv2_pos
    linarith
  -- Step 4: Show ln(1-v²) + n × v⁴/(6(1-v²)) ≤ 1
  have h_arith := nv4_bound_central n v hn hv_sq
  have h_ineq : -v ^ 2 + ↑n * (v ^ 4 / (6 * (1 - v ^ 2))) ≤ 1 := by
    rw [← sub_nonneg]
    have h6_pos : (0:ℝ) < 6 * (1 - v ^ 2) := by positivity
    have : 1 - (-v ^ 2 + ↑n * (v ^ 4 / (6 * (1 - v ^ 2)))) =
        (6 - (↑n + 6) * v ^ 4) / (6 * (1 - v ^ 2)) := by
      field_simp; ring
    rw [this]
    exact div_nonneg (by nlinarith [h_arith]) (le_of_lt h6_pos)
  -- Combine: ln(1-v²) + n(h(v)-v²) ≤ -v² + nv⁴/(6(1-v²)) ≤ 1
  have h_combined : Real.log (1 - v ^ 2) +
      ↑n * ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2) ≤ 1 :=
    by linarith
  -- Now: (1-v²)exp(n(h(v)-v²)) = exp(ln(1-v²) + n(h(v)-v²)) ≤ exp(1)
  calc (1 - v ^ 2) * Real.exp (↑n * ((1 + v) * Real.log (1 + v) +
        (1 - v) * Real.log (1 - v) - v ^ 2))
      = Real.exp (Real.log (1 - v ^ 2) +
        ↑n * ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2)) := by
        rw [Real.exp_add, Real.exp_log h1mv2_pos]
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr h_combined

/-- The key lower bound: for n ≥ 9, 1 ≤ k < n, (2k-n)² ≤ 49n/9,
    exp(-s²/(2n)) / 2 ≤ (π/s₁²) × √(n²/(4k(n-k))) × exp_factor.
    This directly gives gaussApprox/2 ≤ (π/s₁²) × central/2^n after factoring out √(2/(πn)).

    Proof: Express product in terms of v = (2k-n)/n, use combined_exp_bound
    to show √(1/(1-v²)) × exp(-n(h(v)-v²)/2) ≥ 1/√e, then π/s₁² = 2π/e²
    gives product ≥ 2π/e^(5/2) ≥ 1/2 by e⁵ < 16π². -/
theorem lower_bound_exp_factor_ge (n k : ℕ) (hn : 9 ≤ n) (hk_pos : 1 ≤ k) (hk_lt : k < n)
    (hs : (2 * (k : ℝ) - n) ^ 2 ≤ 49 * (n : ℝ) / 9) :
    Real.exp (-(2 * (k : ℝ) - n) ^ 2 / (2 * n)) / 2 ≤
      Real.pi / Stirling.stirlingSeq 1 ^ 2 *
      Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ))) *
      ((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) := by
  -- Setup
  have hn_pos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk_pos' : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hnk_pos : (0:ℝ) < (n - k : ℕ) := Nat.cast_pos.mpr (by omega)
  set v := (2 * (k : ℝ) - n) / n with hv_def
  have hv_plus : 1 + v = 2 * ↑k / ↑n := by
    simp only [hv_def]; field_simp; ring
  have hv_minus : 1 - v = 2 * ↑(n - k) / ↑n := by
    rw [Nat.cast_sub hk_lt.le]; simp only [hv_def]; field_simp; ring
  have h1v_pos : 0 < 1 + v := by rw [hv_plus]; positivity
  have h1mv_pos : 0 < 1 - v := by rw [hv_minus]; positivity
  have hv_abs : |v| < 1 := by
    rw [abs_div, abs_of_pos hn_pos, div_lt_one hn_pos, abs_lt]
    have hk_real : (k : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hk_lt
    constructor <;> nlinarith
  have hv_sq_lt : v ^ 2 < 1 := by nlinarith [sq_abs v]
  have h1mv2_pos : (0:ℝ) < 1 - v ^ 2 := by linarith
  have hv_sq : v ^ 2 ≤ 49 / (9 * (n : ℝ)) := by
    have hv_sq_eq : v ^ 2 = (2 * (k : ℝ) - n) ^ 2 / n ^ 2 := by
      simp only [hv_def]; field_simp
    rw [hv_sq_eq, div_le_div_iff₀ (by positivity : (0:ℝ) < n ^ 2) (by positivity)]
    nlinarith
  -- Reduce to: 1/2 ≤ product × exp(s²/(2n))
  suffices hsuff : 1 / 2 ≤
      Real.pi / Stirling.stirlingSeq 1 ^ 2 *
      Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ))) *
      (((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) *
        Real.exp ((2 * (k : ℝ) - n) ^ 2 / (2 * n))) by
    -- Reassociate: A * B * (C * D * E) = (A * B * C * D) * E
    have h_reassoc : Real.pi / Stirling.stirlingSeq 1 ^ 2 *
        Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ))) *
        (((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) *
          Real.exp ((2 * (k : ℝ) - n) ^ 2 / (2 * n))) =
        (Real.pi / Stirling.stirlingSeq 1 ^ 2 *
        Real.sqrt ((n : ℝ) ^ 2 / (4 * k * (n - k : ℕ))) *
        ((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k)) *
          Real.exp ((2 * (k : ℝ) - n) ^ 2 / (2 * n)) := by
      simp only [mul_assoc]
    rw [h_reassoc] at hsuff
    -- hsuff : 1/2 ≤ product * exp(s²/(2n))
    have hE_pos := Real.exp_pos ((2 * (k : ℝ) - n) ^ 2 / (2 * n))
    rw [← div_le_iff₀ hE_pos] at hsuff
    -- hsuff : 1/2 / exp(s²/(2n)) ≤ product
    -- Convert: exp(-s²/(2n))/2 = 1/(2 * exp(s²/(2n))) = 1/2 / exp(s²/(2n))
    rw [show Real.exp (-(2 * (k : ℝ) - n) ^ 2 / (2 * n)) / 2 =
        1 / 2 / Real.exp ((2 * (k : ℝ) - n) ^ 2 / (2 * n)) from by
      rw [neg_div, Real.exp_neg, ← one_div, div_right_comm]]
    exact hsuff
  -- Rewrite the product in terms of v
  have ha_eq : (n : ℝ) / (2 * k) = 1 / (1 + v) := by rw [hv_plus]; field_simp
  have hb_eq : (n : ℝ) / (2 * (n - k : ℕ)) = 1 / (1 - v) := by rw [hv_minus]; field_simp
  have h_product_eq : ((n : ℝ) / (2 * k)) ^ k * ((n : ℝ) / (2 * (n - k : ℕ))) ^ (n - k) *
      Real.exp ((2 * (k : ℝ) - n) ^ 2 / (2 * n)) =
      Real.exp (↑n / 2 * (v ^ 2 -
        ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v)))) := by
    rw [ha_eq, hb_eq]
    rw [pow_eq_exp_mul_log (by positivity : (0:ℝ) < 1 / (1 + v)) k]
    rw [pow_eq_exp_mul_log (by positivity : (0:ℝ) < 1 / (1 - v)) (n - k)]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt h1v_pos)]
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt h1mv_pos)]
    simp only [Real.log_one, zero_sub]
    have hsq : (2 * (k : ℝ) - n) ^ 2 / (2 * n) = n / 2 * v ^ 2 := by
      simp only [hv_def]; field_simp
    rw [hsq]
    have hk_eq : (k : ℝ) = ↑n * (1 + v) / 2 := by rw [hv_plus]; field_simp
    have hnk_eq : ((n - k : ℕ) : ℝ) = ↑n * (1 - v) / 2 := by rw [hv_minus]; field_simp
    rw [hk_eq, hnk_eq]; ring
  -- Use combined_exp_bound with |v|
  have hv_abs_sq : |v| ^ 2 ≤ 49 / (9 * (n : ℝ)) := by rwa [sq_abs]
  have h_combined := combined_exp_bound n |v| hn (abs_nonneg v)
    (by linarith [(abs_lt.mp hv_abs).2]) hv_abs_sq
  -- Rewrite from |v| to v using symmetry of h
  have h_sym1 : |v| ^ 2 = v ^ 2 := sq_abs v
  have h_exponent_eq : ↑n * ((1 + |v|) * Real.log (1 + |v|) + (1 - |v|) * Real.log (1 - |v|) -
      |v| ^ 2) = ↑n * ((1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) - v ^ 2) := by
    congr 1
    by_cases hv_sign : 0 ≤ v
    · rw [abs_of_nonneg hv_sign]
    · push_neg at hv_sign
      rw [abs_of_neg hv_sign]
      have h1 : (1 : ℝ) + -v = 1 - v := by ring
      have h2 : (1 : ℝ) - -v = 1 + v := by ring
      have h3 : (-v) ^ 2 = v ^ 2 := neg_sq v
      rw [h1, h2, h3, add_comm ((1 - v) * Real.log (1 - v))]
  rw [h_exponent_eq, h_sym1] at h_combined
  -- h_combined : (1-v²) × exp(n(h(v)-v²)) ≤ e
  set h_v := (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) with hv_formula
  -- exp(n(v²-h_v)/2) ≥ √((1-v²)/e)
  have h_exp_lower : Real.sqrt ((1 - v ^ 2) / Real.exp 1) ≤
      Real.exp (↑n / 2 * (v ^ 2 - h_v)) := by
    rw [show Real.exp (↑n / 2 * (v ^ 2 - h_v)) =
        Real.sqrt (Real.exp (↑n / 2 * (v ^ 2 - h_v)) ^ 2) from
      (Real.sqrt_sq (Real.exp_nonneg _)).symm]
    apply Real.sqrt_le_sqrt
    -- Need: (1-v²)/e ≤ [exp(n/2(v²-h_v))]² = exp(n(v²-h_v))
    have h_sq : Real.exp (↑n / 2 * (v ^ 2 - h_v)) ^ 2 =
        Real.exp (↑n * (v ^ 2 - h_v)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h_sq, div_le_iff₀ (Real.exp_pos 1), ← Real.exp_add]
    -- Need: 1-v² ≤ exp(1 + n(v²-h_v))
    -- From h_combined: (1-v²) × exp(n(h_v-v²)) ≤ e = exp(1)
    -- So 1-v² ≤ exp(1) × exp(-n(h_v-v²)) = exp(1+n(v²-h_v))
    -- But exp(-n(h_v-v²)) = exp(n(v²-h_v))
    -- So 1-v² ≤ exp(1) / exp(n(h_v-v²)) = exp(1-n(h_v-v²)) = exp(1+n(v²-h_v))
    -- 1-v² ≤ exp(1)/exp(n(h_v-v²)) = exp(1+n(v²-h_v))
    rw [show ↑n * (v ^ 2 - h_v) + 1 = 1 - ↑n * (h_v - v ^ 2) from by ring,
      Real.exp_sub]
    rwa [le_div_iff₀ (Real.exp_pos _)]
  -- √(n²/(4k(nk))) = √(1/(1-v²))
  have h_ratio : (n : ℝ) ^ 2 / (4 * k * (n - k : ℕ)) = 1 / (1 - v ^ 2) := by
    have h4kink : 4 * (k : ℝ) * (n - k : ℕ) = (n : ℝ) ^ 2 * (1 - v ^ 2) := by
      rw [Nat.cast_sub hk_lt.le]; simp only [hv_def]; field_simp; ring
    rw [h4kink]; field_simp
  -- π/s₁² = 2π/e²
  have hs₁_sq : Stirling.stirlingSeq 1 ^ 2 = Real.exp 1 ^ 2 / 2 := by
    rw [Stirling.stirlingSeq_one, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have h_pi_s1 : Real.pi / Stirling.stirlingSeq 1 ^ 2 = 2 * Real.pi / Real.exp 1 ^ 2 := by
    rw [hs₁_sq]; field_simp
  -- Combine: product ≥ (2π/e²) × √(1/(1-v²)) × √((1-v²)/e) = (2π/e²)/√e ≥ 1/2
  rw [h_product_eq, h_pi_s1, h_ratio]
  -- √(1/(1-v²)) × exp(n/2(v²-h_v)) ≥ √(1/(1-v²)) × √((1-v²)/e)
  have h_sqrt_prod : Real.sqrt (1 / (1 - v ^ 2)) * Real.sqrt ((1 - v ^ 2) / Real.exp 1) =
      1 / Real.sqrt (Real.exp 1) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 1 / (1 - v ^ 2))]
    have h_cancel : 1 / (1 - v ^ 2) * ((1 - v ^ 2) / Real.exp 1) = 1 / Real.exp 1 := by
      field_simp
    rw [h_cancel, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1), Real.sqrt_one]
  -- e^(5/2) ≤ 4π, i.e., e⁵ ≤ 16π²
  have h_final : 1 / 2 ≤ 2 * Real.pi / Real.exp 1 ^ 2 * (1 / Real.sqrt (Real.exp 1)) := by
    -- Need: 1/2 ≤ 2π/(e²√e). Equivalent to e²√e ≤ 4π.
    have h_rhs : 2 * Real.pi / Real.exp 1 ^ 2 * (1 / Real.sqrt (Real.exp 1)) =
        2 * Real.pi / (Real.exp 1 ^ 2 * Real.sqrt (Real.exp 1)) := by
      field_simp
    rw [h_rhs, le_div_iff₀ (by positivity : 0 < Real.exp 1 ^ 2 * Real.sqrt (Real.exp 1))]
    -- Goal: 1/2 * (e² * √e) ≤ 2π. Suffices: e²√e ≤ 4π.
    have h_sq_bound : (Real.exp 1 ^ 2 * Real.sqrt (Real.exp 1)) ^ 2 = Real.exp 1 ^ 5 := by
      rw [mul_pow, ← pow_mul, Real.sq_sqrt (le_of_lt (Real.exp_pos 1))]; ring
    have h_le_4pi : Real.exp 1 ^ 2 * Real.sqrt (Real.exp 1) ≤ 4 * Real.pi := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.exp 1 ^ 2 * Real.sqrt (Real.exp 1)),
          ← Real.sqrt_sq (by positivity : 0 ≤ 4 * Real.pi)]
      apply Real.sqrt_le_sqrt
      have h4pi_sq : (4 * Real.pi) ^ 2 = 16 * Real.pi ^ 2 := by ring
      rw [h_sq_bound, h4pi_sq]
      exact le_of_lt e_fifth_lt_sixteen_pi_sq
    calc 1 / 2 * (Real.exp 1 ^ 2 * Real.sqrt (Real.exp 1))
        ≤ 1 / 2 * (4 * Real.pi) := by
          apply mul_le_mul_of_nonneg_left h_le_4pi (by norm_num)
      _ = 2 * Real.pi := by ring
  -- Assemble the final calc
  calc 1 / 2
      ≤ 2 * Real.pi / Real.exp 1 ^ 2 * (1 / Real.sqrt (Real.exp 1)) := h_final
    _ = 2 * Real.pi / Real.exp 1 ^ 2 *
        (Real.sqrt (1 / (1 - v ^ 2)) * Real.sqrt ((1 - v ^ 2) / Real.exp 1)) := by
        rw [h_sqrt_prod]
    _ ≤ 2 * Real.pi / Real.exp 1 ^ 2 *
        (Real.sqrt (1 / (1 - v ^ 2)) * Real.exp (↑n / 2 * (v ^ 2 - h_v))) := by
        apply mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_exp_lower (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by rw [mul_assoc]

end SPDE.Nonstandard.LocalCLTHelpers
