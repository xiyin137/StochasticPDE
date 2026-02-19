/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.Anderson.LocalCLTHelpers
import StochasticPDE.Nonstandard.Anderson.RatioConvergenceHelpers
import StochasticPDE.Nonstandard.Foundation.Arithmetic

/-!
# Binomial/Gaussian Ratio Helpers

Infrastructure for proving `binomProb_ratio_near_one`: the ratio C(k,j)/2^k
divided by the Gaussian density times mesh width converges to 1.

## Key Results

* `binomProb_stirling_decomp` - algebraic identity: C(k,j)/2^k = θ × decomp,
  where θ = stirlingSeq(k)√π/(stirlingSeq(j)×stirlingSeq(k-j)) → 1.
-/

open Real Finset

namespace SPDE.Nonstandard.BinomGaussRatioHelpers

/-! ## Algebraic Identity: C(k,j)/2^k = θ × decomp -/

/-- √(2πm) = √π × √(2m) for positive m. -/
theorem sqrt_two_pi_eq (m : ℕ) (_hm : (0 : ℝ) < ↑m) :
    Real.sqrt (2 * Real.pi * ↑m) = Real.sqrt Real.pi * Real.sqrt (2 * ↑m) := by
  rw [show 2 * Real.pi * (↑m : ℝ) = Real.pi * (2 * ↑m) from by ring,
      Real.sqrt_mul (le_of_lt Real.pi_pos)]

set_option maxHeartbeats 800000 in
/-- The core factorization identity:
    k!/(j!(k-j)!) × (stirlingK × stirlingNK) / stirlingN = θ.

    After substituting factorial_eq_stirlingSeq and factoring out √(2πm) = √π × √(2m),
    all the √(2m) and (m/e)^m terms cancel, leaving stirlingSeq(k)×√π/(stirlingSeq(j)×stirlingSeq(k-j)). -/
theorem factorial_ratio_over_stirling (k j : ℕ) (hj_pos : 1 ≤ j) (hj_lt : j < k) :
    let kj := k - j
    (k.factorial : ℝ) / (j.factorial * kj.factorial) *
      ((Real.sqrt (2 * Real.pi * ↑j) * (↑j / Real.exp 1) ^ j *
       (Real.sqrt (2 * Real.pi * ↑kj) * (↑kj / Real.exp 1) ^ kj)) /
      (Real.sqrt (2 * Real.pi * ↑k) * (↑k / Real.exp 1) ^ k)) =
    Stirling.stirlingSeq k * Real.sqrt Real.pi /
      (Stirling.stirlingSeq j * Stirling.stirlingSeq kj) := by
  intro kj
  have hk0 : k ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  have hkj0 : kj ≠ 0 := show k - j ≠ 0 by omega
  have hk_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hj_r : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  have hkj_r : (0 : ℝ) < ↑kj := Nat.cast_pos.mpr (by omega)
  have hpi := Real.pi_pos
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsk : 0 < Stirling.stirlingSeq k :=
    lt_of_lt_of_le hspi (Stirling.sqrt_pi_le_stirlingSeq hk0)
  have hsj : 0 < Stirling.stirlingSeq j :=
    lt_of_lt_of_le hspi (Stirling.sqrt_pi_le_stirlingSeq hj0)
  have hskj : 0 < Stirling.stirlingSeq kj :=
    lt_of_lt_of_le hspi (Stirling.sqrt_pi_le_stirlingSeq hkj0)
  -- Substitute factorial formulas: m! = stirlingSeq(m) × √(2m) × (m/e)^m
  rw [Arithmetic.factorial_eq_stirlingSeq k hk0,
      Arithmetic.factorial_eq_stirlingSeq j hj0,
      Arithmetic.factorial_eq_stirlingSeq kj hkj0]
  -- Replace √(2πm) = √π × √(2m)
  rw [sqrt_two_pi_eq k hk_r, sqrt_two_pi_eq j hj_r, sqrt_two_pi_eq kj hkj_r]
  -- After substitution, all atoms are: stirlingSeq(m), √π, √(2m), (m/e)^m
  -- Both sides are the same monomial (just reordered), so field_simp handles it.
  have h2k_pos : (0:ℝ) < Real.sqrt (2 * ↑k) := Real.sqrt_pos.mpr (by positivity)
  have h2j_pos : (0:ℝ) < Real.sqrt (2 * ↑j) := Real.sqrt_pos.mpr (by positivity)
  have h2kj_pos : (0:ℝ) < Real.sqrt (2 * ↑kj) := Real.sqrt_pos.mpr (by positivity)
  have hpk : (0:ℝ) < (↑k / Real.exp 1) ^ k := by positivity
  have hpj : (0:ℝ) < (↑j / Real.exp 1) ^ j := by positivity
  have hpkj : (0:ℝ) < (↑kj / Real.exp 1) ^ kj := by positivity
  field_simp

set_option maxHeartbeats 800000 in
/-- The main algebraic identity:
    C(k,j)/2^k = θ × √(k/(2πj(k-j))) × (k/(2j))^j × (k/(2(k-j)))^(k-j)
    where θ = stirlingSeq(k) × √π / (stirlingSeq(j) × stirlingSeq(k-j)). -/
theorem binomProb_stirling_decomp (k j : ℕ) (hj_pos : 1 ≤ j) (hj_lt : j < k) :
    let kj := k - j
    (Nat.choose k j : ℝ) / 2 ^ k =
    (Stirling.stirlingSeq k * Real.sqrt Real.pi /
      (Stirling.stirlingSeq j * Stirling.stirlingSeq kj)) *
    (Real.sqrt (↑k / (2 * Real.pi * ↑j * ↑kj)) *
      ((↑k / (2 * ↑j)) ^ j * (↑k / (2 * ↑kj)) ^ kj)) := by
  intro kj
  have hk0 : k ≠ 0 := by omega
  have hj0 : j ≠ 0 := by omega
  have hkj0 : kj ≠ 0 := show k - j ≠ 0 by omega
  have hk_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hj_r : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  have hkj_r : (0 : ℝ) < ↑kj := Nat.cast_pos.mpr (by omega)
  have hpi := Real.pi_pos
  have hspi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  have hsk : 0 < Stirling.stirlingSeq k :=
    lt_of_lt_of_le hspi (Stirling.sqrt_pi_le_stirlingSeq hk0)
  have hsj : 0 < Stirling.stirlingSeq j :=
    lt_of_lt_of_le hspi (Stirling.sqrt_pi_le_stirlingSeq hj0)
  have hskj : 0 < Stirling.stirlingSeq kj :=
    lt_of_lt_of_le hspi (Stirling.sqrt_pi_le_stirlingSeq hkj0)
  -- Step 1: Rewrite C(k,j) as k!/(j!(k-j)!)
  have hchoose : (Nat.choose k j : ℝ) =
      (k.factorial : ℝ) / ((j.factorial : ℝ) * ((kj).factorial : ℝ)) := by
    rw [eq_div_iff (by positivity : (j.factorial : ℝ) * (kj.factorial : ℝ) ≠ 0)]
    have h := Nat.choose_mul_factorial_mul_factorial hj_lt.le
    rw [mul_assoc] at h
    exact_mod_cast h
  -- Step 2: Get key identities and remove let bindings
  have h_factor := factorial_ratio_over_stirling k j hj_pos hj_lt
  have h_decomp := LocalCLTHelpers.stirling_ratio_decomp k j hj_pos hj_lt
  -- Remove let bindings so that `set` can match expressions in these hypotheses
  change (k.factorial : ℝ) / (j.factorial * kj.factorial) *
    ((Real.sqrt (2 * Real.pi * ↑j) * (↑j / Real.exp 1) ^ j *
     (Real.sqrt (2 * Real.pi * ↑kj) * (↑kj / Real.exp 1) ^ kj)) /
    (Real.sqrt (2 * Real.pi * ↑k) * (↑k / Real.exp 1) ^ k)) =
    Stirling.stirlingSeq k * Real.sqrt Real.pi /
    (Stirling.stirlingSeq j * Stirling.stirlingSeq kj) at h_factor
  change (Real.sqrt (2 * Real.pi * ↑k) * (↑k / Real.exp 1) ^ k) /
    ((Real.sqrt (2 * Real.pi * ↑j) * (↑j / Real.exp 1) ^ j) *
     (Real.sqrt (2 * Real.pi * ↑kj) * (↑kj / Real.exp 1) ^ kj)) / (2 : ℝ) ^ k =
    Real.sqrt (↑k / (2 * Real.pi * ↑j * ↑kj)) *
    ((↑k / (2 * ↑j)) ^ j * (↑k / (2 * ↑kj)) ^ kj) at h_decomp
  -- Set up abbreviations
  set stirlingN := Real.sqrt (2 * Real.pi * ↑k) * (↑k / Real.exp 1) ^ k
  set stirlingK := Real.sqrt (2 * Real.pi * ↑j) * (↑j / Real.exp 1) ^ j
  set stirlingNK := Real.sqrt (2 * Real.pi * ↑kj) * (↑kj / Real.exp 1) ^ kj
  set θ' := Stirling.stirlingSeq k * Real.sqrt Real.pi /
    (Stirling.stirlingSeq j * Stirling.stirlingSeq kj)
  set decomp := Real.sqrt (↑k / (2 * Real.pi * ↑j * ↑kj)) *
    ((↑k / (2 * ↑j)) ^ j * (↑k / (2 * ↑kj)) ^ kj)
  have hN_pos : 0 < stirlingN := by positivity
  have hK_pos : 0 < stirlingK := by positivity
  have hNK_pos : 0 < stirlingNK := by positivity
  -- h_factor: A * (stirlingK * stirlingNK / stirlingN) = θ'
  -- h_decomp: stirlingN / (stirlingK * stirlingNK) / 2^k = decomp
  -- Goal: C(k,j) / 2^k = θ' * decomp
  -- From h_factor: A = θ' / (stirlingK * stirlingNK / stirlingN)
  have hKNK_div_N_ne : stirlingK * stirlingNK / stirlingN ≠ 0 :=
    ne_of_gt (div_pos (mul_pos hK_pos hNK_pos) hN_pos)
  have hA_eq : (k.factorial : ℝ) / (j.factorial * kj.factorial) =
      θ' / (stirlingK * stirlingNK / stirlingN) :=
    (eq_div_iff hKNK_div_N_ne).mpr h_factor
  rw [hchoose, hA_eq]
  -- Goal: θ' / (KNK/N) / 2^k = θ' * decomp
  -- Transform θ'/(KNK/N) to θ' * (N/KNK) using a/(b/c) = a * (c/b)
  rw [div_eq_mul_inv (θ') (stirlingK * stirlingNK / stirlingN), inv_div]
  -- Goal: θ' * (N/KNK) / 2^k = θ' * decomp
  rw [mul_div_assoc]
  -- Goal: θ' * (N/KNK / 2^k) = θ' * decomp
  congr 1

/-! ## Power-to-Exponential Conversion -/

/-- For a > 0, a^k = exp(k * log a). -/
theorem pow_eq_exp_log {a : ℝ} (ha : 0 < a) (k : ℕ) :
    a ^ k = Real.exp (↑k * Real.log a) := by
  conv_lhs => rw [← Real.exp_log ha]
  rw [← Real.exp_nat_mul]

/-- The power product (k/(2j))^j × (k/(2(k-j)))^(k-j) equals
    exp(-(k/2) × [(1+v)ln(1+v) + (1-v)ln(1-v)])
    where v = (2j-k)/k. -/
theorem power_product_eq_exp (k j : ℕ) (hj_pos : 1 ≤ j) (hj_lt : j < k) :
    let kj := k - j
    let v := (2 * (j : ℝ) - ↑k) / ↑k
    (↑k / (2 * ↑j)) ^ j * (↑k / (2 * ↑kj)) ^ kj =
    Real.exp (-(↑k / 2) * ((1 + v) * Real.log (1 + v) +
      (1 - v) * Real.log (1 - v))) := by
  intro kj v
  have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hj_pos' : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  have hkj_pos : (0 : ℝ) < ↑kj := Nat.cast_pos.mpr (show 0 < k - j by omega)
  -- v = (2j-k)/k, so 1+v = 2j/k, 1-v = 2(k-j)/k
  have hv_plus : 1 + v = 2 * ↑j / ↑k := by
    simp only [v]; field_simp; ring
  have hv_minus : 1 - v = 2 * ↑kj / ↑k := by
    show 1 - (2 * (j : ℝ) - ↑k) / ↑k = 2 * ↑kj / ↑k
    rw [Nat.cast_sub (le_of_lt hj_lt)]; field_simp; ring
  have h1v_pos : 0 < 1 + v := by rw [hv_plus]; positivity
  have h1mv_pos : 0 < 1 - v := by rw [hv_minus]; positivity
  -- k/(2j) = 1/(1+v) and k/(2(k-j)) = 1/(1-v)
  have ha_eq : (↑k : ℝ) / (2 * ↑j) = 1 / (1 + v) := by rw [hv_plus]; field_simp
  have hb_eq : (↑k : ℝ) / (2 * ↑kj) = 1 / (1 - v) := by rw [hv_minus]; field_simp
  rw [ha_eq, hb_eq]
  -- Convert powers to exp
  rw [pow_eq_exp_log (by positivity : (0:ℝ) < 1 / (1 + v)) j]
  rw [pow_eq_exp_log (by positivity : (0:ℝ) < 1 / (1 - v)) kj]
  rw [← Real.exp_add]
  congr 1
  -- Simplify logs: log(1/(1+v)) = -log(1+v)
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt h1v_pos)]
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (ne_of_gt h1mv_pos)]
  simp only [Real.log_one, zero_sub]
  -- j = k(1+v)/2, k-j = k(1-v)/2
  have hj_eq : (j : ℝ) = ↑k * (1 + v) / 2 := by rw [hv_plus]; field_simp
  have hkj_eq : (kj : ℝ) = ↑k * (1 - v) / 2 := by rw [hv_minus]; field_simp
  rw [hj_eq, hkj_eq]
  ring

/-- Four times j(k-j) equals k² - (2j-k)². -/
theorem four_j_kj (k j : ℕ) (hj_le : j ≤ k) :
    4 * (j : ℝ) * ↑(k - j) = (↑k) ^ 2 - (2 * ↑j - ↑k) ^ 2 := by
  rw [Nat.cast_sub hj_le]; ring

/-- The sqrt prefactor simplifies:
    √(k/(2πj(k-j))) × √(2πt) × √N / 2 = √(tN/(k(1-v²)))
    where v = (2j-k)/k and 4j(k-j) = k²(1-v²).
    Proof by squaring both sides. -/
theorem sqrt_prefactor_simplify (k j N : ℕ) (t : ℝ) (hj_pos : 1 ≤ j) (hj_lt : j < k)
    (ht : 0 < t) (hN : 0 < N) :
    let kj := k - j
    let v := (2 * (j : ℝ) - ↑k) / ↑k
    Real.sqrt (↑k / (2 * Real.pi * ↑j * ↑kj)) *
      (Real.sqrt (2 * Real.pi * t) * Real.sqrt ↑N) / 2 =
    Real.sqrt (t * ↑N / (↑k * (1 - v ^ 2))) := by
  intro kj v
  have hk_pos : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hj_pos' : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  have hkj_pos : (0 : ℝ) < ↑kj := Nat.cast_pos.mpr (show 0 < k - j by omega)
  have hpi := Real.pi_pos
  -- 1 - v² = 4j·kj/k²
  have h1mv2 : 1 - v ^ 2 = 4 * ↑j * ↑kj / ↑k ^ 2 := by
    have h4 := four_j_kj k j (le_of_lt hj_lt)
    have hk_sq_pos : (0 : ℝ) < ↑k ^ 2 := by positivity
    rw [eq_div_iff (ne_of_gt hk_sq_pos)]
    have hv_sq : v ^ 2 * ↑k ^ 2 = (2 * ↑j - ↑k) ^ 2 := by
      show ((2 * (↑j : ℝ) - ↑k) / ↑k) ^ 2 * ↑k ^ 2 = (2 * ↑j - ↑k) ^ 2
      rw [div_pow]; field_simp
    nlinarith [h4, hv_sq]
  have h1mv2_pos : 0 < 1 - v ^ 2 := by rw [h1mv2]; positivity
  -- t*N/(k*(1-v²)) = t*N*k/(4*j*kj)
  have hrhs : t * ↑N / (↑k * (1 - v ^ 2)) = t * ↑N * ↑k / (4 * ↑j * ↑kj) := by
    rw [h1mv2]; field_simp
  rw [hrhs]
  -- Prove by squaring both sides. Both are nonneg.
  have h_lhs_nn : 0 ≤ Real.sqrt (↑k / (2 * Real.pi * ↑j * ↑kj)) *
      (Real.sqrt (2 * Real.pi * t) * Real.sqrt ↑N) / 2 := by positivity
  -- LHS² = t*N*k/(4*j*kj)
  have h_sq : (Real.sqrt (↑k / (2 * Real.pi * ↑j * ↑kj)) *
      (Real.sqrt (2 * Real.pi * t) * Real.sqrt ↑N) / 2) ^ 2 =
      t * ↑N * ↑k / (4 * ↑j * ↑kj) := by
    rw [div_pow, mul_pow, mul_pow,
        Real.sq_sqrt (show 0 ≤ ↑k / (2 * Real.pi * ↑j * ↑kj) from by positivity),
        Real.sq_sqrt (show 0 ≤ 2 * Real.pi * t from by positivity),
        Real.sq_sqrt (show 0 ≤ (↑N : ℝ) from by positivity)]
    field_simp; ring
  -- LHS = √(LHS²) = √(t*N*k/(4*j*kj))
  rw [← h_sq, Real.sqrt_sq h_lhs_nn]

end SPDE.Nonstandard.BinomGaussRatioHelpers
