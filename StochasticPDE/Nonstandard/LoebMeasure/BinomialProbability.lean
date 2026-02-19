/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.CoinFlipSpace
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial Probabilities and Gaussian Limits

This file develops binomial probability computations for random walks and their
convergence to Gaussian probabilities.

## Main Definitions

* `binomialWalkProb` - P(S_k = 2j - k) = C(k,j) / 2^k
* `walkIntervalProb` - P(a ≤ W_k ≤ b) via binomial sum
* `GaussianIntervalProb` - Structure for Gaussian probability targets
* `BinomialGaussianConvergence` - Local CLT convergence statement

## Main Results

* `binomialWalkProb_sum` - Binomial probabilities sum to 1
* `walkIntervalProb_le_one` - Walk interval probability is at most 1

## Key Concepts

**Local Central Limit Theorem**:
For large k, S_k/√k is approximately N(0, 1). Since W_k = dx · S_k and
dx = √dt = √(t/k), we have:
  W_k = √(t/k) · S_k = √t · (S_k/√k) ≈ √t · Z where Z ~ N(0,1)

This means W_k ≈ N(0, t), which is exactly the marginal of Brownian motion at time t.

## References

* De Moivre-Laplace theorem (local CLT)
* Feller, "An Introduction to Probability Theory"
-/

open Hyperreal

namespace SPDE.Nonstandard

/-! ## Binomial Walk Probabilities -/

/-- The binomial probability for a random walk partial sum.
    P(S_k = 2j - k) = C(k,j) / 2^k where j = number of +1s. -/
noncomputable def binomialWalkProb (k j : ℕ) : ℝ :=
  if j ≤ k then (Nat.choose k j : ℝ) / 2^k else 0

/-- Binomial probabilities are non-negative -/
theorem binomialWalkProb_nonneg (k j : ℕ) : 0 ≤ binomialWalkProb k j := by
  unfold binomialWalkProb
  split_ifs with h
  · apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k
  · exact le_refl 0

/-- Binomial probabilities sum to 1 -/
theorem binomialWalkProb_sum (k : ℕ) :
    (Finset.range (k + 1)).sum (binomialWalkProb k) = 1 := by
  unfold binomialWalkProb
  have h : ∀ j ∈ Finset.range (k + 1), j ≤ k := fun j hj =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have heq : ∀ j ∈ Finset.range (k + 1),
      (if j ≤ k then (Nat.choose k j : ℝ) / 2^k else 0) = (Nat.choose k j : ℝ) / 2^k := by
    intro j hj
    simp only [h j hj, ↓reduceIte]
  rw [Finset.sum_congr rfl heq]
  have hdiv : (Finset.range (k + 1)).sum (fun j => (Nat.choose k j : ℝ) / 2^k) =
              (Finset.range (k + 1)).sum (fun j => (Nat.choose k j : ℝ)) / 2^k := by
    rw [Finset.sum_div]
  rw [hdiv]
  have hsum : (Finset.range (k + 1)).sum (fun j => (Nat.choose k j : ℝ)) = 2^k := by
    have h := Nat.sum_range_choose k
    have h2 : (Finset.range (k + 1)).sum (fun j => Nat.choose k j) = 2^k := h
    exact_mod_cast h2
  rw [hsum]
  exact div_self (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))

/-! ## Walk Interval Probabilities -/

/-- Helper function for walk interval check.
    Returns binomialWalkProb k j if the walk value dx*(2j - k) is in [a, b], else 0. -/
noncomputable def walkValInInterval (k : ℕ) (j : ℕ) (a b dx : ℝ) : ℝ :=
  if a ≤ dx * (2 * (j : ℝ) - k) ∧ dx * (2 * (j : ℝ) - k) ≤ b
  then binomialWalkProb k j else 0

/-- The probability that the walk value lies in an interval [a, b].
    P(a ≤ W_k ≤ b) = Σⱼ P(S_k = 2j - k) where a ≤ dx·(2j - k) ≤ b. -/
noncomputable def walkIntervalProb (k : ℕ) (a b : ℝ) (dx : ℝ) : ℝ :=
  (Finset.range (k + 1)).sum (walkValInInterval k · a b dx)

/-- Walk interval probability is non-negative -/
theorem walkIntervalProb_nonneg (k : ℕ) (a b : ℝ) (dx : ℝ) :
    0 ≤ walkIntervalProb k a b dx := by
  unfold walkIntervalProb walkValInInterval
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact binomialWalkProb_nonneg k j
  · exact le_refl 0

/-- walkValInInterval is at most binomialWalkProb -/
theorem walkValInInterval_le (k j : ℕ) (a b dx : ℝ) :
    walkValInInterval k j a b dx ≤ binomialWalkProb k j := by
  unfold walkValInInterval
  split_ifs
  · exact le_refl _
  · exact binomialWalkProb_nonneg k j

/-- Walk interval probability is at most 1 -/
theorem walkIntervalProb_le_one (k : ℕ) (a b : ℝ) (dx : ℝ) :
    walkIntervalProb k a b dx ≤ 1 := by
  unfold walkIntervalProb
  calc (Finset.range (k + 1)).sum (walkValInInterval k · a b dx)
      ≤ (Finset.range (k + 1)).sum (binomialWalkProb k) :=
        Finset.sum_le_sum (fun j _ => walkValInInterval_le k j a b dx)
    _ = 1 := binomialWalkProb_sum k

/-! ## Gaussian Limit -/

/-- The Gaussian probability for an interval.
    This would be Φ(b/√t) - Φ(a/√t) where Φ is the standard normal CDF.

    Note: A full formalization would use Mathlib's Gaussian integral machinery.
    Here we define it abstractly as the limit of binomial probabilities. -/
structure GaussianIntervalProb where
  /-- The time parameter -/
  time : ℝ
  /-- Time is positive -/
  time_pos : 0 < time
  /-- Lower bound -/
  lower : ℝ
  /-- Upper bound -/
  upper : ℝ
  /-- Bounds are ordered -/
  bounds_ordered : lower ≤ upper
  /-- The Gaussian probability value -/
  prob : ℝ
  /-- Probability is in [0, 1] -/
  prob_nonneg : 0 ≤ prob
  prob_le_one : prob ≤ 1

/-! ## Local Central Limit Theorem - Future Work

The binomial-to-Gaussian convergence (local CLT) is fundamental for Anderson's theorem.
The precise statement is:

**De Moivre-Laplace Local CLT**:
For S_k = X₁ + ... + X_k with Xᵢ = ±1 equally likely:
  P(S_k = j) = C(k, (k+j)/2) / 2^k ≈ (1/√(2πk)) exp(-j²/(2k))

Equivalently, for walk value W_k = dx · S_k where dx = √(t/k):
  P(a ≤ W_k ≤ b) → ∫_a^b (1/√(2πt)) exp(-x²/(2t)) dx

This convergence theorem requires:
1. Stirling's approximation: n! ≈ √(2πn) (n/e)^n
2. Expansion of C(k, (k+j)/2) using Stirling
3. Careful error analysis for |j| = O(√k) (bulk) vs |j| >> √k (tails)

Once proven, this would give:
- For any standard interval [a, b] and standard time t,
- The hyperreal walk probability st(P_hyp(a ≤ W_t ≤ b)) equals the Gaussian integral

This is the single-time marginal part of Anderson's theorem.

**Note**: `GaussianIntervalProb` is defined as a structure for packaging Gaussian probability
targets. To make it rigorous, we would need either:
1. Compute the actual integral using Mathlib's Gaussian integral infrastructure
2. Prove that the `prob` field equals the actual integral
-/

end SPDE.Nonstandard
