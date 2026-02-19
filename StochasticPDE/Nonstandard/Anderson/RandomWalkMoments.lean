/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.CoinFlipSpace
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Random Walk Moments and Chebyshev Bounds

This file develops the fundamental moment computations for symmetric random walks,
which are essential for Anderson's theorem.

## Main Results

* `sum_partialSum_sq` - Σ_flips S_k² = k * 2^n (E[S_k²] = k)
* `internalExpectation_partialSum_eq_zero` - Σ_flips S_k = 0 (E[S_k] = 0)
* `chebyshev_count` - #{|S_k| > M} * M² ≤ k * 2^n

## Key Ideas

For a symmetric random walk S_k = X₁ + X₂ + ... + X_k where each Xᵢ = ±1:

1. **First moment**: E[S_k] = 0 by symmetry
2. **Second moment**: E[S_k²] = k (since Xᵢ² = 1 and cross terms vanish)
3. **Chebyshev**: P(|S_k| > M) ≤ E[S_k²]/M² = k/M²
-/

open Finset

namespace SPDE.Nonstandard

/-! ## Coin Flip Sequences -/

/-- Convert a boolean to ±1 -/
def boolToInt (b : Bool) : ℤ := if b then 1 else -1

theorem boolToInt_sq (b : Bool) : (boolToInt b)^2 = 1 := by
  cases b <;> simp [boolToInt]

theorem boolToInt_true : boolToInt true = 1 := rfl
theorem boolToInt_false : boolToInt false = -1 := rfl

/-- The partial sum S_k = Σᵢ<k Xᵢ for a coin flip sequence.
    flips : Fin n → Bool represents n coin flips. -/
def partialSumFin (n : ℕ) (flips : Fin n → Bool) (k : ℕ) : ℤ :=
  (Finset.univ.filter (fun i : Fin n => i.val < k)).sum (fun i => boolToInt (flips i))

/-- For k ≥ n, the partial sum is the full sum -/
theorem partialSumFin_ge (n : ℕ) (flips : Fin n → Bool) (k : ℕ) (hk : n ≤ k) :
    partialSumFin n flips k = Finset.univ.sum (fun i : Fin n => boolToInt (flips i)) := by
  simp only [partialSumFin]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, iff_true]
  exact Nat.lt_of_lt_of_le i.isLt hk

/-! ## First Moment: E[S_k] = 0 -/

/-- Negate all coins -/
def negateFlipsFin (n : ℕ) (flips : Fin n → Bool) : Fin n → Bool :=
  fun i => !flips i

theorem negateFlipsFin_involutive (n : ℕ) : Function.Involutive (negateFlipsFin n) := by
  intro flips
  ext i
  simp [negateFlipsFin, Bool.not_not]

theorem negateFlipsFin_bijective (n : ℕ) : Function.Bijective (negateFlipsFin n) :=
  (negateFlipsFin_involutive n).bijective

/-- Negating flips negates boolToInt -/
theorem boolToInt_not (b : Bool) : boolToInt (!b) = -boolToInt b := by
  cases b <;> simp [boolToInt]

/-- Negating all flips negates the partial sum -/
theorem partialSumFin_negate (n : ℕ) (flips : Fin n → Bool) (k : ℕ) :
    partialSumFin n (negateFlipsFin n flips) k = -partialSumFin n flips k := by
  simp only [partialSumFin, negateFlipsFin, boolToInt_not, Finset.sum_neg_distrib]

/-- The sum of partial sums over all flip sequences is 0 -/
theorem sum_partialSumFin_eq_zero (n : ℕ) (k : ℕ) :
    (Finset.univ : Finset (Fin n → Bool)).sum (fun flips => partialSumFin n flips k) = 0 := by
  -- Pairing argument: each flips pairs with negateFlipsFin flips, contributing S + (-S) = 0
  have hbij := negateFlipsFin_bijective n
  -- Sum f(x) = Sum f(negate x) by bijection
  have hsym : (Finset.univ : Finset (Fin n → Bool)).sum
                (fun flips => partialSumFin n (negateFlipsFin n flips) k) =
              (Finset.univ : Finset (Fin n → Bool)).sum (fun flips => partialSumFin n flips k) :=
    Finset.sum_bijective _ hbij (fun _ => Iff.intro (fun _ => mem_univ _) (fun _ => mem_univ _))
      (fun _ _ => rfl)
  -- Rewrite using the negation property
  simp only [partialSumFin_negate, Finset.sum_neg_distrib] at hsym
  -- Now: -sum = sum, so 2*sum = 0, so sum = 0
  linarith

/-! ## Second Moment: E[S_k²] = k -/

/-- Sum of Xᵢ² over all sequences: since Xᵢ² = 1 always, this equals 2^n -/
theorem sum_boolToInt_sq (n : ℕ) (i : Fin n) :
    (Finset.univ : Finset (Fin n → Bool)).sum (fun flips => (boolToInt (flips i))^2) =
    (2^n : ℕ) := by
  simp only [boolToInt_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
             Fintype.card_fin, Fintype.card_bool]
  rw [nsmul_eq_mul, mul_one]

/-- For i ≠ j, sum of XᵢXⱼ over all sequences is 0 (independence) -/
theorem sum_boolToInt_cross (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ : Finset (Fin n → Bool)).sum
      (fun flips => boolToInt (flips i) * boolToInt (flips j)) = 0 := by
  -- Swap the i-th flip; this negates Xᵢ but preserves Xⱼ
  let swapI : (Fin n → Bool) → (Fin n → Bool) := fun flips m =>
    if m = i then !flips m else flips m
  have hswap_invol : Function.Involutive swapI := by
    intro flips; ext m
    simp only [swapI]
    split_ifs with h <;> simp [Bool.not_not]
  have hswap_bij : Function.Bijective swapI := hswap_invol.bijective
  have hswap_i : ∀ flips, boolToInt ((swapI flips) i) = -boolToInt (flips i) := by
    intro flips
    simp only [swapI, if_pos rfl, boolToInt_not]
  have hswap_j : ∀ flips, (swapI flips) j = flips j := by
    intro flips
    simp only [swapI]
    split_ifs with h
    · exact absurd h.symm hij
    · rfl
  -- Pairing: f(x) + f(swap x) = XᵢXⱼ + (-Xᵢ)Xⱼ = 0
  have hsym : (Finset.univ : Finset (Fin n → Bool)).sum
                (fun flips => boolToInt ((swapI flips) i) * boolToInt ((swapI flips) j)) =
              (Finset.univ : Finset (Fin n → Bool)).sum
                (fun flips => boolToInt (flips i) * boolToInt (flips j)) :=
    Finset.sum_bijective _ hswap_bij (fun _ => Iff.intro (fun _ => mem_univ _) (fun _ => mem_univ _))
      (fun _ _ => rfl)
  simp only [hswap_i, hswap_j, neg_mul, Finset.sum_neg_distrib] at hsym
  -- Now hsym : -sum = sum, so sum = 0
  omega

/-- The set of indices less than k, as a Finset of Fin n -/
def indicesLtK (n k : ℕ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)

/-- Cardinality of indicesLtK when k ≤ n -/
theorem card_indicesLtK (n k : ℕ) (hk : k ≤ n) : (indicesLtK n k).card = k := by
  unfold indicesLtK
  -- Bijection with Fin k
  let f : Fin k → Fin n := fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩
  have hf_inj : Function.Injective f := fun a b h => Fin.ext (Fin.mk.injEq _ _ _ _ ▸ h)
  have heq : Finset.filter (fun i => i.val < k) Finset.univ =
             Finset.univ.map ⟨f, hf_inj⟩ := by
    ext ⟨x, hx⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
               Function.Embedding.coeFn_mk, f, Fin.mk.injEq]
    constructor
    · intro hxk
      use ⟨x, hxk⟩
    · rintro ⟨y, _, rfl⟩
      -- y : Fin k
      exact y.isLt
  rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The sum of S_k² over all sequences equals k * 2^n.
    This is the key computation: E[S_k²] = k. -/
theorem sum_partialSumFin_sq (n : ℕ) (k : ℕ) (hk : k ≤ n) :
    (Finset.univ : Finset (Fin n → Bool)).sum
      (fun flips => (partialSumFin n flips k)^2) = (k : ℤ) * 2^n := by
  -- The set of indices i < k
  let S := indicesLtK n k
  have hcardS : S.card = k := card_indicesLtK n k hk
  -- S_k = Σᵢ∈S Xᵢ
  have hpartial : ∀ flips : Fin n → Bool, partialSumFin n flips k = S.sum (fun i => boolToInt (flips i)) := by
    intro flips
    rfl
  -- Diagonal: Σᵢ∈S (Σ_flips Xᵢ²) = |S| * 2^n = k * 2^n
  have hdiag : S.sum (fun i => (Finset.univ : Finset (Fin n → Bool)).sum
                 (fun flips => (boolToInt (flips i))^2)) = (k : ℤ) * 2^n := by
    simp only [boolToInt_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
               Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, mul_one,
               hcardS, Nat.cast_pow, Nat.cast_ofNat]
  -- Cross: Σᵢ≠ⱼ∈S (Σ_flips XᵢXⱼ) = 0
  have hcross : S.sum (fun i => S.sum (fun j =>
      if i = j then 0 else (Finset.univ : Finset (Fin n → Bool)).sum
        (fun flips => boolToInt (flips i) * boolToInt (flips j)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with h
    · rfl
    · exact sum_boolToInt_cross n i j h
  -- Direct calculation: swap order of summation
  -- Σ_flips S_k² = Σ_flips (Σᵢ Xᵢ)² = Σ_flips Σᵢ Σⱼ XᵢXⱼ = Σᵢ Σⱼ Σ_flips XᵢXⱼ
  -- When i = j: Σ_flips Xᵢ² = 2^n
  -- When i ≠ j: Σ_flips XᵢXⱼ = 0
  -- So total = Σᵢ 2^n = k · 2^n
  have hexpand : ∀ flips : Fin n → Bool,
      (S.sum (fun i => boolToInt (flips i)))^2 =
      S.sum (fun i => S.sum (fun j => boolToInt (flips i) * boolToInt (flips j))) := by
    intro flips
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  -- Swap order and compute
  calc (Finset.univ : Finset (Fin n → Bool)).sum (fun flips => (partialSumFin n flips k)^2)
      = (Finset.univ : Finset (Fin n → Bool)).sum (fun flips =>
          S.sum (fun i => S.sum (fun j => boolToInt (flips i) * boolToInt (flips j)))) := by
        apply Finset.sum_congr rfl; intro flips _; rw [hpartial, hexpand]
    _ = S.sum (fun i => S.sum (fun j =>
          (Finset.univ : Finset (Fin n → Bool)).sum (fun flips => boolToInt (flips i) * boolToInt (flips j)))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = S.sum (fun i => S.sum (fun j => if i = j then (2^n : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        split_ifs with h
        · subst h
          convert sum_boolToInt_sq n i using 1
          simp only [sq]
        · exact sum_boolToInt_cross n i j h
    _ = S.sum (fun i => (2^n : ℤ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        -- Convert i = j to j = i, then use sum_ite_eq'
        have hconv : S.sum (fun j => if i = j then (2^n : ℤ) else 0) =
                     S.sum (fun j => if j = i then (2^n : ℤ) else 0) := by
          apply Finset.sum_congr rfl; intro j _; simp only [eq_comm]
        rw [hconv, Finset.sum_ite_eq' S i (fun _ => (2^n : ℤ)), if_pos hi]
    _ = S.card • (2^n : ℤ) := Finset.sum_const (2^n : ℤ)
    _ = (k : ℤ) * 2^n := by rw [hcardS, nsmul_eq_mul]

/-! ## Chebyshev Inequality -/

/-- The number of sequences where |S_k| > M times M² is at most k * 2^n.
    This is the counting form of Chebyshev's inequality. -/
theorem chebyshev_count (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < |partialSumFin n flips k|)).card * M^2 ≤ k * 2^n := by
  have hsum := sum_partialSumFin_sq n k hk
  -- On {|S| > M}, we have M² ≤ S², so card * M² ≤ Σ S² = k * 2^n
  let exceed := (Finset.univ : Finset (Fin n → Bool)).filter
                  (fun flips => (M : ℤ) < |partialSumFin n flips k|)
  -- Each element in exceed contributes at least M² to the sum of squares
  have h1 : (exceed.card : ℤ) * (M : ℤ)^2 ≤ exceed.sum (fun flips => (partialSumFin n flips k)^2) := by
    have hle : ∀ flips ∈ exceed, (M : ℤ)^2 ≤ (partialSumFin n flips k)^2 := by
      intro flips hflips
      simp only [exceed, Finset.mem_filter] at hflips
      have habs : (M : ℤ) < |partialSumFin n flips k| := hflips.2
      have hM_nonneg : (0 : ℤ) ≤ M := Nat.cast_nonneg M
      have habs_nonneg : 0 ≤ |partialSumFin n flips k| := abs_nonneg _
      have hsq_le : (M : ℤ)^2 ≤ |partialSumFin n flips k|^2 :=
        sq_le_sq' (by linarith) (le_of_lt habs)
      rw [sq_abs] at hsq_le
      exact hsq_le
    calc (exceed.card : ℤ) * (M : ℤ)^2
        = exceed.sum (fun _ => (M : ℤ)^2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ exceed.sum (fun flips => (partialSumFin n flips k)^2) := Finset.sum_le_sum hle
  -- The sum over exceed is at most the sum over all (both are nonneg sums, exceed ⊆ univ)
  have h2 : exceed.sum (fun flips => (partialSumFin n flips k)^2) ≤
             (Finset.univ : Finset (Fin n → Bool)).sum
               (fun flips => (partialSumFin n flips k)^2) := by
    have hsub : exceed ⊆ Finset.univ := Finset.filter_subset _ _
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => sq_nonneg _)
  -- Combine
  have hfinal : (exceed.card : ℤ) * (M : ℤ)^2 ≤ (k : ℤ) * 2^n := by
    calc (exceed.card : ℤ) * (M : ℤ)^2
        ≤ exceed.sum (fun flips => (partialSumFin n flips k)^2) := h1
      _ ≤ (Finset.univ : Finset (Fin n → Bool)).sum
            (fun flips => (partialSumFin n flips k)^2) := h2
      _ = (k : ℤ) * 2^n := hsum
  -- Convert to ℕ inequality
  have hfinal' : ((exceed.card : ℕ) * M^2 : ℤ) ≤ ((k * 2^n : ℕ) : ℤ) := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact hfinal
  exact Nat.cast_le.mp hfinal'

/-- Chebyshev inequality as probability bound:
    #{|S_k| > M} / 2^n ≤ k / M² -/
theorem chebyshev_prob (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) (_hn : 0 < n) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < |partialSumFin n flips k|)).card : ℚ) / 2^n ≤
    (k : ℚ) / M^2 := by
  have hcount := chebyshev_count n k M hk hM
  have h2n_pos : (0 : ℚ) < 2^n := by positivity
  have hM2_pos : (0 : ℚ) < (M : ℚ)^2 := by positivity
  have hcount_rat : (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < |partialSumFin n flips k|)).card * M^2 : ℚ) ≤
        (k : ℚ) * 2^n := by
    have : ((k * 2^n : ℕ) : ℚ) = (k : ℚ) * 2^n := by simp [Nat.cast_mul, Nat.cast_pow]
    rw [← this]
    exact_mod_cast hcount
  calc (((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < |partialSumFin n flips k|)).card : ℚ) / 2^n
      = (((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < |partialSumFin n flips k|)).card * M^2 : ℚ) / (2^n * M^2) := by
        field_simp
    _ ≤ ((k : ℚ) * 2^n) / (2^n * M^2) := by
        apply div_le_div_of_nonneg_right hcount_rat
        positivity
    _ = (k : ℚ) / M^2 := by field_simp

end SPDE.Nonstandard
