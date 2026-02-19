/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.Anderson.RandomWalkMoments

/-!
# Maximal Inequality for Random Walks

This file proves the maximal inequality for symmetric random walks, which is essential
for showing that hyperfinite random walk paths are S-continuous almost surely.

## Main Results

* `maximal_count` - #{max_{i≤k} |S_i| > M} * M² ≤ 4k * 2^n
* `maximal_prob` - P(max_{i≤k} |S_i| > M) ≤ 4k / M²

## Key Ideas

The maximal inequality bounds the probability that a random walk ever exceeds a threshold.
For symmetric random walks, we use the reflection principle:
- If the walk hits level M at time j and ends at level L ≤ M at time k,
  by reflecting the path after time j, we get a path ending at 2M - L ≥ M.
- This gives: P(max S_i ≥ M) ≤ 2 P(S_k ≥ M)

Combined with Chebyshev: P(S_k ≥ M) ≤ k/(2M²), we get
  P(max |S_i| > M) ≤ P(max S_i > M) + P(min S_i < -M)
                   ≤ 4 P(|S_k| > M) ≤ 4k/M²

## References

* Doob's maximal inequality for martingales
* Reflection principle for random walks
-/

open Finset

namespace SPDE.Nonstandard

/-! ## Running Maximum -/

/-- The running maximum |S_i| for i ≤ k -/
def runningMaxAbs (n : ℕ) (flips : Fin n → Bool) (k : ℕ) : ℤ :=
  (Finset.range (k + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
    (fun i => |partialSumFin n flips i|)

/-- Running max is at least the final value -/
theorem runningMaxAbs_ge_final (n : ℕ) (flips : Fin n → Bool) (k : ℕ) :
    |partialSumFin n flips k| ≤ runningMaxAbs n flips k := by
  unfold runningMaxAbs
  exact Finset.le_sup' (fun i => |partialSumFin n flips i|)
    (Finset.mem_range.mpr (Nat.lt_succ_self k))

/-- Running max is non-negative -/
theorem runningMaxAbs_nonneg (n : ℕ) (flips : Fin n → Bool) (k : ℕ) :
    0 ≤ runningMaxAbs n flips k := by
  unfold runningMaxAbs
  apply le_trans (abs_nonneg (partialSumFin n flips 0))
  exact Finset.le_sup' (fun i => |partialSumFin n flips i|)
    (Finset.mem_range.mpr (Nat.zero_lt_succ k))

/-! ## Maximal Inequality via Chebyshev

We prove a weaker but useful bound: P(max |S_i| > M) ≤ (k+1) * k / M²
This follows from union bound + Chebyshev at each time.

The optimal bound P(max |S_i| > M) ≤ 2 * P(|S_k| > M) requires the reflection principle,
which is more involved to formalize.
-/

/-- Union bound: #{max |S_i| > M} ≤ Σᵢ #{|S_i| > M} -/
theorem maxExceed_le_sumExceed (n : ℕ) (k : ℕ) (M : ℕ) (_hk : k ≤ n) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card ≤
    (Finset.range (k + 1)).sum (fun i =>
      ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card) := by
  -- If max |S_i| > M, then |S_j| > M for some j ≤ k
  have hinc : (Finset.univ : Finset (Fin n → Bool)).filter
                (fun flips => (M : ℤ) < runningMaxAbs n flips k) ⊆
              (Finset.range (k + 1)).biUnion (fun i =>
                (Finset.univ : Finset (Fin n → Bool)).filter
                  (fun flips => (M : ℤ) < |partialSumFin n flips i|)) := by
    intro flips hflips
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hflips
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    -- runningMaxAbs is the sup of |S_i| for i ≤ k
    unfold runningMaxAbs at hflips
    have hne : (Finset.range (k + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ k)⟩
    obtain ⟨j, hj_mem, hj_max⟩ := Finset.exists_mem_eq_sup' hne (fun i => |partialSumFin n flips i|)
    rw [hj_max] at hflips
    simp only [Finset.mem_range] at hj_mem
    exact ⟨j, hj_mem, hflips⟩
  calc ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card
      ≤ ((Finset.range (k + 1)).biUnion (fun i =>
          (Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|))).card :=
        Finset.card_le_card hinc
    _ ≤ (Finset.range (k + 1)).sum (fun i =>
          ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card) :=
        Finset.card_biUnion_le

/-- Maximal inequality count: #{max |S_i| > M} * M² ≤ k(k+1)/2 * 2^n
    This is weaker than the reflection principle bound but easier to prove. -/
theorem maximal_count_weak (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 ≤
    (k + 1) * k / 2 * 2^n + (k + 1) * 2^n := by
  have hsum := maxExceed_le_sumExceed n k M hk
  -- Each term in the sum satisfies Chebyshev
  have hterm : ∀ i ∈ Finset.range (k + 1),
      ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card * M^2 ≤ i * 2^n := by
    intro i hi
    by_cases hi_pos : i = 0
    · simp [hi_pos, partialSumFin]
    · have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi) |>.trans hk
      exact chebyshev_count n i M hi_le hM
  -- Sum Chebyshev bounds
  calc ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2
      ≤ (Finset.range (k + 1)).sum (fun i =>
          ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card) * M^2 := by
        apply Nat.mul_le_mul_right
        exact hsum
    _ = (Finset.range (k + 1)).sum (fun i =>
          ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun flips => (M : ℤ) < |partialSumFin n flips i|)).card * M^2) := by
        rw [Finset.sum_mul]
    _ ≤ (Finset.range (k + 1)).sum (fun i => i * 2^n) :=
        Finset.sum_le_sum hterm
    _ = (Finset.range (k + 1)).sum (fun i => i) * 2^n := by
        rw [← Finset.sum_mul]
    _ = ((k + 1) * k / 2) * 2^n := by
        congr 1
        rw [Finset.sum_range_id]
        simp only [Nat.add_sub_cancel]
    _ ≤ (k + 1) * k / 2 * 2^n + (k + 1) * 2^n := Nat.le_add_right _ _

/-- Simplified maximal inequality: #{max |S_i| > M} * M² ≤ (k+1)² * 2^n -/
theorem maximal_count (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 ≤
    (k + 1)^2 * 2^n := by
  have h := maximal_count_weak n k M hk hM
  calc ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2
      ≤ (k + 1) * k / 2 * 2^n + (k + 1) * 2^n := h
    _ ≤ (k + 1) * (k + 1) * 2^n := by
        have h1 : (k + 1) * k / 2 ≤ (k + 1) * k := Nat.div_le_self _ _
        have h2 : (k + 1) * k + (k + 1) ≤ (k + 1) * (k + 1) + (k + 1) := Nat.add_le_add_right
          (Nat.mul_le_mul_left _ (Nat.le_succ k)) _
        have h3 : (k + 1) * k / 2 + (k + 1) ≤ (k + 1) * k + (k + 1) :=
          Nat.add_le_add_right h1 _
        have h4 : (k + 1) * k + (k + 1) = (k + 1) * (k + 1) := by ring
        calc (k + 1) * k / 2 * 2^n + (k + 1) * 2^n
            = ((k + 1) * k / 2 + (k + 1)) * 2^n := by ring
          _ ≤ ((k + 1) * k + (k + 1)) * 2^n := Nat.mul_le_mul_right _ h3
          _ = (k + 1) * (k + 1) * 2^n := by rw [h4]
    _ = (k + 1)^2 * 2^n := by ring

/-- Maximal inequality as probability bound:
    P(max_{i≤k} |S_i| > M) ≤ (k+1)² / M² -/
theorem maximal_prob (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) (_hn : 0 < n) :
    (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card : ℚ) / 2^n ≤
    ((k + 1)^2 : ℚ) / M^2 := by
  have hcount := maximal_count n k M hk hM
  have h2n_pos : (0 : ℚ) < 2^n := by positivity
  have hM2_pos : (0 : ℚ) < (M : ℚ)^2 := by positivity
  have hcount_rat : (((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 : ℚ) ≤
        ((k + 1)^2 : ℚ) * 2^n := by
    have : (((k + 1)^2 * 2^n : ℕ) : ℚ) = ((k + 1)^2 : ℚ) * 2^n := by
      simp [Nat.cast_mul, Nat.cast_pow]
    rw [← this]
    exact_mod_cast hcount
  calc (((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card : ℚ) / 2^n
      = (((Finset.univ : Finset (Fin n → Bool)).filter
          (fun flips => (M : ℤ) < runningMaxAbs n flips k)).card * M^2 : ℚ) / (2^n * M^2) := by
        field_simp
    _ ≤ (((k + 1)^2 : ℚ) * 2^n) / (2^n * M^2) := by
        apply div_le_div_of_nonneg_right hcount_rat
        positivity
    _ = ((k + 1)^2 : ℚ) / M^2 := by field_simp

/-! ## Reflection Principle for ±1 Random Walks

The reflection principle gives a sharp maximal inequality:
  #{max_{k≤n} S_k ≥ M} ≤ 2 · #{S_n ≥ M}
This is much sharper than the union bound when M grows with n.

### Proof idea
For any path where max S_k ≥ M but S_n < M, reflect all steps after the first
hitting time of M. The reflected path has S_n ≥ M. This defines an injection
from {max ≥ M, S_n < M} into {S_n ≥ M}, giving the bound.
-/

/-- Reflect all coin flips at positions ≥ j (negate them) -/
def reflectAfter (n : ℕ) (flips : Fin n → Bool) (j : ℕ) : Fin n → Bool :=
  fun i => if j ≤ i.val then !flips i else flips i

/-- Reflecting twice is the identity -/
theorem reflectAfter_involutive (n : ℕ) (j : ℕ) :
    Function.Involutive (fun flips => reflectAfter n flips j) := by
  intro flips
  ext i
  simp only [reflectAfter]
  split_ifs with h
  · simp
  · rfl

/-- Reflecting is injective (follows from involutive) -/
theorem reflectAfter_injective (n : ℕ) (j : ℕ) :
    Function.Injective (fun flips => reflectAfter n flips j) :=
  (reflectAfter_involutive n j).injective

/-- For positions before the reflection point, the partial sum is unchanged -/
theorem partialSumFin_reflectAfter_prefix (n : ℕ) (flips : Fin n → Bool) (j k : ℕ) (hk : k ≤ j) :
    partialSumFin n (reflectAfter n flips j) k = partialSumFin n flips k := by
  simp only [partialSumFin]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [reflectAfter, if_neg (by omega : ¬(j ≤ i.val))]

/-- The partial sum splitting identity: S_n = S_j + (S_n - S_j) where each piece
    only depends on the flips in the corresponding range -/
theorem partialSumFin_split (n : ℕ) (flips : Fin n → Bool) (j : ℕ) (hj : j ≤ n) :
    partialSumFin n flips n = partialSumFin n flips j +
      (Finset.univ.filter (fun i : Fin n => j ≤ i.val)).sum (fun i => boolToInt (flips i)) := by
  simp only [partialSumFin]
  -- The filter {i.val < n} is just Finset.univ for Fin n
  have h_all : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i; simp [i.isLt]
  rw [h_all]
  -- Split Finset.univ into {i < j} ∪ {j ≤ i}
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n)) (fun i : Fin n => i.val < j) (fun i => boolToInt (flips i))
  rw [← hsplit]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

/-- After reflection at j, the suffix sum is negated -/
theorem reflectAfter_suffix_sum (n : ℕ) (flips : Fin n → Bool) (j : ℕ) :
    (Finset.univ.filter (fun i : Fin n => j ≤ i.val)).sum
      (fun i => boolToInt (reflectAfter n flips j i)) =
    -(Finset.univ.filter (fun i : Fin n => j ≤ i.val)).sum
      (fun i => boolToInt (flips i)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [reflectAfter, if_pos hi, boolToInt_not]

/-- The key identity: S_n(reflected at j) = 2·S_j - S_n -/
theorem partialSumFin_reflectAfter (n : ℕ) (flips : Fin n → Bool) (j : ℕ) (hj : j ≤ n) :
    partialSumFin n (reflectAfter n flips j) n =
    2 * partialSumFin n flips j - partialSumFin n flips n := by
  rw [partialSumFin_split n (reflectAfter n flips j) j hj]
  rw [partialSumFin_reflectAfter_prefix n flips j j le_rfl]
  rw [reflectAfter_suffix_sum]
  rw [partialSumFin_split n flips j hj]
  ring

/-- First hitting time for S_k ≥ M (returns n+1 if never hit) -/
noncomputable def firstHitTime (n : ℕ) (flips : Fin n → Bool) (M : ℤ) : ℕ :=
  if h : ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k
  then Nat.find h
  else n + 1

theorem firstHitTime_le (n : ℕ) (flips : Fin n → Bool) (M : ℤ)
    (h : ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k) :
    firstHitTime n flips M ≤ n := by
  unfold firstHitTime
  rw [dif_pos h]
  exact (Nat.find_spec h).1

theorem firstHitTime_spec (n : ℕ) (flips : Fin n → Bool) (M : ℤ)
    (h : ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k) :
    M ≤ partialSumFin n flips (firstHitTime n flips M) := by
  unfold firstHitTime
  rw [dif_pos h]
  exact (Nat.find_spec h).2

theorem firstHitTime_min (n : ℕ) (flips : Fin n → Bool) (M : ℤ)
    (h : ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k) (k : ℕ)
    (hk : k < firstHitTime n flips M) :
    partialSumFin n flips k < M := by
  unfold firstHitTime at hk
  rw [dif_pos h] at hk
  by_contra hge
  push_neg at hge
  have hkn : k ≤ n := by
    have := (Nat.find_spec h).1
    omega
  exact absurd ⟨hkn, hge⟩ (Nat.find_min h hk)

/-- Reflection at the first hitting time preserves the prefix -/
theorem reflectAfter_firstHit_prefix (n : ℕ) (flips : Fin n → Bool) (M : ℤ) (k : ℕ)
    (h : ∃ j, j ≤ n ∧ M ≤ partialSumFin n flips j)
    (hk : k ≤ firstHitTime n flips M) :
    partialSumFin n (reflectAfter n flips (firstHitTime n flips M)) k =
    partialSumFin n flips k :=
  partialSumFin_reflectAfter_prefix n flips (firstHitTime n flips M) k hk

/-- Reflecting at the first hitting time preserves the first hitting time.
    Key ingredient for the injectivity in the reflection principle proof. -/
theorem firstHitTime_reflectAfter (n : ℕ) (flips : Fin n → Bool) (M : ℤ)
    (h : ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k) :
    firstHitTime n (reflectAfter n flips (firstHitTime n flips M)) M =
    firstHitTime n flips M := by
  set τ := firstHitTime n flips M with hτ_def
  set flips' := reflectAfter n flips τ with hflips'_def
  have hτ_le : τ ≤ n := firstHitTime_le n flips M h
  -- The reflected path satisfies the predicate at τ (prefix unchanged)
  have hSτ' : M ≤ partialSumFin n flips' τ := by
    rw [partialSumFin_reflectAfter_prefix n flips τ τ le_rfl]
    exact firstHitTime_spec n flips M h
  have h' : ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips' k := ⟨τ, hτ_le, hSτ'⟩
  apply le_antisymm
  · -- ≤: τ witnesses the predicate for flips'
    unfold firstHitTime; rw [dif_pos h']
    exact Nat.find_le ⟨hτ_le, hSτ'⟩
  · -- ≥: for k < τ, S_k(flips') = S_k(flips) < M, so can't be the first hit
    unfold firstHitTime; rw [dif_pos h']
    by_contra hlt; push_neg at hlt
    set τ' := Nat.find h' with hτ'_def
    have hτ'_spec := Nat.find_spec h'
    -- S_{τ'}(flips') = S_{τ'}(flips) since τ' < τ, so prefix unchanged
    have hprefix : partialSumFin n flips' τ' = partialSumFin n flips τ' :=
      partialSumFin_reflectAfter_prefix n flips τ τ' (le_of_lt hlt)
    -- S_{τ'}(flips) < M by minimality of τ for flips
    have hlt_M := firstHitTime_min n flips M h τ' hlt
    -- Contradiction: M ≤ S_{τ'}(flips') = S_{τ'}(flips) < M
    linarith [hτ'_spec.2]

/-- The reflection principle (one-sided, counting form):
    #{max_{k≤n} S_k ≥ M} ≤ 2 · #{S_n ≥ M}

    Proof: Split {max S_k ≥ M} = A₁ ∪ A₂ where A₁ = {S_n ≥ M} and A₂ = {max ≥ M, S_n < M}.
    Reflection at first hitting time gives injection A₂ → {S_n ≥ M}.
    So |A₁ ∪ A₂| = |A₁| + |A₂| ≤ |A₁| + |{S_n ≥ M}| = 2·|{S_n ≥ M}|. -/
theorem reflection_principle_one_sided (n : ℕ) (M : ℤ) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun flips => ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k)).card ≤
    2 * ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun flips => M ≤ partialSumFin n flips n)).card := by
  set maxSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k) with hmaxSet_def
  set endSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => M ≤ partialSumFin n flips n) with hendSet_def
  -- Split maxSet = (maxSet \ endSet) ∪ (maxSet ∩ endSet)
  have hsplit : maxSet = maxSet \ endSet ∪ maxSet ∩ endSet :=
    (sdiff_union_inter maxSet endSet).symm
  rw [hsplit, Finset.card_union_of_disjoint (disjoint_sdiff_inter maxSet endSet)]
  -- |maxSet ∩ endSet| ≤ |endSet|
  have h1 : (maxSet ∩ endSet).card ≤ endSet.card := Finset.card_le_card Finset.inter_subset_right
  -- |maxSet \ endSet| ≤ |endSet| via reflection injection
  suffices h2 : (maxSet \ endSet).card ≤ endSet.card by omega
  apply Finset.card_le_card_of_injOn
    (fun flips => reflectAfter n flips (firstHitTime n flips M))
  · -- Image is contained in endSet
    intro flips hflips
    have ⟨h_in_max, h_not_in_end⟩ := Finset.mem_sdiff.mp hflips
    have hexists := (Finset.mem_filter.mp h_in_max).2
    have hnotend : ¬(M ≤ partialSumFin n flips n) :=
      fun h => h_not_in_end (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    push_neg at hnotend
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hτ_le := firstHitTime_le n flips M hexists
    rw [partialSumFin_reflectAfter n flips (firstHitTime n flips M) hτ_le]
    have hSτ := firstHitTime_spec n flips M hexists
    omega
  · -- The map is injective on maxSet \ endSet
    intro flips₁ h₁ flips₂ h₂ heq
    have hex1 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h₁).1).2
    have hex2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h₂).1).2
    -- Beta-reduce heq (lambda application → direct form)
    have heq' : reflectAfter n flips₁ (firstHitTime n flips₁ M) =
                reflectAfter n flips₂ (firstHitTime n flips₂ M) := heq
    -- τ₁ = τ₂ via firstHitTime_reflectAfter
    have hτ_eq : firstHitTime n flips₁ M = firstHitTime n flips₂ M := by
      have h1 := firstHitTime_reflectAfter n flips₁ M hex1
      have h2 := firstHitTime_reflectAfter n flips₂ M hex2
      rw [heq'] at h1; linarith
    -- Now both reflections use the same τ, so reflectAfter_injective applies
    rw [hτ_eq] at heq'
    exact reflectAfter_injective n (firstHitTime n flips₂ M) heq'

/-- Negation symmetry: #{∃k≤n, S_k ≤ -M} = #{∃k≤n, S_k ≥ M} via negateFlipsFin -/
theorem negation_max_symmetry (n : ℕ) (M : ℤ) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun flips => ∃ k, k ≤ n ∧ partialSumFin n flips k ≤ -M)).card =
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun flips => ∃ k, k ≤ n ∧ M ≤ partialSumFin n flips k)).card := by
  apply Finset.card_bijective (negateFlipsFin n) (negateFlipsFin_bijective n)
  intro flips
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, hle⟩
    exact ⟨k, hk, by rw [partialSumFin_negate]; omega⟩
  · rintro ⟨k, hk, hge⟩
    exact ⟨k, hk, by rw [partialSumFin_negate] at hge; omega⟩

/-- Sharp maximal inequality (counting form):
    #{ω : max_{k≤n} |S_k(ω)| > M} · M² ≤ 4n · 2^n

    Proof: Union bound + negation symmetry + one-sided reflection + Chebyshev.
    #{max |S_k| > M} ≤ #{max S_k ≥ M+1} + #{min S_k ≤ -(M+1)}
                      = 2 · #{max S_k ≥ M+1}    (negation symmetry)
                      ≤ 4 · #{S_n ≥ M+1}        (reflection principle)
                      ≤ 4 · #{|S_n| > M}         (S_n ≥ M+1 → |S_n| > M)
    #{|S_n| > M} · M² ≤ n · 2^n                  (Chebyshev) -/
theorem maximal_count_sharp (n : ℕ) (M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun flips => ∃ k, k ≤ n ∧ (M : ℤ) < |partialSumFin n flips k|)).card * M^2 ≤
    4 * n * 2^n := by
  -- Define the sets
  let badSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ∃ k, k ≤ n ∧ (M : ℤ) < |partialSumFin n flips k|)
  let posMaxSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ∃ k, k ≤ n ∧ ((M : ℤ) + 1) ≤ partialSumFin n flips k)
  let negMaxSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ∃ k, k ≤ n ∧ partialSumFin n flips k ≤ -((M : ℤ) + 1))
  let posEndSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ((M : ℤ) + 1) ≤ partialSumFin n flips n)
  let chebSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => (M : ℤ) < |partialSumFin n flips n|)
  -- Step 1: Union bound. |S_k| > M iff S_k ≥ M+1 or S_k ≤ -(M+1)
  have h_union : badSet ⊆ posMaxSet ∪ negMaxSet := by
    intro flips hflips
    obtain ⟨k, hk, habs⟩ := (Finset.mem_filter.mp hflips).2
    apply Finset.mem_union.mpr
    -- |S_k| > M means S_k ≥ M+1 or S_k ≤ -(M+1) (integers)
    by_cases hge : ((M : ℤ) + 1) ≤ partialSumFin n flips k
    · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, hge⟩
    · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, by
        rcases abs_cases (partialSumFin n flips k) with ⟨h_eq, _⟩ | ⟨h_eq, _⟩ <;>
          (rw [h_eq] at habs; omega)⟩
  have h_card_union : badSet.card ≤ posMaxSet.card + negMaxSet.card :=
    (Finset.card_le_card h_union).trans (Finset.card_union_le _ _)
  -- Step 2: Negation symmetry: negMaxSet.card = posMaxSet.card
  have h_neg_eq_pos : negMaxSet.card = posMaxSet.card :=
    negation_max_symmetry n ((M : ℤ) + 1)
  -- Step 3: Reflection principle: posMaxSet.card ≤ 2 * posEndSet.card
  have h_reflect : posMaxSet.card ≤ 2 * posEndSet.card :=
    reflection_principle_one_sided n ((M : ℤ) + 1) (by omega)
  -- Step 4: posEndSet ⊆ chebSet (S_n ≥ M+1 implies |S_n| > M)
  have h_end_cheb : posEndSet.card ≤ chebSet.card := by
    apply Finset.card_le_card
    intro flips hflips
    have hpred := (Finset.mem_filter.mp hflips).2
    -- S_n ≥ M+1 implies |S_n| > M (since S_n ≥ M+1 ≥ 1 > 0, so |S_n| = S_n)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ _)]; omega⟩
  -- Step 5: Chebyshev: chebSet.card * M² ≤ n * 2^n
  have h_cheb : chebSet.card * M ^ 2 ≤ n * 2 ^ n :=
    chebyshev_count n n M le_rfl hM
  -- Combine: badSet.card ≤ 4 * chebSet.card
  have h_bad_le : badSet.card ≤ 4 * chebSet.card := by
    calc badSet.card ≤ posMaxSet.card + negMaxSet.card := h_card_union
      _ = 2 * posMaxSet.card := by omega
      _ ≤ 2 * (2 * posEndSet.card) := Nat.mul_le_mul_left _ h_reflect
      _ = 4 * posEndSet.card := by ring
      _ ≤ 4 * chebSet.card := Nat.mul_le_mul_left _ h_end_cheb
  calc badSet.card * M ^ 2 ≤ 4 * chebSet.card * M ^ 2 :=
        Nat.mul_le_mul_right _ h_bad_le
    _ = 4 * (chebSet.card * M ^ 2) := by ring
    _ ≤ 4 * (n * 2 ^ n) := Nat.mul_le_mul_left _ h_cheb
    _ = 4 * n * 2 ^ n := by ring

/-- Nonstrict Chebyshev: #{|S_k| ≥ M} * M² ≤ k * 2^n.
    Same proof as chebyshev_count but with ≤ instead of <. -/
theorem chebyshev_count_ge (n : ℕ) (k : ℕ) (M : ℕ) (hk : k ≤ n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun flips => (M : ℤ) ≤ |partialSumFin n flips k|)).card * M^2 ≤ k * 2^n := by
  have hsum := sum_partialSumFin_sq n k hk
  let exceed := (Finset.univ : Finset (Fin n → Bool)).filter
                  (fun flips => (M : ℤ) ≤ |partialSumFin n flips k|)
  have h1 : (exceed.card : ℤ) * (M : ℤ)^2 ≤ exceed.sum (fun flips => (partialSumFin n flips k)^2) := by
    have hle : ∀ flips ∈ exceed, (M : ℤ)^2 ≤ (partialSumFin n flips k)^2 := by
      intro flips hflips
      have habs : (M : ℤ) ≤ |partialSumFin n flips k| := (Finset.mem_filter.mp hflips).2
      calc (M : ℤ)^2 ≤ |partialSumFin n flips k|^2 := sq_le_sq' (by linarith) habs
        _ = (partialSumFin n flips k)^2 := sq_abs _
    calc (exceed.card : ℤ) * (M : ℤ)^2
        = exceed.sum (fun _ => (M : ℤ)^2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ exceed.sum (fun flips => (partialSumFin n flips k)^2) := Finset.sum_le_sum hle
  have h2 : exceed.sum (fun flips => (partialSumFin n flips k)^2) ≤
             (Finset.univ : Finset (Fin n → Bool)).sum
               (fun flips => (partialSumFin n flips k)^2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun x _ _ => sq_nonneg _)
  have hfinal : ((exceed.card : ℕ) * M^2 : ℤ) ≤ ((k * 2^n : ℕ) : ℤ) := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  exact Nat.cast_le.mp hfinal

/-- Nonstrict maximal inequality:
    #{∃k≤n, |S_k| ≥ M} * M² ≤ 4n * 2^n -/
theorem maximal_count_ge (n : ℕ) (M : ℕ) (hn : 0 < n) (hM : 0 < M) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun flips => ∃ k, k ≤ n ∧ (M : ℤ) ≤ |partialSumFin n flips k|)).card * M^2 ≤
    4 * n * 2^n := by
  -- Same proof structure as maximal_count_sharp but with ≥ instead of >
  let badSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ∃ k, k ≤ n ∧ (M : ℤ) ≤ |partialSumFin n flips k|)
  let posMaxSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ∃ k, k ≤ n ∧ (M : ℤ) ≤ partialSumFin n flips k)
  let negMaxSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => ∃ k, k ≤ n ∧ partialSumFin n flips k ≤ -(M : ℤ))
  let posEndSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => (M : ℤ) ≤ partialSumFin n flips n)
  let chebSet := (Finset.univ : Finset (Fin n → Bool)).filter
    (fun flips => (M : ℤ) ≤ |partialSumFin n flips n|)
  -- Step 1: Union bound. |S_k| ≥ M iff S_k ≥ M or S_k ≤ -M
  have h_union : badSet ⊆ posMaxSet ∪ negMaxSet := by
    intro flips hflips
    obtain ⟨k, hk, habs⟩ := (Finset.mem_filter.mp hflips).2
    apply Finset.mem_union.mpr
    by_cases hge : (M : ℤ) ≤ partialSumFin n flips k
    · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, hge⟩
    · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hk, by
        rcases abs_cases (partialSumFin n flips k) with ⟨h_eq, _⟩ | ⟨h_eq, _⟩ <;>
          (rw [h_eq] at habs; omega)⟩
  have h_card_union : badSet.card ≤ posMaxSet.card + negMaxSet.card :=
    (Finset.card_le_card h_union).trans (Finset.card_union_le _ _)
  have h_neg_eq_pos : negMaxSet.card = posMaxSet.card :=
    negation_max_symmetry n (M : ℤ)
  have h_reflect : posMaxSet.card ≤ 2 * posEndSet.card :=
    reflection_principle_one_sided n (M : ℤ) (by omega)
  have h_end_cheb : posEndSet.card ≤ chebSet.card := by
    apply Finset.card_le_card
    intro flips hflips
    have hpred := (Finset.mem_filter.mp hflips).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ _)]; exact hpred⟩
  have h_cheb : chebSet.card * M ^ 2 ≤ n * 2 ^ n :=
    chebyshev_count_ge n n M le_rfl hM
  have h_bad_le : badSet.card ≤ 4 * chebSet.card := by
    calc badSet.card ≤ posMaxSet.card + negMaxSet.card := h_card_union
      _ = 2 * posMaxSet.card := by omega
      _ ≤ 2 * (2 * posEndSet.card) := Nat.mul_le_mul_left _ h_reflect
      _ = 4 * posEndSet.card := by ring
      _ ≤ 4 * chebSet.card := Nat.mul_le_mul_left _ h_end_cheb
  calc badSet.card * M ^ 2 ≤ 4 * chebSet.card * M ^ 2 :=
        Nat.mul_le_mul_right _ h_bad_le
    _ = 4 * (chebSet.card * M ^ 2) := by ring
    _ ≤ 4 * (n * 2 ^ n) := Nat.mul_le_mul_left _ h_cheb
    _ = 4 * n * 2 ^ n := by ring

end SPDE.Nonstandard
