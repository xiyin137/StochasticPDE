/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.CommonRefinement

/-!
# valueAtTime linearity for the merged process

The key identity: valueAtTime of mergedProcess equals the linear
combination of the original processes' valueAtTime values.

This follows because the merged partition refines both original partitions,
so valueAtTime of each original process is constant on merged intervals.
-/

namespace SPDE
open MeasureTheory ProbabilityTheory Finset
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
namespace SimpleProcess
variable {F : Filtration Ω ℝ}

/-- No merged finset element lies strictly between consecutive merged times. -/
private theorem no_mergedFinset_in_Ioo (H₁ H₂ : SimpleProcess F) {k : ℕ}
    (hk : k + 1 < (mergedList H₁ H₂).length)
    {x : ℝ} (hx_mem : x ∈ mergedFinset H₁ H₂)
    (hx_lo : (mergedList H₁ H₂)[k] < x)
    (hx_hi : x < (mergedList H₁ H₂)[k + 1]) : False := by
  have hsorted := mergedList_sortedLT H₁ H₂
  have hx_in : x ∈ mergedList H₁ H₂ := (Finset.mem_sort _).mpr hx_mem
  obtain ⟨p, hp_lt, hp_eq⟩ := List.getElem_of_mem hx_in
  rw [← hp_eq] at hx_lo hx_hi
  have h1 : k < p := by
    by_contra h; push_neg at h
    rcases h.eq_or_lt with rfl | h
    · exact lt_irrefl _ hx_lo
    · exact absurd hx_lo (not_lt.mpr (le_of_lt
        (hsorted.strictMono_get
          (show (⟨p, hp_lt⟩ : Fin _) < ⟨k, by omega⟩ from h))))
  have h2 : p < k + 1 := by
    by_contra h; push_neg at h
    rcases h.eq_or_lt with rfl | h
    · exact lt_irrefl _ hx_hi
    · exact absurd hx_hi (not_lt.mpr (le_of_lt
        (hsorted.strictMono_get
          (show (⟨k + 1, hk⟩ : Fin _) < ⟨p, hp_lt⟩ from h))))
  omega

/-- valueAtTime of H₁ is constant on merged intervals. -/
private theorem H1_valueAtTime_const_on_merged
    (H₁ H₂ : SimpleProcess F) {k : ℕ}
    (hk : k + 1 < (mergedList H₁ H₂).length) {s : ℝ}
    (hs_lo : (mergedList H₁ H₂)[k] ≤ s)
    (hs_hi : s < (mergedList H₁ H₂)[k + 1]) :
    H₁.valueAtTime (mergedList H₁ H₂)[k] = H₁.valueAtTime s := by
  rcases eq_or_lt_of_le hs_lo with rfl | h_lt
  · rfl
  · apply valueAtTime_eq_no_partition_in_Ioc H₁ h_lt
    intro i ⟨hlo, hhi⟩
    exact no_mergedFinset_in_Ioo H₁ H₂ hk
      (times_mem_merged₁ H₁ H₂ i) hlo (lt_of_le_of_lt hhi hs_hi)

/-- valueAtTime of H₂ is constant on merged intervals. -/
private theorem H2_valueAtTime_const_on_merged
    (H₁ H₂ : SimpleProcess F) {k : ℕ}
    (hk : k + 1 < (mergedList H₁ H₂).length) {s : ℝ}
    (hs_lo : (mergedList H₁ H₂)[k] ≤ s)
    (hs_hi : s < (mergedList H₁ H₂)[k + 1]) :
    H₂.valueAtTime (mergedList H₁ H₂)[k] = H₂.valueAtTime s := by
  rcases eq_or_lt_of_le hs_lo with rfl | h_lt
  · rfl
  · apply valueAtTime_eq_no_partition_in_Ioc H₂ h_lt
    intro j ⟨hlo, hhi⟩
    exact no_mergedFinset_in_Ioo H₁ H₂ hk
      (times_mem_merged₂ H₁ H₂ j) hlo (lt_of_le_of_lt hhi hs_hi)

/-- Find a merged interval containing s between two known list positions.
    Uses ℕ indices with explicit bounds to avoid Fin proof-irrelevance issues. -/
private theorem find_merged_interval {L : List ℝ} (_hL : L.SortedLT)
    {p q : ℕ} (hp : p < L.length) (hq : q < L.length) (hpq : p < q)
    {s : ℝ} (hp_le : L[p] ≤ s) (hs_lt : s < L[q]) :
    ∃ k, ∃ hk1 : k + 1 < L.length, p ≤ k ∧
      L[k] ≤ s ∧ s < L[k + 1] := by
  obtain ⟨d, hd⟩ : ∃ d, q - p = d + 1 := ⟨q - p - 1, by omega⟩
  induction d generalizing p q with
  | zero =>
    have : q = p + 1 := by omega
    subst this
    exact ⟨p, hq, le_refl _, hp_le, hs_lt⟩
  | succ d ih =>
    have hp1_lt : p + 1 < L.length := by omega
    by_cases h : s < L[p + 1]
    · exact ⟨p, hp1_lt, le_refl _, hp_le, h⟩
    · push_neg at h
      obtain ⟨k, hk1, hkp, hk_le, hk_lt⟩ := ih hp1_lt hq (by omega) h hs_lt (by omega)
      exact ⟨k, hk1, by omega, hk_le, hk_lt⟩

/-- If s is in an original process interval, it is in a merged interval. -/
private theorem original_interval_implies_merged
    (H₁ H₂ : SimpleProcess F) (a b : ℝ) {s t_lo t_hi : ℝ}
    (h_lo_mem : t_lo ∈ mergedFinset H₁ H₂)
    (h_hi_mem : t_hi ∈ mergedFinset H₁ H₂)
    (hs_lo : t_lo ≤ s) (hs_hi : s < t_hi) :
    ∃ (k : Fin (mergedProcess H₁ H₂ a b).n)
      (_ : (k : ℕ) + 1 < (mergedProcess H₁ H₂ a b).n),
      (mergedProcess H₁ H₂ a b).times k ≤ s ∧
      s < (mergedProcess H₁ H₂ a b).times ⟨(k : ℕ) + 1, ‹_›⟩ := by
  set M := mergedProcess H₁ H₂ a b
  set L := mergedList H₁ H₂
  have h_lo_in : t_lo ∈ L := (Finset.mem_sort _).mpr h_lo_mem
  have h_hi_in : t_hi ∈ L := (Finset.mem_sort _).mpr h_hi_mem
  obtain ⟨p, hp_lt, hp_eq⟩ := List.getElem_of_mem h_lo_in
  obtain ⟨q, hq_lt, hq_eq⟩ := List.getElem_of_mem h_hi_in
  rw [← hp_eq] at hs_lo
  rw [← hq_eq] at hs_hi
  have hpq : p < q := by
    by_contra h; push_neg at h
    rcases h.eq_or_lt with rfl | h
    · linarith
    · have := (mergedList_sortedLT H₁ H₂).strictMono_get
        (show (⟨q, hq_lt⟩ : Fin _) < ⟨p, hp_lt⟩ from h)
      simp [List.get_eq_getElem] at this
      linarith
  obtain ⟨k, hk1, _, hk_le, hk_lt⟩ := find_merged_interval
    (mergedList_sortedLT H₁ H₂) hp_lt hq_lt hpq hs_lo hs_hi
  have hk_n : k < M.n := by
    change k < mergedLen H₁ H₂; rw [← mergedList_length]; omega
  have hk1_n : k + 1 < M.n := by
    change k + 1 < mergedLen H₁ H₂; rw [← mergedList_length]; exact hk1
  refine ⟨⟨k, hk_n⟩, hk1_n, ?_, ?_⟩
  · show L.get ((⟨k, hk_n⟩ : Fin M.n).cast (mergedList_length H₁ H₂).symm) ≤ s
    simp [List.get_eq_getElem]; exact hk_le
  · show s < L.get ((⟨k + 1, hk1_n⟩ : Fin M.n).cast (mergedList_length H₁ H₂).symm)
    simp [List.get_eq_getElem]; exact hk_lt

/-- The valueAtTime of the merged process equals the linear combination
    of the original processes' valueAtTime, pointwise for all s and ω. -/
theorem mergedProcess_valueAtTime_linear
    (H₁ H₂ : SimpleProcess F) (a b : ℝ) (s : ℝ) (ω : Ω) :
    (mergedProcess H₁ H₂ a b).valueAtTime s ω =
    a * H₁.valueAtTime s ω + b * H₂.valueAtTime s ω := by
  set M := mergedProcess H₁ H₂ a b
  set L := mergedList H₁ H₂
  by_cases h_in : ∃ (k : Fin M.n) (_ : (k : ℕ) + 1 < M.n),
      M.times k ≤ s ∧ s < M.times ⟨(k : ℕ) + 1, ‹_›⟩
  · obtain ⟨k, hk1, hs_lo, hs_hi⟩ := h_in
    rw [valueAtTime_in_interval M hk1 hs_lo hs_hi]
    show a * H₁.valueAtTime
           (L.get (k.cast (mergedList_length H₁ H₂).symm)) ω +
         b * H₂.valueAtTime
           (L.get (k.cast (mergedList_length H₁ H₂).symm)) ω =
         a * H₁.valueAtTime s ω + b * H₂.valueAtTime s ω
    have hk_lt : (k : ℕ) + 1 < L.length := by rw [mergedList_length]; exact hk1
    have hget : L.get (k.cast (mergedList_length H₁ H₂).symm) =
        L[(k : ℕ)] := by simp [List.get_eq_getElem]
    have ht_k : M.times k = L[(k : ℕ)] := hget
    have ht_k1 : M.times ⟨(k : ℕ) + 1, hk1⟩ = L[(k : ℕ) + 1] := by
      show L.get ((⟨(k : ℕ) + 1, hk1⟩ : Fin M.n).cast
        (mergedList_length H₁ H₂).symm) = L[(k : ℕ) + 1]
      simp [List.get_eq_getElem]
    rw [ht_k] at hs_lo; rw [ht_k1] at hs_hi
    rw [hget,
      congr_fun (H1_valueAtTime_const_on_merged H₁ H₂ hk_lt hs_lo hs_hi) ω,
      congr_fun (H2_valueAtTime_const_on_merged H₁ H₂ hk_lt hs_lo hs_hi) ω]
  · -- M.valueAtTime s = 0 since s is not in any merged interval
    have hM_zero : M.valueAtTime s ω = 0 := by
      unfold valueAtTime; simp only [dif_neg h_in]
    have hH₁_zero : H₁.valueAtTime s ω = 0 := by
      unfold valueAtTime; simp only
      split
      next h =>
        exfalso; obtain ⟨j, hj, hj_lo, hj_hi⟩ := h
        exact h_in (original_interval_implies_merged H₁ H₂ a b
          (times_mem_merged₁ H₁ H₂ j)
          (times_mem_merged₁ H₁ H₂ ⟨(j : ℕ) + 1, hj⟩) hj_lo hj_hi)
      next => rfl
    have hH₂_zero : H₂.valueAtTime s ω = 0 := by
      unfold valueAtTime; simp only
      split
      next h =>
        exfalso; obtain ⟨j, hj, hj_lo, hj_hi⟩ := h
        exact h_in (original_interval_implies_merged H₁ H₂ a b
          (times_mem_merged₂ H₁ H₂ j)
          (times_mem_merged₂ H₁ H₂ ⟨(j : ℕ) + 1, hj⟩) hj_lo hj_hi)
      next => rfl
    rw [hM_zero, hH₁_zero, hH₂_zero, mul_zero, mul_zero, add_zero]

end SimpleProcess
end SPDE
