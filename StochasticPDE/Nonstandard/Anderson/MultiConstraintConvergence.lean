/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.Anderson.CylinderConvergenceHelpers
import StochasticPDE.Nonstandard.Anderson.LocalCLT

/-!
# Multi-Constraint Convergence

Infrastructure for proving `anderson_theorem_cylinder` for n ≥ 2 time points.

The key idea: random walk increments between disjoint time intervals are independent.
This allows the count of paths satisfying multiple constraints to factor as
a product of transition counts, each converging to a Gaussian density.

## Main Results

* `card_prefix_constraint_suffix_product` - Product counting principle for independent
  prefix/suffix constraints
* `partialSumFin_decompose` - Partial sum decomposes as prefix sum + suffix increment
* `fiber_decomposition` - Conditioning on walk value at a time point
-/

open MeasureTheory Finset BigOperators

namespace SPDE.Nonstandard

/-! ## Product Counting Principle

The fundamental tool: if a predicate on `Fin N → Bool` decomposes as
P_prefix(first k bits) ∧ P_suffix(remaining N-k bits), then the count
factors as count(prefix) × count(suffix). -/

/-- **Product counting for independent prefix/suffix constraints.**

    This is the probabilistic independence of disjoint segments of coin flips:
    the first k flips are independent of the remaining N-k flips.

    Generalizes `card_prefix_suffix_product` (which handles P_suffix = True). -/
theorem card_prefix_constraint_suffix_product (N k : ℕ) (hk : k ≤ N)
    (P_prefix : (Fin k → Bool) → Prop) [DecidablePred P_prefix]
    (P_suffix : (Fin (N - k) → Bool) → Prop) [DecidablePred P_suffix] :
    ((Finset.univ : Finset (Fin N → Bool)).filter (fun f =>
      P_prefix (fun i => f ⟨i.val, i.isLt.trans_le hk⟩) ∧
      P_suffix (fun i => f ⟨k + i.val, by omega⟩))).card =
    ((Finset.univ : Finset (Fin k → Bool)).filter P_prefix).card *
    ((Finset.univ : Finset (Fin (N - k) → Bool)).filter P_suffix).card := by
  -- Forward/backward maps (same as in card_prefix_suffix_product)
  let fwd : (Fin N → Bool) → (Fin k → Bool) × (Fin (N - k) → Bool) :=
    fun f => (fun i => f ⟨i.val, i.isLt.trans_le hk⟩, fun i => f ⟨k + i.val, by omega⟩)
  let bwd : (Fin k → Bool) × (Fin (N - k) → Bool) → (Fin N → Bool) :=
    fun p => fun i => if hlt : i.val < k then p.1 ⟨i.val, hlt⟩
                      else p.2 ⟨i.val - k, by omega⟩
  let source := (Finset.univ : Finset (Fin N → Bool)).filter (fun f =>
    P_prefix (fun i => f ⟨i.val, i.isLt.trans_le hk⟩) ∧
    P_suffix (fun i => f ⟨k + i.val, by omega⟩))
  let target := ((Finset.univ : Finset (Fin k → Bool)).filter P_prefix) ×ˢ
    ((Finset.univ : Finset (Fin (N - k) → Bool)).filter P_suffix)
  suffices hsuff : source.card = target.card by
    rw [hsuff, Finset.card_product]
  show source.card = target.card
  apply Finset.card_bij' (fun f _ => fwd f) (fun p _ => bwd p)
  · -- fwd maps source to target
    intro f hf
    simp only [source, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [target, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hf
  · -- bwd maps target to source
    intro p hp
    simp only [target, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · convert hp.1 using 1
      ext i; show bwd p ⟨i.val, _⟩ = p.1 i
      simp only [bwd, show (i.val : ℕ) < k from i.isLt, ↓reduceDIte]
    · convert hp.2 using 1
      ext i; show bwd p ⟨k + i.val, _⟩ = p.2 i
      dsimp only [bwd]
      simp only [show ¬((k + i.val : ℕ) < k) from by omega, ↓reduceDIte,
        show k + i.val - k = i.val from by omega]
  · -- left_inv: bwd (fwd f) = f
    intro f _; ext ⟨i, hi⟩
    show bwd (fwd f) ⟨i, hi⟩ = f ⟨i, hi⟩
    dsimp only [fwd, bwd]
    split
    · next hlt => rfl
    · next hlt =>
        simp only [show k + (i - k) = i from by omega]
  · -- right_inv: fwd (bwd p) = p
    intro p _
    show fwd (bwd p) = p
    ext ⟨i, hi⟩
    · -- First component
      show (fwd (bwd p)).1 ⟨i, hi⟩ = p.1 ⟨i, hi⟩
      simp only [fwd, bwd, show (i : ℕ) < k from hi, ↓reduceDIte]
    · -- Second component
      show (fwd (bwd p)).2 ⟨i, hi⟩ = p.2 ⟨i, hi⟩
      dsimp only [fwd, bwd]
      simp only [show ¬((k + ↑i : ℕ) < k) from by omega, ↓reduceDIte,
        show k + i - k = i from by omega]

/-! ## Partial Sum Decomposition -/

/-- The partial sum decomposes as prefix sum + suffix increment.

    For k ≤ m: S_m(f) = S_k(f) + S_{m-k}(suffix(f,k))
    where suffix(f,k)(j) = f(k+j) is the suffix walk. -/
theorem partialSumFin_decompose (N : ℕ) (f : Fin N → Bool) (k m : ℕ)
    (hk : k ≤ N) (hkm : k ≤ m) :
    partialSumFin N f m = partialSumFin N f k +
      partialSumFin (N - k) (fun i : Fin (N - k) => f ⟨k + i.val, by omega⟩) (m - k) := by
  unfold partialSumFin
  -- Split {i : Fin N | i < m} = {i | i < k} ∪ {i | k ≤ i < m}
  rw [show (Finset.univ.filter (fun i : Fin N => i.val < m)) =
      (Finset.univ.filter (fun i : Fin N => i.val < k)) ∪
      (Finset.univ.filter (fun i : Fin N => k ≤ i.val ∧ i.val < m)) from by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega]
  rw [Finset.sum_union (Finset.disjoint_filter.mpr (fun i _ h1 h2 => by omega))]
  congr 1
  -- The sum over {i : Fin N | k ≤ i < m} equals the suffix partial sum
  -- Strategy: use Finset.sum_map with the embedding j ↦ k + j
  let e : Fin (N - k) ↪ Fin N :=
    ⟨fun j => ⟨k + j.val, by omega⟩, fun j₁ j₂ h => by ext; simp [Fin.ext_iff] at h; omega⟩
  have hmap : (Finset.univ.filter (fun i : Fin N => k ≤ i.val ∧ i.val < m)) =
      (Finset.univ.filter (fun j : Fin (N - k) => j.val < m - k)).map e := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro ⟨hki, him⟩
      exact ⟨⟨i.val - k, by omega⟩, by simp; omega,
        by ext; show k + (i.val - k) = i.val; omega⟩
    · rintro ⟨j, hj, rfl⟩
      -- hj : j.val < m - k, goal : k ≤ (e j).val ∧ (e j).val < m
      have hval : (e j).val = k + j.val := rfl
      rw [hval]; exact ⟨by omega, by omega⟩
  rw [hmap, Finset.sum_map]
  apply Finset.sum_congr rfl; intro x _; congr 1

/-- The prefix partial sum (at step m ≤ k) depends only on the first k values. -/
theorem partialSumFin_prefix_eq (N : ℕ) (f : Fin N → Bool) (k m : ℕ)
    (hk : k ≤ N) (hmk : m ≤ k) :
    partialSumFin N f m =
    partialSumFin k (fun i : Fin k => f ⟨i.val, i.isLt.trans_le hk⟩) m := by
  unfold partialSumFin
  -- Embed Fin k into Fin N
  let e : Fin k ↪ Fin N :=
    ⟨fun i => ⟨i.val, i.isLt.trans_le hk⟩,
     fun i₁ i₂ h => Fin.ext (by simp [Fin.ext_iff] at h; exact h)⟩
  -- The filter {i : Fin N | i < m} equals the image of {i : Fin k | i < m} under e
  have hmap : (Finset.univ.filter (fun i : Fin N => i.val < m)) =
      (Finset.univ.filter (fun i : Fin k => i.val < m)).map e := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro him
      exact ⟨⟨i, by omega⟩, him, Fin.ext rfl⟩
    · rintro ⟨⟨j, hj⟩, hjm, hjj⟩
      simp only [Fin.ext_iff] at hjj
      have : (e ⟨j, hj⟩).val = j := rfl
      rw [← hjj]; exact hjm
  rw [hmap, Finset.sum_map]; rfl

/-! ## Fiber Decomposition -/

/-- **Fiber decomposition: conditioning on walk value at step k.**

    The number of paths with S_k = v AND satisfying a suffix constraint
    factors as #{prefix with S_k = v} × #{suffix satisfying constraint}. -/
theorem fiber_decomposition (N k : ℕ) (hk : k ≤ N)
    (v : ℤ) (P_suffix : (Fin (N - k) → Bool) → Prop) [DecidablePred P_suffix] :
    ((Finset.univ : Finset (Fin N → Bool)).filter (fun f =>
      partialSumFin N f k = v ∧
      P_suffix (fun i : Fin (N - k) => f ⟨k + i.val, by omega⟩))).card =
    ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => partialSumFin k g k = v)).card *
    ((Finset.univ : Finset (Fin (N - k) → Bool)).filter P_suffix).card := by
  -- Reduce to card_prefix_constraint_suffix_product
  have h := card_prefix_constraint_suffix_product N k hk
    (fun g₁ => partialSumFin k g₁ k = v) P_suffix
  rw [← h]
  congr 1; ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hv, hp⟩
    exact ⟨by rwa [← partialSumFin_prefix_eq N f k k hk le_rfl], hp⟩
  · rintro ⟨hv, hp⟩
    exact ⟨by rwa [partialSumFin_prefix_eq N f k k hk le_rfl], hp⟩

/-- Walk value count: #{f : Fin k → Bool | S_k = v}.
    When |v| ≤ k and k ≡ v (mod 2), this equals C(k, (k+v)/2). -/
theorem walkValueCount_eq_choose (k : ℕ) (j : ℕ) (hj : j ≤ k) :
    ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => partialSumFin k g k = (2 * (j : ℤ) - k))).card =
    Nat.choose k j := by
  -- S_k = 2·#trues - k, so S_k = 2j - k ⟺ #trues = j
  -- This is card_prefix_suffix_product with N = k (trivial suffix)
  -- combined with card_bool_trues_eq_choose
  rw [show ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => partialSumFin k g k = (2 * (j : ℤ) - k))).card =
    ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => countTruesBelow k g k = j)).card from by
    congr 1; ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [partialSumFin_eq_countTrues k g k le_rfl]
    omega]
  -- Now use card_bool_trues_eq_choose
  -- Need: #{g : Fin k → Bool | countTruesBelow k g k = j} = C(k, j)
  -- countTruesBelow k g k = #{i : Fin k | i.val < k ∧ g i = true} = #{i | g i = true}
  rw [show ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => countTruesBelow k g k = j)).card =
    ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => (Finset.univ.filter (fun i => g i = true)).card = j)).card from by
    congr 1; ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold countTruesBelow
    have : (Finset.univ.filter (fun i : Fin k => i.val < k ∧ g i = true)) =
           (Finset.univ.filter (fun i : Fin k => g i = true)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right i.isLt]
    rw [this]]
  exact card_bool_trues_eq_choose k j hj

/-! ## CountTruesBelow bound -/

/-- countTruesBelow is at most k (public version). -/
theorem countTruesBelow_le (M k₁ : ℕ) (f : Fin M → Bool) (hk₁ : k₁ ≤ M) :
    countTruesBelow M f k₁ ≤ k₁ := by
  unfold countTruesBelow
  calc ((Finset.univ.filter (fun i : Fin M => i.val < k₁ ∧ f i = true)).card)
      ≤ ((Finset.univ.filter (fun i : Fin M => i.val < k₁)).card) := by
        apply Finset.card_le_card
        intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact And.left
    _ = k₁ := card_filter_lt M k₁ hk₁

/-! ## Fiber Decomposition Sum with Dependent Suffix -/

/-- **Fiber decomposition sum with dependent suffix constraint.**

    For walks of M steps, decomposing at step k₁:
    - P_first checks a condition on the walk value at step k₁
    - P_suffix checks a condition depending on both the walk value and the suffix flips

    The total count equals a sum over possible walk values (indexed by #trues = j),
    factoring as C(k₁,j) × #{suffix satisfying the constraint}. -/
theorem card_walk_first_suffix_sum (M k₁ : ℕ) (hk₁ : k₁ ≤ M)
    (P_first : ℤ → Prop) [DecidablePred P_first]
    (P_suffix : ℤ → (Fin (M - k₁) → Bool) → Prop)
    [∀ v, DecidablePred (P_suffix v)] :
    ((Finset.univ : Finset (Fin M → Bool)).filter (fun f =>
      P_first (partialSumFin M f k₁) ∧
      P_suffix (partialSumFin M f k₁) (fun i => f ⟨k₁ + i.val, by omega⟩))).card =
    ∑ j ∈ Finset.range (k₁ + 1),
      if P_first (2 * (j : ℤ) - k₁) then
        Nat.choose k₁ j *
        ((Finset.univ : Finset (Fin (M - k₁) → Bool)).filter
          (P_suffix (2 * (j : ℤ) - k₁))).card
      else 0 := by
  -- Step 1: Partition by countTruesBelow value
  set S := (Finset.univ : Finset (Fin M → Bool)).filter (fun f =>
    P_first (partialSumFin M f k₁) ∧
    P_suffix (partialSumFin M f k₁) (fun i => f ⟨k₁ + i.val, by omega⟩)) with hS_def
  set g := fun f : Fin M → Bool => countTruesBelow M f k₁ with hg_def
  have hg_range : (S : Set _).MapsTo g ↑(Finset.range (k₁ + 1)) := by
    intro f _; simp only [Finset.coe_range, Set.mem_Iio, g]
    exact Nat.lt_succ_of_le (countTruesBelow_le M k₁ f hk₁)
  rw [Finset.card_eq_sum_card_fiberwise hg_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k₁ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- Key: in fiber j, partialSumFin = 2j - k₁
  have hval_in_fiber : ∀ f : Fin M → Bool, countTruesBelow M f k₁ = j →
      partialSumFin M f k₁ = (2 * (j : ℤ) - ↑k₁) := by
    intro f hctb
    have h := partialSumFin_eq_countTrues M f k₁ hk₁
    rw [hctb] at h; linarith
  by_cases hcond : P_first (2 * (j : ℤ) - ↑k₁)
  · rw [if_pos hcond]
    -- Fiber = {f | S_{k₁} = 2j-k₁ ∧ P_suffix(2j-k₁, suffix(f))}
    have hfiber_eq : S.filter (fun f => g f = j) =
        (Finset.univ : Finset (Fin M → Bool)).filter (fun f =>
          partialSumFin M f k₁ = (2 * (j : ℤ) - ↑k₁) ∧
          P_suffix (2 * (j : ℤ) - ↑k₁) (fun i => f ⟨k₁ + i.val, by omega⟩)) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, g]
      constructor
      · rintro ⟨⟨hPf, hPs⟩, hctb⟩
        have hval := hval_in_fiber f hctb
        exact ⟨hval, by rwa [hval] at hPs⟩
      · rintro ⟨hval, hPs⟩
        have hctb : countTruesBelow M f k₁ = j := by
          have h := partialSumFin_eq_countTrues M f k₁ hk₁
          rw [hval] at h; omega
        refine ⟨⟨by rwa [hval_in_fiber f hctb], by rwa [hval_in_fiber f hctb]⟩, hctb⟩
    rw [hfiber_eq]
    -- Apply fiber_decomposition + walkValueCount_eq_choose
    rw [fiber_decomposition M k₁ hk₁ (2 * (j : ℤ) - ↑k₁) (P_suffix (2 * (j : ℤ) - ↑k₁)),
        walkValueCount_eq_choose k₁ j hjk]
  · rw [if_neg hcond]
    -- Fiber is empty: P_first(S_{k₁}) is false when ctb = j
    have hempty : S.filter (fun f => g f = j) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro f hf
      have hf' := Finset.mem_filter.mp hf
      have hfS := Finset.mem_filter.mp hf'.1
      have hctb : countTruesBelow M f k₁ = j := hf'.2
      have hval := hval_in_fiber f hctb
      have h1 : P_first (partialSumFin M f k₁) := hfS.2.1
      rw [hval] at h1
      exact hcond h1
    simp [hempty]

end SPDE.Nonstandard
