/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import StochasticPDE.Nonstandard.Foundation.InternalMembership

/-!
# ℵ₁-Saturation for Ultraproducts

This file develops the ℵ₁-saturation property for the ultraproduct ℝ* = ℝ^ℕ / U
(where U is a non-principal ultrafilter on ℕ).

## Main Definitions

* `CountableInternalFamily` - A countable family of internal sets
* `HasFIP` - The finite intersection property for internal sets
* `HasStandardFIP` - Standard-level FIP (stronger, directly usable)

## Main Results

* `countable_saturation` - If a countable family of internal sets has standard FIP,
  then their intersection is non-empty. This is ℵ₁-saturation.

## Key Ideas

The proof of ℵ₁-saturation for ultrapowers uses a diagonal argument:

Given a countable family {Aᵢ}_{i∈ℕ} of internal sets:
1. Each Aᵢ is represented by a sequence of standard sets (Aᵢⁿ)_{n∈ℕ}
2. Standard FIP: for each n, ⋂_{i≤n} Aᵢⁿ ≠ ∅ (n-th level intersection nonempty)
3. Choose xₙ ∈ ⋂_{i≤n} Aᵢⁿ
4. The element [xₙ] = ofSeq x is in every Aᵢ

Why step 4 works: For fixed i, {n | xₙ ∈ Aᵢⁿ} ⊇ {n | n ≥ i}, which is cofinite.

## References

* Goldblatt, "Lectures on the Hyperreals", Chapter 11
* Chang & Keisler, "Model Theory", Chapter 6
-/

open Hyperreal Filter Set

namespace SPDE.Nonstandard.Foundation

/-! ## Countable Families of Internal Sets -/

/-- A countable family of internal sets -/
structure CountableInternalFamily where
  /-- The family indexed by ℕ -/
  family : ℕ → InternalSet

namespace CountableInternalFamily

variable (F : CountableInternalFamily)

/-- A point is in all sets of the family -/
def memAll (x : ℝ*) : Prop := ∀ i : ℕ, F.family i |>.mem x

/-- The finite intersection property at the internal level:
    every finite subfamily has nonempty internal intersection -/
def HasFIP : Prop :=
  ∀ (n : ℕ), ∃ x : ℝ*, ∀ i ≤ n, F.family i |>.mem x

/-- The finite intersection property at the standard level:
    for each n, the n-th level intersection is nonempty.
    This is: ⋂_{i≤n} (F.family i).sets n ≠ ∅ for all n.
    This is a stronger, more directly usable condition. -/
def HasStandardFIP : Prop :=
  ∀ (n : ℕ), ∃ x : ℝ, ∀ i ≤ n, x ∈ (F.family i).sets n

/-! ### Note on HasFIP vs HasStandardFIP

HasFIP and HasStandardFIP are DIFFERENT conditions in general.

- **HasFIP**: For each n, ∃ y : ℝ* such that y is in the internal intersection
  of F.family 0, ..., F.family n. Internal membership means the representative
  f satisfies f(k) ∈ (F.family i).sets k for ALMOST ALL k (in the ultrafilter).

- **HasStandardFIP**: For each n, ∃ x : ℝ such that x ∈ (F.family i).sets n for all i ≤ n.
  This gives a witness at ONE SPECIFIC level n.

The implication HasStandardFIP → HasFIP does NOT hold in general because:
- HasStandardFIP gives xₙ ∈ (F.family i).sets n (at level n only)
- Internal membership requires f(k) ∈ (F.family i).sets k for almost all k
- A constant sequence (x, x, ...) would need x ∈ (F.family i).sets k for almost all k,
  but we only know about level n.

However, for UNIFORM families (where sets k = sets m for all k, m), the
conditions become equivalent. See `uniform_hasFIP_implies_hasStandardFIP`.

The key insight is that the saturation theorem `countable_saturation_standard`
uses HasStandardFIP directly, bypassing HasFIP entirely. The diagonal construction
in that proof explicitly uses the level-matching property of HasStandardFIP.
-/

end CountableInternalFamily

/-! ## Helper Lemmas -/

/-- Helper: combine finitely many Eventually conditions -/
theorem eventually_forall_le {α : Type*} {f : Filter α} [f.NeBot]
    {P : ℕ → α → Prop} (n : ℕ) (h : ∀ i ≤ n, ∀ᶠ m in f, P i m) :
    ∀ᶠ m in f, ∀ i ≤ n, P i m := by
  induction n with
  | zero =>
    have h0 := h 0 (le_refl 0)
    exact h0.mono (fun m hm i hi => by simp only [Nat.le_zero] at hi; subst hi; exact hm)
  | succ n ih =>
    have hn := h (n + 1) (le_refl (n + 1))
    have hprev : ∀ᶠ m in f, ∀ i ≤ n, P i m := ih (fun i hi => h i (Nat.le_succ_of_le hi))
    exact (hprev.and hn).mono (fun m ⟨hm1, hm2⟩ i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with hlt | heq
      · exact hm1 i (Nat.le_of_lt_succ hlt)
      · exact heq ▸ hm2)

/-- The complement of {m | n ≤ m} is {m | m < n}, which is finite -/
theorem compl_ge_finite (n : ℕ) : {m : ℕ | n ≤ m}ᶜ.Finite := by
  convert finite_lt_nat n using 1
  ext m
  simp only [mem_compl_iff, mem_setOf_eq, not_le]

/-- {m | n ≤ m} is in the hyperfilter -/
theorem ge_mem_hyperfilter (n : ℕ) : {m | n ≤ m} ∈ (hyperfilter ℕ : Filter ℕ) :=
  mem_hyperfilter_of_finite_compl (compl_ge_finite n)

/-- Sets in an ultrafilter are nonempty -/
theorem Ultrafilter.nonempty_of_mem {α : Type*} (U : Ultrafilter α) {s : Set α}
    (hs : s ∈ (U : Filter α)) : s.Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hbot : (U : Filter α) = ⊥ := Filter.empty_mem_iff_bot.mp (hemp ▸ hs)
  exact (Filter.NeBot.ne U.neBot) hbot

/-! ## The Saturation Theorem via Standard FIP -/

/-- The main saturation theorem using standard FIP.

    If a countable family of internal sets has standard FIP (for each n,
    the n-th level intersection ⋂_{i≤n} (F.family i).sets n is nonempty),
    then there exists an element in all the internal sets. -/
theorem countable_saturation_standard (F : CountableInternalFamily)
    (hFIP : F.HasStandardFIP) : ∃ x : ℝ*, F.memAll x := by
  -- Build diagonal witness: for each n, pick xₙ ∈ ⋂_{i≤n} (F.family i).sets n
  choose xseq hxseq using hFIP

  -- Define x as the ultraproduct of xseq
  let x : ℝ* := ofSeq xseq
  use x

  -- Show x ∈ F.family i for each i
  intro i
  -- Need: (F.family i).mem x = ∃ f, x = ofSeq f ∧ ∀ᶠ n, f n ∈ (F.family i).sets n
  refine ⟨xseq, rfl, ?_⟩

  -- For n ≥ i, we have i ≤ n, so xseq n ∈ (F.family i).sets n by hxseq
  have hmem : ∀ n, i ≤ n → xseq n ∈ (F.family i).sets n := fun n hin => hxseq n i hin

  -- {n | i ≤ n} is in the hyperfilter
  have hcofin : {n | i ≤ n} ∈ (hyperfilter ℕ : Filter ℕ) := ge_mem_hyperfilter i

  -- Convert to Eventually
  have hev : ∀ᶠ n in hyperfilter ℕ, xseq n ∈ (F.family i).sets n := by
    apply Filter.mem_of_superset hcofin
    intro n hn
    exact hmem n hn

  exact hev

/-! ## Relating Internal FIP to Standard FIP -/

/-- For "uniform" internal families where each level set is the same,
    internal FIP implies standard FIP. -/
def CountableInternalFamily.IsUniform (F : CountableInternalFamily) : Prop :=
  ∀ i : ℕ, ∃ S : Set ℝ, ∀ n : ℕ, (F.family i).sets n = S

/-- For uniform families, internal FIP implies standard FIP -/
theorem uniform_hasFIP_implies_hasStandardFIP (F : CountableInternalFamily)
    (huni : F.IsUniform) (hFIP : F.HasFIP) : F.HasStandardFIP := by
  intro n
  obtain ⟨y, hy⟩ := hFIP n

  -- For uniform families, each (F.family i).sets k = Sᵢ for all k
  -- So y ∈ F.family i means y = ofSeq f with f k ∈ Sᵢ for almost all k
  -- In particular, there exists some k where f k ∈ Sᵢ for all i ≤ n

  -- Get a common representative
  obtain ⟨f, hf⟩ := ofSeq_surjective y

  -- For each i ≤ n, y ∈ F.family i
  have hmem : ∀ i ≤ n, ∀ᶠ k in hyperfilter ℕ, f k ∈ (F.family i).sets k := by
    intro i hi
    obtain ⟨g, hg_eq, hg_mem⟩ := hy i hi
    -- g and f both represent y
    have heq : ofSeq g = ofSeq f := hg_eq.symm.trans hf.symm
    unfold ofSeq at heq
    have hae : ∀ᶠ k in hyperfilter ℕ, g k = f k := Germ.coe_eq.mp heq
    exact (hae.and hg_mem).mono (fun k ⟨he, hm⟩ => he ▸ hm)

  -- Combine
  have hcomb : ∀ᶠ k in hyperfilter ℕ, ∀ i ≤ n, f k ∈ (F.family i).sets k :=
    eventually_forall_le n hmem

  -- Get a witness
  have hne := Ultrafilter.nonempty_of_mem (hyperfilter ℕ) hcomb
  obtain ⟨k, hk⟩ := hne

  -- For uniform families, (F.family i).sets k = (F.family i).sets n = Sᵢ
  -- So f k ∈ (F.family i).sets k implies f k ∈ (F.family i).sets n
  use f k
  intro i hi
  have heq : (F.family i).sets k = (F.family i).sets n := by
    obtain ⟨S, hS⟩ := huni i
    rw [hS k, hS n]
  rw [← heq]
  exact hk i hi

/-! ## Alternative Approach: FIP for Decreasing Families -/

/-- A family is decreasing if each set contains the next level's set -/
def CountableInternalFamily.IsDecreasing (F : CountableInternalFamily) : Prop :=
  ∀ i n : ℕ, (F.family i).sets (n + 1) ⊆ (F.family i).sets n

-- Note: For uniform families, HasFIP implies HasStandardFIP regardless of whether
-- the family is decreasing. The IsDecreasing property may be useful for other
-- constructions but is not needed for the main saturation theorem.

/-! ## General Saturation via Level-Adjusted FIP -/

/-- Level-adjusted FIP: A stronger condition that directly gives diagonal witnesses.
    For each n, the n-th level intersection of the first n+1 sets is nonempty. -/
def CountableInternalFamily.HasLevelAdjustedFIP (F : CountableInternalFamily) : Prop :=
  ∀ n : ℕ, (⋂ i ∈ Finset.range (n + 1), (F.family i).sets n).Nonempty

/-- HasLevelAdjustedFIP is equivalent to HasStandardFIP -/
theorem hasLevelAdjustedFIP_iff_hasStandardFIP (F : CountableInternalFamily) :
    F.HasLevelAdjustedFIP ↔ F.HasStandardFIP := by
  constructor
  · intro h n
    obtain ⟨x, hx⟩ := h n
    use x
    intro i hi
    have hmem : x ∈ ⋂ j ∈ Finset.range (n + 1), (F.family j).sets n := hx
    rw [Set.mem_iInter₂] at hmem
    exact hmem i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · intro h n
    obtain ⟨x, hx⟩ := h n
    use x
    rw [Set.mem_iInter₂]
    intro i hi
    exact hx i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-! ## Main Saturation Corollary -/

/-- Main saturation theorem: given HasStandardFIP, the intersection is nonempty -/
theorem countable_saturation (F : CountableInternalFamily)
    (hFIP : F.HasStandardFIP) : ∃ x : ℝ*, ∀ i : ℕ, (F.family i).mem x :=
  countable_saturation_standard F hFIP

/-! ## Application to Loeb Measure: What We Need

For the Loeb measure construction, we work with internal probability spaces:
- Sample space Ω with hyperfinite cardinality N
- Internal probability P : internal subsets → ℝ* with P(Ω) = 1
- Pre-Loeb measure: μ*(A) = st(P(A)) for internal sets A

The key property we need is σ-additivity of the Loeb extension.
This follows from saturation applied to specific internal families.

For a decreasing sequence of internal sets A₁ ⊇ A₂ ⊇ ... with ⋂ Aᵢ = ∅:
- We need to show P(Aᵢ) → 0
- This uses saturation to derive a contradiction if all P(Aᵢ) ≥ ε

The internal families arising in Loeb measure constructions typically
satisfy HasStandardFIP due to their specific structure (cylinder sets,
sets defined by finitely many constraints, etc.).
-/

end SPDE.Nonstandard.Foundation
