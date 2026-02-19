/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.LoebMeasurable
import StochasticPDE.Nonstandard.LoebMeasure.SigmaAdditivity
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.Caratheodory

/-!
# Mathlib Bridge: Loeb Measure as MeasureTheory.Measure

This file outlines the strategy for constructing the Loeb measure as an instance of
Mathlib's `MeasureTheory.Measure`.

## Goal

Bridge our nonstandard Loeb measure construction to Mathlib's measure theory, enabling:
1. Use of Mathlib's integration theorems (Fubini, dominated convergence)
2. Application of probability theory (expectation, variance, martingales)
3. Statement of Anderson's theorem: pushforward of Loeb measure = Wiener measure

## Current Infrastructure

Our existing construction works with **cardinalities** rather than sets:
- `InternalProbSpace` has `size : ℝ*` but no carrier type
- `InternalSubset` stores `card : ℝ*` as the cardinality
- `preLoebMeasure` computes `st(card/size)`

This abstracts away the underlying sample space, which is sufficient for
probability computations but not for constructing a Mathlib Measure directly.

## Strategy for Full Construction

To create a proper `MeasureTheory.Measure`, we need a concrete sample space.
For the hyperfinite random walk, this would be:

1. **Define the sample space**: For N steps, Ω_N = Fin N → Bool (coin flips)

2. **Define the hyperfinite sample space**: Use the ultraproduct construction
   Ω = Germ (hyperfilter ℕ) (fun n => Fin n → Bool)

3. **Define internal sets**: An internal set is a family A_n ⊆ Ω_n for each n,
   with coherence conditions from the ultrafilter

4. **Apply Carathéodory**: Extend preLoeb from internal algebra to σ-algebra

The key insight is that Mathlib's `OuterMeasure.toMeasure` already provides
Carathéodory extension—we just need to set up the types correctly.

## References

* Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
* Carathéodory, C. "Vorlesungen über reelle Funktionen" (1918)
* Mathlib documentation on MeasureTheory.OuterMeasure
-/

open scoped ENNReal
open MeasureTheory Set Hyperreal Filter

namespace SPDE.Nonstandard

/-! ## Concrete Sample Space for Hyperfinite Random Walk

For the Mathlib bridge, we work with the concrete hyperfinite coin flip space.
-/

/-- The sample space at level n: n coin flips -/
abbrev CoinFlips (n : ℕ) := Fin n → Bool

/-- An internal set in the hyperfinite probability space is a family of sets
    at each level, respecting the ultrafilter equivalence. -/
structure LevelwiseSet where
  /-- The set at each level -/
  sets : ∀ n : ℕ, Set (CoinFlips n)

/-- The cardinality at level n -/
noncomputable def LevelwiseSet.cardAtLevel (A : LevelwiseSet) (n : ℕ) : ℕ :=
  (A.sets n).toFinite.toFinset.card

/-- Two levelwise sets are equivalent if they agree on an ultrafilter-large set of levels -/
def LevelwiseSet.equiv (A B : LevelwiseSet) : Prop :=
  ∀ᶠ n in hyperfilter ℕ, A.sets n = B.sets n

/-- The hyperfinite cardinality as a hyperreal -/
noncomputable def LevelwiseSet.hyperCard (A : LevelwiseSet) : ℝ* :=
  Hyperreal.ofSeq (fun n => (A.cardAtLevel n : ℝ))

/-- The hyperfinite probability -/
noncomputable def LevelwiseSet.hyperProb (A : LevelwiseSet) : ℝ* :=
  Hyperreal.ofSeq (fun n => if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n)

/-- The pre-Loeb measure: standard part of the hyperfinite probability.
    We use Classical.propDecidable to handle the decidability issue. -/
noncomputable def LevelwiseSet.preLoeb (A : LevelwiseSet) : ℝ :=
  @dite ℝ (Hyperreal.Infinite A.hyperProb) (Classical.propDecidable _) (fun _ => 0) (fun _ => Hyperreal.st A.hyperProb)

/-! ## Properties of Pre-Loeb Measure -/

theorem LevelwiseSet.preLoeb_nonneg (A : LevelwiseSet) : 0 ≤ A.preLoeb := by
  unfold preLoeb
  by_cases h : Infinite A.hyperProb
  · simp only [dif_pos h, le_refl]
  · simp only [dif_neg h]
    have hnn : 0 ≤ A.hyperProb := by
      unfold hyperProb ofSeq
      have hle : ∀ n, (0 : ℝ) ≤ (if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) := by
        intro n
        split_ifs
        · exact le_refl 0
        · apply div_nonneg
          · exact Nat.cast_nonneg _
          · exact pow_nonneg (by norm_num) _
      exact Germ.coe_le.mpr (Eventually.of_forall hle)
    have h0 : ¬Infinite (0 : ℝ*) := not_infinite_zero
    rw [← st_id_real 0]
    exact st_le_of_le h0 h hnn

theorem LevelwiseSet.preLoeb_le_one (A : LevelwiseSet) : A.preLoeb ≤ 1 := by
  unfold preLoeb
  by_cases h : Infinite A.hyperProb
  · simp only [dif_pos h]; linarith
  · simp only [dif_neg h]
    have hle : A.hyperProb ≤ 1 := by
      unfold hyperProb ofSeq
      have hle' : ∀ n, (if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) ≤ (1 : ℝ) := by
        intro n
        split_ifs with hn
        · linarith
        · apply div_le_one_of_le₀
          · have hcard : A.cardAtLevel n ≤ 2^n := by
              unfold cardAtLevel
              have hfin : (A.sets n).Finite := Set.toFinite _
              calc hfin.toFinset.card
                  ≤ (Finset.univ : Finset (CoinFlips n)).card := Finset.card_le_card (Finset.subset_univ _)
                _ = Fintype.card (CoinFlips n) := Finset.card_univ
                _ = Fintype.card (Fin n → Bool) := rfl
                _ = 2^n := by simp [Fintype.card_bool, Fintype.card_fin]
            calc (A.cardAtLevel n : ℝ)
                ≤ (2^n : ℕ) := Nat.cast_le.mpr hcard
              _ = 2^n := by norm_cast
          · exact pow_nonneg (by norm_num) _
      exact Germ.coe_le.mpr (Eventually.of_forall hle')
    have h1 : ¬Infinite (1 : ℝ*) := not_infinite_real 1
    rw [← st_id_real 1]
    exact st_le_of_le h h1 hle

/-- Empty set has pre-Loeb measure 0 -/
def LevelwiseSet.empty : LevelwiseSet where
  sets := fun _ => ∅

theorem LevelwiseSet.preLoeb_empty : LevelwiseSet.empty.preLoeb = 0 := by
  unfold preLoeb
  have hzero : LevelwiseSet.empty.hyperProb = 0 := by
    unfold hyperProb cardAtLevel ofSeq empty
    have h : (fun n => if n = 0 then (0 : ℝ) else
        (∅ : Set (CoinFlips n)).toFinite.toFinset.card / 2^n) = fun _ => 0 := by
      ext n
      split_ifs with hn
      · rfl
      · simp only [Set.toFinite_toFinset, Set.toFinset_empty, Finset.card_empty,
          Nat.cast_zero, zero_div]
    simp only [h]
    rfl
  rw [hzero]
  have h : ¬Infinite (0 : ℝ*) := not_infinite_zero
  simp only [dif_neg h]
  exact st_id_real 0

/-- Full set has pre-Loeb measure 1 -/
def LevelwiseSet.univ : LevelwiseSet where
  sets := fun _ => Set.univ

theorem LevelwiseSet.preLoeb_univ : LevelwiseSet.univ.preLoeb = 1 := by
  unfold preLoeb
  have hprob : LevelwiseSet.univ.hyperProb = 1 := by
    unfold hyperProb cardAtLevel ofSeq univ
    have h : (fun n => if n = 0 then (0 : ℝ) else
        (Set.univ : Set (CoinFlips n)).toFinite.toFinset.card / 2^n) =ᶠ[hyperfilter ℕ]
        (fun _ => (1 : ℝ)) := by
      -- Eventually n ≥ 1, and for n ≥ 1 the statement holds
      have hcofin : {n : ℕ | n ≠ 0} ∈ hyperfilter ℕ := by
        apply mem_hyperfilter_of_finite_compl
        simp only [Set.compl_setOf, ne_eq, Decidable.not_not]
        exact Set.finite_singleton 0
      apply Eventually.mono hcofin
      intro n hn
      simp only [ne_eq] at hn
      simp only [if_neg hn]
      have hcard : (Set.univ : Set (CoinFlips n)).toFinite.toFinset.card = 2^n := by
        simp only [Set.Finite.toFinset_univ, Finset.card_univ]
        simp [Fintype.card_bool, Fintype.card_fin]
      simp only [hcard, Nat.cast_pow, Nat.cast_ofNat]
      have hpos : (2 : ℝ)^n ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hpos]
    exact Germ.coe_eq.mpr h
  rw [hprob]
  have h1 : ¬Infinite (1 : ℝ*) := not_infinite_real 1
  simp only [dif_neg h1]
  exact st_id_real 1

/-! ## Finite Additivity

The pre-Loeb measure is finitely additive on disjoint levelwise sets.
-/

/-- Disjoint levelwise sets -/
def LevelwiseSet.AreDisjoint (A B : LevelwiseSet) : Prop :=
  ∀ n, Disjoint (A.sets n) (B.sets n)

/-- Union of levelwise sets -/
def LevelwiseSet.union (A B : LevelwiseSet) : LevelwiseSet where
  sets := fun n => A.sets n ∪ B.sets n

/-- For disjoint sets at each level, the union cardinality equals the sum -/
theorem LevelwiseSet.cardAtLevel_union_disjoint (A B : LevelwiseSet) (h : A.AreDisjoint B) (n : ℕ) :
    (A.union B).cardAtLevel n = A.cardAtLevel n + B.cardAtLevel n := by
  unfold cardAtLevel union
  simp only
  have hdisj : Disjoint (A.sets n) (B.sets n) := h n
  -- The finite toFinsets of disjoint sets have disjoint toFinsets
  have hfinA : (A.sets n).Finite := Set.toFinite _
  have hfinB : (B.sets n).Finite := Set.toFinite _
  have hfinU : (A.sets n ∪ B.sets n).Finite := Set.toFinite _
  -- Convert to Finset disjointness
  have hfindisj : Disjoint hfinA.toFinset hfinB.toFinset := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Set.Finite.mem_toFinset] at ha hb
    intro heq
    rw [heq] at ha
    exact Set.disjoint_iff.mp hdisj ⟨ha, hb⟩
  -- The union toFinset equals the disjoint union of toFinsets
  have hunion : hfinU.toFinset = hfinA.toFinset ∪ hfinB.toFinset := by
    ext x
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_union]
  rw [hunion, Finset.card_union_of_disjoint hfindisj]

/-- The hyperfinite probability of disjoint union equals the sum -/
theorem LevelwiseSet.hyperProb_add_disjoint (A B : LevelwiseSet) (h : A.AreDisjoint B) :
    (A.union B).hyperProb = A.hyperProb + B.hyperProb := by
  unfold hyperProb ofSeq
  have hadd : (fun n => if n = 0 then (0 : ℝ) else ((A.union B).cardAtLevel n : ℝ) / 2^n) =
              (fun n => if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) +
              (fun n => if n = 0 then 0 else (B.cardAtLevel n : ℝ) / 2^n) := by
    ext n
    simp only [Pi.add_apply]
    split_ifs with hn
    · ring
    · rw [cardAtLevel_union_disjoint A B h n]
      simp only [Nat.cast_add, add_div]
  rw [hadd, Germ.coe_add]

theorem LevelwiseSet.preLoeb_add_disjoint (A B : LevelwiseSet) (h : A.AreDisjoint B) :
    (A.union B).preLoeb = A.preLoeb + B.preLoeb := by
  unfold preLoeb
  rw [hyperProb_add_disjoint A B h]
  -- Case analysis on finiteness
  -- Helper: hyperProb is bounded between 0 and 1, hence not infinite
  have hyperProb_not_infinite : ∀ X : LevelwiseSet, ¬Infinite X.hyperProb := by
    intro X
    have hle : X.hyperProb ≤ 1 := by
      unfold hyperProb ofSeq
      have hle' : ∀ n, (if n = 0 then 0 else (X.cardAtLevel n : ℝ) / 2^n) ≤ (1 : ℝ) := by
        intro n
        split_ifs with hn
        · linarith
        · apply div_le_one_of_le₀
          · have hcard : X.cardAtLevel n ≤ 2^n := by
              unfold cardAtLevel
              have hfin : (X.sets n).Finite := Set.toFinite _
              calc hfin.toFinset.card
                  ≤ (Finset.univ : Finset (CoinFlips n)).card := Finset.card_le_card (Finset.subset_univ _)
                _ = Fintype.card (CoinFlips n) := Finset.card_univ
                _ = 2^n := by simp [Fintype.card_bool, Fintype.card_fin]
            calc (X.cardAtLevel n : ℝ) ≤ (2^n : ℕ) := Nat.cast_le.mpr hcard
              _ = 2^n := by norm_cast
          · exact pow_nonneg (by norm_num) _
      exact Germ.coe_le.mpr (Eventually.of_forall hle')
    have hnn : 0 ≤ X.hyperProb := by
      unfold hyperProb ofSeq
      have hle' : ∀ n, (0 : ℝ) ≤ (if n = 0 then 0 else (X.cardAtLevel n : ℝ) / 2^n) := by
        intro n
        split_ifs
        · linarith
        · apply div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
      exact Germ.coe_le.mpr (Eventually.of_forall hle')
    -- If 0 ≤ x ≤ 1, then x is not infinite
    rw [not_infinite_iff_exist_lt_gt]
    refine ⟨-1, 2, ?_, ?_⟩
    · calc (-1 : ℝ*) < 0 := by norm_num
        _ ≤ X.hyperProb := hnn
    · calc X.hyperProb ≤ 1 := hle
        _ < 2 := by norm_num
  by_cases hA : Infinite A.hyperProb
  · exact absurd hA (hyperProb_not_infinite A)
  · by_cases hB : Infinite B.hyperProb
    · exact absurd hB (hyperProb_not_infinite B)
    · -- Both finite, so use st_add
      have hAB : ¬Infinite (A.hyperProb + B.hyperProb) := not_infinite_add hA hB
      simp only [dif_neg hA, dif_neg hB, dif_neg hAB]
      exact st_add hA hB

/-! ## Subadditivity

The pre-Loeb measure is subadditive: preLoeb(A ∪ B) ≤ preLoeb(A) + preLoeb(B).
This follows from |A ∪ B| ≤ |A| + |B|.
-/

/-- The cardinality of a union is at most the sum of cardinalities -/
theorem LevelwiseSet.cardAtLevel_union_le (A B : LevelwiseSet) (n : ℕ) :
    (A.union B).cardAtLevel n ≤ A.cardAtLevel n + B.cardAtLevel n := by
  unfold cardAtLevel union
  simp only
  have hfinA : (A.sets n).Finite := Set.toFinite _
  have hfinB : (B.sets n).Finite := Set.toFinite _
  have hfinU : (A.sets n ∪ B.sets n).Finite := Set.toFinite _
  have hunion : hfinU.toFinset ⊆ hfinA.toFinset ∪ hfinB.toFinset := by
    intro x hx
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_union] at hx ⊢
    exact hx
  calc hfinU.toFinset.card
      ≤ (hfinA.toFinset ∪ hfinB.toFinset).card := Finset.card_le_card hunion
    _ ≤ hfinA.toFinset.card + hfinB.toFinset.card := Finset.card_union_le _ _

/-- The hyperfinite probability is subadditive -/
theorem LevelwiseSet.hyperProb_le_add (A B : LevelwiseSet) :
    (A.union B).hyperProb ≤ A.hyperProb + B.hyperProb := by
  unfold hyperProb ofSeq
  have hle : ∀ n, (if n = 0 then (0 : ℝ) else ((A.union B).cardAtLevel n : ℝ) / 2^n) ≤
                  (if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) +
                  (if n = 0 then 0 else (B.cardAtLevel n : ℝ) / 2^n) := by
    intro n
    split_ifs with hn
    · simp
    · have hcard := cardAtLevel_union_le A B n
      have hpos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
      calc ((A.union B).cardAtLevel n : ℝ) / 2^n
          ≤ (A.cardAtLevel n + B.cardAtLevel n : ℕ) / 2^n := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
            exact Nat.cast_le.mpr hcard
        _ = (A.cardAtLevel n : ℝ) / 2^n + (B.cardAtLevel n : ℝ) / 2^n := by
            simp only [Nat.cast_add, add_div]
  have hle' : (fun n => if n = 0 then (0 : ℝ) else ((A.union B).cardAtLevel n : ℝ) / 2^n) ≤
              (fun n => if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) +
              (fun n => if n = 0 then 0 else (B.cardAtLevel n : ℝ) / 2^n) := by
    intro n
    simp only [Pi.add_apply]
    exact hle n
  calc ofSeq (fun n => if n = 0 then (0 : ℝ) else ((A.union B).cardAtLevel n : ℝ) / 2^n)
      ≤ ofSeq ((fun n => if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) +
                    (fun n => if n = 0 then 0 else (B.cardAtLevel n : ℝ) / 2^n)) := by
        exact Germ.coe_le.mpr (Eventually.of_forall hle')
    _ = ofSeq (fun n => if n = 0 then 0 else (A.cardAtLevel n : ℝ) / 2^n) +
        ofSeq (fun n => if n = 0 then 0 else (B.cardAtLevel n : ℝ) / 2^n) := rfl

/-- The pre-Loeb measure is subadditive -/
theorem LevelwiseSet.preLoeb_le_add (A B : LevelwiseSet) :
    (A.union B).preLoeb ≤ A.preLoeb + B.preLoeb := by
  unfold preLoeb
  -- All hyperProbs are in [0,1], hence not infinite
  have hyperProb_not_infinite : ∀ X : LevelwiseSet, ¬Infinite X.hyperProb := by
    intro X
    rw [not_infinite_iff_exist_lt_gt]
    refine ⟨-1, 2, ?_, ?_⟩
    · calc (-1 : ℝ*) < 0 := by norm_num
        _ ≤ X.hyperProb := by
          unfold hyperProb ofSeq
          apply Germ.coe_le.mpr
          apply Eventually.of_forall
          intro n
          simp only
          split_ifs <;> positivity
    · calc X.hyperProb ≤ 1 := by
            unfold hyperProb ofSeq
            apply Germ.coe_le.mpr
            apply Eventually.of_forall
            intro n
            simp only
            split_ifs with hn
            · linarith
            · apply div_le_one_of_le₀
              · have hcard : X.cardAtLevel n ≤ 2^n := by
                  unfold cardAtLevel
                  have hfin : (X.sets n).Finite := Set.toFinite _
                  calc hfin.toFinset.card
                      ≤ (Finset.univ : Finset (CoinFlips n)).card := Finset.card_le_card (Finset.subset_univ _)
                    _ = Fintype.card (CoinFlips n) := Finset.card_univ
                    _ = 2^n := by simp [Fintype.card_bool, Fintype.card_fin]
                calc (X.cardAtLevel n : ℝ) ≤ (2^n : ℕ) := Nat.cast_le.mpr hcard
                  _ = 2^n := by norm_cast
              · exact pow_nonneg (by norm_num) _
        _ < 2 := by norm_num
  have hU : ¬Infinite (A.union B).hyperProb := hyperProb_not_infinite (A.union B)
  have hA : ¬Infinite A.hyperProb := hyperProb_not_infinite A
  have hB : ¬Infinite B.hyperProb := hyperProb_not_infinite B
  have hAB : ¬Infinite (A.hyperProb + B.hyperProb) := not_infinite_add hA hB
  simp only [dif_neg hU, dif_neg hA, dif_neg hB]
  have hle := hyperProb_le_add A B
  -- st(union) ≤ st(A + B) = st(A) + st(B)
  calc st (A.union B).hyperProb
      ≤ st (A.hyperProb + B.hyperProb) := st_le_of_le hU hAB hle
    _ = st A.hyperProb + st B.hyperProb := st_add hA hB

/-! ## Toward Carathéodory Extension

For a full Mathlib measure, we need to:
1. Define the outer measure via countable covers
2. Show internal sets satisfy the Carathéodory condition
3. Verify the resulting measure agrees with pre-Loeb on internal sets

The key theorem that enables this is `DecreasingConcreteEvents.sigma_additivity`
from SigmaAdditivity.lean, which shows that for decreasing sequences with
empty intersection, the pre-Loeb measures converge to 0.
-/

/-- The Loeb outer measure on levelwise sets.
    μ*(E) = inf { Σ preLoeb(A_i) : E ⊆ ⋃ A_i, A_i internal } -/
noncomputable def loebOuterMeasureValue (E : LevelwiseSet) : ℝ≥0∞ :=
  ⨅ (cover : ℕ → LevelwiseSet) (_ : ∀ m, ∀ᶠ k in hyperfilter ℕ,
      E.sets k ⊆ ⋃ i ∈ Finset.range (m + 1), (cover i).sets k),
    ∑' i, ENNReal.ofReal (cover i).preLoeb

/-! ## Constructing the Mathlib OuterMeasure

For a full Mathlib measure, we need to define an OuterMeasure and verify
the Carathéodory condition.
-/

/-- The sample space type: sequences of coin flips for each level n.
    The Loeb measure will be defined on the ultraproduct Germ (hyperfilter ℕ) Ω_n
    where Ω_n = Fin n → Bool. -/
abbrev HyperfiniteSampleSpace := Germ (↑(hyperfilter ℕ) : Filter ℕ) (ℕ → (ℕ → Bool))

/-! ## Outer Measure from Pre-Loeb

We define the outer measure via countable covers by internal (levelwise) sets.
-/

/-- A countable cover of a levelwise set by internal sets.
    This represents a sequence of internal sets whose union contains the target. -/
structure LevelwiseCover (E : LevelwiseSet) where
  /-- The covering sets -/
  cover : ℕ → LevelwiseSet
  /-- Coverage property: eventually at each level, E is contained in the union -/
  covers : ∀ m, ∀ᶠ k in hyperfilter ℕ, E.sets k ⊆ ⋃ i ∈ Finset.range (m + 1), (cover i).sets k

/-- The cost of a cover: the sum of pre-Loeb measures. -/
noncomputable def LevelwiseCover.cost {E : LevelwiseSet} (C : LevelwiseCover E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (C.cover i).preLoeb

/-- The outer measure defined via covers.
    μ*(E) = inf { Σ preLoeb(Aᵢ) : E ⊆ ⋃ Aᵢ eventually } -/
noncomputable def loebOuterMeasure' (E : LevelwiseSet) : ℝ≥0∞ :=
  ⨅ (C : LevelwiseCover E), C.cost

/-- The trivial cover of E by itself (with zeros for other indices). -/
noncomputable def trivialCover (E : LevelwiseSet) : LevelwiseCover E where
  cover := fun n => if n = 0 then E else LevelwiseSet.empty
  covers := fun m => by
    apply Filter.Eventually.of_forall
    intro k x hx
    -- Goal: x ∈ ⋃ i ∈ Finset.range (m + 1), (if i = 0 then E else empty).sets k
    -- We show x ∈ E.sets k = (cover 0).sets k
    rw [Set.mem_iUnion]
    use 0
    rw [Set.mem_iUnion]
    use Finset.mem_range.mpr (Nat.zero_lt_succ m)
    -- Goal: x ∈ (if 0 = 0 then E else empty).sets k
    simp only [↓reduceIte]
    exact hx

/-- The outer measure is bounded above by the pre-Loeb measure. -/
theorem loebOuterMeasure'_le_preLoeb (E : LevelwiseSet) :
    loebOuterMeasure' E ≤ ENNReal.ofReal E.preLoeb := by
  unfold loebOuterMeasure'
  apply iInf_le_of_le (trivialCover E)
  -- Show cost of trivial cover ≤ preLoeb(E)
  unfold LevelwiseCover.cost trivialCover
  simp only
  -- The sum is preLoeb(E) + 0 + 0 + ...
  have hsum : ∑' i, ENNReal.ofReal ((if i = 0 then E else LevelwiseSet.empty).preLoeb) =
      ENNReal.ofReal E.preLoeb := by
    rw [tsum_eq_single 0]
    · simp only [if_true]
    · intro n hn
      simp only [if_neg hn]
      rw [LevelwiseSet.preLoeb_empty]
      simp
  exact le_of_eq hsum

/-- The outer measure of the empty set is 0. -/
theorem loebOuterMeasure'_empty : loebOuterMeasure' LevelwiseSet.empty = 0 := by
  apply le_antisymm
  · -- Upper bound via trivial cover
    calc loebOuterMeasure' LevelwiseSet.empty
        ≤ ENNReal.ofReal LevelwiseSet.empty.preLoeb := loebOuterMeasure'_le_preLoeb _
      _ = ENNReal.ofReal 0 := by rw [LevelwiseSet.preLoeb_empty]
      _ = 0 := by simp
  · exact zero_le _

/-- The outer measure is monotone with respect to eventual subset. -/
theorem loebOuterMeasure'_mono {E F : LevelwiseSet}
    (h : ∀ᶠ k in hyperfilter ℕ, E.sets k ⊆ F.sets k) :
    loebOuterMeasure' E ≤ loebOuterMeasure' F := by
  unfold loebOuterMeasure'
  -- For each cover C of F, construct a cover of E with same cost
  -- Then iInf over E ≤ iInf over F by comparing at each F-cover
  apply le_iInf
  intro C
  -- C is a cover of F, so it's also a cover of E (since E ⊆ F eventually)
  let C' : LevelwiseCover E := {
    cover := C.cover
    covers := fun m => by
      apply Filter.Eventually.mono (h.and (C.covers m))
      intro k ⟨hEF, hcover⟩ x hx
      exact hcover (hEF hx)
  }
  calc ⨅ D : LevelwiseCover E, D.cost ≤ C'.cost := iInf_le _ C'
    _ = C.cost := rfl

/-! ## Carathéodory Measurability

An internal set A is Carathéodory measurable if for all E:
  μ*(E) = μ*(E ∩ A) + μ*(E ∩ Aᶜ)
-/

/-- Intersection of levelwise sets. -/
def LevelwiseSet.inter (A B : LevelwiseSet) : LevelwiseSet where
  sets := fun n => A.sets n ∩ B.sets n

/-- Set difference of levelwise sets. -/
def LevelwiseSet.diff (A B : LevelwiseSet) : LevelwiseSet where
  sets := fun n => A.sets n \ B.sets n

/-- Complement of a levelwise set (relative to full coin flip space). -/
def LevelwiseSet.compl' (A : LevelwiseSet) : LevelwiseSet where
  sets := fun n => (A.sets n)ᶜ

/-- (E ∩ A) and (E \ A) are disjoint levelwise sets. -/
theorem LevelwiseSet.inter_diff_disjoint (E A : LevelwiseSet) :
    (E.inter A).AreDisjoint (E.diff A) := by
  intro n
  simp only [inter, diff, Set.disjoint_iff]
  intro x ⟨⟨hxE, hxA⟩, hxEA, hxnA⟩
  exact hxnA hxA

/-- (E ∩ A) ∪ (E \ A) = E at each level. -/
theorem LevelwiseSet.inter_union_diff (E A : LevelwiseSet) :
    ∀ n, (E.inter A).sets n ∪ (E.diff A).sets n = E.sets n := by
  intro n
  simp only [inter, diff]
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
  constructor
  · intro h
    cases h with
    | inl h => exact h.1
    | inr h => exact h.1
  · intro hxE
    by_cases hxA : x ∈ A.sets n
    · left; exact ⟨hxE, hxA⟩
    · right; exact ⟨hxE, hxA⟩

/-- The union (E ∩ A) ∪ (E \ A) equals E as a levelwise set. -/
theorem LevelwiseSet.inter_union_diff_eq (E A : LevelwiseSet) :
    (E.inter A).union (E.diff A) = E := by
  have h : ∀ n, ((E.inter A).union (E.diff A)).sets n = E.sets n := inter_union_diff E A
  cases E with | mk sets => simp only [union, inter, diff] at h ⊢; congr; funext n; exact h n

/-- A levelwise set is Carathéodory measurable if it "splits" all sets correctly. -/
def LoebCaratheodoryMeasurable (A : LevelwiseSet) : Prop :=
  ∀ E : LevelwiseSet, loebOuterMeasure' E =
    loebOuterMeasure' (E.inter A) + loebOuterMeasure' (E.diff A)

/-- Interleave two sequences: (a₀, b₀, a₁, b₁, ...) -/
def interleave {α : Type*} (a b : ℕ → α) : ℕ → α :=
  fun n => if n % 2 = 0 then a (n / 2) else b (n / 2)

/-- The sum of an interleaved sequence equals the sum of the two parts. -/
theorem tsum_interleave_eq_add {a b : ℕ → ℝ≥0∞} :
    ∑' n, interleave a b n = ∑' n, a n + ∑' n, b n := by
  -- Use tsum_even_add_odd: ∑ f(2k) + ∑ f(2k+1) = ∑ f(n)
  have heven : (fun k => interleave a b (2 * k)) = a := by
    ext n
    unfold interleave
    have h : (2 * n) % 2 = 0 := Nat.mul_mod_right 2 n
    simp only [h, ↓reduceIte, Nat.mul_div_right _ (by norm_num : 0 < 2)]
  have hodd : (fun k => interleave a b (2 * k + 1)) = b := by
    ext n
    unfold interleave
    have h : (2 * n + 1) % 2 ≠ 0 := by omega
    rw [if_neg h]
    congr 1
    omega
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable, heven, hodd]

/-- Internal sets are Carathéodory measurable.

    This is the key theorem enabling the Carathéodory extension.
    The proof uses finite additivity of preLoeb on internal sets.

    **Proof Strategy**:
    - (≤) Subadditivity: E = (E ∩ A) ∪ (E \ A), so μ*(E) ≤ μ*(E ∩ A) + μ*(E \ A)
      by combining covers of the two parts
    - (≥) Superadditivity: Any cover C of E splits into covers of (E ∩ A) and (E \ A)
      with cost(C) ≥ μ*(E ∩ A) + μ*(E \ A) because we can extract covers from C -/
theorem loebCaratheodory_of_internal (A : LevelwiseSet) :
    LoebCaratheodoryMeasurable A := by
  intro E
  apply le_antisymm
  · -- μ*(E) ≤ μ*(E ∩ A) + μ*(E \ A) by subadditivity
    -- Given any covers C of (E ∩ A) and D of (E \ A), interleave them to cover E
    -- We show: ⨅ X, X.cost ≤ (⨅ C, C.cost) + (⨅ D, D.cost)
    -- For each pair (C, D), construct X with X.cost = C.cost + D.cost
    -- Then ⨅ X ≤ X.cost = C.cost + D.cost, and taking inf over (C,D) gives the result
    show loebOuterMeasure' E ≤ loebOuterMeasure' (E.inter A) + loebOuterMeasure' (E.diff A)
    unfold loebOuterMeasure'
    -- Rewrite RHS: (⨅ C) + (⨅ D) = ⨅ C, ⨅ D, (C + D) using ENNReal lemmas
    conv_rhs => rw [ENNReal.iInf_add]; arg 1; ext C; rw [ENNReal.add_iInf]
    -- Now goal is: ⨅ X ≤ ⨅ C, ⨅ D, (C.cost + D.cost)
    apply le_iInf
    intro C  -- C is a cover of E.inter A
    apply le_iInf
    intro D  -- D is a cover of E.diff A
    -- Combine C and D into a cover of E using unions at each index
    -- This avoids the interleaving coverage issues at low levels
    let CD : LevelwiseCover E := {
        cover := fun i => (C.cover i).union (D.cover i)
        covers := fun m => by
          -- E = (E ∩ A) ∪ (E \ A), C covers E ∩ A, D covers E \ A
          have hC := C.covers m
          have hD := D.covers m
          apply Filter.Eventually.mono (hC.and hD)
          intro k ⟨hCk, hDk⟩ x hxE
          have hdecomp := LevelwiseSet.inter_union_diff E A k
          rw [← hdecomp] at hxE
          cases hxE with
          | inl hxEA =>
            obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hCk hxEA)
            rw [Set.mem_iUnion₂]
            refine ⟨i, hi, ?_⟩
            simp only [LevelwiseSet.union, Set.mem_union]
            left; exact hxi
          | inr hxEA' =>
            obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hDk hxEA')
            rw [Set.mem_iUnion₂]
            refine ⟨i, hi, ?_⟩
            simp only [LevelwiseSet.union, Set.mem_union]
            right; exact hxi
      }
    -- Cost bound: preLoeb(A ∪ B) ≤ preLoeb(A) + preLoeb(B) by subadditivity
    calc ⨅ X : LevelwiseCover E, X.cost ≤ CD.cost := iInf_le _ CD
      _ = ∑' n, ENNReal.ofReal ((C.cover n).union (D.cover n)).preLoeb := rfl
      _ ≤ ∑' n, (ENNReal.ofReal (C.cover n).preLoeb + ENNReal.ofReal (D.cover n).preLoeb) := by
        apply ENNReal.tsum_le_tsum
        intro n
        -- Use preLoeb subadditivity: preLoeb(A ∪ B) ≤ preLoeb(A) + preLoeb(B)
        have hle := LevelwiseSet.preLoeb_le_add (C.cover n) (D.cover n)
        have hnnC : 0 ≤ (C.cover n).preLoeb := LevelwiseSet.preLoeb_nonneg _
        have hnnD : 0 ≤ (D.cover n).preLoeb := LevelwiseSet.preLoeb_nonneg _
        calc ENNReal.ofReal ((C.cover n).union (D.cover n)).preLoeb
            ≤ ENNReal.ofReal ((C.cover n).preLoeb + (D.cover n).preLoeb) :=
              ENNReal.ofReal_le_ofReal hle
          _ = ENNReal.ofReal (C.cover n).preLoeb + ENNReal.ofReal (D.cover n).preLoeb :=
              ENNReal.ofReal_add hnnC hnnD
      _ = ∑' n, ENNReal.ofReal (C.cover n).preLoeb +
          ∑' n, ENNReal.ofReal (D.cover n).preLoeb := ENNReal.tsum_add
      _ = C.cost + D.cost := rfl
  · -- μ*(E ∩ A) + μ*(E \ A) ≤ μ*(E)
    -- For any cover C of E, the restrictions C_i ∩ A cover E ∩ A
    -- and the restrictions C_i \ A cover E \ A
    unfold loebOuterMeasure'
    -- We show: (⨅ C, C.cost) + (⨅ D, D.cost) ≤ ⨅ X, X.cost
    -- For any X covering E, construct covers XA of E ∩ A and XA' of E \ A
    -- Then (⨅ C) + (⨅ D) ≤ XA.cost + XA'.cost = X.cost
    apply le_iInf
    intro X  -- X is a cover of E
    -- Construct cover of E ∩ A by restricting X
    let XA : LevelwiseCover (E.inter A) := {
      cover := fun n => (X.cover n).inter A
      covers := fun m => by
        apply Filter.Eventually.mono (X.covers m)
        intro k hXk x hx
        -- x ∈ (E ∩ A) ⊆ E, so x ∈ ⋃ X_i
        have hxE : x ∈ E.sets k := hx.1
        have hxA : x ∈ A.sets k := hx.2
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hXk hxE)
        rw [Set.mem_iUnion₂]
        use i, hi
        simp only [LevelwiseSet.inter]
        exact ⟨hxi, hxA⟩
    }
    -- Construct cover of E \ A by restricting X
    let XA' : LevelwiseCover (E.diff A) := {
      cover := fun n => (X.cover n).diff A
      covers := fun m => by
        apply Filter.Eventually.mono (X.covers m)
        intro k hXk x hx
        -- x ∈ (E \ A) ⊆ E, so x ∈ ⋃ X_i
        have hxE : x ∈ E.sets k := hx.1
        have hxnA : x ∉ A.sets k := hx.2
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hXk hxE)
        rw [Set.mem_iUnion₂]
        use i, hi
        simp only [LevelwiseSet.diff]
        exact ⟨hxi, hxnA⟩
    }
    -- Now show costs add up: X_i = (X_i ∩ A) ∪ (X_i \ A) disjointly
    -- So preLoeb(X_i) = preLoeb(X_i ∩ A) + preLoeb(X_i \ A)
    calc (⨅ C : LevelwiseCover (E.inter A), C.cost) +
         (⨅ D : LevelwiseCover (E.diff A), D.cost)
        ≤ XA.cost + XA'.cost := by
          apply add_le_add (iInf_le _ XA) (iInf_le _ XA')
      _ = ∑' n, ENNReal.ofReal ((X.cover n).inter A).preLoeb +
          ∑' n, ENNReal.ofReal ((X.cover n).diff A).preLoeb := rfl
      _ = X.cost := by
            -- Key: preLoeb(B ∩ A) + preLoeb(B \ A) = preLoeb(B) by finite additivity
            rw [← ENNReal.tsum_add]
            unfold LevelwiseCover.cost
            apply tsum_congr
            intro n
            let B := X.cover n
            -- (B ∩ A) and (B \ A) are disjoint
            have hdisj : (B.inter A).AreDisjoint (B.diff A) :=
              LevelwiseSet.inter_diff_disjoint B A
            -- Their union equals B
            have hunion : (B.inter A).union (B.diff A) = B :=
              LevelwiseSet.inter_union_diff_eq B A
            -- By finite additivity: preLoeb((B ∩ A) ∪ (B \ A)) = preLoeb(B ∩ A) + preLoeb(B \ A)
            have hadd : ((B.inter A).union (B.diff A)).preLoeb =
                (B.inter A).preLoeb + (B.diff A).preLoeb :=
              LevelwiseSet.preLoeb_add_disjoint (B.inter A) (B.diff A) hdisj
            -- Substitute using hunion to get: B.preLoeb = (B.inter A).preLoeb + (B.diff A).preLoeb
            rw [hunion] at hadd
            -- Convert to ENNReal
            have hnn1 : 0 ≤ (B.inter A).preLoeb := LevelwiseSet.preLoeb_nonneg _
            have hnn2 : 0 ≤ (B.diff A).preLoeb := LevelwiseSet.preLoeb_nonneg _
            rw [hadd, ENNReal.ofReal_add hnn1 hnn2]

/-! ## Construction of the Mathlib Measure

Using Carathéodory's theorem, we extend the outer measure to a measure
on the σ-algebra of Carathéodory-measurable sets.
-/

/-- The Loeb outer measure as a Mathlib OuterMeasure on coin flip sequences.

    We define this on the type `ℕ → Bool` (infinite coin flip sequences).
    For now, this is a placeholder; the proper construction would use
    the ultraproduct structure and connect to `loebOuterMeasure'`.

    Note: This uses Classical decidability for set membership. -/
noncomputable def loebOuterMeasureOnCoinFlips : OuterMeasure (ℕ → Bool) :=
  OuterMeasure.ofFunction
    (fun s : Set (ℕ → Bool) =>
      -- Placeholder: proper construction needs ultraproduct connection
      @dite _ (s = ∅) (Classical.propDecidable _) (fun _ => 0)
        (fun _ => @dite _ (s = Set.univ) (Classical.propDecidable _)
          (fun _ => 1) (fun _ => ENNReal.ofReal (1/2))))
    (by simp only [dif_pos])

/-! ## Summary

**Completed (All Proofs Without Sorries):**
- `LevelwiseSet`: Concrete representation of internal sets
- `hyperProb`, `preLoeb`: Hyperfinite probability and standard part
- `preLoeb_add_disjoint`: Finite additivity
- `cardAtLevel_union_le`, `hyperProb_le_add`, `preLoeb_le_add`: Subadditivity
- `loebOuterMeasure'`: Outer measure via covers
- `loebOuterMeasure'_empty`: μ*(∅) = 0
- `loebOuterMeasure'_mono`: Monotonicity
- `loebCaratheodory_of_internal`: **Internal sets are Carathéodory measurable**

**Key Insight:**
The Carathéodory extension theorem (Mathlib's `OuterMeasure.toMeasure`) can now
be applied once we connect our `loebOuterMeasure'` (on `LevelwiseSet`) to a
proper Mathlib `OuterMeasure` on a concrete carrier type.

The σ-additivity theorem `DecreasingConcreteEvents.sigma_additivity` in
`SigmaAdditivity.lean` provides the crucial property: for decreasing
internal sets with empty intersection, the measures converge to 0.

**Remaining Work:**
1. Define the proper carrier space (ultraproduct `Germ (hyperfilter ℕ) (Fin n → Bool)`)
2. Connect `loebOuterMeasure'` to Mathlib's `OuterMeasure` structure
3. Connect to Mathlib's `OuterMeasure.toMeasure`
4. Prove Anderson's theorem: Measure.map st loebMeasure = wienerMeasure

The foundational work (σ-additivity via saturation) is complete.
The remaining work is type-theoretic: setting up the correct Mathlib structures.
-/

end SPDE.Nonstandard
