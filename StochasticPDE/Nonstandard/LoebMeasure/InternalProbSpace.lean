/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal

/-!
# Internal Probability Spaces

This file defines internal (hyperfinite) probability spaces and the pre-Loeb measure.

## Main Definitions

* `InternalProbSpace` - A hyperfinite probability space with counting measure
* `preLoebMeasure` - Standard part of internal probability

## Main Results

* `prob_whole` - The whole space has probability 1
* `prob_add` - Probability is additive
* `prob_finite` - Bounded probabilities are finite

## References

* Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
-/

open Hyperreal Classical

namespace SPDE.Nonstandard

/-! ## Internal Probability Spaces

An internal probability space is a hyperfinite set with counting measure.
-/

/-- An internal (hyperfinite) probability space.
    This is a set of size N with uniform probability 1/N on each element. -/
structure InternalProbSpace where
  /-- The (hyperfinite) size of the sample space -/
  size : ℝ*
  /-- The size is positive -/
  size_pos : 0 < size

namespace InternalProbSpace

variable (Ω : InternalProbSpace)

/-- The internal probability of a subset with given cardinality -/
noncomputable def prob (card : ℝ*) : ℝ* :=
  card / Ω.size

/-- The whole space has probability 1 -/
theorem prob_whole : Ω.prob Ω.size = 1 := by
  unfold prob
  exact div_self (ne_of_gt Ω.size_pos)

/-- The empty set has probability 0 -/
theorem prob_empty : Ω.prob 0 = 0 := by
  simp [prob]

/-- The internal probability is non-negative for non-negative cardinalities -/
theorem prob_nonneg (card : ℝ*) (hcard : 0 ≤ card) :
    0 ≤ Ω.prob card :=
  div_nonneg hcard (le_of_lt Ω.size_pos)

/-- The internal probability is at most 1 for valid cardinalities -/
theorem prob_le_one (card : ℝ*) (hcard : card ≤ Ω.size) :
    Ω.prob card ≤ 1 := by
  unfold prob
  rw [div_le_one (Ω.size_pos)]
  exact hcard

/-- Probability is additive: P(A ∪ B) = P(A) + P(B) for disjoint A, B -/
theorem prob_add (card₁ card₂ : ℝ*) :
    Ω.prob (card₁ + card₂) = Ω.prob card₁ + Ω.prob card₂ := by
  unfold prob
  rw [add_div]

/-- Probability of the complement: P(Ω \ A) = 1 - P(A) -/
theorem prob_compl (card : ℝ*) (_hcard : card ≤ Ω.size) :
    Ω.prob (Ω.size - card) = 1 - Ω.prob card := by
  unfold prob
  rw [sub_div, div_self (ne_of_gt Ω.size_pos)]

/-- Probability is monotone: if |A| ≤ |B| then P(A) ≤ P(B) -/
theorem prob_mono (card₁ card₂ : ℝ*) (h : card₁ ≤ card₂) :
    Ω.prob card₁ ≤ Ω.prob card₂ :=
  div_le_div_of_nonneg_right h (le_of_lt Ω.size_pos)

/-- Probability difference: P(A) - P(B) = P(|A| - |B|) -/
theorem prob_sub (card₁ card₂ : ℝ*) :
    Ω.prob card₁ - Ω.prob card₂ = Ω.prob (card₁ - card₂) := by
  unfold prob
  rw [sub_div]

/-- Probability scales linearly with cardinality -/
theorem prob_smul (c : ℝ*) (card : ℝ*) :
    Ω.prob (c * card) = c * Ω.prob card := by
  unfold prob
  rw [mul_div_assoc]

/-- The probability is finite when cardinality is bounded -/
theorem prob_finite (card : ℝ*) (hcard₁ : 0 ≤ card)
    (hcard₂ : card ≤ Ω.size) (_hsize : ¬Infinite Ω.size) : ¬Infinite (Ω.prob card) := by
  intro hinf
  have h1 : Ω.prob card ≤ 1 := prob_le_one Ω card hcard₂
  have h2 : 0 ≤ Ω.prob card := prob_nonneg Ω card hcard₁
  -- A value in [0, 1] cannot be infinite
  cases hinf with
  | inl hpos =>
    -- Positive infinite: prob > r for all real r, contradicts prob ≤ 1
    have : (1 : ℝ*) < Ω.prob card := hpos 1
    exact absurd h1 (not_le.mpr this)
  | inr hneg =>
    -- Negative infinite: prob < r for all real r, contradicts 0 ≤ prob
    have : Ω.prob card < (0 : ℝ*) := hneg 0
    exact absurd h2 (not_le.mpr this)

end InternalProbSpace

/-! ## Pre-Loeb Measure

The pre-Loeb measure takes standard parts of internal probabilities.
-/

/-- The pre-Loeb measure: standard part of internal probability.
    For probabilities in [0,1], this is always well-defined (not infinite). -/
noncomputable def preLoebMeasure (Ω : InternalProbSpace) (card : ℝ*) : ℝ :=
  if _ : ¬Infinite (Ω.prob card) then st (Ω.prob card) else 0

/-- When the probability is finite (between 0 and 1), preLoebMeasure equals st -/
theorem preLoebMeasure_eq_st (Ω : InternalProbSpace) (card : ℝ*)
    (hfinite : ¬Infinite (Ω.prob card)) : preLoebMeasure Ω card = st (Ω.prob card) := by
  simp [preLoebMeasure, hfinite]

/-- Pre-Loeb measure of empty set is 0 -/
theorem preLoebMeasure_empty (Ω : InternalProbSpace) :
    preLoebMeasure Ω 0 = 0 := by
  have h : Ω.prob 0 = 0 := Ω.prob_empty
  have hfin : ¬Infinite (Ω.prob 0) := by rw [h]; exact not_infinite_zero
  rw [preLoebMeasure, dif_pos hfin, h]
  exact st_id_real 0

/-- Pre-Loeb measure of whole space is 1 -/
theorem preLoebMeasure_whole (Ω : InternalProbSpace) :
    preLoebMeasure Ω Ω.size = 1 := by
  have h : Ω.prob Ω.size = 1 := Ω.prob_whole
  have hfin : ¬Infinite (Ω.prob Ω.size) := by rw [h]; exact not_infinite_real 1
  rw [preLoebMeasure, dif_pos hfin, h]
  exact st_id_real 1

/-- Pre-Loeb measure is non-negative for valid cardinalities -/
theorem preLoebMeasure_nonneg (Ω : InternalProbSpace) (card : ℝ*)
    (hcard : 0 ≤ card) (hfinite : ¬Infinite (Ω.prob card)) :
    0 ≤ preLoebMeasure Ω card := by
  rw [preLoebMeasure_eq_st Ω card hfinite]
  have hprob : 0 ≤ Ω.prob card := Ω.prob_nonneg card hcard
  have h0 : ¬Infinite (0 : ℝ*) := not_infinite_zero
  rw [← st_id_real 0]
  exact st_le_of_le h0 hfinite hprob

/-- Pre-Loeb measure is at most 1 for valid cardinalities -/
theorem preLoebMeasure_le_one (Ω : InternalProbSpace) (card : ℝ*)
    (hcard : card ≤ Ω.size) (hfinite : ¬Infinite (Ω.prob card)) :
    preLoebMeasure Ω card ≤ 1 := by
  rw [preLoebMeasure_eq_st Ω card hfinite]
  have hprob : Ω.prob card ≤ 1 := Ω.prob_le_one card hcard
  have h1 : ¬Infinite (1 : ℝ*) := not_infinite_real 1
  rw [← st_id_real 1]
  exact st_le_of_le hfinite h1 hprob

/-- Pre-Loeb measure is finitely additive for disjoint sets -/
theorem preLoebMeasure_add (Ω : InternalProbSpace) (card₁ card₂ : ℝ*)
    (hfinite₁ : ¬Infinite (Ω.prob card₁)) (hfinite₂ : ¬Infinite (Ω.prob card₂))
    (hfinite_sum : ¬Infinite (Ω.prob (card₁ + card₂))) :
    preLoebMeasure Ω (card₁ + card₂) = preLoebMeasure Ω card₁ + preLoebMeasure Ω card₂ := by
  rw [preLoebMeasure_eq_st Ω (card₁ + card₂) hfinite_sum]
  rw [preLoebMeasure_eq_st Ω card₁ hfinite₁]
  rw [preLoebMeasure_eq_st Ω card₂ hfinite₂]
  rw [Ω.prob_add card₁ card₂]
  exact st_add hfinite₁ hfinite₂

end SPDE.Nonstandard
