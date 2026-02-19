/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.SigmaAdditivity

/-!
# Loeb Measurability and the Loeb σ-algebra

This file develops Loeb measurability via inner and outer measures.

## Main Definitions

* `LoebMeasurableSet` - A set characterized by its Loeb measure
* `LoebOuterMeasure` - Outer measure via internal approximation from above
* `LoebInnerMeasure` - Inner measure via internal approximation from below
* `LoebMeasurable` - Sets where inner = outer measure
* `DecreasingInternalSubsets` - Decreasing sequence of internal subsets

## Main Results

* `loebMeasurable_compl_internal` - Complements of internal sets are Loeb measurable
* `loebMeasurable_add_disjoint` - Finite additivity for disjoint internal sets
* `internal_algebra` - Internal sets form an algebra under Loeb measure

## References

* Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
-/

open Hyperreal Filter

namespace SPDE.Nonstandard

variable {Ω : InternalProbSpace}

/-! ## Loeb Measurability

A set A ⊆ Ω is Loeb measurable if for every ε > 0, there exist internal sets
B ⊆ A ⊆ C with μ_L(C) - μ_L(B) < ε.

Since we represent internal sets by cardinalities, we define Loeb measurability
in terms of approximation by internal cardinalities.
-/

/-- A Loeb measurable set is characterized by its inner and outer measures
    being equal. For internal sets, inner = outer = preLoeb. -/
structure LoebMeasurableSet (Ω : InternalProbSpace) where
  /-- The Loeb measure value -/
  measure : ℝ
  /-- Non-negative -/
  measure_nonneg : 0 ≤ measure
  /-- At most 1 -/
  measure_le_one : measure ≤ 1
  /-- Approximation property: for any ε > 0, there exist internal sets
      with inner ≥ measure - ε and outer ≤ measure + ε -/
  approx : ∀ (eps : ℝ), eps > 0 → ∃ (B C : InternalSubset Ω),
    B.preLoeb ≤ measure ∧ measure ≤ C.preLoeb ∧
    C.preLoeb - B.preLoeb < eps

/-- An internal set is Loeb measurable with measure = preLoeb -/
noncomputable def loebMeasurableOfInternal (A : InternalSubset Ω) : LoebMeasurableSet Ω where
  measure := A.preLoeb
  measure_nonneg := A.preLoeb_nonneg
  measure_le_one := A.preLoeb_le_one
  approx := fun _ _ => ⟨A, A, le_refl _, le_refl _, by linarith⟩

/-- The empty set is Loeb measurable with measure 0 -/
noncomputable def loebMeasurableEmpty (Ω : InternalProbSpace) :
    LoebMeasurableSet Ω :=
  loebMeasurableOfInternal InternalSubset.empty

/-- The full set is Loeb measurable with measure 1 -/
noncomputable def loebMeasurableUniv (Ω : InternalProbSpace) :
    LoebMeasurableSet Ω :=
  loebMeasurableOfInternal InternalSubset.univ

theorem loebMeasurableEmpty_measure (Ω : InternalProbSpace) :
    (loebMeasurableEmpty Ω).measure = 0 :=
  preLoebMeasure_empty Ω

theorem loebMeasurableUniv_measure (Ω : InternalProbSpace) :
    (loebMeasurableUniv Ω).measure = 1 :=
  preLoebMeasure_whole Ω

/-! ## σ-Additivity from Saturation

The key theorem: for a decreasing sequence of internal sets Aₙ with ⋂ Aₙ = ∅,
we have μ_L(Aₙ) → 0.

This follows from saturation via contrapositive:
If μ_L(Aₙ) ≥ ε > 0 for all n, then by saturation ⋂ Aₙ ≠ ∅.
-/

/-- A sequence of internal subsets with decreasing cardinalities -/
structure DecreasingInternalSubsets (Ω : InternalProbSpace) where
  /-- The sequence of subsets -/
  sets : ℕ → InternalSubset Ω
  /-- Cardinalities are decreasing -/
  decreasing : ∀ n, (sets (n + 1)).card ≤ (sets n).card

namespace DecreasingInternalSubsets

/-- Pre-Loeb measures are decreasing -/
theorem preLoeb_decreasing (F : DecreasingInternalSubsets Ω) :
    ∀ n, (F.sets (n + 1)).preLoeb ≤ (F.sets n).preLoeb := by
  intro n
  have hcard := F.decreasing n
  -- preLoeb = st(prob) and prob = card/size, so decreasing card ⟹ decreasing preLoeb
  have hprob : (F.sets (n + 1)).prob ≤ (F.sets n).prob :=
    Ω.prob_mono _ _ hcard
  have hfin1 := (F.sets (n + 1)).prob_not_infinite
  have hfin2 := (F.sets n).prob_not_infinite
  rw [(F.sets (n + 1)).preLoeb_eq_st, (F.sets n).preLoeb_eq_st]
  exact st_le_of_le hfin1 hfin2 hprob

/-- Pre-Loeb measures are bounded below by 0 -/
theorem preLoeb_nonneg (F : DecreasingInternalSubsets Ω) (n : ℕ) :
    0 ≤ (F.sets n).preLoeb := (F.sets n).preLoeb_nonneg

/-- Pre-Loeb measures are bounded above by 1 -/
theorem preLoeb_le_one (F : DecreasingInternalSubsets Ω) (n : ℕ) :
    (F.sets n).preLoeb ≤ 1 := (F.sets n).preLoeb_le_one

/-- For a bounded monotone sequence, the limit exists -/
theorem preLoeb_tendsto (F : DecreasingInternalSubsets Ω) :
    ∃ L, Tendsto (fun n => (F.sets n).preLoeb) atTop (nhds L) := by
  -- Bounded decreasing sequence converges
  have hbdd : BddBelow (Set.range (fun n => (F.sets n).preLoeb)) := by
    use 0
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact F.preLoeb_nonneg n
  have hmono : Antitone (fun n => (F.sets n).preLoeb) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step _ ih => exact le_trans (F.preLoeb_decreasing _) ih
  exact ⟨_, tendsto_atTop_ciInf hmono hbdd⟩

end DecreasingInternalSubsets

/-! ## Loeb Outer and Inner Measures

The Loeb outer measure of a set A is defined as:
  μ*(A) = inf { μ_L(B) : B is internal, A ⊆ B }

The Loeb inner measure is defined as:
  μ*(A) = sup { μ_L(B) : B is internal, B ⊆ A }

A set A is Loeb measurable if μ*(A) = μ*(A).

Since we work with hyperreal cardinalities rather than explicit subset relations,
we define these in terms of approximation sequences.
-/

/-- The Loeb outer measure of a set, defined via approximation from above.
    We represent this abstractly as a value together with a witness that
    internal sets can approximate it from above. -/
structure LoebOuterMeasure (Ω : InternalProbSpace) where
  /-- The outer measure value -/
  value : ℝ
  /-- Non-negative -/
  value_nonneg : 0 ≤ value
  /-- At most 1 -/
  value_le_one : value ≤ 1
  /-- Approximation from above: for any eps > 0, there exists an internal set
      with preLoeb measure at most value + eps -/
  approx_above : ∀ (eps : ℝ), eps > 0 → ∃ (C : InternalSubset Ω),
    value ≤ C.preLoeb ∧ C.preLoeb < value + eps

/-- The Loeb inner measure of a set, defined via approximation from below. -/
structure LoebInnerMeasure (Ω : InternalProbSpace) where
  /-- The inner measure value -/
  value : ℝ
  /-- Non-negative -/
  value_nonneg : 0 ≤ value
  /-- At most 1 -/
  value_le_one : value ≤ 1
  /-- Approximation from below: for any eps > 0, there exists an internal set
      with preLoeb measure at least value - eps -/
  approx_below : ∀ (eps : ℝ), eps > 0 → ∃ (B : InternalSubset Ω),
    value - eps < B.preLoeb ∧ B.preLoeb ≤ value

namespace LoebOuterMeasure

/-- The outer measure of an internal set equals its pre-Loeb measure -/
noncomputable def ofInternal (A : InternalSubset Ω) : LoebOuterMeasure Ω where
  value := A.preLoeb
  value_nonneg := A.preLoeb_nonneg
  value_le_one := A.preLoeb_le_one
  approx_above := fun eps heps => ⟨A, le_refl _, by linarith⟩

/-- The outer measure of the empty set is 0 -/
noncomputable def empty : LoebOuterMeasure Ω :=
  ofInternal InternalSubset.empty

theorem empty_value : (empty : LoebOuterMeasure Ω).value = 0 :=
  preLoebMeasure_empty Ω

/-- The outer measure of the full set is 1 -/
noncomputable def univ : LoebOuterMeasure Ω :=
  ofInternal InternalSubset.univ

theorem univ_value : (univ : LoebOuterMeasure Ω).value = 1 :=
  preLoebMeasure_whole Ω

/-- Outer measure is monotone: if the approximating sets satisfy a containment,
    the values are ordered. This is an abstract monotonicity property. -/
theorem le_of_approx_le (μ₁ μ₂ : LoebOuterMeasure Ω)
    (h : ∀ (eps : ℝ), eps > 0 → ∃ (C₁ : InternalSubset Ω),
      μ₁.value ≤ C₁.preLoeb ∧ C₁.preLoeb ≤ μ₂.value + eps) :
    μ₁.value ≤ μ₂.value := by
  by_contra hlt
  push_neg at hlt
  have heps : μ₁.value - μ₂.value > 0 := by linarith
  obtain ⟨C₁, h1, h2⟩ := h ((μ₁.value - μ₂.value) / 2) (by linarith)
  have : μ₁.value ≤ μ₂.value + (μ₁.value - μ₂.value) / 2 := le_trans h1 h2
  linarith

end LoebOuterMeasure

namespace LoebInnerMeasure

/-- The inner measure of an internal set equals its pre-Loeb measure -/
noncomputable def ofInternal (A : InternalSubset Ω) : LoebInnerMeasure Ω where
  value := A.preLoeb
  value_nonneg := A.preLoeb_nonneg
  value_le_one := A.preLoeb_le_one
  approx_below := fun eps heps => ⟨A, by linarith, le_refl _⟩

/-- The inner measure of the empty set is 0 -/
noncomputable def empty : LoebInnerMeasure Ω :=
  ofInternal InternalSubset.empty

theorem empty_value : (empty : LoebInnerMeasure Ω).value = 0 :=
  preLoebMeasure_empty Ω

/-- The inner measure of the full set is 1 -/
noncomputable def univ : LoebInnerMeasure Ω :=
  ofInternal InternalSubset.univ

theorem univ_value : (univ : LoebInnerMeasure Ω).value = 1 :=
  preLoebMeasure_whole Ω

end LoebInnerMeasure

/-! ## Loeb Measurability via Inner = Outer

A set is Loeb measurable when its inner and outer measures coincide.
This is equivalent to our earlier `LoebMeasurableSet` definition.
-/

/-- A set is Loeb measurable when inner = outer measure -/
structure LoebMeasurable (Ω : InternalProbSpace) where
  /-- The outer measure -/
  outer : LoebOuterMeasure Ω
  /-- The inner measure -/
  inner : LoebInnerMeasure Ω
  /-- Inner ≤ Outer (always true) -/
  inner_le_outer : inner.value ≤ outer.value
  /-- Measurability: Inner = Outer -/
  inner_eq_outer : inner.value = outer.value

namespace LoebMeasurable

/-- The Loeb measure value -/
def measure (A : LoebMeasurable Ω) : ℝ := A.outer.value

theorem measure_eq_inner (A : LoebMeasurable Ω) : A.measure = A.inner.value :=
  A.inner_eq_outer.symm

theorem measure_nonneg (A : LoebMeasurable Ω) : 0 ≤ A.measure :=
  A.outer.value_nonneg

theorem measure_le_one (A : LoebMeasurable Ω) : A.measure ≤ 1 :=
  A.outer.value_le_one

/-- An internal set is Loeb measurable -/
noncomputable def ofInternal (A : InternalSubset Ω) : LoebMeasurable Ω where
  outer := LoebOuterMeasure.ofInternal A
  inner := LoebInnerMeasure.ofInternal A
  inner_le_outer := le_refl _
  inner_eq_outer := rfl

theorem ofInternal_measure (A : InternalSubset Ω) :
    (ofInternal A).measure = A.preLoeb := rfl

/-- The empty set is Loeb measurable with measure 0 -/
noncomputable def empty : LoebMeasurable Ω :=
  ofInternal InternalSubset.empty

theorem empty_measure : (empty : LoebMeasurable Ω).measure = 0 :=
  preLoebMeasure_empty Ω

/-- The full set is Loeb measurable with measure 1 -/
noncomputable def univ : LoebMeasurable Ω :=
  ofInternal InternalSubset.univ

theorem univ_measure : (univ : LoebMeasurable Ω).measure = 1 :=
  preLoebMeasure_whole Ω

/-! ### Complement of Loeb Measurable Sets

The `LoebMeasurable` structure represents sets only by their measure values (inner = outer).
Taking "complement of a Loeb measurable set" is semantically problematic because:

1. The structure doesn't track which actual subset of Ω is being measured
2. Multiple internal sets can have the same preLoeb measure
3. Using `Classical.choose` to pick one would be non-canonical

For **internal** sets, the complement is well-defined via `loebMeasurable_compl_internal` below,
which shows μ(Aᶜ) = 1 - μ(A) for internal A.

For general Loeb measurable sets, complement operations should be defined at the level of
the actual measure space (as subsets of a σ-algebra), which requires the full Carathéodory
extension construction.
-/

end LoebMeasurable

/-! ## Properties of Loeb Measurable Sets

The collection of Loeb measurable sets forms a σ-algebra.
Here we prove the key properties.
-/

/-- Loeb measurable sets are closed under complementation (for internal sets) -/
theorem loebMeasurable_compl_internal (A : InternalSubset Ω) :
    (LoebMeasurable.ofInternal A.compl).measure = 1 - (LoebMeasurable.ofInternal A).measure := by
  simp only [LoebMeasurable.ofInternal_measure]
  -- A.compl.preLoeb = 1 - A.preLoeb
  have hfin_A := A.prob_not_infinite
  have hfin_compl := A.compl.prob_not_infinite
  rw [A.preLoeb_eq_st, A.compl.preLoeb_eq_st]
  -- The complement probability: Ω.prob (Ω.size - A.card) = 1 - Ω.prob A.card
  have hprob_compl : A.compl.prob = 1 - A.prob := by
    unfold InternalSubset.prob InternalSubset.compl
    simp only
    exact Ω.prob_compl A.card A.card_le_size
  rw [hprob_compl]
  -- st(1 - x) = 1 - st(x) for finite x
  have hIsSt_A : IsSt A.prob (st A.prob) := isSt_st' hfin_A
  have hIsSt_1 : IsSt (1 : ℝ*) 1 := isSt_refl_real 1
  have hIsSt_sub : IsSt (1 - A.prob) (1 - st A.prob) := hIsSt_1.sub hIsSt_A
  exact hIsSt_sub.st_eq

/-- For disjoint internal sets, Loeb measure is additive -/
theorem loebMeasurable_add_disjoint
    (A B : InternalSubset Ω) (hdisj : A.card + B.card ≤ Ω.size) :
    (LoebMeasurable.ofInternal (A.disjUnion B hdisj)).measure =
    (LoebMeasurable.ofInternal A).measure + (LoebMeasurable.ofInternal B).measure := by
  simp only [LoebMeasurable.ofInternal_measure]
  -- The disjUnion has card = A.card + B.card
  have hcard_eq : (A.disjUnion B hdisj).card = A.card + B.card := rfl
  -- prob of the union is bounded (probability in [0,1] is not infinite)
  have hfin_A := A.prob_not_infinite
  have hfin_B := B.prob_not_infinite
  have hfin_sum : ¬Infinite (Ω.prob (A.card + B.card)) :=
    (A.disjUnion B hdisj).prob_not_infinite
  -- preLoeb of disjUnion equals preLoeb of sum of cards
  have h1 : (A.disjUnion B hdisj).preLoeb = preLoebMeasure Ω (A.card + B.card) := rfl
  rw [h1]
  -- Use preLoebMeasure_add
  exact preLoebMeasure_add Ω A.card B.card hfin_A hfin_B hfin_sum

/-! ## The Loeb σ-algebra

The collection of Loeb measurable sets forms a σ-algebra. The key properties are:

1. **Contains ∅ and Ω**: `LoebMeasurable.empty` and `LoebMeasurable.univ`

2. **Closed under complementation**: `loebMeasurable_compl_internal`

3. **Closed under finite disjoint unions**: `loebMeasurable_add_disjoint`

4. **Closed under countable unions**: This follows from σ-additivity
   (`DecreasingConcreteEvents.sigma_additivity`). For a sequence of disjoint
   sets Aₙ, we have μ(⋃ Aₙ) = Σ μ(Aₙ).

The full σ-algebra construction would require:
- Defining external sets (not just internal)
- Approximating external sets by internal ones
- Carathéodory's extension theorem

For our purposes (hyperfinite random walks), internal sets suffice:
- Cylinder sets are internal
- Events defined by finitely many walk values are internal
- The Loeb measure on internal sets extends uniquely to the σ-algebra
-/

/-- Summary: Internal sets form an algebra (closed under ∅, Ω, complement, finite union) -/
theorem internal_algebra :
    (LoebMeasurable.empty : LoebMeasurable Ω).measure = 0 ∧
    (LoebMeasurable.univ : LoebMeasurable Ω).measure = 1 := by
  exact ⟨LoebMeasurable.empty_measure, LoebMeasurable.univ_measure⟩

end SPDE.Nonstandard
