/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.InternalProbSpace
import StochasticPDE.Nonstandard.Foundation.InternalMembership
import StochasticPDE.Nonstandard.Foundation.Saturation

/-!
# σ-Additivity for Loeb Measure

This file proves σ-additivity for decreasing families of internal events
using the ℵ₁-saturation theorem.

## Main Definitions

* `InternalSubset` - A subset of an internal probability space
* `InternalEvent` - An internal set with cardinality bounds
* `ConcreteInternalEvent` - Internal event with level-wise nonemptiness
* `DecreasingConcreteEvents` - Decreasing sequence of concrete events

## Main Results

* `sigma_additivity` - Decreasing events with empty intersection have measure → 0

## References

* Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
-/

open Hyperreal Filter

namespace SPDE.Nonstandard

/-! ## σ-Additivity via Saturation

The key to proving σ-additivity of Loeb measure is the following lemma:
For a decreasing sequence of internal sets Aₙ with μ(Aₙ) ≥ ε > 0 for all n,
the intersection ⋂ₙ Aₙ is nonempty (by saturation).

Contrapositive: If ⋂ₙ Aₙ = ∅, then μ(Aₙ) → 0.

This gives σ-additivity from above (continuity at ∅), which together with
finite additivity implies full σ-additivity.

The saturation theorem is in `Foundation.Saturation.countable_saturation_standard`.
-/

/-- A decreasing sequence of internal sets (for the saturation argument).
    This represents Aₙ ⊇ Aₙ₊₁ for all n. -/
structure DecreasingInternalFamily where
  /-- The sequence of internal sets -/
  sets : ℕ → Foundation.InternalSet
  /-- Decreasing: Aₙ ⊇ Aₙ₊₁ at each level -/
  decreasing : ∀ (n m k : ℕ), n ≤ m → (sets m).sets k ⊆ (sets n).sets k

/-- Convert a decreasing family to a CountableInternalFamily for saturation. -/
def DecreasingInternalFamily.toCountableFamily (F : DecreasingInternalFamily) :
    Foundation.CountableInternalFamily where
  family := F.sets

/-- The key lemma for σ-additivity: if all sets in a decreasing family are
    "nonempty at level n" (for the saturation argument), then the intersection
    is nonempty.

    This follows from `countable_saturation_standard` applied to the family.
    The decreasing property ensures that level-n witnesses transfer correctly. -/
theorem decreasing_family_saturation (F : DecreasingInternalFamily)
    (hFIP : F.toCountableFamily.HasStandardFIP) :
    ∃ x : ℝ*, ∀ n : ℕ, (F.sets n).mem x :=
  Foundation.countable_saturation_standard F.toCountableFamily hFIP

/-! ### Application to Loeb Measure σ-Additivity

For the actual σ-additivity proof, we would need to:
1. Define internal sets Aₙ with μ(Aₙ) ≥ ε
2. Show these form a family with HasStandardFIP
3. Apply saturation to get a point in ⋂ Aₙ
4. Derive contradiction if ⋂ Aₙ was assumed empty

The details depend on how internal sets are represented. The saturation
infrastructure is ready; the remaining work is in the measure-theoretic setup.
-/

variable {Ω : InternalProbSpace}

/-! ## Internal Subsets -/

/-- An internal subset of a hyperfinite probability space.
    Represented by its hyperreal cardinality. -/
structure InternalSubset (Ω : InternalProbSpace) where
  /-- The cardinality as a hyperreal -/
  card : ℝ*
  /-- Cardinality is non-negative -/
  card_nonneg : 0 ≤ card
  /-- Cardinality is at most the size of Ω -/
  card_le_size : card ≤ Ω.size

namespace InternalSubset

/-- The internal probability of a subset -/
noncomputable def prob (A : InternalSubset Ω) : ℝ* := Ω.prob A.card

/-- The pre-Loeb measure of a subset -/
noncomputable def preLoeb (A : InternalSubset Ω) : ℝ :=
  preLoebMeasure Ω A.card

/-- The empty subset -/
noncomputable def empty : InternalSubset Ω where
  card := 0
  card_nonneg := le_refl 0
  card_le_size := le_of_lt Ω.size_pos

/-- The full subset -/
noncomputable def univ : InternalSubset Ω where
  card := Ω.size
  card_nonneg := le_of_lt Ω.size_pos
  card_le_size := le_refl Ω.size

/-- Complement of a subset -/
noncomputable def compl (A : InternalSubset Ω) : InternalSubset Ω where
  card := Ω.size - A.card
  card_nonneg := sub_nonneg.mpr A.card_le_size
  card_le_size := by linarith [A.card_nonneg]

/-- Disjoint union of two subsets -/
noncomputable def disjUnion (A B : InternalSubset Ω) (hdisj : A.card + B.card ≤ Ω.size) :
    InternalSubset Ω where
  card := A.card + B.card
  card_nonneg := add_nonneg A.card_nonneg B.card_nonneg
  card_le_size := hdisj

theorem empty_prob : (empty : InternalSubset Ω).prob = 0 := Ω.prob_empty

theorem univ_prob : (univ : InternalSubset Ω).prob = 1 := Ω.prob_whole

theorem prob_nonneg (A : InternalSubset Ω) : 0 ≤ A.prob :=
  Ω.prob_nonneg A.card A.card_nonneg

theorem prob_le_one (A : InternalSubset Ω) : A.prob ≤ 1 :=
  Ω.prob_le_one A.card A.card_le_size

/-- The probability is not infinite (bounded in [0,1]) -/
theorem prob_not_infinite (A : InternalSubset Ω) : ¬Infinite A.prob := by
  intro hinf
  cases hinf with
  | inl hpos =>
    have h1 : (1 : ℝ*) < A.prob := hpos 1
    exact absurd A.prob_le_one (not_le.mpr h1)
  | inr hneg =>
    have h0 : A.prob < (0 : ℝ*) := hneg 0
    exact absurd A.prob_nonneg (not_le.mpr h0)

/-- Pre-Loeb measure equals st of probability -/
theorem preLoeb_eq_st (A : InternalSubset Ω) :
    A.preLoeb = st A.prob :=
  preLoebMeasure_eq_st Ω A.card A.prob_not_infinite

theorem preLoeb_nonneg (A : InternalSubset Ω) : 0 ≤ A.preLoeb :=
  preLoebMeasure_nonneg Ω A.card A.card_nonneg A.prob_not_infinite

theorem preLoeb_le_one (A : InternalSubset Ω) : A.preLoeb ≤ 1 :=
  preLoebMeasure_le_one Ω A.card A.card_le_size A.prob_not_infinite

end InternalSubset

/-! ## Internal Events -/

/-- An internal event: an internal set with cardinality bounds.
    This pairs the underlying set structure (for saturation) with
    the cardinality (for probability). -/
structure InternalEvent (Ω : InternalProbSpace) where
  /-- The underlying internal set -/
  set : Foundation.InternalSet
  /-- The cardinality as a hyperreal -/
  card : ℝ*
  /-- Cardinality is non-negative -/
  card_nonneg : 0 ≤ card
  /-- Cardinality is at most the size of Ω -/
  card_le_size : card ≤ Ω.size
  /-- Consistency: positive cardinality implies nonempty at almost all levels -/
  card_nonempty : 0 < card → ∀ᶠ n in hyperfilter ℕ, (set.sets n).Nonempty

/-- A stronger version with level-wise nonemptiness. -/
structure ConcreteInternalEvent (Ω : InternalProbSpace) extends InternalEvent Ω where
  /-- Positive cardinality implies nonempty at every level -/
  card_nonempty_all : 0 < card → ∀ n, (set.sets n).Nonempty

namespace InternalEvent

/-- Convert to an InternalSubset -/
def toSubset (E : InternalEvent Ω) : InternalSubset Ω where
  card := E.card
  card_nonneg := E.card_nonneg
  card_le_size := E.card_le_size

/-- The internal probability -/
noncomputable def prob (E : InternalEvent Ω) : ℝ* := Ω.prob E.card

/-- The pre-Loeb measure -/
noncomputable def preLoeb (E : InternalEvent Ω) : ℝ :=
  preLoebMeasure Ω E.card

theorem prob_nonneg (E : InternalEvent Ω) : 0 ≤ E.prob :=
  Ω.prob_nonneg E.card E.card_nonneg

theorem prob_le_one (E : InternalEvent Ω) : E.prob ≤ 1 :=
  Ω.prob_le_one E.card E.card_le_size

theorem prob_not_infinite (E : InternalEvent Ω) : ¬Infinite E.prob := by
  intro hinf
  cases hinf with
  | inl hpos =>
    have h1 : (1 : ℝ*) < E.prob := hpos 1
    exact absurd E.prob_le_one (not_le.mpr h1)
  | inr hneg =>
    have h0 : E.prob < (0 : ℝ*) := hneg 0
    exact absurd E.prob_nonneg (not_le.mpr h0)

theorem preLoeb_eq_st (E : InternalEvent Ω) : E.preLoeb = st E.prob :=
  preLoebMeasure_eq_st Ω E.card E.prob_not_infinite

theorem preLoeb_nonneg (E : InternalEvent Ω) : 0 ≤ E.preLoeb :=
  preLoebMeasure_nonneg Ω E.card E.card_nonneg E.prob_not_infinite

theorem preLoeb_le_one (E : InternalEvent Ω) : E.preLoeb ≤ 1 :=
  preLoebMeasure_le_one Ω E.card E.card_le_size E.prob_not_infinite

/-- If pre-Loeb measure is positive, the internal probability is not infinitesimal -/
theorem prob_not_infinitesimal_of_preLoeb_pos (E : InternalEvent Ω) (hpos : 0 < E.preLoeb) :
    ¬Infinitesimal E.prob := by
  intro hinf
  have hst : st E.prob = 0 := hinf.st_eq
  rw [← E.preLoeb_eq_st] at hst
  linarith

/-- If pre-Loeb measure is ≥ eps > 0, then internal probability is > eps/2 -/
theorem prob_ge_of_preLoeb_ge (E : InternalEvent Ω) (eps : ℝ) (heps : 0 < eps)
    (hge : eps ≤ E.preLoeb) : (eps / 2 : ℝ*) < E.prob := by
  have hst : st E.prob ≥ eps := by rw [← E.preLoeb_eq_st]; exact hge
  have hfin : ¬Infinite E.prob := E.prob_not_infinite
  have hisSt : IsSt E.prob (st E.prob) := isSt_st' hfin
  by_contra hlt
  push_neg at hlt
  have hst_le : st E.prob ≤ eps / 2 := by
    have h1 : st E.prob ≤ st (eps / 2 : ℝ*) :=
      st_le_of_le hfin (not_infinite_real (eps / 2)) hlt
    have h2 : st (eps / 2 : ℝ*) = eps / 2 := st_id_real (eps / 2)
    rw [h2] at h1
    exact h1
  linarith

end InternalEvent

/-! ## Decreasing Families -/

/-- A decreasing sequence of internal events -/
structure DecreasingInternalEvents (Ω : InternalProbSpace) where
  events : ℕ → InternalEvent Ω
  decreasing : ∀ (n k : ℕ), (events (n + 1)).set.sets k ⊆ (events n).set.sets k
  card_decreasing : ∀ n, (events (n + 1)).card ≤ (events n).card

namespace DecreasingInternalEvents

def toCountableFamily (F : DecreasingInternalEvents Ω) :
    Foundation.CountableInternalFamily where
  family := fun n => (F.events n).set

theorem preLoeb_decreasing (F : DecreasingInternalEvents Ω) :
    ∀ n, (F.events (n + 1)).preLoeb ≤ (F.events n).preLoeb := by
  intro n
  have hcard := F.card_decreasing n
  have hprob : (F.events (n + 1)).prob ≤ (F.events n).prob :=
    Ω.prob_mono _ _ hcard
  have hfin1 := (F.events (n + 1)).prob_not_infinite
  have hfin2 := (F.events n).prob_not_infinite
  rw [(F.events (n + 1)).preLoeb_eq_st, (F.events n).preLoeb_eq_st]
  exact st_le_of_le hfin1 hfin2 hprob

theorem preLoeb_tendsto (F : DecreasingInternalEvents Ω) :
    ∃ L, Tendsto (fun n => (F.events n).preLoeb) atTop (nhds L) := by
  have hbdd : BddBelow (Set.range (fun n => (F.events n).preLoeb)) := by
    use 0
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact (F.events n).preLoeb_nonneg
  have hmono : Antitone (fun n => (F.events n).preLoeb) := by
    intro m n hmn
    induction hmn with
    | refl => exact le_refl _
    | step _ ih => exact le_trans (F.preLoeb_decreasing _) ih
  exact ⟨_, tendsto_atTop_ciInf hmono hbdd⟩

end DecreasingInternalEvents

/-- A decreasing sequence of concrete internal events -/
structure DecreasingConcreteEvents (Ω : InternalProbSpace) where
  events : ℕ → ConcreteInternalEvent Ω
  decreasing : ∀ (n k : ℕ), (events (n + 1)).set.sets k ⊆ (events n).set.sets k
  card_decreasing : ∀ n, (events (n + 1)).card ≤ (events n).card

namespace DecreasingConcreteEvents

def toCountableFamily (F : DecreasingConcreteEvents Ω) :
    Foundation.CountableInternalFamily where
  family := fun n => (F.events n).set

theorem decreasing_trans (F : DecreasingConcreteEvents Ω) (m n k : ℕ) (hmn : m ≤ n) :
    (F.events n).set.sets k ⊆ (F.events m).set.sets k := by
  induction hmn with
  | refl => exact Set.Subset.refl _
  | step _ ih => exact Set.Subset.trans (F.decreasing _ k) ih

/-- Key lemma: if all pre-Loeb measures are ≥ eps > 0, the family has HasStandardFIP -/
theorem hasStandardFIP_of_preLoeb_bounded (F : DecreasingConcreteEvents Ω)
    (eps : ℝ) (heps : 0 < eps) (hbound : ∀ n, eps ≤ (F.events n).preLoeb) :
    F.toCountableFamily.HasStandardFIP := by
  intro n
  have hprob_pos : (eps / 2 : ℝ*) < (F.events n).prob :=
    (F.events n).toInternalEvent.prob_ge_of_preLoeb_ge eps heps (hbound n)
  have hcard_pos : 0 < (F.events n).card := by
    have heps2 : (0 : ℝ*) < (eps / 2 : ℝ*) := by
      have h : (0 : ℝ) < eps / 2 := by linarith
      exact_mod_cast h
    have hprob : 0 < (F.events n).prob := lt_trans heps2 hprob_pos
    unfold InternalEvent.prob InternalProbSpace.prob at hprob
    have hsize_pos : 0 < Ω.size := Ω.size_pos
    have hpos : 0 < (F.events n).card / Ω.size := hprob
    exact (div_pos_iff_of_pos_right hsize_pos).mp hpos
  have hnonempty_n : ((F.events n).set.sets n).Nonempty :=
    (F.events n).card_nonempty_all hcard_pos n
  obtain ⟨x, hx⟩ := hnonempty_n
  use x
  intro i hi
  exact F.decreasing_trans i n n hi hx

def toInternalEvents (F : DecreasingConcreteEvents Ω) : DecreasingInternalEvents Ω where
  events := fun n => (F.events n).toInternalEvent
  decreasing := F.decreasing
  card_decreasing := F.card_decreasing

theorem preLoeb_tendsto (F : DecreasingConcreteEvents Ω) :
    ∃ L, Tendsto (fun n => (F.events n).preLoeb) atTop (nhds L) :=
  F.toInternalEvents.preLoeb_tendsto

/-- The σ-additivity theorem for concrete internal events -/
theorem sigma_additivity (F : DecreasingConcreteEvents Ω)
    (hempty : ¬∃ x : ℝ*, ∀ n, (F.events n).set.mem x) :
    Tendsto (fun n => (F.events n).preLoeb) atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := F.preLoeb_tendsto
  have hL_ge : 0 ≤ L := by
    have hge : ∀ n, 0 ≤ (F.events n).preLoeb := fun n => (F.events n).preLoeb_nonneg
    exact ge_of_tendsto hL (Eventually.of_forall hge)
  by_cases hL_zero : L = 0
  · rw [hL_zero] at hL; exact hL
  have hL_pos : 0 < L := lt_of_le_of_ne hL_ge (Ne.symm hL_zero)
  have hbound : ∃ N, ∀ n ≥ N, L / 2 ≤ (F.events n).preLoeb := by
    rw [Metric.tendsto_atTop] at hL
    obtain ⟨N, hN⟩ := hL (L / 2) (by linarith)
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq] at hN
    have habs : |((F.events n).preLoeb) - L| < L / 2 := hN
    have h1 : -(L/2) < (F.events n).preLoeb - L := neg_lt_of_abs_lt habs
    linarith
  obtain ⟨N, hN⟩ := hbound
  have hbound_all : ∀ n, L / 2 ≤ (F.events (N + n)).preLoeb := by
    intro n; exact hN (N + n) (Nat.le_add_right N n)
  let F' : DecreasingConcreteEvents Ω := {
    events := fun n => F.events (N + n)
    decreasing := fun n k => by
      have h : N + (n + 1) = N + n + 1 := by ring
      rw [h]; exact F.decreasing (N + n) k
    card_decreasing := fun n => by
      have h : N + (n + 1) = N + n + 1 := by ring
      rw [h]; exact F.card_decreasing (N + n)
  }
  have hFIP : F'.toCountableFamily.HasStandardFIP :=
    F'.hasStandardFIP_of_preLoeb_bounded (L / 2) (by linarith) hbound_all
  obtain ⟨x, hx⟩ := Foundation.countable_saturation_standard F'.toCountableFamily hFIP
  have hx_all : ∀ n, (F.events (N + n)).set.mem x := fun n => hx n
  have hx_all' : ∀ n, (F.events n).set.mem x := by
    intro n
    by_cases h : N ≤ n
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
      exact hx_all k
    · push_neg at h
      obtain ⟨f, hf_eq, hf_mem⟩ := hx_all 0
      simp only [Nat.add_zero] at hf_eq hf_mem
      refine ⟨f, hf_eq, ?_⟩
      apply hf_mem.mono
      intro k hk
      exact F.decreasing_trans n N k (Nat.le_of_lt h) hk
  exfalso
  exact hempty ⟨x, hx_all'⟩

end DecreasingConcreteEvents

end SPDE.Nonstandard
