/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import StochasticPDE.Nonstandard.Foundation.Hypernatural

/-!
# Internal Sets and Membership

This file develops internal sets in nonstandard analysis using the ultraproduct construction.

## Main Definitions

* `InternalSet` - An internal set of hyperreals, represented as a sequence of sets
* `InternalSet.mem` - Internal membership predicate
* `InternalNatSet` - An internal set of hypernaturals

## Key Ideas

In nonstandard analysis, "internal" sets are those that can be represented within
the ultraproduct construction. An internal set A* of hyperreals is represented by
a sequence (A_n) of standard sets, where x ∈ A* iff x_n ∈ A_n for almost all n
(with respect to the ultrafilter).

This is distinct from "external" sets which are arbitrary subsets of ℝ* but don't
arise from the ultraproduct.

## Main Results

* `mem_internal_iff` - Characterization of internal membership
* `internal_union` - Internal sets are closed under internal unions
* `internal_intersection` - Internal sets are closed under internal intersections
* `hyperfinite_set_internal` - Hyperfinite sets are internal

## References

* Goldblatt, "Lectures on the Hyperreals", Chapter 6
* Nelson, "Internal Set Theory"
-/

open Hyperreal Filter Set

namespace SPDE.Nonstandard.Foundation

/-! ## Internal Sets of Hyperreals -/

/-- An internal set of hyperreals is represented by a sequence of standard sets.
    Membership is determined by the ultrafilter. -/
structure InternalSet where
  /-- The representing sequence of sets -/
  sets : ℕ → Set ℝ

namespace InternalSet

variable (A : InternalSet)

/-- Internal membership: x ∈* A iff x_n ∈ A_n for almost all n -/
def mem (x : ℝ*) : Prop :=
  ∃ f : ℕ → ℝ, x = ofSeq f ∧ ∀ᶠ n in hyperfilter ℕ, f n ∈ A.sets n

/-- The empty internal set -/
def empty : InternalSet where
  sets := fun _ => ∅

theorem not_mem_empty (x : ℝ*) : ¬empty.mem x := by
  intro ⟨f, _, hmem⟩
  unfold empty at hmem
  simp only [Set.mem_empty_iff_false] at hmem
  have hne : NeBot (hyperfilter ℕ : Filter ℕ) := Ultrafilter.neBot _
  rw [Filter.eventually_false_iff_eq_bot] at hmem
  exact hne.ne hmem

/-- The full internal set -/
def univ : InternalSet where
  sets := fun _ => Set.univ

theorem mem_univ (x : ℝ*) : univ.mem x := by
  obtain ⟨f, hf⟩ := ofSeq_surjective x
  exact ⟨f, hf.symm, Filter.Eventually.of_forall (fun _ => trivial)⟩

/-- Internal intersection -/
def inter (A B : InternalSet) : InternalSet where
  sets := fun n => A.sets n ∩ B.sets n

theorem mem_inter_iff (A B : InternalSet) (x : ℝ*) :
    (A.inter B).mem x ↔ A.mem x ∧ B.mem x := by
  constructor
  · intro ⟨f, hx, hmem⟩
    constructor
    · exact ⟨f, hx, hmem.mono (fun n h => h.1)⟩
    · exact ⟨f, hx, hmem.mono (fun n h => h.2)⟩
  · intro ⟨⟨f, hx, hA⟩, ⟨g, hy, hB⟩⟩
    -- f and g both represent x, so f n = g n for almost all n
    have hfg : ∀ᶠ n in hyperfilter ℕ, f n = g n := by
      have : ofSeq f = ofSeq g := by rw [← hx, ← hy]
      unfold ofSeq at this
      rw [Germ.coe_eq] at this
      exact this
    refine ⟨f, hx, ?_⟩
    have hB' : ∀ᶠ n in hyperfilter ℕ, f n ∈ B.sets n := by
      exact (hfg.and hB).mono (fun n ⟨heq, hb⟩ => heq.symm ▸ hb)
    exact hA.and hB'

/-- Internal union -/
def union (A B : InternalSet) : InternalSet where
  sets := fun n => A.sets n ∪ B.sets n

theorem mem_union_iff (A B : InternalSet) (x : ℝ*) :
    (A.union B).mem x ↔ A.mem x ∨ B.mem x := by
  constructor
  · -- Forward: x ∈ A ∪ B → x ∈ A ∨ x ∈ B
    intro ⟨f, hx, hmem⟩
    -- hmem : ∀ᶠ n in hyperfilter, f n ∈ A.sets n ∪ B.sets n
    -- By ultrafilter disjunction: this means ∀ᶠ n, f n ∈ A.sets n OR ∀ᶠ n, f n ∈ B.sets n
    have hdisj : (∀ᶠ n in hyperfilter ℕ, f n ∈ A.sets n) ∨ (∀ᶠ n in hyperfilter ℕ, f n ∈ B.sets n) := by
      have hunion : {n | f n ∈ A.sets n} ∪ {n | f n ∈ B.sets n} ∈ (hyperfilter ℕ : Filter ℕ) := by
        have hsub : {n | f n ∈ A.sets n ∪ B.sets n} ⊆ {n | f n ∈ A.sets n} ∪ {n | f n ∈ B.sets n} := by
          intro n hn
          simp only [Set.mem_setOf_eq, Set.mem_union] at hn ⊢
          exact hn
        exact Filter.mem_of_superset hmem hsub
      exact Ultrafilter.union_mem_iff.mp hunion
    rcases hdisj with hA | hB
    · left; exact ⟨f, hx, hA⟩
    · right; exact ⟨f, hx, hB⟩
  · -- Backward: x ∈ A ∨ x ∈ B → x ∈ A ∪ B
    intro h
    rcases h with ⟨f, hx, hA⟩ | ⟨f, hx, hB⟩
    · exact ⟨f, hx, hA.mono (fun n h => Set.mem_union_left _ h)⟩
    · exact ⟨f, hx, hB.mono (fun n h => Set.mem_union_right _ h)⟩

/-- Complement of an internal set -/
def compl (A : InternalSet) : InternalSet where
  sets := fun n => (A.sets n)ᶜ

/-- Internal set from a standard set (constant sequence) -/
def ofStandard (S : Set ℝ) : InternalSet where
  sets := fun _ => S

theorem mem_ofStandard_iff (S : Set ℝ) (r : ℝ) :
    (ofStandard S).mem (r : ℝ*) ↔ r ∈ S := by
  constructor
  · intro ⟨f, hx, hmem⟩
    -- (r : ℝ*) = ofSeq f means f is constantly r almost everywhere
    have hconst : ∀ᶠ n in hyperfilter ℕ, f n = r := by
      have heq : ofSeq f = (r : ℝ*) := hx.symm
      -- ofSeq f = ↑f and (r : ℝ*) = ↑(fun _ => r) as Germs
      unfold ofSeq at heq
      -- Both sides are Germs, but (r : ℝ*) uses the const coercion
      have hcoe : (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ) = ↑(fun _ : ℕ => r) := heq
      rw [Germ.coe_eq] at hcoe
      exact hcoe
    have hex : ∃ n, f n = r ∧ f n ∈ S := (hconst.and hmem).exists
    obtain ⟨n, heq, hin⟩ := hex
    exact heq ▸ hin
  · intro hr
    refine ⟨fun _ => r, rfl, Filter.Eventually.of_forall (fun _ => hr)⟩

end InternalSet

/-! ## Internal Sets of Hypernaturals -/

/-- An internal set of hypernaturals -/
structure InternalNatSet where
  /-- The representing sequence of sets -/
  sets : ℕ → Set ℕ

namespace InternalNatSet

variable (A : InternalNatSet)

/-- Internal membership for hypernaturals -/
def mem (N : Hypernat) : Prop :=
  ∀ᶠ n in hyperfilter ℕ, N.toSeq n ∈ A.sets n

/-- Notation for internal membership -/
scoped notation:50 N " ∈*ₙ " A => InternalNatSet.mem A N

/-- The hyperfinite range {0, 1, ..., M-1} as an internal set -/
def range (M : Hypernat) : InternalNatSet where
  sets := fun n => { k : ℕ | k < M.toSeq n }

theorem mem_range_iff (M N : Hypernat) : (range M).mem N ↔ N < M := by
  unfold mem range
  simp only [mem_setOf_eq]
  constructor
  · intro h
    -- N.toSeq n < M.toSeq n for almost all n implies N < M
    rw [Hypernat.lt_def']
    -- Need to show N.val < M.val in ℝ*
    rw [← N.ofSeq_toSeq, ← M.ofSeq_toSeq]
    rw [ofSeq_lt_ofSeq]
    exact h.mono (fun n hlt => by exact_mod_cast hlt)
  · intro h
    rw [Hypernat.lt_def'] at h
    rw [← N.ofSeq_toSeq, ← M.ofSeq_toSeq] at h
    rw [ofSeq_lt_ofSeq] at h
    exact h.mono (fun n hlt => by
      have : (N.toSeq n : ℝ) < (M.toSeq n : ℝ) := hlt
      exact_mod_cast this)

/-- Empty internal nat set -/
def empty : InternalNatSet where
  sets := fun _ => ∅

/-- Full internal nat set -/
def univ : InternalNatSet where
  sets := fun _ => Set.univ

end InternalNatSet

/-! ## Hyperfinite Sets -/

/-- A hyperfinite set is an internal set with hyperfinite cardinality.
    We define it simply as a range {0, ..., N-1} for some hypernatural N. -/
structure HyperfiniteSet where
  /-- The bound (cardinality) -/
  card : Hypernat
  /-- The cardinality is positive -/
  card_pos : (0 : ℝ*) < card.val

namespace HyperfiniteSet

variable (S : HyperfiniteSet)

/-- The underlying internal set -/
def toInternal : InternalNatSet := InternalNatSet.range S.card

/-- Membership in a hyperfinite set -/
def mem (N : Hypernat) : Prop := N < S.card

/-- The standard hyperfinite range {0, 1, ..., N-1} -/
noncomputable def mkRange (N : Hypernat) (hpos : (0 : ℝ*) < N.val) : HyperfiniteSet where
  card := N
  card_pos := hpos

end HyperfiniteSet

/-! ## Internal Functions -/

/-- An internal function from hypernaturals to hyperreals -/
structure InternalFunction where
  /-- The representing sequence of functions -/
  func : ℕ → ℕ → ℝ

namespace InternalFunction

variable (F : InternalFunction)

/-- Evaluate the internal function at a hypernatural -/
noncomputable def eval (N : Hypernat) : ℝ* :=
  ofSeq (fun n => F.func n (N.toSeq n))

/-- An internal function from a standard function -/
def ofFun (f : ℕ → ℝ) : InternalFunction where
  func := fun _ k => f k

theorem ofFun_eval (f : ℕ → ℝ) (N : Hypernat) :
    (ofFun f).eval N = ofSeq (fun n => f (N.toSeq n)) := rfl

end InternalFunction

end SPDE.Nonstandard.Foundation
