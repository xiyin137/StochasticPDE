/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal

/-!
# Internal Sets in Nonstandard Analysis

This file develops the theory of internal sets and hyperfinite structures.

## Main Ideas

An internal set is a set that can be represented as an ultraproduct of standard sets.
We develop just enough infrastructure for hyperfinite random walks and integration.

## Main Definitions

* `InternalSet` - An internal subset of ℝ* via sequences
* `HyperfiniteInterval` - The internal interval {0, 1, ..., N-1}
* `InternalFun` - Internal functions ℝ* → ℝ*
* `hyperfiniteSum` - Sum over a hyperfinite interval

## References

* Goldblatt, "Lectures on the Hyperreals", Chapter 11
-/

open Hyperreal Filter

namespace SPDE.Nonstandard.InternalSets

/-! ## Internal Sets

An internal set is represented as a sequence of standard sets.
-/

/-- An internal subset of ℝ* is given by a sequence of standard subsets of ℝ. -/
structure InternalSet where
  /-- The representing sequence of sets -/
  sets : ℕ → Set ℝ

namespace InternalSet

/-- The empty internal set -/
def empty : InternalSet where
  sets := fun _ => ∅

instance : EmptyCollection InternalSet := ⟨empty⟩

/-- The full internal set -/
def univ : InternalSet where
  sets := fun _ => Set.univ

/-- Internal set from a constant set -/
def ofSet (S : Set ℝ) : InternalSet where
  sets := fun _ => S

/-- Union of internal sets -/
def union (A B : InternalSet) : InternalSet where
  sets := fun n => A.sets n ∪ B.sets n

instance : Union InternalSet := ⟨union⟩

/-- Intersection of internal sets -/
def inter (A B : InternalSet) : InternalSet where
  sets := fun n => A.sets n ∩ B.sets n

instance : Inter InternalSet := ⟨inter⟩

/-- Complement of an internal set -/
def compl (A : InternalSet) : InternalSet where
  sets := fun n => (A.sets n)ᶜ

instance : Compl InternalSet := ⟨compl⟩

end InternalSet

/-! ## Hyperfinite Intervals

A hyperfinite interval {0, 1, ..., N-1} where N is a hypernatural.
-/

/-- A hyperfinite interval with length given by a sequence of naturals -/
structure HyperfiniteInterval where
  /-- The sequence of lengths -/
  lengthSeq : ℕ → ℕ
  /-- The lengths are positive -/
  length_pos : ∀ n, 0 < lengthSeq n

namespace HyperfiniteInterval

/-- The length as a hyperreal -/
noncomputable def length (I : HyperfiniteInterval) : ℝ* :=
  ofSeq (fun n => (I.lengthSeq n : ℝ))

/-- The length is positive -/
theorem length_pos' (I : HyperfiniteInterval) : 0 < I.length := by
  have h : ∀ n, (0 : ℝ) < I.lengthSeq n := fun n => Nat.cast_pos.mpr (I.length_pos n)
  have hev : ∀ᶠ n in hyperfilter ℕ, (0 : ℝ) < I.lengthSeq n :=
    Filter.Eventually.of_forall h
  exact ofSeq_lt_ofSeq.mpr hev

/-- When lengthSeq → ∞, the interval has infinite cardinality -/
theorem infinite_length (I : HyperfiniteInterval)
    (h : Tendsto (fun n => (I.lengthSeq n : ℝ)) atTop atTop) :
    Hyperreal.Infinite I.length := by
  left  -- Show InfinitePos
  intro M
  -- h eventually M < lengthSeq n, which means M < I.length
  have hev : ∀ᶠ n in atTop, M < I.lengthSeq n := h.eventually_gt_atTop M
  -- cofinite sets are in hyperfilter
  have hcofin : {n | M < I.lengthSeq n}ᶜ.Finite := by
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine (Set.finite_lt_nat N).subset ?_
    intro n hn
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hn
    -- n is in the complement means ¬(M < lengthSeq n), i.e., lengthSeq n ≤ M
    -- We need to show n < N
    simp only [Set.mem_setOf_eq]
    by_contra hge
    -- hge : ¬(n < N), i.e., N ≤ n
    have hNlen : N ≤ n := Nat.not_lt.mp hge
    -- so by hN, M < lengthSeq n, contradicting hn
    exact not_lt.mpr hn (hN n hNlen)
  exact ofSeq_lt_ofSeq.mpr (mem_hyperfilter_of_finite_compl hcofin)

/-- The cardinality -/
noncomputable def card (I : HyperfiniteInterval) : ℝ* := I.length

/-- The k-th element -/
noncomputable def element (_I : HyperfiniteInterval) (k : ℕ) : ℝ* := (k : ℝ*)

end HyperfiniteInterval

/-! ## Internal Functions

An internal function is represented as a sequence of standard functions.
-/

/-- An internal function given by a sequence of standard functions -/
structure InternalFun where
  /-- The representing sequence of functions -/
  funs : ℕ → ℝ → ℝ

namespace InternalFun

/-- Lift a standard function to an internal function -/
def ofFun (f : ℝ → ℝ) : InternalFun where
  funs := fun _ => f

/-- Simple apply for standard functions lifted via ofFun.
    This is the key operation: Germ.map lifts f pointwise. -/
noncomputable def applySimple (f : ℝ → ℝ) (x : ℝ*) : ℝ* := Germ.map f x

theorem applySimple_ofSeq (f : ℝ → ℝ) (s : ℕ → ℝ) :
    applySimple f (ofSeq s) = ofSeq (f ∘ s) := rfl

theorem applySimple_coe (f : ℝ → ℝ) (r : ℝ) :
    applySimple f (r : ℝ*) = (f r : ℝ*) := rfl

end InternalFun

/-! ## Hyperfinite Sums

The sum over a hyperfinite interval is the ofSeq of finite sums.
-/

/-- Sum of a function over a hyperfinite interval.
    The function is given as a sequence of standard functions. -/
noncomputable def hyperfiniteSum (F : InternalFun) (I : HyperfiniteInterval) : ℝ* :=
  ofSeq (fun n => ∑ k ∈ Finset.range (I.lengthSeq n), F.funs n k)

/-- Sum of a standard function -/
noncomputable def hyperfiniteSumStd (f : ℝ → ℝ) (I : HyperfiniteInterval) : ℝ* :=
  ofSeq (fun n => ∑ k ∈ Finset.range (I.lengthSeq n), f k)

/-- Linearity of hyperfinite sums -/
theorem hyperfiniteSumStd_add (f g : ℝ → ℝ) (I : HyperfiniteInterval) :
    hyperfiniteSumStd (f + g) I = hyperfiniteSumStd f I + hyperfiniteSumStd g I := by
  unfold hyperfiniteSumStd
  congr 1
  ext n
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]

/-- Scalar multiplication for hyperfinite sums -/
theorem hyperfiniteSumStd_smul (c : ℝ) (f : ℝ → ℝ) (I : HyperfiniteInterval) :
    hyperfiniteSumStd (fun x => c * f x) I = (c : ℝ*) * hyperfiniteSumStd f I := by
  unfold hyperfiniteSumStd
  congr 1
  ext n
  rw [← Finset.mul_sum]

/-! ## Standard Part of Hyperfinite Sums

Key theorem: if the partial sums converge, the standard part equals the limit.
-/

/-- If partial sums converge, the standard part of the hyperfinite sum is the limit -/
theorem st_hyperfiniteSum_eq_limit (f : ℕ → ℝ) (I : HyperfiniteInterval)
    (L : ℝ) (hconv : Tendsto (fun n => ∑ k ∈ Finset.range n, f k) atTop (nhds L))
    (hunbdd : Tendsto I.lengthSeq atTop atTop) :
    st (ofSeq (fun n => ∑ k ∈ Finset.range (I.lengthSeq n), f k)) = L := by
  -- The composition with lengthSeq also converges to L
  have hcomp : Tendsto (fun n => ∑ k ∈ Finset.range (I.lengthSeq n), f k) atTop (nhds L) :=
    hconv.comp hunbdd
  have hIsSt : IsSt (ofSeq (fun n => ∑ k ∈ Finset.range (I.lengthSeq n), f k)) L :=
    isSt_of_tendsto hcomp
  exact hIsSt.st_eq

/-! ## Connection to Riemann Integration

The hyperfinite Riemann sum equals the standard Riemann sum at each level.
-/

/-- Standard Riemann sum with n subdivisions (from HyperfiniteIntegration) -/
noncomputable def standardRiemannSum' (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else
    let dx := (b - a) / n
    ∑ i ∈ Finset.range n, f (a + i * dx) * dx

/-- The hyperfinite Riemann sum using our framework -/
noncomputable def hyperfiniteRiemannSum' (f : ℝ → ℝ) (a b : ℝ) : ℝ* :=
  ofSeq (fun n => standardRiemannSum' f a b (n + 1))

end SPDE.Nonstandard.InternalSets
