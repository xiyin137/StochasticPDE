/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import StochasticPDE.Nonstandard.Foundation.Hypernatural

/-!
# Hyperfinite Sums

This file develops hyperfinite sums - sums indexed by hypernatural numbers.
These are essential for defining hyperfinite integrals and working with
internal functions in nonstandard analysis.

## Main Definitions

* `HyperfiniteSum` - A hyperfinite sum represented by its sequence of partial sums
* `HyperfiniteSum.sum` - The value of a hyperfinite sum at a hypernatural index
* `HyperfiniteSum.ofFiniteSum` - Lift a sequence of finite sums to a hyperfinite sum

## Main Results

* `sum_add` - Hyperfinite sums distribute over addition
* `sum_mul_const` - Scalar multiplication of hyperfinite sums
* `sum_mono` - Monotonicity of hyperfinite sums

## Implementation Notes

Since we don't have the full transfer principle, we work with sequences of partial sums
and use the ultraproduct construction to define hyperfinite sums.

A hyperfinite sum Σ_{k=0}^{N-1} f(k) where N is a hypernatural is represented by:
- For each standard n, the partial sum Σ_{k=0}^{n-1} f_n(k) where f_n is the n-th representative
- The ultraproduct of these partial sums

## References

* Goldblatt, "Lectures on the Hyperreals", Chapter 9
* Lindstrøm, "Hyperfinite Stochastic Integration"
-/

open Hyperreal Filter Set

namespace SPDE.Nonstandard.Foundation

open Hypernat

/-! ## Hyperfinite Sum Structure -/

/-- A hyperfinite sum is represented by a sequence of finite sums.
    At the n-th level, we have a function f_n : ℕ → ℝ and we sum it. -/
structure HyperfiniteSum where
  /-- The summand at each level: summand n k is the k-th term in the n-th approximation -/
  summand : ℕ → ℕ → ℝ

namespace HyperfiniteSum

variable (S : HyperfiniteSum)

/-- The partial sum at level n up to index m -/
noncomputable def partialSum (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, S.summand n k

/-- The hyperfinite sum at a hypernatural index.
    For N : Hypernat with representative sequence (n_k), we define
    Σ_{i<N} f(i) as the ultraproduct of partial sums. -/
noncomputable def sum (N : Hypernat) : ℝ* :=
  ofSeq (fun n => S.partialSum n (N.toSeq n))

/-- Basic property: sum at 0 is 0 -/
theorem sum_zero : S.sum (Hypernat.ofNat' 0) = 0 := by
  unfold sum partialSum
  -- For ofNat' 0, toSeq n = 0 for almost all n
  -- So partialSum n 0 = sum over empty range = 0
  -- We use that the germ of the constant 0 sequence is 0
  have hae : ∀ᶠ n in hyperfilter ℕ, (Hypernat.ofNat' 0).toSeq n = 0 := Hypernat.toSeq_ofNat'_ae 0
  have hzero : ∀ᶠ n in hyperfilter ℕ, ∑ k ∈ Finset.range ((Hypernat.ofNat' 0).toSeq n), S.summand n k = 0 := by
    exact hae.mono (fun n h => by simp [h])
  unfold ofSeq
  rw [← Germ.coe_zero]
  exact Germ.coe_eq.mpr hzero

/-- Construct a hyperfinite sum from a single function (internal function) -/
noncomputable def ofFun (f : ℕ → ℝ) : HyperfiniteSum where
  summand := fun _ k => f k

theorem ofFun_partialSum (f : ℕ → ℝ) (n m : ℕ) :
    (ofFun f).partialSum n m = ∑ k ∈ Finset.range m, f k := rfl

/-- For a standard function and standard index, the sum equals the finite sum -/
theorem ofFun_sum_ofNat' (f : ℕ → ℝ) (m : ℕ) :
    (ofFun f).sum (Hypernat.ofNat' m) = (∑ k ∈ Finset.range m, f k : ℝ) := by
  unfold sum ofFun partialSum
  simp only
  -- The toSeq of ofNat' m is m almost everywhere
  have hae : ∀ᶠ n in hyperfilter ℕ, (Hypernat.ofNat' m).toSeq n = m := Hypernat.toSeq_ofNat'_ae m
  -- So the partial sum is constantly ∑ k ∈ Finset.range m, f k almost everywhere
  have hsum : ∀ᶠ n in hyperfilter ℕ,
      ∑ k ∈ Finset.range ((Hypernat.ofNat' m).toSeq n), f k = ∑ k ∈ Finset.range m, f k := by
    exact hae.mono (fun n h => by rw [h])
  unfold ofSeq
  exact Germ.coe_eq.mpr hsum

/-! ## Arithmetic Operations on Hyperfinite Sums -/

/-- Addition of hyperfinite sums -/
noncomputable def add (S T : HyperfiniteSum) : HyperfiniteSum where
  summand := fun n k => S.summand n k + T.summand n k

noncomputable instance : Add HyperfiniteSum := ⟨add⟩

/-- Scalar multiplication -/
noncomputable def smul (c : ℝ) (S : HyperfiniteSum) : HyperfiniteSum where
  summand := fun n k => c * S.summand n k

noncomputable instance : SMul ℝ HyperfiniteSum := ⟨smul⟩

/-- Sum of addition equals addition of sums -/
theorem sum_add (S T : HyperfiniteSum) (N : Hypernat) :
    (S + T).sum N = S.sum N + T.sum N := by
  show (add S T).sum N = S.sum N + T.sum N
  unfold sum add partialSum
  simp only [Finset.sum_add_distrib]
  unfold ofSeq
  have h : (fun n => ∑ x ∈ Finset.range (N.toSeq n), S.summand n x +
                     ∑ x ∈ Finset.range (N.toSeq n), T.summand n x) =
           (fun n => ∑ k ∈ Finset.range (N.toSeq n), S.summand n k) +
           (fun n => ∑ k ∈ Finset.range (N.toSeq n), T.summand n k) := by
    funext n; rfl
  rw [h, Germ.coe_add]

/-- Sum of scalar multiple equals scalar multiple of sum -/
theorem sum_smul (c : ℝ) (S : HyperfiniteSum) (N : Hypernat) :
    (c • S).sum N = c * S.sum N := by
  show (smul c S).sum N = c * S.sum N
  unfold sum smul partialSum
  simp only [← Finset.mul_sum]
  unfold ofSeq
  have h : (fun n => c * ∑ i ∈ Finset.range (N.toSeq n), S.summand n i) =
           (fun _ => c) * (fun n => ∑ i ∈ Finset.range (N.toSeq n), S.summand n i) := by
    funext n; rfl
  rw [h, Germ.coe_mul]
  -- ↑(fun _ => c) is the constant germ which equals (c : ℝ*)
  rfl

/-! ## Monotonicity -/

/-- If all terms are nonnegative, partial sums are monotone -/
theorem partialSum_mono {S : HyperfiniteSum} (hpos : ∀ n k, 0 ≤ S.summand n k)
    {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂) (n : ℕ) :
    S.partialSum n m₁ ≤ S.partialSum n m₂ := by
  unfold partialSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hle
  · intros k _ _
    exact hpos n k

/-- For nonnegative sums, larger index gives larger sum -/
theorem sum_mono {S : HyperfiniteSum} (hpos : ∀ n k, 0 ≤ S.summand n k)
    {N M : Hypernat} (hle : N ≤ M) : S.sum N ≤ S.sum M := by
  unfold sum ofSeq
  -- Need to show that the germ of partial sums is monotone
  -- This requires showing N.toSeq n ≤ M.toSeq n almost everywhere
  -- which follows from N ≤ M in the hypernatural sense
  have hseq : ∀ᶠ n in hyperfilter ℕ, N.toSeq n ≤ M.toSeq n := Hypernat.toSeq_le_of_le hle
  have h : ∀ᶠ n in hyperfilter ℕ, S.partialSum n (N.toSeq n) ≤ S.partialSum n (M.toSeq n) :=
    hseq.mono (fun n hle => partialSum_mono hpos hle n)
  exact Germ.coe_le.mpr h

/-! ## Telescoping Sums -/

/-- A telescoping sum Σ (f(k+1) - f(k)) = f(N) - f(0) -/
noncomputable def telescope (f : ℕ → ℝ) : HyperfiniteSum where
  summand := fun _ k => f (k + 1) - f k

theorem telescope_partialSum (f : ℕ → ℝ) (n m : ℕ) :
    (telescope f).partialSum n m = f m - f 0 := by
  unfold telescope partialSum
  simp only
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The hyperfinite telescoping sum -/
theorem telescope_sum (f : ℕ → ℝ) (N : Hypernat) :
    (telescope f).sum N = ofSeq (fun n => f (N.toSeq n)) - ofSeq (fun _ => f 0) := by
  unfold sum
  simp only [telescope_partialSum]
  unfold ofSeq
  have h : (fun n => f (N.toSeq n) - f 0) =
           (fun n => f (N.toSeq n)) - (fun _ => f 0) := by
    funext n; rfl
  rw [h, Germ.coe_sub]

end HyperfiniteSum

/-! ## Hyperfinite Products -/

/-- A hyperfinite product is represented similarly to sums -/
structure HyperfiniteProduct where
  /-- The factor at each level -/
  factor : ℕ → ℕ → ℝ

namespace HyperfiniteProduct

variable (P : HyperfiniteProduct)

/-- The partial product at level n up to index m -/
noncomputable def partialProduct (n m : ℕ) : ℝ :=
  ∏ k ∈ Finset.range m, P.factor n k

/-- The hyperfinite product at a hypernatural index -/
noncomputable def prod (N : Hypernat) : ℝ* :=
  ofSeq (fun n => P.partialProduct n (N.toSeq n))

end HyperfiniteProduct

end SPDE.Nonstandard.Foundation
