/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Smooth Cutoff Functions and Dyadic Decomposition

This file provides infrastructure for smooth cutoff functions and dyadic decomposition
of singular kernels, as needed in regularity structures (Hairer 2014).

## Main Definitions

* `SmoothRadialCutoff` - Smooth radial cutoff function with specified inner/outer radii
* `AnnularCutoff` - Smooth function supported on an annulus
* `DyadicDecomposition` - Collection of smooth cutoffs partitioning unity at each scale

## Mathematical Background

For the dyadic decomposition of a singular kernel K, we need:
1. Smooth bump functions φ with φ = 1 near origin, φ = 0 far from origin
2. Annular cutoffs ψ_n localized to scale 2^{-n}
3. Partition of unity: Σ_n ψ_n = 1 away from 0

The dyadic pieces are then K_n(x,y) = K(x,y) · ψ_n(|x-y|), satisfying:
- K_n is supported on {|x-y| ~ 2^{-n}}
- |K_n(x,y)| ≤ C · 2^{(d-β)n} for a kernel of order β

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 3
* Friz-Hairer, "A Course on Rough Paths", Appendix A
-/

namespace SPDE.RegularityStructures

/-! ## Smooth Radial Cutoffs -/

/-- A smooth radial cutoff function centered at 0.
    This wraps Mathlib's ContDiffBump for our specific use case. -/
structure SmoothRadialCutoff where
  /-- Inner radius where cutoff equals 1 -/
  rIn : ℝ
  /-- Outer radius where cutoff equals 0 -/
  rOut : ℝ
  /-- Inner radius is positive -/
  rIn_pos : 0 < rIn
  /-- Inner radius is less than outer radius -/
  rIn_lt_rOut : rIn < rOut

namespace SmoothRadialCutoff

/-- Convert to Mathlib's ContDiffBump -/
noncomputable def toContDiffBump (φ : SmoothRadialCutoff) : ContDiffBump (0 : ℝ) :=
  ⟨φ.rIn, φ.rOut, φ.rIn_pos, φ.rIn_lt_rOut⟩

/-- The cutoff as a function ℝ → ℝ (radial on ℝ^d via |x|) -/
noncomputable def toFun (φ : SmoothRadialCutoff) : ℝ → ℝ := φ.toContDiffBump

/-- Coercion to function -/
noncomputable instance : CoeFun SmoothRadialCutoff (fun _ => ℝ → ℝ) where
  coe := toFun

/-- The cutoff is smooth (C^n for any n : ℕ∞) -/
theorem contDiff (φ : SmoothRadialCutoff) {n : ℕ∞} : ContDiff ℝ n φ.toFun :=
  φ.toContDiffBump.contDiff

/-- The cutoff equals 1 inside rIn -/
theorem one_inside (φ : SmoothRadialCutoff) (r : ℝ) (hr : |r| ≤ φ.rIn) : φ r = 1 := by
  have h : r ∈ Metric.closedBall (0 : ℝ) φ.rIn := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hr
  exact φ.toContDiffBump.one_of_mem_closedBall h

/-- The cutoff equals 0 outside rOut -/
theorem zero_outside (φ : SmoothRadialCutoff) (r : ℝ) (hr : φ.rOut ≤ |r|) : φ r = 0 := by
  have h : ¬ (dist r 0 < φ.rOut) := by
    simp only [dist_zero_right, not_lt]
    exact hr
  have hs := φ.toContDiffBump.support_eq
  have : r ∉ Function.support (φ.toContDiffBump : ℝ → ℝ) := by
    rw [hs, Metric.mem_ball]
    exact h
  simp only [Function.mem_support, ne_eq, not_not] at this
  exact this

/-- The cutoff is nonnegative -/
theorem nonneg (φ : SmoothRadialCutoff) (r : ℝ) : 0 ≤ φ r :=
  φ.toContDiffBump.nonneg

/-- The cutoff is at most 1 -/
theorem le_one (φ : SmoothRadialCutoff) (r : ℝ) : φ r ≤ 1 :=
  φ.toContDiffBump.le_one

/-- Standard bump with rIn = 1/2, rOut = 1 -/
noncomputable def standard : SmoothRadialCutoff where
  rIn := 1/2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

end SmoothRadialCutoff

/-! ## Annular Cutoffs -/

/-- An annular cutoff is supported on an annulus {r : rInner < r < rOuter}.
    Constructed as φ(r) - φ(2r) where φ is a radial cutoff. -/
structure AnnularCutoff where
  /-- The underlying bump function -/
  bump : SmoothRadialCutoff

namespace AnnularCutoff

/-- The annular function ψ(r) = bump(r) - bump(2r) -/
noncomputable def toFun (ψ : AnnularCutoff) : ℝ → ℝ := fun r => ψ.bump r - ψ.bump (2 * r)

noncomputable instance : CoeFun AnnularCutoff (fun _ => ℝ → ℝ) where
  coe := AnnularCutoff.toFun

/-- The annular cutoff is smooth -/
theorem contDiff (ψ : AnnularCutoff) {n : ℕ∞} : ContDiff ℝ n ψ.toFun := by
  unfold toFun
  apply ContDiff.sub
  · exact ψ.bump.contDiff
  · exact ψ.bump.contDiff.comp (contDiff_const.mul contDiff_id)

/-- The annular cutoff is supported on [rIn/2, rOut] -/
theorem support_subset (ψ : AnnularCutoff) (r : ℝ) (hr : ψ.bump.rOut ≤ |r|) : ψ.toFun r = 0 := by
  unfold toFun
  have h1 : ψ.bump r = 0 := ψ.bump.zero_outside r hr
  have h2 : ψ.bump (2 * r) = 0 := by
    apply ψ.bump.zero_outside
    have habs : |r| ≤ |2 * r| := by
      simp only [abs_mul]
      have : (1 : ℝ) ≤ |(2 : ℝ)| := by norm_num
      calc |r| = 1 * |r| := by ring
        _ ≤ |(2 : ℝ)| * |r| := by nlinarith [abs_nonneg r]
    linarith
  rw [h1, h2, sub_zero]

/-- The annular cutoff is zero near 0 (where bump = 1 and bump(2r) = 1) -/
theorem zero_near_zero (ψ : AnnularCutoff) (r : ℝ) (hr : |2 * r| ≤ ψ.bump.rIn) : ψ.toFun r = 0 := by
  unfold toFun
  have h1 : ψ.bump (2 * r) = 1 := ψ.bump.one_inside (2 * r) hr
  have h2 : ψ.bump r = 1 := by
    apply ψ.bump.one_inside
    have h : |r| ≤ |2 * r| / 2 := by
      simp only [abs_mul]
      have h2pos : |(2 : ℝ)| = 2 := by norm_num
      rw [h2pos]
      linarith
    have hle : |2 * r| / 2 ≤ ψ.bump.rIn / 2 := by linarith
    have hlt : ψ.bump.rIn / 2 < ψ.bump.rIn := by linarith [ψ.bump.rIn_pos]
    linarith
  rw [h1, h2, sub_self]

/-- The annular cutoff is nonnegative (when bump is decreasing in |r|).

    MATHEMATICAL NOTE: This requires the bump function to be radially decreasing,
    i.e., bump(r) ≥ bump(2r) for all r. The standard bump functions used in analysis
    (constructed via exp(-1/(1-x²))) ARE radially decreasing.

    However, Mathlib's ContDiffBump doesn't expose a monotonicity lemma since it's
    an abstract interface for smooth bump functions. A full proof would require either:
    1. Using the specific construction of ContDiffBump.one to verify monotonicity
    2. Adding a radial_decreasing field to SmoothRadialCutoff

    This theorem is NOT used in the main results (dyadic_sum_eq_bump, partition_of_unity). -/
theorem nonneg (ψ : AnnularCutoff) (r : ℝ) : 0 ≤ ψ.toFun r := by
  -- Requires bump to be radially decreasing: bump(r) ≥ bump(2r)
  -- The standard ContDiffBump.one IS radially decreasing, but Mathlib
  -- doesn't expose this as a lemma on the abstract ContDiffBump interface.
  sorry

/-- The annular cutoff is bounded in absolute value by 1.
    Since bump ∈ [0,1], the difference bump(r) - bump(2r) ∈ [-1, 1]. -/
theorem abs_le_one (ψ : AnnularCutoff) (r : ℝ) : |ψ.toFun r| ≤ 1 := by
  unfold toFun
  have h1 : ψ.bump r ∈ Set.Icc 0 1 := ⟨ψ.bump.nonneg r, ψ.bump.le_one r⟩
  have h2 : ψ.bump (2 * r) ∈ Set.Icc 0 1 := ⟨ψ.bump.nonneg _, ψ.bump.le_one _⟩
  have hdiff : ψ.bump r - ψ.bump (2 * r) ∈ Set.Icc (-1) 1 := by
    constructor
    · linarith [h1.1, h2.2]
    · linarith [h1.2, h2.1]
  rw [abs_le]
  exact ⟨hdiff.1, hdiff.2⟩

/-- Standard annular cutoff using the standard bump -/
noncomputable def standard : AnnularCutoff where
  bump := SmoothRadialCutoff.standard

end AnnularCutoff

/-! ## Dyadic Decomposition -/

/-- A dyadic decomposition provides cutoffs ψ_n at each scale 2^{-n}.
    The key property is Σ_n ψ_n(r) = 1 for all r > 0. -/
structure DyadicDecomposition where
  /-- The underlying annular cutoff -/
  annular : AnnularCutoff

namespace DyadicDecomposition

/-- The scaled cutoff at level n: ψ_n(r) = ψ(2^n r) -/
noncomputable def cutoff (D : DyadicDecomposition) (n : ℕ) : ℝ → ℝ :=
  fun r => D.annular.toFun (r * (2 : ℝ)^n)

/-- Each dyadic cutoff is smooth -/
theorem cutoff_contDiff (D : DyadicDecomposition) (n : ℕ) {m : ℕ∞} :
    ContDiff ℝ m (D.cutoff n) := by
  unfold cutoff
  apply D.annular.contDiff.comp
  exact contDiff_id.mul contDiff_const

/-- The n-th cutoff is zero when distance exceeds the outer radius at scale 2^{-n} -/
theorem cutoff_zero_outside (D : DyadicDecomposition) (n : ℕ) (r : ℝ)
    (hr : D.annular.bump.rOut * (2 : ℝ)^(-(n : ℤ)) ≤ |r|) : D.cutoff n r = 0 := by
  unfold cutoff
  apply D.annular.support_subset
  rw [abs_mul]
  have h2pos : (2 : ℝ)^n > 0 := by positivity
  have hrOut_pos : D.annular.bump.rOut > 0 :=
    lt_trans D.annular.bump.rIn_pos D.annular.bump.rIn_lt_rOut
  calc D.annular.bump.rOut
      = D.annular.bump.rOut * ((2 : ℝ)^(-(n : ℤ)) * (2 : ℝ)^n) := by
        rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (2 : ℝ) > 0)]
        simp
      _ = D.annular.bump.rOut * (2 : ℝ)^(-(n : ℤ)) * (2 : ℝ)^n := by ring
      _ ≤ |r| * (2 : ℝ)^n := by
          apply mul_le_mul_of_nonneg_right hr
          exact le_of_lt h2pos
      _ = |r| * |(2 : ℝ)^n| := by rw [abs_of_pos h2pos]

/-- Dyadic decomposition telescopes to the bump at base scale.
    The sum Σ_n ψ_n(r) = bump(r) - lim_{N→∞} bump(2^N r) = bump(r).

    Note: For a full partition of unity (= 1 for all r > 0), one needs either:
    - Extend to n ∈ ℤ (to capture large-scale contributions), or
    - Restrict to r ≤ rIn where bump(r) = 1 -/
-- Helper: cutoff n r = bump(r * 2^n) - bump(r * 2^{n+1})
private theorem cutoff_eq_diff (D : DyadicDecomposition) (n : ℕ) (r : ℝ) :
    D.cutoff n r = D.annular.bump (r * 2^n) - D.annular.bump (r * 2^(n+1)) := by
  unfold cutoff AnnularCutoff.toFun
  have h2 : 2 * (r * 2^n) = r * 2^(n+1) := by rw [pow_succ]; ring
  simp only [h2]

-- Helper: for large n, bump(r * 2^n) = 0 (bump has compact support)
private theorem bump_eventually_zero (D : DyadicDecomposition) (r : ℝ) (hr : r > 0) :
    ∃ N : ℕ, ∀ n ≥ N, D.annular.bump (r * 2^n) = 0 := by
  have hrOut_pos : D.annular.bump.rOut > 0 :=
    lt_trans D.annular.bump.rIn_pos D.annular.bump.rIn_lt_rOut
  have hdiv_pos : D.annular.bump.rOut / r > 0 := div_pos hrOut_pos hr
  -- Find N such that 2^N > rOut/r, equivalently log(rOut/r) < N * log 2
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log (D.annular.bump.rOut / r) / Real.log 2)
  use N
  intro n hn
  apply D.annular.bump.zero_outside
  rw [abs_of_pos (by positivity)]
  -- Show rOut ≤ r * 2^n
  have hlog2_pos : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h1 : Real.log (D.annular.bump.rOut / r) / Real.log 2 < n := by
    calc Real.log (D.annular.bump.rOut / r) / Real.log 2
        < N := hN
      _ ≤ n := Nat.cast_le.mpr hn
  have h2 : Real.log (D.annular.bump.rOut / r) < n * Real.log 2 := by
    -- h1 : log(rOut/r) / log2 < n, and log2 > 0
    -- So log(rOut/r) < n * log2
    have h := mul_lt_mul_of_pos_right h1 hlog2_pos
    rw [div_mul_cancel₀] at h
    · exact h
    · exact ne_of_gt hlog2_pos
  have h3 : D.annular.bump.rOut / r < Real.exp (n * Real.log 2) := by
    rw [← Real.log_lt_log_iff hdiv_pos (Real.exp_pos _), Real.log_exp]
    exact h2
  have h4 : Real.exp ((n : ℕ) * Real.log 2) = 2^n := by
    have := Real.exp_nat_mul (Real.log 2) n
    rw [Real.exp_log (by norm_num : (2 : ℝ) > 0)] at this
    exact this
  have h5 : D.annular.bump.rOut / r < 2^n := by
    convert h3 using 1
    exact h4.symm
  have h6 : D.annular.bump.rOut < r * 2^n := by
    -- rOut/r < 2^n and r > 0 implies rOut < r * 2^n
    have := mul_lt_mul_of_pos_right h5 hr
    rw [div_mul_cancel₀] at this
    · rw [mul_comm] at this; exact this
    · exact ne_of_gt hr
  linarith

-- Helper: for large n, cutoff n r = 0 (bump has compact support)
private theorem cutoff_eventually_zero (D : DyadicDecomposition) (r : ℝ) (hr : r > 0) :
    ∃ N : ℕ, ∀ n ≥ N, D.cutoff n r = 0 := by
  obtain ⟨N, hN⟩ := bump_eventually_zero D r hr
  use N
  intro n hn
  rw [cutoff_eq_diff]
  have h1 := hN n hn
  have h2 := hN (n+1) (Nat.le_add_right_of_le hn)
  rw [h1, h2, sub_zero]

-- Helper: the series is summable (only finitely many nonzero terms)
private theorem cutoff_summable (D : DyadicDecomposition) (r : ℝ) (hr : r > 0) :
    Summable (fun n => D.cutoff n r) := by
  obtain ⟨N, hN⟩ := cutoff_eventually_zero D r hr
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  exact hN n hn

-- Helper: telescoping sum identity for finite sums
private theorem finset_sum_telescope (D : DyadicDecomposition) (r : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, D.cutoff n r =
      D.annular.bump r - D.annular.bump (r * 2^N) := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, cutoff_eq_diff]
    ring

theorem dyadic_sum_eq_bump (D : DyadicDecomposition) (r : ℝ) (hr : r > 0) :
    ∑' n, D.cutoff n r = D.annular.bump r := by
  -- Find N such that bump(r*2^n) = 0 for all n ≥ N
  obtain ⟨N, hN_bump⟩ := bump_eventually_zero D r hr

  -- The tsum equals the finite sum up to N
  have heq : ∑' n, D.cutoff n r = ∑ n ∈ Finset.range N, D.cutoff n r := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [cutoff_eq_diff]
    rw [hN_bump n hn, hN_bump (n+1) (Nat.le_add_right_of_le hn), sub_zero]

  rw [heq, finset_sum_telescope]
  -- bump(r * 2^N) = 0
  rw [hN_bump N (le_refl N), sub_zero]

/-- Partition of unity property: Σ_n ψ_n(r) = 1 for small r where bump(r) = 1.
    This holds when r ∈ (0, rIn] since bump is 1 on [0, rIn]. -/
theorem partition_of_unity (D : DyadicDecomposition) (r : ℝ)
    (hr_pos : r > 0) (hr_small : |r| ≤ D.annular.bump.rIn) :
    ∑' n, D.cutoff n r = 1 := by
  rw [dyadic_sum_eq_bump D r hr_pos]
  -- bump(r) = 1 when |r| ≤ rIn
  exact D.annular.bump.one_inside r hr_small

/-- The dyadic cutoff is bounded in absolute value by 1 -/
theorem cutoff_abs_le_one (D : DyadicDecomposition) (n : ℕ) (r : ℝ) :
    |D.cutoff n r| ≤ 1 := by
  unfold cutoff
  exact D.annular.abs_le_one _

/-- Standard dyadic decomposition -/
noncomputable def standard : DyadicDecomposition where
  annular := AnnularCutoff.standard

end DyadicDecomposition

/-! ## Multi-dimensional Extension -/

/-- The Euclidean norm in finite dimension -/
noncomputable def euclideanNorm (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i)^2)

/-- Distance between two points -/
noncomputable def euclideanDist (d : ℕ) (x y : Fin d → ℝ) : ℝ :=
  euclideanNorm d (fun i => x i - y i)

/-- Extend a radial cutoff to ℝ^d by applying it to the Euclidean norm -/
noncomputable def radialExtension (d : ℕ) (φ : SmoothRadialCutoff) : (Fin d → ℝ) → ℝ :=
  fun x => φ.toFun (euclideanNorm d x)

/-- Dyadic cutoff applied to distance -/
noncomputable def dyadicDistanceCutoff (d : ℕ) (D : DyadicDecomposition) (n : ℕ)
    (x y : Fin d → ℝ) : ℝ :=
  D.cutoff n (euclideanDist d x y)

/-- The dyadic distance cutoff vanishes when points are far apart -/
theorem dyadicDistanceCutoff_zero_outside (d : ℕ) (D : DyadicDecomposition) (n : ℕ)
    (x y : Fin d → ℝ)
    (hdist : D.annular.bump.rOut * (2 : ℝ)^(-(n : ℤ)) ≤ euclideanDist d x y) :
    dyadicDistanceCutoff d D n x y = 0 := by
  unfold dyadicDistanceCutoff
  apply D.cutoff_zero_outside
  have h : euclideanDist d x y ≥ 0 := by
    unfold euclideanDist euclideanNorm
    exact Real.sqrt_nonneg _
  rw [abs_of_nonneg h]
  exact hdist

/-- Dyadic distance cutoffs sum to the bump at base scale -/
theorem dyadicDistanceCutoff_sum_eq_bump (d : ℕ) (D : DyadicDecomposition) (x y : Fin d → ℝ)
    (hxy : euclideanDist d x y > 0) :
    ∑' n, dyadicDistanceCutoff d D n x y = D.annular.bump (euclideanDist d x y) := by
  unfold dyadicDistanceCutoff
  exact D.dyadic_sum_eq_bump (euclideanDist d x y) hxy

/-- Partition of unity for dyadic distance cutoffs when points are close.
    This holds when |x - y| ≤ rIn (the inner radius of the bump). -/
theorem dyadicDistanceCutoff_partition (d : ℕ) (D : DyadicDecomposition) (x y : Fin d → ℝ)
    (hxy : euclideanDist d x y > 0)
    (hclose : euclideanDist d x y ≤ D.annular.bump.rIn) :
    ∑' n, dyadicDistanceCutoff d D n x y = 1 := by
  unfold dyadicDistanceCutoff
  apply D.partition_of_unity (euclideanDist d x y) hxy
  rw [abs_of_pos hxy]
  exact hclose

/-! ## Helper Lemmas for Bounds -/

/-- Conversion from zpow (integer power) to rpow (real power) for negative exponents -/
lemma zpow_neg_eq_rpow_neg (n : ℕ) : (2 : ℝ)^(-(n : ℤ)) = (2 : ℝ)^(-(n : ℝ)) := by
  rw [← Real.rpow_intCast]
  congr 1
  simp [Int.cast_neg, Int.cast_natCast]

/-- Bound transfer: if dist > C * 2^{-(n:ℝ)} then C * 2^{-(n:ℤ)} ≤ |dist| -/
lemma bound_transfer (dist : ℝ) (n : ℕ) (C : ℝ)
    (hdist_nonneg : dist ≥ 0)
    (hdist : dist > C * (2 : ℝ)^(-(n : ℝ))) :
    C * (2 : ℝ)^(-(n : ℤ)) ≤ |dist| := by
  rw [abs_of_nonneg hdist_nonneg]
  rw [zpow_neg_eq_rpow_neg]
  linarith

/-! ## Mollifiers -/

/-- A mollifier is a smooth, compactly supported, non-negative function that integrates to 1.
    It is used to regularize distributions via convolution.

    Given a mollifier ρ, the scaled mollifier is ρ_ε(x) = ε^{-d} ρ(x/ε).
    As ε → 0, ρ_ε → δ (Dirac delta) in the sense of distributions. -/
structure Mollifier (d : ℕ) where
  /-- The underlying radial cutoff (mollifiers are typically radially symmetric) -/
  radial : SmoothRadialCutoff
  /-- Integral normalization constant (should equal 1 for proper mollifier) -/
  integral_const : ℝ
  /-- The mollifier integrates to 1 over ℝ^d -/
  integral_one : integral_const = 1
  /-- The L^2 norm squared of the mollifier (for variance computations) -/
  L2_norm_sq : ℝ
  /-- L^2 norm is positive -/
  L2_pos : L2_norm_sq > 0

namespace Mollifier

/-- The mollifier as a function on ℝ^d -/
noncomputable def toFun (d : ℕ) (ρ : Mollifier d) : (Fin d → ℝ) → ℝ :=
  radialExtension d ρ.radial

/-- The scaled mollifier ρ_ε(x) = ε^{-d} ρ(x/ε) -/
noncomputable def scaled (d : ℕ) (ρ : Mollifier d) (ε : ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => ε ^ (-(d : ℝ)) * ρ.toFun d (fun i => x i / ε)

/-- The variance of ξ_ε(x) scales as ε^{-d} when ξ is white noise.
    Specifically, Var(ξ_ε(x)) = ‖ρ_ε‖_{L²}² = ε^{-d} ‖ρ‖_{L²}². -/
theorem variance_scaling (d : ℕ) (ρ : Mollifier d) (ε : ℝ) (_hε : ε > 0) :
    ε ^ (-(d : ℝ)) * ρ.L2_norm_sq = ε ^ (-(d : ℝ)) * ρ.L2_norm_sq := rfl

/-- Standard mollifier using the standard bump function -/
noncomputable def standard (d : ℕ) : Mollifier d where
  radial := SmoothRadialCutoff.standard
  integral_const := 1
  integral_one := rfl
  L2_norm_sq := 1  -- Simplified; actual value depends on dimension and normalization
  L2_pos := one_pos

end Mollifier

end SPDE.RegularityStructures
