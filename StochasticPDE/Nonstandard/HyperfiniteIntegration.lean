/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Hyperfinite Integration

This file develops hyperfinite Riemann sums and their connection to standard integrals.

## Main Ideas

A hyperfinite Riemann sum is a sum Σᵢ₌₀^{N-1} f(xᵢ)·Δx where N may be infinite.
For standard continuous functions, the standard part of this sum equals the
Riemann integral.

## Key Technical Point

We do NOT use a general transfer principle (which would require an axiom).
Instead, we prove specific instances directly from the ultraproduct definition:
- If `Tendsto f atTop (𝓝 r)`, then `IsSt (ofSeq f) r` (via `isSt_of_tendsto`)
- This is the rigorous way to connect limits to standard parts

## Main Definitions

* `standardRiemannSum` - Standard Riemann sum with n subdivisions
* `hyperfiniteRiemannSum` - Riemann sum lifted to hyperreals via ofSeq

## Main Results

* `st_hyperfiniteRiemannSum_eq_integral` - Standard part equals integral

## References

* Keisler, "Foundations of Infinitesimal Calculus"
* Goldblatt, "Lectures on the Hyperreals"
-/

open MeasureTheory Hyperreal Filter Topology

namespace SPDE.Nonstandard.Integration

/-! ## Standard Riemann Sums

First, we define standard Riemann sums with n subdivisions.
These are the building blocks lifted to hyperreals.
-/

/-- Standard Riemann sum of f on [a, b] with n equal subdivisions.
    Uses left endpoints: Σᵢ f(a + i·Δx)·Δx where Δx = (b-a)/n -/
noncomputable def standardRiemannSum (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else
    let dx := (b - a) / n
    ∑ i : Fin n, f (a + i * dx) * dx

theorem standardRiemannSum_zero (f : ℝ → ℝ) (a b : ℝ) :
    standardRiemannSum f a b 0 = 0 := by simp [standardRiemannSum]

theorem standardRiemannSum_succ (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    standardRiemannSum f a b (n + 1) =
    let dx := (b - a) / (n + 1)
    ∑ i : Fin (n + 1), f (a + i * dx) * dx := by
  simp [standardRiemannSum]

/-! ## Key Lemma: Riemann Sums Converge

For continuous f on [a,b], the standard Riemann sums converge to the integral.
This is the fundamental theorem of calculus for Riemann sums.
-/

/-- The mesh size tends to zero -/
theorem mesh_tendsto_zero (a b : ℝ) (hab : a < b) :
    Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h : (b - a) > 0 := sub_pos.mpr hab
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact tendsto_const_nhds.div_atTop h1

/-- For continuous f, Riemann sums converge to the integral.
    This requires showing that the error between the Riemann sum and the
    integral tends to zero as the mesh size decreases.

    **Proof outline**:
    1. Case a = b: both sides equal 0
    2. Case a < b: use uniform continuity of f on [a,b] to bound error

    The key insight is that for uniform continuous f with modulus ω,
    |S_n - ∫f| ≤ (b-a) · ω((b-a)/(n+1)) → 0 as n → ∞.

    **Note**: A complete formal proof requires substantial machinery connecting
    Riemann sums to the Lebesgue integral. The core mathematical content is
    straightforward but the formalization is technical. -/
theorem riemannSum_tendsto_integral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : Continuous f) :
    Tendsto (fun n => standardRiemannSum f a b (n + 1)) atTop (𝓝 (∫ x in a..b, f x)) := by
  by_cases hab' : a = b
  · -- Case a = b: integral is 0, Riemann sum is 0
    subst hab'
    simp only [intervalIntegral.integral_same]
    have heq : (fun n => standardRiemannSum f a a (n + 1)) = (fun _ => 0) := by
      funext n
      simp only [standardRiemannSum, sub_self, zero_div]
      have hne : n + 1 ≠ 0 := Nat.succ_ne_zero n
      simp only [hne, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro i _
      ring
    rw [heq]
    exact tendsto_const_nhds
  · -- Case a < b: use uniform continuity
    have hab'' : a < b := lt_of_le_of_ne hab hab'
    have hab_pos : 0 < b - a := sub_pos.mpr hab''
    -- f is uniformly continuous on [a,b] (Heine-Cantor theorem)
    have huc : UniformContinuousOn f (Set.Icc a b) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
    -- f is interval integrable (continuous functions are integrable)
    have hint : ∀ c d, IntervalIntegrable f MeasureTheory.volume c d :=
      fun c d => hf.intervalIntegrable c d
    -- Use metric convergence
    rw [Metric.tendsto_atTop]
    intro eps heps
    -- Get modulus of uniform continuity: |x - y| < δ → |f(x) - f(y)| < eps/(2(b-a))
    -- We use eps/2 so that the final bound is < eps (strict)
    rw [Metric.uniformContinuousOn_iff] at huc
    have heps' : 0 < eps / 2 / (b - a) := div_pos (half_pos heps) hab_pos
    obtain ⟨δ, hδ_pos, hδ⟩ := huc (eps / 2 / (b - a)) heps'
    -- Mesh tends to zero (for natural numbers)
    have hmesh_tends : Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      mesh_tendsto_zero a b hab''
    -- Get N such that mesh < δ for n ≥ N
    have hev : ∀ᶠ n : ℕ in atTop, (b - a) / ((n : ℝ) + 1) < δ :=
      hmesh_tends.eventually (Iio_mem_nhds hδ_pos)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    use N
    intro n hn
    -- The mesh for n+1 subdivisions (standardRiemannSum uses n+1 subdivisions)
    have hm_ne : ((n : ℝ) + 1) ≠ 0 := by
      have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hm_pos : (0 : ℝ) < (n : ℝ) + 1 := by
      have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    set Δx := (b - a) / ((n : ℝ) + 1) with hΔx_def
    have hΔx_pos : 0 < Δx := div_pos hab_pos hm_pos
    have hΔx_lt_δ : Δx < δ := hN n hn
    have hn_Δx : ((n : ℝ) + 1) * Δx = b - a := mul_div_cancel₀ (b - a) hm_ne
    -- The key estimate: |S_n - ∫f| ≤ (b-a) · eps/(b-a) = eps
    -- We prove this by bounding each term.
    --
    -- Define partition points: xᵢ = a + i · Δx
    let x : ℕ → ℝ := fun i => a + i * Δx
    have hx0 : x 0 = a := by simp [x]
    have hxn : x (n + 1) = b := by
      simp only [x]
      have h : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
      rw [h]
      linarith [hn_Δx]
    -- Each xᵢ is in [a, b] for i ≤ n + 1
    have hx_mem : ∀ i ≤ n + 1, x i ∈ Set.Icc a b := by
      intro i hi
      constructor
      · simp only [x]
        have : (0 : ℝ) ≤ i * Δx := mul_nonneg (Nat.cast_nonneg i) (le_of_lt hΔx_pos)
        linarith
      · simp only [x]
        have hi' : (i : ℝ) ≤ n + 1 := by exact_mod_cast hi
        calc a + i * Δx ≤ a + (n + 1) * Δx := by nlinarith [hΔx_pos]
          _ = a + (b - a) := by rw [hn_Δx]
          _ = b := by ring
    -- The distance formula
    rw [Real.dist_eq]
    -- Use the estimate |S - ∫f| ≤ (n+1) · Δx · eps/(b-a) = eps
    -- This is the core technical step using:
    -- 1. Sum of integrals over adjacent intervals = total integral
    -- 2. Each term |f(xᵢ)·Δx - ∫_{xᵢ}^{xᵢ₊₁} f| ≤ Δx · eps/(b-a)
    --    (by uniform continuity: |f(xᵢ) - f(y)| < eps/(b-a) for y ∈ [xᵢ, xᵢ₊₁])
    -- 3. Triangle inequality to sum the bounds
    --
    -- The formal proof requires:
    -- - intervalIntegral.sum_integral_adjacent_intervals
    -- - MeasureTheory.norm_integral_le_of_norm_le_const
    -- - Careful bookkeeping of the partition
    --
    -- This is a standard theorem in real analysis (Riemann sums converge to
    -- Lebesgue integral for continuous functions). The key nonstandard insight
    -- is that once we have this, st_hyperfiniteRiemannSum_eq_integral follows
    -- immediately via isSt_of_tendsto without needing transfer principles.
    -- The goal is to show: |S - ∫f| < eps
    -- We prove: |S - ∫f| ≤ (n+1) * Δx * (eps/2)/(b-a) = (b-a) * (eps/2)/(b-a) = eps/2 < eps
    have hbound : |standardRiemannSum f a b (n + 1) - ∫ y in a..b, f y|
        ≤ ((n : ℝ) + 1) * Δx * (eps / 2 / (b - a)) := by
      -- Step 1: Rewrite the Riemann sum (Δx = (b-a)/(n+1) by definition)
      have hRS : standardRiemannSum f a b (n + 1) = ∑ i : Fin (n + 1), f (x i) * Δx := by
        simp only [standardRiemannSum, Nat.succ_ne_zero, ↓reduceIte, x, Nat.cast_add, Nat.cast_one]
        rfl
      -- Step 2: Split the integral into sum of adjacent integrals
      -- ∫_a^b f = Σᵢ ∫_{xᵢ}^{xᵢ₊₁} f
      have hsplit : ∫ y in a..b, f y =
          ∑ i : Fin (n + 1), ∫ y in (x i)..(x (i + 1)), f y := by
        -- Use intervalIntegral.sum_integral_adjacent_intervals
        have hint' : ∀ k < n + 1, IntervalIntegrable f volume (x k) (x (k + 1)) := by
          intro k _
          exact hint (x k) (x (k + 1))
        have heq := intervalIntegral.sum_integral_adjacent_intervals hint'
        rw [hx0, hxn] at heq
        rw [← heq]
        -- Convert Finset.range sum to Fin sum using Fin.sum_univ_eq_sum_range
        rw [← Fin.sum_univ_eq_sum_range]
      -- Step 3: Bound each term |f(xᵢ)·Δx - ∫_{xᵢ}^{xᵢ₊₁} f|
      -- f(xᵢ)·Δx = ∫_{xᵢ}^{xᵢ₊₁} f(xᵢ) (constant function)
      -- So |f(xᵢ)·Δx - ∫_{xᵢ}^{xᵢ₊₁} f| = |∫_{xᵢ}^{xᵢ₊₁} (f(xᵢ) - f)|
      --                                  ≤ Δx · sup|f(xᵢ) - f(y)| for y ∈ [xᵢ, xᵢ₊₁]
      --                                  ≤ Δx · (eps/2)/(b-a) by uniform continuity
      have hterm : ∀ i : Fin (n + 1),
          |f (x i) * Δx - ∫ y in (x i)..(x (i + 1)), f y| ≤ Δx * (eps / 2 / (b - a)) := by
        intro i
        -- The subinterval length is Δx
        have hlen : x (↑i + 1) - x ↑i = Δx := by
          simp only [x]
          have h1 : (((i : ℕ) + 1 : ℕ) : ℝ) = (i : ℕ) + 1 := by norm_cast
          rw [h1]
          ring
        -- x i and x (i+1) are both in [a, b]
        have hi_le : (i : ℕ) ≤ n + 1 := le_of_lt i.isLt
        have hi1_le : (i : ℕ) + 1 ≤ n + 1 := Nat.succ_le_of_lt i.isLt
        have hxi_mem : x i ∈ Set.Icc a b := hx_mem i hi_le
        have hxi1_mem : x (i + 1) ∈ Set.Icc a b := hx_mem (i + 1) hi1_le
        -- For any y in [x i, x (i+1)], |y - x i| ≤ Δx < δ
        -- So |f(x i) - f(y)| < eps/2/(b-a) by uniform continuity (hδ)
        have hf_bound : ∀ y ∈ Set.Icc (x i) (x (i + 1)), |f (x i) - f y| ≤ eps / 2 / (b - a) := by
          intro y hy
          have hy_dist : dist (x i) y < δ := by
            rw [Real.dist_eq, abs_sub_comm]
            have hy_sub : y - x i ≤ Δx := by
              have := hy.2
              simp only [x] at this ⊢
              linarith
            have hy_sub' : 0 ≤ y - x i := by
              have := hy.1
              linarith
            rw [abs_of_nonneg hy_sub']
            calc y - x i ≤ Δx := hy_sub
              _ < δ := hΔx_lt_δ
          have hy_mem : y ∈ Set.Icc a b := by
            constructor
            · have := hy.1
              have := hxi_mem.1
              linarith
            · have := hy.2
              have := hxi1_mem.2
              linarith
          have h := hδ (x i) hxi_mem y hy_mem hy_dist
          rw [Real.dist_eq] at h
          exact le_of_lt h
        -- f(x i) * Δx = ∫_{x i}^{x (i+1)} f(x i) dy
        have hconst_int : f (x ↑i) * Δx = ∫ y in (x ↑i)..(x (↑i + 1)), f (x ↑i) := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          rw [hlen, mul_comm]
        rw [hconst_int]
        -- |∫(f(xi) - f)| ≤ ∫|f(xi) - f| ≤ Δx * bound
        have hxi_le_xi1 : x ↑i ≤ x (↑i + 1) := by
          simp only [x]
          have hi_nn : (0 : ℝ) ≤ (i : ℕ) := Nat.cast_nonneg i
          nlinarith [hΔx_pos, hi_nn]
        rw [← intervalIntegral.integral_sub (intervalIntegrable_const) (hint _ _)]
        -- The function y ↦ |f(x i) - f y| is continuous hence integrable
        have hcont_diff : Continuous (fun y => f (x ↑i) - f y) := continuous_const.sub hf
        have hint_abs : IntervalIntegrable (fun y => |f (x ↑i) - f y|) volume (x ↑i) (x (↑i + 1)) :=
          hcont_diff.abs.intervalIntegrable _ _
        calc |∫ y in (x ↑i)..(x (↑i + 1)), (f (x ↑i) - f y)|
            ≤ ∫ y in (x ↑i)..(x (↑i + 1)), |f (x ↑i) - f y| := by
              apply intervalIntegral.abs_integral_le_integral_abs hxi_le_xi1
          _ ≤ ∫ _y in (x ↑i)..(x (↑i + 1)), (eps / 2 / (b - a)) := by
              have hint_const : IntervalIntegrable (fun _ => eps / 2 / (b - a)) volume (x ↑i) (x (↑i + 1)) :=
                intervalIntegrable_const
              exact intervalIntegral.integral_mono_on (hab := hxi_le_xi1)
                (hf := hint_abs) (hg := hint_const) hf_bound
          _ = (eps / 2 / (b - a)) * (x (↑i + 1) - x ↑i) := by
              rw [intervalIntegral.integral_const]
              simp only [smul_eq_mul]
              ring
          _ = Δx * (eps / 2 / (b - a)) := by rw [hlen]; ring
      -- Step 4: Sum the bounds
      rw [hRS, hsplit]
      calc |∑ i : Fin (n + 1), f (x i) * Δx - ∑ i : Fin (n + 1), ∫ y in (x i)..(x (i + 1)), f y|
          = |∑ i : Fin (n + 1), (f (x i) * Δx - ∫ y in (x i)..(x (i + 1)), f y)| := by
            congr 1; rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i : Fin (n + 1), |f (x i) * Δx - ∫ y in (x i)..(x (i + 1)), f y| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin (n + 1), (Δx * (eps / 2 / (b - a))) := by
            apply Finset.sum_le_sum
            intro i _
            exact hterm i
        _ = ((n : ℝ) + 1) * (Δx * (eps / 2 / (b - a))) := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        _ = ((n : ℝ) + 1) * Δx * (eps / 2 / (b - a)) := by ring
    calc |standardRiemannSum f a b (n + 1) - ∫ y in a..b, f y|
        ≤ ((n : ℝ) + 1) * Δx * (eps / 2 / (b - a)) := hbound
      _ = (b - a) * (eps / 2 / (b - a)) := by rw [hn_Δx]
      _ = eps / 2 := by field_simp
      _ < eps := half_lt_self heps

/-! ## Hyperfinite Riemann Sum

The hyperfinite Riemann sum is defined by lifting the sequence of standard
Riemann sums via `ofSeq`. The key property is that if the standard sums
converge to L, then the hyperfinite sum has standard part L.
-/

/-- The hyperfinite Riemann sum: lift the sequence of standard Riemann sums -/
noncomputable def hyperfiniteRiemannSum (f : ℝ → ℝ) (a b : ℝ) : ℝ* :=
  ofSeq (fun n => standardRiemannSum f a b (n + 1))

/-- The standard part of the hyperfinite Riemann sum equals the integral.

    **Proof strategy**: We use `isSt_of_tendsto`:
    If `Tendsto s atTop (𝓝 L)`, then `IsSt (ofSeq s) L`.

    This is the rigorous bridge from limits to standard parts,
    built into mathlib's Hyperreal API. No transfer principle needed. -/
theorem st_hyperfiniteRiemannSum_eq_integral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : Continuous f) :
    st (hyperfiniteRiemannSum f a b) = ∫ x in a..b, f x := by
  unfold hyperfiniteRiemannSum
  -- Key lemma: Tendsto implies IsSt for ofSeq
  have hconv : Tendsto (fun n => standardRiemannSum f a b (n + 1)) atTop
               (𝓝 (∫ x in a..b, f x)) := riemannSum_tendsto_integral f a b hab hf
  have hIsSt : IsSt (ofSeq (fun n => standardRiemannSum f a b (n + 1))) (∫ x in a..b, f x) :=
    isSt_of_tendsto hconv
  exact hIsSt.st_eq

/-! ## Properties of Hyperfinite Sums

Basic algebraic properties. Since `ofSeq` is a ring homomorphism,
these follow directly from the definitions.
-/

/-- Linearity: hyperfinite sum of sum equals sum of hyperfinite sums -/
theorem hyperfiniteRiemannSum_add (f g : ℝ → ℝ) (a b : ℝ) :
    hyperfiniteRiemannSum (f + g) a b =
    hyperfiniteRiemannSum f a b + hyperfiniteRiemannSum g a b := by
  unfold hyperfiniteRiemannSum
  -- ofSeq is additive: ofSeq (s + t) = ofSeq s + ofSeq t
  -- This is definitional via the Germ addition
  congr 1
  ext n
  simp only [Pi.add_apply, standardRiemannSum]
  -- n + 1 ≠ 0 always
  have h : n + 1 ≠ 0 := Nat.succ_ne_zero n
  simp only [h, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext i
  ring

/-- Scalar multiplication -/
theorem hyperfiniteRiemannSum_smul (c : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
    hyperfiniteRiemannSum (fun x => c * f x) a b =
    (c : ℝ*) * hyperfiniteRiemannSum f a b := by
  unfold hyperfiniteRiemannSum
  -- Need: ofSeq (c * s) = c * ofSeq s
  -- This follows from the ring structure
  have h : ofSeq (fun n => standardRiemannSum (fun x => c * f x) a b (n + 1)) =
           ofSeq (fun n => c * standardRiemannSum f a b (n + 1)) := by
    congr 1
    ext n
    simp only [standardRiemannSum]
    -- n + 1 ≠ 0 always
    have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simp only [hn, ↓reduceIte]
    rw [Finset.mul_sum]
    congr 1
    ext i
    ring
  rw [h]
  -- ofSeq (fun n => c * s n) = c * ofSeq s
  rfl  -- This is definitional

/-! ## Hyperfinite Mesh Size

When working with the hyperfinite partition, the mesh size is infinitesimal.
-/

/-- The hyperfinite mesh size as a function of n -/
noncomputable def meshSeq (a b : ℝ) (n : ℕ) : ℝ := (b - a) / (n + 1)

/-- The hyperfinite mesh size -/
noncomputable def hyperfiniteMesh (a b : ℝ) : ℝ* := ofSeq (meshSeq a b)

/-- The hyperfinite mesh is infinitesimal when a < b -/
theorem hyperfiniteMesh_infinitesimal (a b : ℝ) (hab : a < b) :
    Infinitesimal (hyperfiniteMesh a b) := by
  unfold hyperfiniteMesh meshSeq Infinitesimal
  -- Need: IsSt (ofSeq (fun n => (b-a)/(n+1))) 0
  -- Use isSt_of_tendsto with the limit being 0
  apply isSt_of_tendsto
  exact mesh_tendsto_zero a b hab

/-! ## Hyperfinite Stochastic Sums

For stochastic integrals, we need sums where the integrand depends
on the random walk value.
-/

/-- A standard stochastic sum: Σᵢ Hᵢ · ΔWᵢ where ΔWᵢ = ±dx -/
noncomputable def standardStochasticSum
    (H : ℕ → ℝ)  -- Integrand values
    (flips : ℕ → ℝ)  -- Coin flips (±1)
    (dx : ℝ)  -- Space step
    (k : ℕ) : ℝ :=
  ∑ i : Fin k, H i * flips i * dx

/-- The Itô isometry at the discrete level:
    E[Σ(HΔW)²] = Σ H² · dt when flips are ±1 -/
theorem standardStochasticSum_sq_eq
    (H : ℕ → ℝ) (flips : ℕ → ℝ) (dx : ℝ) (k : ℕ)
    (hflips : ∀ i, (flips i)^2 = 1) :
    ∑ i : Fin k, (H i * flips i * dx)^2 =
    dx^2 * ∑ i : Fin k, (H i)^2 := by
  rw [Finset.mul_sum]
  congr 1
  ext i
  have h : (H i * flips i * dx)^2 = (H i)^2 * (flips i)^2 * dx^2 := by ring
  rw [h, hflips i, mul_one]
  ring

/-- Hyperfinite stochastic sum for hyperreal values -/
noncomputable def hyperfiniteStochasticSum
    (H : ℕ → ℝ*)  -- Integrand (hyperreal-valued)
    (flips : ℕ → ℝ*)  -- Coin flips (±1)
    (dx : ℝ*)  -- Space step
    (k : ℕ) : ℝ* :=
  ∑ i : Fin k, H i * flips i * dx

/-- When each flip squares to 1, the sum of squared increments simplifies -/
theorem hyperfiniteStochasticSum_sq_variation
    (H : ℕ → ℝ*) (flips : ℕ → ℝ*) (dx : ℝ*) (k : ℕ)
    (hflips : ∀ i, (flips i)^2 = 1) :
    ∑ i : Fin k, (H i * flips i * dx)^2 =
    dx^2 * ∑ i : Fin k, (H i)^2 := by
  rw [Finset.mul_sum]
  congr 1
  ext i
  have h : (H i * flips i * dx)^2 = (H i)^2 * (flips i)^2 * dx^2 := by ring
  rw [h, hflips i, mul_one]
  ring

/-! ## Lifting Standard Functions to Hyperreals

To evaluate f at hyperreal points, we need to lift standard functions.
For a standard function f : ℝ → ℝ, we define f* : ℝ* → ℝ* by
f*(ofSeq s) = ofSeq (f ∘ s).
-/

/-- Lift a standard function to hyperreals -/
noncomputable def liftFun (f : ℝ → ℝ) : ℝ* → ℝ* :=
  Germ.map f

/-- The lift agrees with f on standard reals -/
theorem liftFun_coe (f : ℝ → ℝ) (r : ℝ) : liftFun f r = f r := rfl

/-- The lift of ofSeq is ofSeq of composition -/
theorem liftFun_ofSeq (f : ℝ → ℝ) (s : ℕ → ℝ) :
    liftFun f (ofSeq s) = ofSeq (f ∘ s) := rfl

/-- Continuous functions preserve infinitesimals at standard points -/
theorem liftFun_continuous_at (f : ℝ → ℝ) (r : ℝ) (hf : ContinuousAt f r)
    (x : ℝ*) (hx : IsSt x r) :
    IsSt (liftFun f x) (f r) :=
  hx.map hf

end SPDE.Nonstandard.Integration
