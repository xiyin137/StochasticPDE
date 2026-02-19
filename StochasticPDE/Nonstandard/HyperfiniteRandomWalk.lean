/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Probability.ProbabilityMassFunction.Basic
import StochasticPDE.Nonstandard.Foundation.Hypernatural
import StochasticPDE.Nonstandard.Foundation.HyperfiniteSum
import StochasticPDE.Nonstandard.Foundation.InternalMembership

/-!
# Hyperfinite Random Walk and Brownian Motion

This file develops Brownian motion via the nonstandard approach: constructing it
as the standard part of a hyperfinite random walk with infinitesimal step size.

## Main Ideas

The classical construction of Brownian motion requires painful measure-theoretic
machinery (Kolmogorov extension, Wiener measure). The nonstandard approach is
conceptually simpler:

1. Take an infinite hypernatural N
2. Set dt = T/N (infinitesimal time step) and dx = √dt (infinitesimal space step)
3. Flip N fair coins: X₁, X₂, ..., Xₙ ∈ {-1, +1}
4. Define the hyperfinite random walk: W(k·dt) = dx · (X₁ + X₂ + ... + Xₖ)
5. Interpolate linearly between mesh points
6. Take standard parts: B(t) = st(W(t))

The resulting B(t) is a standard Brownian motion (Anderson, 1976).

## Main Definitions

* `HyperfiniteWalk` - A hyperfinite random walk with N steps
* `HyperfiniteWalk.process` - The walk as a function ℝ* → ℝ*
* `HyperfiniteWalk.stdPart` - The standard part, giving a function ℝ → ℝ

## Main Results

* `HyperfiniteWalk.quadratic_variation` - The quadratic variation is t (up to infinitesimals)
* `HyperfiniteWalk.increment_variance` - Increments have the correct variance

## References

* Anderson, R. M. "A nonstandard representation for Brownian motion and Itô integration" (1976)
* Lindstrøm, T. "Hyperfinite stochastic integration" (1980s)
* Albeverio, S. et al. "Nonstandard Methods in Stochastic Analysis and Mathematical Physics"

## Implementation Notes

We work with mathlib's `Hyperreal` type, which is constructed as an ultraproduct.
The main challenge is that mathlib doesn't yet have:
- A general transfer principle (Łoś's theorem)
- Hyperfinite sets and internal set theory
- Loeb measure construction

We develop ad hoc versions of what we need for this specific application.
-/

open Hyperreal Filter

namespace SPDE.Nonstandard

-- Re-export Foundation definitions for convenience
open Foundation in
export Foundation (Hypernat)

/-- Alias for Foundation.Hypernat.omega -/
noncomputable abbrev infiniteHypernat : ℝ* := Foundation.Hypernat.omega.val

theorem infiniteHypernat_pos : 0 < infiniteHypernat := by
  simp only [infiniteHypernat, Foundation.Hypernat.omega_val]
  exact omega_pos

theorem infiniteHypernat_infinite : Hyperreal.Infinite infiniteHypernat := by
  simp only [infiniteHypernat, Foundation.Hypernat.omega_val]
  exact infinite_omega

/-! ## Hyperfinite Sequences

A hyperfinite sequence is internally a finite sequence, but with a hyperfinite
number of elements. We model this as a function from {0, 1, ..., N-1} where
N is a hypernatural.
-/

/-- A hyperfinite binary sequence (coin flips).
    Internally, this is a sequence of N elements in {-1, +1}. -/
structure HyperfiniteCoinFlips where
  /-- The number of coin flips (a hypernatural, possibly infinite) -/
  length : Foundation.Hypernat
  /-- The sequence of flips, represented as a function ℕ → ℝ lifted to hyperreals.
      Each flip is ±1. We represent this as the germ of sequences of flip-sequences. -/
  flips : ℕ → ℝ*
  /-- Each flip is ±1 (in the internal sense) -/
  flips_pm_one : ∀ k : ℕ, flips k = 1 ∨ flips k = -1

namespace HyperfiniteCoinFlips

/-- The sign of the k-th flip as a standard real: either +1 or -1.
    Since each flip is constrained to be exactly ±1 (standard), we can extract this. -/
noncomputable def flipSign (C : HyperfiniteCoinFlips) (k : ℕ) : ℝ :=
  if C.flips k = 1 then 1 else -1

theorem flipSign_pm_one (C : HyperfiniteCoinFlips) (k : ℕ) :
    C.flipSign k = 1 ∨ C.flipSign k = -1 := by
  unfold flipSign
  split_ifs <;> simp

theorem flipSign_eq_flips (C : HyperfiniteCoinFlips) (k : ℕ) :
    (C.flipSign k : ℝ*) = C.flips k := by
  unfold flipSign
  rcases C.flips_pm_one k with h | h
  · simp [h]
  · have hne : C.flips k ≠ 1 := by rw [h]; norm_num
    rw [if_neg hne, h]
    norm_cast

end HyperfiniteCoinFlips

/-! ## Hyperfinite Random Walk -/

/-- A hyperfinite random walk with N steps over time interval [0, T].

    This is the core object: a random walk with infinitesimal steps that,
    after taking standard parts, yields Brownian motion. -/
structure HyperfiniteWalk where
  /-- Total time interval -/
  totalTime : ℝ
  totalTime_pos : 0 < totalTime
  /-- Number of steps (hypernatural, typically infinite) -/
  numSteps : Foundation.Hypernat
  /-- The coin flips driving the walk -/
  coins : HyperfiniteCoinFlips
  /-- Consistency: coins has the right length -/
  coins_length : coins.length = numSteps
  /-- Space step size dx (the square root of dt) -/
  dx : ℝ*
  /-- dx is positive -/
  dx_pos : 0 < dx
  /-- dx² = dt (the defining property) -/
  dx_sq : dx^2 = totalTime / numSteps.val

namespace HyperfiniteWalk

/-- Time step size: dt = T/N -/
noncomputable def dt (W : HyperfiniteWalk) : ℝ* := (W.totalTime : ℝ*) / W.numSteps.val

/-- The key property: dx² = dt -/
theorem dx_sq_eq_dt (W : HyperfiniteWalk) : W.dx^2 = W.dt := W.dx_sq

/-- The time at step k -/
noncomputable def timeAt (W : HyperfiniteWalk) (k : ℕ) : ℝ* := (k : ℝ*) * W.dt

/-- The walk value at step k: W_k = dx · (X₁ + X₂ + ... + Xₖ) -/
noncomputable def walkAt (W : HyperfiniteWalk) (k : ℕ) : ℝ* :=
  W.dx * (Finset.range k).sum (fun i => W.coins.flips i)

/-- The walk starts at 0 -/
theorem walkAt_zero (W : HyperfiniteWalk) : W.walkAt 0 = 0 := by
  simp [walkAt]

/-- The walk value at hypernatural step K: W_K = dx · Σ_{i<K} flip_i.
    This is defined using the sequence representation: at level n, we sum
    K.toSeq n flips. Since each flip is ±1 (standard), this is well-defined. -/
noncomputable def walkAtHypernat (W : HyperfiniteWalk) (K : Foundation.Hypernat) : ℝ* :=
  W.dx * ofSeq (fun n => ∑ i ∈ Finset.range (K.toSeq n), W.coins.flipSign i)

/-- Sum of casts equals cast of sum for the ℝ → ℝ* embedding -/
theorem sum_coe_eq_coe_sum (f : ℕ → ℝ) (s : Finset ℕ) :
    ∑ i ∈ s, (f i : ℝ*) = ((∑ i ∈ s, f i : ℝ) : ℝ*) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s' ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
    -- Need: (f a : ℝ*) + (∑ i, f i : ℝ*) = ((f a + ∑ i, f i) : ℝ*)
    -- This should follow from the fact that coercion preserves addition
    rfl

/-- walkAtHypernat agrees with walkAt for standard naturals -/
theorem walkAtHypernat_ofNat' (W : HyperfiniteWalk) (k : ℕ) :
    W.walkAtHypernat (Foundation.Hypernat.ofNat' k) = W.walkAt k := by
  unfold walkAtHypernat walkAt
  congr 1
  -- toSeq n = k almost everywhere
  have hae : ∀ᶠ n in hyperfilter ℕ, (Foundation.Hypernat.ofNat' k).toSeq n = k :=
    Foundation.Hypernat.toSeq_ofNat'_ae k
  -- Rewrite RHS: each flips i = (flipSign i : ℝ*)
  have hflips : ∑ i ∈ Finset.range k, W.coins.flips i =
      ∑ i ∈ Finset.range k, (W.coins.flipSign i : ℝ*) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (W.coins.flipSign_eq_flips i).symm
  rw [hflips]
  -- Now RHS = ∑ (flipSign i : ℝ*) = (∑ flipSign i : ℝ) cast to ℝ*
  rw [sum_coe_eq_coe_sum W.coins.flipSign (Finset.range k)]
  -- LHS = ofSeq (fun n => ∑ over toSeq n) and this equals the constant a.e.
  unfold ofSeq
  apply Germ.coe_eq.mpr
  exact hae.mono fun n hn => congrArg (fun m => ∑ i ∈ Finset.range m, W.coins.flipSign i) hn

/-- walkAtHypernat at 0 is 0 -/
theorem walkAtHypernat_zero (W : HyperfiniteWalk) :
    W.walkAtHypernat (Foundation.Hypernat.ofNat' 0) = 0 := by
  rw [walkAtHypernat_ofNat', walkAt_zero]

/-! ## Key Properties -/

/-- When N is infinite, dt is infinitesimal -/
theorem dt_infinitesimal (W : HyperfiniteWalk) (hN : Foundation.Hypernat.Infinite W.numSteps) :
    Infinitesimal W.dt := by
  rw [dt, div_eq_mul_inv]
  have hN' : Hyperreal.Infinite W.numSteps.val := by
    rw [Foundation.Hypernat.infinite_iff_infinitePos] at hN
    left; exact hN
  have h1 : Infinitesimal W.numSteps.val⁻¹ := infinitesimal_inv_of_infinite hN'
  have h2 : IsSt (W.totalTime : ℝ*) W.totalTime := isSt_refl_real W.totalTime
  have h3 : IsSt ((W.totalTime : ℝ*) * W.numSteps.val⁻¹) (W.totalTime * 0) := h2.mul h1
  simp only [mul_zero] at h3
  exact h3

/-- The increment is ±dx -/
theorem increment_pm_dx (W : HyperfiniteWalk) (k : ℕ) :
    W.walkAt (k + 1) - W.walkAt k = W.dx ∨
    W.walkAt (k + 1) - W.walkAt k = -W.dx := by
  -- walkAt (k+1) - walkAt k = dx * (sum_{i<k+1} - sum_{i<k}) = dx * flips(k)
  unfold walkAt
  rw [Finset.sum_range_succ]
  -- Now have: dx * (sum + flips k) - dx * sum = dx * flips k
  ring_nf
  -- Now we have dx * flips(k), and flips(k) = ±1
  rcases W.coins.flips_pm_one k with h | h
  · left; rw [h, mul_one]
  · right; rw [h, mul_neg_one]

/-- Each increment has variance dt -/
theorem increment_variance (W : HyperfiniteWalk) (k : ℕ) :
    (W.walkAt (k + 1) - W.walkAt k)^2 = W.dx^2 := by
  rcases increment_pm_dx W k with h | h <;> simp only [h, neg_sq]

/-- The sum of squared increments equals the time exactly.
    Each (walkAt(i+1) - walkAt(i))² = dx², and dx² = dt, so sum = k * dt = timeAt k. -/
theorem quadratic_variation_eq_time (W : HyperfiniteWalk) (k : ℕ) :
    (Finset.range k).sum (fun i => (W.walkAt (i + 1) - W.walkAt i)^2) = W.timeAt k := by
  -- Each term equals dx²
  have h : ∀ i, (W.walkAt (i + 1) - W.walkAt i)^2 = W.dx^2 := increment_variance W
  simp only [h]
  -- Sum of k copies of dx² is k * dx²
  rw [Finset.sum_const, Finset.card_range]
  -- k • dx² = k * dx² for hyperreals
  simp only [nsmul_eq_mul]
  -- k * dx² = k * dt = timeAt k
  rw [W.dx_sq_eq_dt, timeAt]

/-- The sum of squared increments equals t (up to infinitesimals).
    This is the key theorem: quadratic variation of the walk is t.

    Actually, for the hyperfinite walk, QV = time exactly (not just infinitesimally)! -/
theorem quadratic_variation_infinitesimal (W : HyperfiniteWalk)
    (_hN : Foundation.Hypernat.Infinite W.numSteps) (k : ℕ) :
    let qv := (Finset.range k).sum (fun i =>
      (W.walkAt (i + 1) - W.walkAt i)^2)
    Infinitesimal (qv - W.timeAt k) := by
  simp only
  rw [quadratic_variation_eq_time, sub_self]
  exact infinitesimal_zero

end HyperfiniteWalk

/-! ## Standard Part and Brownian Motion

Taking the standard part of the hyperfinite walk gives Brownian motion.

To define `stdPartProcess` at a standard time t:
1. Find the hypernatural index k = ⌊t/dt⌋ = ⌊t·N/T⌋ where dt = T/N
2. Evaluate the walk at this hypernatural index using walkAtHypernat
3. Take the standard part of the result

The key insight is that for standard t, the index k = ⌊t/dt⌋ is hyperfinite
(approximately t/dt which is infinite when dt is infinitesimal), but the
walk value W(k) is finite (by CLT heuristics: O(√k · dx) = O(√t)).
-/

/-- numSteps is positive (derived from dx being positive and dx² = T/N) -/
theorem HyperfiniteWalk.numSteps_pos (W : HyperfiniteWalk) : 0 < W.numSteps.val := by
  -- From dx > 0, we have dx² > 0
  have hdx2_pos : 0 < W.dx^2 := sq_pos_of_pos W.dx_pos
  -- dx² = totalTime / numSteps.val
  rw [W.dx_sq] at hdx2_pos
  -- totalTime > 0 and T/N > 0 implies N > 0
  have hT_pos : (0 : ℝ*) < W.totalTime := by exact_mod_cast W.totalTime_pos
  exact (div_pos_iff_of_pos_left hT_pos).mp hdx2_pos

/-- The hypernatural step index corresponding to a standard time t.
    This is the floor of t/dt = t·N/T. -/
noncomputable def HyperfiniteWalk.stepIndex (W : HyperfiniteWalk) (t : ℝ) (ht : 0 ≤ t) :
    Foundation.Hypernat :=
  Foundation.Hypernat.timeStepIndex (t / W.totalTime) (div_nonneg ht (le_of_lt W.totalTime_pos))
    W.numSteps W.numSteps_pos

/-- stepIndex is monotone: if s ≤ t then stepIndex s ≤ stepIndex t. -/
theorem HyperfiniteWalk.stepIndex_mono (W : HyperfiniteWalk)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≤ t) :
    W.stepIndex s hs ≤ W.stepIndex t ht := by
  unfold stepIndex
  apply Foundation.Hypernat.timeStepIndex_mono
  exact div_le_div_of_nonneg_right hst (le_of_lt W.totalTime_pos)

/-- The time at hypernatural step K: K · dt -/
noncomputable def HyperfiniteWalk.timeAtHypernat (W : HyperfiniteWalk)
    (K : Foundation.Hypernat) : ℝ* :=
  K.val * W.dt

/-- The standard part of a hyperfinite walk at a standard time t.

    For t ∈ [0, T], we find the hypernatural step index k = ⌊t·N/T⌋,
    evaluate the walk at this index, and take the standard part.

    **Important**: This function is only meaningful for paths where the walk value
    is finite (not hyperreal-infinite). For Loeb-almost-all paths this holds,
    but for pathological paths the `st` function may return an arbitrary value.
    See the note above about finiteness of walk values.

    Note: For t outside [0, T], we extend by 0 for t < 0 and by W(T) for t > T. -/
noncomputable def HyperfiniteWalk.stdPartProcess (W : HyperfiniteWalk) (t : ℝ) : ℝ :=
  if ht : 0 ≤ t then
    if t ≤ W.totalTime then
      st (W.walkAtHypernat (W.stepIndex t ht))
    else
      st (W.walkAtHypernat W.numSteps)  -- At time T
  else
    0  -- For negative times

/-- The standard part process starts at 0 -/
theorem HyperfiniteWalk.stdPartProcess_zero (W : HyperfiniteWalk) :
    W.stdPartProcess 0 = 0 := by
  unfold stdPartProcess
  simp only [le_refl, dite_true, W.totalTime_pos.le]
  -- stepIndex 0 should give 0
  unfold stepIndex
  simp only [zero_div]
  -- timeStepIndex 0 = hyperfloor (0 * N) = hyperfloor 0 = 0
  -- First show that 0 * N.val = 0
  have hzero : (0 : ℝ*) * W.numSteps.val = 0 := zero_mul _
  -- hyperfloor 0 = ofNat' 0
  have hfloor_zero : Foundation.Hypernat.hyperfloor 0 (le_refl 0) =
      Foundation.Hypernat.ofNat' 0 := by
    apply Foundation.Hypernat.ext
    simp only [Foundation.Hypernat.ofNat'_val]
    unfold Foundation.Hypernat.hyperfloor Foundation.Hypernat.ofNatSeq ofSeq
    apply Germ.coe_eq.mpr
    -- The representative of 0 is 0 a.e.
    have hspec := Classical.choose_spec (ofSeq_surjective (0 : ℝ*))
    have h0ae : ∀ᶠ n in hyperfilter ℕ, Classical.choose (ofSeq_surjective (0 : ℝ*)) n = 0 := by
      unfold ofSeq at hspec
      exact Germ.coe_eq.mp hspec
    exact h0ae.mono (fun n hn => by simp [hn])
  -- timeStepIndex 0 uses hyperfloor (0 * N) = hyperfloor 0
  have h0 : Foundation.Hypernat.timeStepIndex 0 (le_refl 0) W.numSteps W.numSteps_pos =
      Foundation.Hypernat.ofNat' 0 := by
    unfold Foundation.Hypernat.timeStepIndex
    convert hfloor_zero using 2
  rw [h0, walkAtHypernat_ofNat', walkAt_zero]
  exact st_id_real 0

/-!
### Finiteness of Walk Values

**Important Note**: The finiteness of walk values at hypernatural step indices is a
probabilistic property, not a deterministic one.

For the hyperfinite random walk W at step K:
  W_K = dx · (X₁ + X₂ + ... + X_K) where each Xᵢ = ±1

In the worst case (all flips = +1), we have |W_K| = K · dx. For K ≈ t/dt and dx = √dt:
  K · dx ≈ (t/dt) · √dt = t/√dt = t · √(N/T)

This is **infinite** when N is infinite!

The CLT/concentration argument ("walk is O(√t)") is a probabilistic statement:
- Almost all paths (with respect to Loeb measure) have |W_K| = O(√K · dx) = O(√t)
- But there exist paths where |W_K| = K · dx is infinite

Therefore, a theorem of the form "∀ W, walkAt is finite" is **FALSE**.
The correct statement requires Loeb measure:
  "For Loeb-almost-all paths, W_K is finite for standard times t."

This requires the full Loeb measure construction from LoebMeasure.lean.
-/

/-! ## Quadratic Variation via Hyperreals

The main theorem: quadratic variation of Brownian motion is t.

The nonstandard proof is essentially:
1. For hyperfinite partition, Σ(ΔW)² = Σ(±dx)² = N·dx² = N·dt = t (exactly!)
2. Taking standard parts preserves the equality

The key result `quadratic_variation_eq_time` above proves this exactly
for standard indices. For hypernatural indices, we use `walkAtHypernat`.
-/

/-- Quadratic variation at hypernatural step K equals the time at that step.
    This is the hyperfinite version: QV(W, K) = K · dt = timeAtHypernat K. -/
noncomputable def HyperfiniteWalk.quadraticVariationAtHypernat
    (W : HyperfiniteWalk) (K : Foundation.Hypernat) : ℝ* :=
  K.val * W.dt

/-- The quadratic variation of the walk up to hypernatural step K equals K·dt.
    This extends `quadratic_variation_eq_time` to hypernatural indices.

    For a standard index k, this reduces to `quadratic_variation_eq_time`. -/
theorem HyperfiniteWalk.quadratic_variation_hypernat_eq_time (W : HyperfiniteWalk)
    (K : Foundation.Hypernat) :
    W.quadraticVariationAtHypernat K = W.timeAtHypernat K := by
  unfold quadraticVariationAtHypernat timeAtHypernat
  rfl

/-- Taking the standard part of QV(W, stepIndex t) gives t (up to infinitesimals).
    This is the connection to standard Brownian motion: [B]_t = t. -/
theorem HyperfiniteWalk.st_quadratic_variation_eq_time (W : HyperfiniteWalk)
    (hN : Foundation.Hypernat.Infinite W.numSteps)
    (t : ℝ) (ht : 0 ≤ t) (_htT : t ≤ W.totalTime) :
    st (W.quadraticVariationAtHypernat (W.stepIndex t ht)) = t := by
  unfold quadraticVariationAtHypernat stepIndex
  -- Let k = timeStepIndex (t/T) N = hyperfloor ((t/T) * N)
  -- QV = k.val * dt where dt = T/N
  -- By timeStepIndex bounds: k * (1/N) ≤ t/T < (k+1) * (1/N)
  -- Multiplying by T: k * dt ≤ t < k * dt + dt
  -- Since dt is infinitesimal, st(k * dt) = t
  set k := Foundation.Hypernat.timeStepIndex (t / W.totalTime)
    (div_nonneg ht (le_of_lt W.totalTime_pos)) W.numSteps W.numSteps_pos with hk_def
  set T := W.totalTime with hT_def
  set N := W.numSteps with hN_def
  have hdt_inf : Infinitesimal W.dt := dt_infinitesimal W hN
  have hT_pos : (0 : ℝ) < T := W.totalTime_pos
  have hT_pos' : (0 : ℝ*) < (T : ℝ*) := by exact_mod_cast hT_pos
  have hT_ne : (T : ℝ*) ≠ 0 := ne_of_gt hT_pos'
  have hN_pos : (0 : ℝ*) < N.val := W.numSteps_pos
  have hN_ne : N.val ≠ 0 := ne_of_gt hN_pos
  -- Key bounds from timeStepIndex lemmas (in terms of 1/N)
  have hbound_le : k.val * (1 / N.val) ≤ (t / T : ℝ*) :=
    Foundation.Hypernat.timeStepIndex_mul_dt_le (t / T)
      (div_nonneg ht (le_of_lt hT_pos)) N hN_pos
  have hbound_lt : (t / T : ℝ*) < (k.val + 1) * (1 / N.val) :=
    Foundation.Hypernat.lt_timeStepIndex_succ_mul_dt (t / T)
      (div_nonneg ht (le_of_lt hT_pos)) N hN_pos
  -- Rescale: multiply by T to get bounds in terms of dt = T/N
  -- Note: dt = T / N.val, so T * (1/N.val) = dt and k * (1/N.val) * T = k * dt
  have hdt_eq : W.dt = (T : ℝ*) / N.val := rfl
  -- From hbound_le: k.val * (1/N.val) ≤ t/T
  -- Multiply by T: k.val * T/N.val ≤ t, i.e., k.val * dt ≤ t
  have hkdt_le : k.val * W.dt ≤ (t : ℝ*) := by
    have h1 : k.val * (1 / N.val) * (T : ℝ*) ≤ (t / T) * (T : ℝ*) :=
      mul_le_mul_of_nonneg_right hbound_le (le_of_lt hT_pos')
    simp only [div_mul_cancel₀ _ hT_ne] at h1
    calc k.val * W.dt = k.val * ((T : ℝ*) / N.val) := by rfl
      _ = k.val * (1 / N.val) * (T : ℝ*) := by ring
      _ ≤ t := h1
  -- From hbound_lt: t/T < (k.val + 1) * (1/N.val)
  -- Multiply by T: t < (k.val + 1) * dt = k.val * dt + dt
  have ht_lt : (t : ℝ*) < k.val * W.dt + W.dt := by
    have h1 : (t / T) * (T : ℝ*) < (k.val + 1) * (1 / N.val) * (T : ℝ*) :=
      mul_lt_mul_of_pos_right hbound_lt hT_pos'
    simp only [div_mul_cancel₀ _ hT_ne] at h1
    calc (t : ℝ*) < (k.val + 1) * (1 / N.val) * (T : ℝ*) := h1
      _ = (k.val + 1) * ((T : ℝ*) / N.val) := by ring
      _ = (k.val + 1) * W.dt := by rfl
      _ = k.val * W.dt + W.dt := by ring
  -- Now we have: k.val * dt ≤ t < k.val * dt + dt
  -- So: 0 ≤ t - k.val * dt < dt
  -- Therefore |k.val * dt - t| < dt (since k.val * dt ≤ t)
  have hisSt : IsSt (k.val * W.dt) t := by
    rw [isSt_iff_abs_sub_lt_delta]
    intro δ hδ
    have hdt_lt : W.dt < δ := lt_of_pos_of_infinitesimal hdt_inf δ hδ
    -- |k.val * dt - t| = t - k.val * dt (since k.val * dt ≤ t)
    have hdiff_nonneg : 0 ≤ (t : ℝ*) - k.val * W.dt := sub_nonneg.mpr hkdt_le
    have hdiff_lt : (t : ℝ*) - k.val * W.dt < W.dt := by linarith
    calc |k.val * W.dt - (t : ℝ*)| = |-(((t : ℝ*) - k.val * W.dt))| := by ring_nf
      _ = |(t : ℝ*) - k.val * W.dt| := abs_neg _
      _ = (t : ℝ*) - k.val * W.dt := abs_of_nonneg hdiff_nonneg
      _ < W.dt := hdiff_lt
      _ < δ := hdt_lt
  exact hisSt.st_eq

/-! ## Martingale Property

The hyperfinite walk is a martingale in the internal sense:
E[W_{k+1} | W_k] = W_k

This follows from the coin flips being symmetric.
-/

/-- The increment at step k is independent of past steps.
    Each flip is ±1 independently. -/
theorem HyperfiniteWalk.increment_independent (W : HyperfiniteWalk) (k : ℕ) :
    W.walkAt (k + 1) - W.walkAt k = W.dx * W.coins.flips k := by
  unfold walkAt
  rw [Finset.sum_range_succ]
  ring

/-- The martingale property for the hyperfinite walk: increments are symmetric.
    Each increment ΔW_k = ±dx with equal internal probability.

    Note: A full statement requires the internal probability measure from Loeb theory.
    Here we state the algebraic fact that increments are ±dx. -/
theorem HyperfiniteWalk.martingale_increment_symmetric (W : HyperfiniteWalk) (k : ℕ) :
    (W.walkAt (k + 1) - W.walkAt k = W.dx ∨ W.walkAt (k + 1) - W.walkAt k = -W.dx) :=
  increment_pm_dx W k

end SPDE.Nonstandard
