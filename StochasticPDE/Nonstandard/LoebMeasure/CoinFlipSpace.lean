/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.InternalProbSpace
import StochasticPDE.Nonstandard.Foundation.Hypernatural
import Mathlib.Data.Real.Sqrt

/-!
# Coin Flip Spaces and Hyperfinite Path Spaces

This file defines the coin flip probability space and hyperfinite path spaces.

## Main Definitions

* `hyperPow2Seq` - Hyperreal exponentiation 2^N for sequence-defined N
* `coinFlipSpaceHypernat` - The coin flip space with 2^N outcomes
* `HyperfinitePathSpace` - Path space for hyperfinite random walks

## Main Results

* `hyperPow2Seq_pos` - 2^N is positive
* `hyperPow2Seq_infinite` - 2^N is infinite when N is infinite
* `dt_infinitesimal` - Time step is infinitesimal for infinite N
* `path_prob_infinitesimal` - Individual paths have infinitesimal probability

## References

* Anderson, R. M. "A nonstandard representation for Brownian motion" (1976)
-/

open Hyperreal Filter

namespace SPDE.Nonstandard

/-! ## Hyperreal Exponentiation -/

/-- Hyperreal exponentiation: 2^n for sequence-defined hyperreals.
    For a hyperreal N = ofSeq f, we define 2^N = ofSeq (2^(f n)).
    This requires N to be a hypernatural (from a sequence of naturals). -/
noncomputable def hyperPow2Seq (f : ℕ → ℕ) : ℝ* :=
  ofSeq (fun n => (2 : ℝ)^(f n))

/-- 2^N is positive for any sequence -/
theorem hyperPow2Seq_pos (f : ℕ → ℕ) : 0 < hyperPow2Seq f := by
  have h : ∀ n, (0 : ℝ) < 2^(f n) := fun n => pow_pos (by norm_num : (0 : ℝ) < 2) (f n)
  exact ofSeq_lt_ofSeq.mpr (Eventually.of_forall h)

/-- 2^N is infinite when N → ∞.
    The key idea: 2^(f n) → ∞ as f n → ∞, so 2^(f n) > M for almost all n. -/
theorem hyperPow2Seq_infinite (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) :
    Infinite (hyperPow2Seq f) := by
  left  -- Show InfinitePos
  intro M
  have hev : ∀ᶠ n in atTop, M < (2 : ℝ)^(f n) := by
    have h2pow : Tendsto (fun n => (2 : ℝ)^(f n)) atTop atTop := by
      have hbase : Tendsto (fun k : ℕ => (2 : ℝ)^k) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
      exact hbase.comp hf
    exact h2pow.eventually_gt_atTop M
  rw [eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  have hcofin : {n | M < (2 : ℝ)^(f n)} ∈ cofinite := by
    rw [mem_cofinite]
    refine (Set.finite_lt_nat N₀).subset ?_
    intro n hn
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hn
    simp only [Set.mem_setOf_eq]
    -- hn : 2^(f n) ≤ M, need to show n < N₀
    -- From hN₀: ∀ n ≥ N₀, M < 2^(f n), contrapositive gives n < N₀
    by_contra h_ge
    push_neg at h_ge  -- h_ge : N₀ ≤ n
    exact absurd (hN₀ n h_ge) (not_lt.mpr hn)
  have hmem : {n | M < (2 : ℝ)^(f n)} ∈ (hyperfilter ℕ : Filter ℕ) :=
    mem_hyperfilter_of_finite_compl (by simpa using hcofin)
  apply ofSeq_lt_ofSeq.mpr
  exact hmem

/-- 2^N is infinite when N is an infinite hypernatural -/
theorem hyperPow2Seq_infinite_of_hypernat (N : Foundation.Hypernat)
    (hNinf : Foundation.Hypernat.Infinite N) :
    Infinite (hyperPow2Seq N.toSeq) := by
  -- Show positive infinite
  left
  intro M
  -- For any bound M, we need {n | M < 2^(N.toSeq n)} ∈ hyperfilter
  -- First find K such that 2^K > M
  have hlogM : ∃ K : ℕ, (M : ℝ) < 2^K := by
    -- 2^n → ∞ as n → ∞, so eventually exceeds M
    have htend : Tendsto (fun n : ℕ => (2 : ℝ)^n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    rw [tendsto_atTop_atTop] at htend
    obtain ⟨K, hK⟩ := htend (M + 1)
    use K
    calc M < M + 1 := lt_add_one M
      _ ≤ 2^K := hK K (le_refl K)
  obtain ⟨K, hK⟩ := hlogM
  -- Since N is infinite, K < N.toSeq n almost everywhere
  have hev : ∀ᶠ n in hyperfilter ℕ, K < N.toSeq n :=
    Foundation.Hypernat.toSeq_eventually_gt_of_infinite N hNinf K
  -- This implies 2^K ≤ 2^(N.toSeq n) almost everywhere
  have hev2 : ∀ᶠ n in hyperfilter ℕ, M < (2 : ℝ)^(N.toSeq n) := by
    apply hev.mono
    intro n hKn
    calc (M : ℝ) < 2^K := hK
      _ ≤ 2^(N.toSeq n) := by
          have h : (2 : ℕ)^K ≤ 2^(N.toSeq n) :=
            Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_lt hKn)
          exact_mod_cast h
  -- Convert to ofSeq form
  apply ofSeq_lt_ofSeq.mpr
  exact hev2

/-! ## Coin Flip Space -/

/-- The internal probability space of N coin flips.
    Uses hyperPow2Seq to properly compute 2^N from the underlying sequence. -/
noncomputable def coinFlipSpace (f : ℕ → ℕ) : InternalProbSpace where
  size := hyperPow2Seq f
  size_pos := hyperPow2Seq_pos f

/-- The coin flip space with 2^N outcomes -/
noncomputable def coinFlipSpaceHypernat (N : Foundation.Hypernat) : InternalProbSpace where
  size := hyperPow2Seq N.toSeq
  size_pos := hyperPow2Seq_pos N.toSeq

/-- For a random walk with N steps, the probability space has 2^N outcomes -/
noncomputable def walkProbSpace (N : Foundation.Hypernat) : InternalProbSpace :=
  coinFlipSpaceHypernat N

/-- The probability of a single path is 1/2^N -/
theorem singlePath_prob (N : Foundation.Hypernat) :
    (walkProbSpace N).prob 1 = 1 / (walkProbSpace N).size := by
  unfold walkProbSpace coinFlipSpaceHypernat InternalProbSpace.prob
  simp

/-- When N is infinite, individual paths have infinitesimal probability -/
theorem singlePath_infinitesimal (N : Foundation.Hypernat) (hNinf : Foundation.Hypernat.Infinite N) :
    Infinitesimal ((walkProbSpace N).prob 1) := by
  rw [singlePath_prob N, one_div]
  have hsize : Infinite (walkProbSpace N).size := by
    unfold walkProbSpace coinFlipSpaceHypernat
    simp only
    exact hyperPow2Seq_infinite_of_hypernat N hNinf
  exact infinitesimal_inv_of_infinite hsize

/-! ## Hyperfinite Path Space -/

/-- The hyperfinite path space: sequences of N coin flips -/
structure HyperfinitePathSpace where
  /-- The number of steps as a hypernatural -/
  numSteps : Foundation.Hypernat
  /-- The number of steps is infinite -/
  numSteps_infinite : Foundation.Hypernat.Infinite numSteps

namespace HyperfinitePathSpace

/-- The underlying probability space of a hyperfinite path space -/
noncomputable def probSpace (Ω : HyperfinitePathSpace) : InternalProbSpace :=
  walkProbSpace Ω.numSteps

/-- The time step dt = T/N for unit time interval T = 1 -/
noncomputable def dt (Ω : HyperfinitePathSpace) : ℝ* := 1 / Ω.numSteps.val

/-- The space step dx = √dt.
    We store dx as a hyperreal satisfying dx² = dt. -/
structure SqrtData (Ω : HyperfinitePathSpace) where
  /-- The value of √dt -/
  dx : ℝ*
  /-- The defining property: dx² = dt -/
  dx_sq : dx ^ 2 = Ω.dt
  /-- dx is positive -/
  dx_pos : 0 < dx

/-! ### Hyperreal Square Root

The Hyperreal type `ℝ*` is defined as `Germ (hyperfilter ℕ) ℝ`, where operations are pointwise:
- `ofSeq f * ofSeq g = ofSeq (f * g)` (definitional by Germ structure)
- `(ofSeq f)⁻¹ = ofSeq f⁻¹` when f is eventually nonzero

For positive hyperreals, the square root is well-defined via the sequence representation:
if `x = ofSeq f` with `f n > 0` for all n, then `√x = ofSeq (√f)` satisfies `(√x)² = x`.
-/

/-- For sequences that are eventually equal, their ofSeq values are equal.
    This is fundamental: Germ equality is equivalence modulo the filter. -/
theorem ofSeq_congr {f g : ℕ → ℝ} (h : ∀ᶠ n in hyperfilter ℕ, f n = g n) :
    ofSeq f = ofSeq g := by
  -- ofSeq is the coercion to Germ, and Germ equality is Filter.EventuallyEq
  exact Quotient.sound h

/-- For a sequence with eventually positive terms, the sqrt sequence squares to it.
    This is the key lemma: (ofSeq(√f))² = ofSeq(f) when f > 0 eventually.

    We define √f(n) = Real.sqrt (max 0 (f n)) to handle non-positive values,
    but when f n > 0 eventually, this equals ofSeq f. -/
theorem hyperrealSqrt_sq_eventually (f : ℕ → ℝ) (hpos : ∀ᶠ n in hyperfilter ℕ, 0 < f n) :
    (ofSeq (fun n => Real.sqrt (max 0 (f n))))^2 = ofSeq f := by
  -- For n where f n > 0: max 0 (f n) = f n, so √(max 0 (f n)) = √(f n)
  -- and √(f n)² = f n
  have hsqrt_sq : ∀ᶠ n in hyperfilter ℕ, Real.sqrt (max 0 (f n)) * Real.sqrt (max 0 (f n)) = f n := by
    apply hpos.mono
    intro n hn
    have hle : 0 ≤ f n := le_of_lt hn
    simp only [max_eq_right hle]
    exact Real.mul_self_sqrt hle
  -- sq = self * self
  rw [sq]
  -- Germ multiplication is pointwise
  have hmul : (ofSeq fun n => Real.sqrt (max 0 (f n))) * (ofSeq fun n => Real.sqrt (max 0 (f n))) =
              ofSeq (fun n => Real.sqrt (max 0 (f n)) * Real.sqrt (max 0 (f n))) := rfl
  rw [hmul]
  -- Use eventual equality
  exact ofSeq_congr hsqrt_sq

/-- For a sequence with eventually positive terms, the sqrt sequence is positive. -/
theorem hyperrealSqrt_pos_eventually (f : ℕ → ℝ) (hpos : ∀ᶠ n in hyperfilter ℕ, 0 < f n) :
    0 < ofSeq (fun n => Real.sqrt (max 0 (f n))) := by
  have h : ∀ᶠ n in hyperfilter ℕ, (0 : ℝ) < Real.sqrt (max 0 (f n)) := by
    apply hpos.mono
    intro n hn
    have hle : 0 ≤ f n := le_of_lt hn
    simp only [max_eq_right hle]
    exact Real.sqrt_pos_of_pos hn
  exact ofSeq_lt_ofSeq.mpr h

/-- For an infinite hypernatural N, toSeq n > 0 eventually.
    Since N is infinite, N.val > 1, so by ofSeq_toSeq and ofSeq_lt_ofSeq,
    toSeq n > 1 (hence > 0) for almost all n in the hyperfilter sense. -/
theorem Hypernat_toSeq_eventually_pos (N : Foundation.Hypernat)
    (hN : Foundation.Hypernat.Infinite N) :
    ∀ᶠ n in hyperfilter ℕ, 0 < N.toSeq n := by
  -- Infinite N means N.val > any standard real, in particular > 1
  rw [Foundation.Hypernat.infinite_iff_infinitePos] at hN
  have h1 : (1 : ℝ*) < N.val := hN 1
  -- N.val = ofSeq (fun n => (N.toSeq n : ℝ)) by ofSeq_toSeq
  rw [← Foundation.Hypernat.ofSeq_toSeq N] at h1
  -- Convert 1 to ofSeq form: (1 : ℝ*) = ofSeq (fun _ => 1)
  have hone : (1 : ℝ*) = ofSeq (fun _ => (1 : ℝ)) := rfl
  rw [hone] at h1
  -- By ofSeq_lt_ofSeq, this means toSeq n > 1 eventually
  rw [ofSeq_lt_ofSeq] at h1
  -- toSeq n > 1 implies toSeq n > 0
  apply h1.mono
  intro n hn
  -- hn : 1 < (N.toSeq n : ℝ)
  -- Need: 0 < N.toSeq n
  have hcast : (1 : ℝ) < (N.toSeq n : ℝ) := hn
  have hnat : 1 < N.toSeq n := by exact_mod_cast hcast
  omega

/-- Square root data exists for any hyperfinite path space.
    The construction: dt = 1/N, dx = ofSeq(√(1/N.toSeq n)), then dx² = dt and dx > 0.

    This proves that the hyperfinite random walk structure can actually be instantiated. -/
noncomputable def SqrtData.mk' (Ω : HyperfinitePathSpace) : SqrtData Ω where
  dx := ofSeq (fun n => Real.sqrt (max 0 (1 / Ω.numSteps.toSeq n)))
  dx_sq := by
    -- Step 1: toSeq is eventually positive for infinite numSteps
    have htoSeq_ev_pos : ∀ᶠ n in hyperfilter ℕ, 0 < Ω.numSteps.toSeq n :=
      Hypernat_toSeq_eventually_pos Ω.numSteps Ω.numSteps_infinite
    -- Step 2: 1/toSeq is eventually positive
    have hdiv_ev_pos : ∀ᶠ n in hyperfilter ℕ, 0 < (1 : ℝ) / Ω.numSteps.toSeq n := by
      apply htoSeq_ev_pos.mono
      intro n hn
      exact div_pos one_pos (Nat.cast_pos.mpr hn)
    -- Step 3: Use hyperrealSqrt_sq_eventually
    have hsq := hyperrealSqrt_sq_eventually (fun n => 1 / Ω.numSteps.toSeq n) hdiv_ev_pos
    -- Step 4: Show ofSeq(1/toSeq) = dt = 1/numSteps.val
    unfold dt
    rw [one_div]
    have hval : Ω.numSteps.val = ofSeq (fun n => (Ω.numSteps.toSeq n : ℝ)) :=
      (Foundation.Hypernat.ofSeq_toSeq Ω.numSteps).symm
    rw [hval]
    -- Step 5: Show (ofSeq f)⁻¹ = ofSeq(f⁻¹) eventually
    have hne : ∀ᶠ n in hyperfilter ℕ, (Ω.numSteps.toSeq n : ℝ) ≠ 0 := by
      apply htoSeq_ev_pos.mono
      intro n hn
      exact ne_of_gt (Nat.cast_pos.mpr hn)
    -- Germ inverse: (↑f)⁻¹ = ↑(f⁻¹) definitionally
    have hinv : (ofSeq (fun n => (Ω.numSteps.toSeq n : ℝ)))⁻¹ =
                ofSeq (fun n => (Ω.numSteps.toSeq n : ℝ)⁻¹) := rfl
    rw [hinv]
    -- Step 6: 1/x = x⁻¹, so ofSeq(1/f) = ofSeq(f⁻¹)
    have hdiv_eq : ∀ᶠ n in hyperfilter ℕ, (1 : ℝ) / Ω.numSteps.toSeq n = (Ω.numSteps.toSeq n : ℝ)⁻¹ := by
      apply Eventually.of_forall
      intro n
      ring
    rw [← ofSeq_congr hdiv_eq, ← hsq]
  dx_pos := by
    have htoSeq_ev_pos : ∀ᶠ n in hyperfilter ℕ, 0 < Ω.numSteps.toSeq n :=
      Hypernat_toSeq_eventually_pos Ω.numSteps Ω.numSteps_infinite
    have hdiv_ev_pos : ∀ᶠ n in hyperfilter ℕ, 0 < (1 : ℝ) / Ω.numSteps.toSeq n := by
      apply htoSeq_ev_pos.mono
      intro n hn
      exact div_pos one_pos (Nat.cast_pos.mpr hn)
    exact hyperrealSqrt_pos_eventually _ hdiv_ev_pos

/-- The time step is infinitesimal -/
theorem dt_infinitesimal (Ω : HyperfinitePathSpace) : Infinitesimal Ω.dt := by
  unfold dt
  rw [one_div]
  have hinfN := Ω.numSteps_infinite
  rw [Foundation.Hypernat.infinite_iff_infinitePos] at hinfN
  have hinf : Infinite Ω.numSteps.val := Or.inl hinfN
  exact infinitesimal_inv_of_infinite hinf

/-- Individual paths have infinitesimal probability -/
theorem path_prob_infinitesimal (Ω : HyperfinitePathSpace) :
    Infinitesimal (Ω.probSpace.prob 1) :=
  singlePath_infinitesimal Ω.numSteps Ω.numSteps_infinite

/-- The pre-Loeb measure of individual paths is 0 -/
theorem path_preLoeb_zero (Ω : HyperfinitePathSpace) :
    preLoebMeasure Ω.probSpace 1 = 0 := by
  have hinf : Infinitesimal (Ω.probSpace.prob 1) := Ω.path_prob_infinitesimal
  have hfin : ¬Infinite (Ω.probSpace.prob 1) := hinf.not_infinite
  rw [preLoebMeasure_eq_st _ _ hfin]
  exact hinf.st_eq

end HyperfinitePathSpace

end SPDE.Nonstandard
