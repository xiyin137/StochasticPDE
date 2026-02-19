/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.CoinFlipSpace
import Mathlib.Data.Real.Sqrt

/-!
# Path Continuity Infrastructure

For Anderson's theorem, we need to show that Loeb-almost-all hyperfinite paths
have continuous standard parts. This requires:

1. **Modulus of continuity**: A bound δ(ε, ω) such that
   |s - t| < δ implies |W(s, ω) - W(t, ω)| < ε

2. **Uniform bound**: For typical paths, the modulus depends only on ε
   (uniformly in the path). This is Lévy's modulus of continuity.

3. **High probability estimate**: P(modulus fails) → 0 as we tighten the bound.

For a hyperfinite random walk, the key is the maximal inequality:
  P(max_{k≤N} |W_k| > M) ≤ 2 · P(|W_N| > M)

Combined with the CLT, this controls the path oscillation.
-/

open Hyperreal Filter

namespace SPDE.Nonstandard

/-- Comparison of hyperreals via eventually. -/
theorem ofSeq_le_ofSeq {f g : ℕ → ℝ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Filter.Germ.coe_le

/-- The modulus of continuity event: all increments within a window are small.
    For a hyperfinite walk, we check: for all i, j with |i - j| ≤ windowSize,
    we have |W_i - W_j| ≤ bound. -/
structure ModulusOfContinuityEvent (Ω : HyperfinitePathSpace) where
  /-- The window size in steps -/
  windowSize : ℕ
  /-- The bound on increments within the window -/
  bound : ℝ
  /-- The bound is positive -/
  bound_pos : 0 < bound
  /-- Window is at most the total path length (at each level) -/
  window_le : ∀ n : ℕ, windowSize ≤ Ω.numSteps.toSeq n

/-! ### Modulus of Continuity - Future Work

The `ModulusOfContinuityEvent` structure packages window size and bound data.
To actually prove modulus of continuity bounds, we need:

1. **Internal set of paths**: The set of paths satisfying the modulus constraint
   should be an internal set on the path space (2^N for N steps), not just
   a set of walk values. This requires encoding the full path, not just final value.

2. **Chebyshev bound**: P(modulus violation in window h) ≤ h·dt/B²
   This requires computing E[|W_{k+h} - W_k|²] = h·dt and applying Chebyshev.

3. **Union bound**: P(any window violates) ≤ (N/h) · h·dt/B² = N·dt/B²
   Then choose B = √(2·h·log(N/h)) to make this → 0.

These require binomial statistics infrastructure not yet formalized.
-/

/-- S-continuity: A hyperfinite path is S-continuous if whenever s ≈ t
    (s, t infinitesimally close), we have W(s) ≈ W(t).

    This is the hyperfinite analog of path continuity.

    For a path represented at level n with N_n steps and step size dx_n:
    - Walk value at step k is path(k) * dx_n (cumulative sum × step size)
    - S-continuity requires: for any standard eps > 0, there exists standard delta > 0
      such that |k - m| < delta * N_n implies |W_k - W_m| < eps

    We express this using the modulus of continuity: for all pairs (k, m) with
    |k - m| ≤ h*N (where h is infinitesimal), |W_k - W_m| is infinitesimal. -/
def HyperfiniteWalkPath.is_S_continuous (Ω : HyperfinitePathSpace)
    (path : ℕ → ℤ) : Prop :=
  -- The path satisfies modulus of continuity for any standard epsilon
  -- For all standard eps > 0, there exists standard delta > 0 such that:
  -- for all k, m with |k - m| ≤ delta * N, we have |dx * path(k) - dx * path(m)| < eps
  -- This is equivalent to: the oscillation within any infinitesimal time window is infinitesimal
  ∀ (eps : ℝ), 0 < eps →
    ∃ (delta : ℝ), 0 < delta ∧
      ∀ (n : ℕ) (k m : ℕ),
        k ≤ Ω.numSteps.toSeq n → m ≤ Ω.numSteps.toSeq n →
        (k : ℤ) - m ≤ (delta * Ω.numSteps.toSeq n : ℝ) →
        (m : ℤ) - k ≤ (delta * Ω.numSteps.toSeq n : ℝ) →
        let dx := Real.sqrt (1 / Ω.numSteps.toSeq n)  -- Assuming T = 1
        |dx * (path k : ℝ) - dx * (path m : ℝ)| < eps

/-- The zero path is S-continuous.
    This is a trivial example: the constant zero path satisfies the modulus
    of continuity condition for any ε with δ = 1. -/
theorem zero_path_S_continuous (Ω : HyperfinitePathSpace) :
    HyperfiniteWalkPath.is_S_continuous Ω (fun _ => 0) := by
  intro eps heps
  use 1, one_pos
  intro n k m _hk _hm _hkm1 _hkm2
  simp only [sub_self, abs_zero]
  exact heps

/-- There exists an S-continuous path (the zero path).
    This is a weak existence result; the full theorem would be that
    Loeb-almost-all paths are S-continuous. -/
theorem exists_S_continuous_path (Ω : HyperfinitePathSpace) :
    ∃ (path : ℕ → ℤ), HyperfiniteWalkPath.is_S_continuous Ω path :=
  ⟨fun _ => 0, zero_path_S_continuous Ω⟩

/-! ### TODO: Loeb-Almost-All S-Continuity

The main S-continuity theorem (Loeb-almost-all paths are S-continuous) requires:

1. **Maximal inequality**: P(max_{k≤N} |W_k| > M) ≤ 2 · P(|W_N| > M)

2. **Lévy's modulus of continuity**: For Brownian motion B,
   lim sup_{h→0} sup_{|s-t|≤h} |B_s - B_t| / √(2h log(1/h)) = 1 a.s.

3. **Probability bound**: For window size h and bound B = √(2h log(N/h)):
   P(any window violates modulus) → 0 as N → ∞

4. **Measure theory**: The set of non-S-continuous paths has Loeb measure 0.

This requires significant infrastructure beyond what is currently formalized.
-/

/-! ### The Standard Part Map

For Anderson's theorem, we need the standard part map from hyperfinite paths
to the space C([0,T], ℝ) of continuous functions.

For a hyperfinite walk W with N steps over time T:
- Define W*(t) = W_k where k = ⌊t·N/T⌋ (the walk value at the nearest step)
- The standard part st(W*(t)) is defined for each standard t
- By S-continuity, this extends to a continuous function on [0, T]

The pushforward of Loeb measure under this map is Wiener measure.
-/

/-- The hyperfinite walk value at a standard time for a single path.
    For path : ℕ → ℤ and time t ∈ [0, 1], this evaluates to the hyperreal
    ofSeq (fun n => dx_n * path(⌊t · N_n⌋)) where N_n = numSteps.toSeq n. -/
noncomputable def hyperfiniteWalkValuePath (Ω : HyperfinitePathSpace)
    (path : ℕ → ℤ) (t : ℝ) : ℝ* :=
  ofSeq (fun n =>
    let totalSteps := Ω.numSteps.toSeq n
    let k := min (Nat.floor (t * totalSteps)) totalSteps
    let dx := Real.sqrt (1 / totalSteps)
    dx * (path k : ℝ))

/-- The approximate evaluation of a hyperfinite walk at a standard time.
    Given a standard time t ∈ [0, T], we find the nearest step index
    and return the walk value there. -/
noncomputable def hyperfiniteWalkEval (Ω : HyperfinitePathSpace)
    (walkSeq : ℕ → ℕ → ℤ)  -- walkSeq n k = cumulative sum at step k, level n
    (t : ℝ) (_ht : 0 ≤ t) (_htT : t ≤ 1) : ℝ* :=
  -- At level n, the step index is k = ⌊t · numSteps.toSeq n⌋
  -- Walk value is dx * walkSeq n k
  ofSeq (fun n =>
    let totalSteps := Ω.numSteps.toSeq n
    let k := min (Nat.floor (t * totalSteps)) (totalSteps - 1)
    let dx := Real.sqrt (1 / totalSteps)  -- T = 1
    dx * (walkSeq n k : ℝ))

/-! ## The Standard Part Function for S-Continuous Paths

For an S-continuous hyperfinite walk, we define the standard part function
f : [0, 1] → ℝ by f(t) = st(W(⌊t·N⌋)/√N).

The key properties are:
1. **Well-definedness**: For S-continuous paths, the hyperfinite walk value
   at any standard time is finite (not infinite), so the standard part exists.
2. **Continuity**: S-continuity implies that f is continuous on [0, 1].

-/

/-- Chaining lemma: If increments within w steps are bounded by B, then the
    total oscillation from 0 to k is at most (k/w + 1) * B.

    This is the key lemma for proving finiteness of S-continuous paths.
    The proof uses induction on k, taking steps of size at most w. -/
theorem oscillation_bound_by_chaining
    (path : ℕ → ℤ) (dx : ℝ) (_hdx_pos : 0 < dx)
    (N w k : ℕ) (hw_pos : 0 < w) (hk_le_N : k ≤ N)
    (B : ℝ) (hB_pos : 0 < B)
    (hincr : ∀ i j : ℕ, i ≤ N → j ≤ N → (i : ℤ) - j ≤ w → (j : ℤ) - i ≤ w →
        |dx * (path i : ℝ) - dx * (path j : ℝ)| < B) :
    |dx * (path k : ℝ) - dx * (path 0 : ℝ)| ≤ ((k / w : ℕ) + 1 : ℕ) * B := by
  -- Proof by strong induction on k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  by_cases hk_small : k ≤ w
  · -- Base case: k ≤ w, so we can apply hincr directly
    have h1 : (k : ℤ) - 0 ≤ w := by simp; exact_mod_cast hk_small
    have h2 : (0 : ℤ) - k ≤ w := by
      have hk_nonneg : (0 : ℤ) ≤ k := Int.natCast_nonneg k
      have hw_nonneg : (0 : ℤ) ≤ w := Int.natCast_nonneg w
      omega
    have hlt := hincr k 0 hk_le_N (Nat.zero_le N) h1 h2
    -- Since k/w + 1 ≥ 1, we have (k/w + 1) * B ≥ B
    have hone_le : (1 : ℕ) ≤ k / w + 1 := Nat.le_add_left 1 (k / w)
    calc |dx * (path k : ℝ) - dx * (path 0 : ℝ)|
        ≤ B := le_of_lt hlt
      _ = 1 * B := by ring
      _ ≤ ((k / w + 1 : ℕ) : ℝ) * B := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hB_pos)
          exact_mod_cast hone_le
  · -- Inductive case: k > w
    push_neg at hk_small
    -- Consider the previous step at index k - w
    have hk_ge_w : w ≤ k := Nat.le_of_lt hk_small
    let k' := k - w
    have hk'_lt_k : k' < k := Nat.sub_lt (Nat.lt_of_lt_of_le hw_pos hk_ge_w) hw_pos
    have hk'_le_N : k' ≤ N := Nat.le_trans (Nat.sub_le k w) hk_le_N
    -- The increment from k' to k
    have hincr_step : |dx * (path k : ℝ) - dx * (path k' : ℝ)| < B := by
      have h1 : (k : ℤ) - k' ≤ w := by
        simp only [k']
        have : k - (k - w) = w := Nat.sub_sub_self hk_ge_w
        omega
      have h2 : (k' : ℤ) - k ≤ w := by
        simp only [k']
        omega
      exact hincr k k' hk_le_N hk'_le_N h1 h2
    -- Apply induction hypothesis
    have hih := ih k' hk'_lt_k hk'_le_N
    -- Triangle inequality
    have htri : |dx * (path k : ℝ) - dx * (path 0 : ℝ)| ≤
        |dx * (path k : ℝ) - dx * (path k' : ℝ)| + |dx * (path k' : ℝ) - dx * (path 0 : ℝ)| := by
      have heq : dx * (path k : ℝ) - dx * (path 0 : ℝ) =
          (dx * (path k : ℝ) - dx * (path k' : ℝ)) + (dx * (path k' : ℝ) - dx * (path 0 : ℝ)) := by ring
      calc |dx * (path k : ℝ) - dx * (path 0 : ℝ)|
          = |(dx * (path k : ℝ) - dx * (path k' : ℝ)) + (dx * (path k' : ℝ) - dx * (path 0 : ℝ))| := by
            rw [heq]
        _ ≤ |dx * (path k : ℝ) - dx * (path k' : ℝ)| + |dx * (path k' : ℝ) - dx * (path 0 : ℝ)| :=
            abs_add_le _ _
    -- Key division fact: k / w = k' / w + 1 when k = k' + w
    have hdiv : k / w = k' / w + 1 := by
      simp only [k']
      have heq : k = (k - w) + w := (Nat.sub_add_cancel hk_ge_w).symm
      conv_lhs => rw [heq]
      exact Nat.add_div_right (k - w) hw_pos
    -- Combine bounds
    have hsum : |dx * (path k : ℝ) - dx * (path k' : ℝ)| + |dx * (path k' : ℝ) - dx * (path 0 : ℝ)|
        < B + ((k' / w : ℕ) + 1 : ℕ) * B := by linarith
    -- Simplify: B + (k'/w + 1) * B = (k'/w + 2) * B = (k/w + 1) * B
    have hnat_eq : (k' / w + 1 : ℕ) + 1 = k / w + 1 := by omega
    have harith : B + ((k' / w : ℕ) + 1 : ℕ) * B = ((k / w : ℕ) + 1 : ℕ) * B := by
      have h1 : B + ((k' / w + 1 : ℕ) : ℝ) * B = (1 + (k' / w + 1 : ℕ)) * B := by ring
      have h2 : (1 : ℝ) + (k' / w + 1 : ℕ) = ((k' / w + 1 : ℕ) + 1 : ℕ) := by
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      rw [h1, h2, hnat_eq]
    calc |dx * (path k : ℝ) - dx * (path 0 : ℝ)|
        ≤ |dx * (path k : ℝ) - dx * (path k' : ℝ)| + |dx * (path k' : ℝ) - dx * (path 0 : ℝ)| := htri
      _ ≤ B + ((k' / w : ℕ) + 1 : ℕ) * B := le_of_lt hsum
      _ = ((k / w : ℕ) + 1 : ℕ) * B := harith

/-- For an S-continuous path, the hyperfinite walk value is finite at each
    standard time. This is because S-continuity bounds the walk increments.

    **Proof sketch**: S-continuity with ε = 1 gives δ > 0. Covering [0, t] with
    windows of size δ and summing the bounds shows |W(t)| ≤ (t/δ + 1) · 1 = O(1/δ),
    which is finite for standard δ. -/
theorem hyperfiniteWalkValue_finite_of_S_continuous (Ω : HyperfinitePathSpace)
    (path : ℕ → ℤ) (hS : HyperfiniteWalkPath.is_S_continuous Ω path)
    (t : ℝ) (ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    ¬Infinite (hyperfiniteWalkValuePath Ω path t) := by
  -- S-continuity with eps = 1 gives a delta > 0 such that increments within
  -- delta*N steps are bounded by 1.
  obtain ⟨delta, hdelta_pos, hmod⟩ := hS 1 one_pos
  -- We'll show the walk value is bounded by M = |path 0| + 2*t/delta + 4
  -- which is a standard constant, hence the hyperreal is not infinite.
  rw [not_infinite_iff_exist_lt_gt]
  -- Define the bound (use |↑(path 0)| for consistent typing)
  -- We use +4 instead of +3 to ensure strict inequality even when |path 0| = 0
  let M : ℝ := |(path 0 : ℝ)| + 2 * t / delta + 4
  have hM_pos : 0 < M := by
    have h1 : (0 : ℝ) ≤ |(path 0 : ℝ)| := abs_nonneg _
    have h2 : 0 ≤ 2 * t / delta := by positivity
    linarith
  use (-M - 1), (M + 1)
  -- We prove both bounds using the same eventually filter
  -- First, establish when N is large enough
  have hN_large : ∀ᶠ n in hyperfilter ℕ, 2 < delta * Ω.numSteps.toSeq n ∧
      |(path 0 : ℝ)| * Real.sqrt (1 / Ω.numSteps.toSeq n) < 1 := by
    -- Use that numSteps is infinite
    have hinf := Ω.numSteps_infinite
    rw [Foundation.Hypernat.infinite_iff_infinitePos] at hinf
    -- Get bounds for delta * N > 2
    have hev1 : ∀ᶠ n in hyperfilter ℕ, 2 / delta < Ω.numSteps.toSeq n := by
      have hbig : (2 / delta : ℝ*) < Ω.numSteps.val := by
        calc (2 / delta : ℝ*) = ((2 / delta : ℝ) : ℝ*) := rfl
          _ < Ω.numSteps.val := hinf (2 / delta)
      rw [← Foundation.Hypernat.ofSeq_toSeq Ω.numSteps] at hbig
      exact ofSeq_lt_ofSeq.mp hbig
    have hev1' : ∀ᶠ n in hyperfilter ℕ, 2 < delta * Ω.numSteps.toSeq n := by
      apply hev1.mono
      intro n hn
      have hdp : 0 < delta := hdelta_pos
      calc 2 = delta * (2 / delta) := by field_simp
        _ < delta * Ω.numSteps.toSeq n := by nlinarith
    -- Get bounds for |path 0| * sqrt(1/N) < 1
    have hev2 : ∀ᶠ n in hyperfilter ℕ, |(path 0 : ℝ)| * Real.sqrt (1 / Ω.numSteps.toSeq n) < 1 := by
      by_cases hp0 : path 0 = 0
      · simp only [hp0, Int.cast_zero, abs_zero, zero_mul]
        exact Eventually.of_forall (fun _ => one_pos)
      · -- |path 0| > 0, so need N > |path 0|²
        have habsr : 0 < |(path 0 : ℝ)| := by
          rw [abs_pos]
          exact_mod_cast hp0
        have hbig : (|(path 0 : ℝ)|^2 : ℝ*) < Ω.numSteps.val := hinf (|(path 0 : ℝ)|^2)
        rw [← Foundation.Hypernat.ofSeq_toSeq Ω.numSteps] at hbig
        have hev := ofSeq_lt_ofSeq.mp hbig
        apply hev.mono
        intro n hn
        -- hn : |path 0|² < N.toSeq n (as reals)
        -- Simplify hn first
        simp only [Function.comp_apply] at hn
        have hNpos : 0 < (Ω.numSteps.toSeq n : ℝ) := by
          calc (0 : ℝ) < |(path 0 : ℝ)|^2 := by positivity
            _ < Ω.numSteps.toSeq n := hn
        have hNpos' : 0 < Ω.numSteps.toSeq n := Nat.cast_pos.mp hNpos
        -- sqrt(1/N) < 1/|path 0| iff 1/N < 1/|path 0|² iff |path 0|² < N
        have hsqrt_bound : Real.sqrt (1 / Ω.numSteps.toSeq n) < 1 / |(path 0 : ℝ)| := by
          have h1 : 1 / (Ω.numSteps.toSeq n : ℝ) < 1 / |(path 0 : ℝ)|^2 := by
            apply one_div_lt_one_div_of_lt
            · positivity
            · exact hn
          have h2 : (1 / |(path 0 : ℝ)|)^2 = 1 / |(path 0 : ℝ)|^2 := by ring
          rw [← h2] at h1
          have h3 := Real.sqrt_lt_sqrt (by positivity) h1
          rwa [Real.sqrt_sq (by positivity : 0 ≤ 1 / |(path 0 : ℝ)|)] at h3
        calc |(path 0 : ℝ)| * Real.sqrt (1 / Ω.numSteps.toSeq n)
            < |(path 0 : ℝ)| * (1 / |(path 0 : ℝ)|) := by
              apply mul_lt_mul_of_pos_left hsqrt_bound habsr
          _ = 1 := by field_simp
    exact hev1'.and hev2
  constructor
  -- Lower bound: -M - 1 < hyperfiniteWalkValuePath
  · unfold hyperfiniteWalkValuePath
    apply ofSeq_lt_ofSeq.mpr
    apply hN_large.mono
    intro n ⟨hNbig, hpath0_small⟩
    simp only
    -- The bound |dx * path k| < M eventually, so -M - 1 < dx * path k
    set N := Ω.numSteps.toSeq n
    set k := min (Nat.floor (t * N)) N
    set dx := Real.sqrt (1 / N)
    have hNpos : 0 < N := by
      by_contra h; push_neg at h
      have : delta * (N : ℝ) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdelta_pos)
        exact_mod_cast h
      linarith
    have hdx_pos : 0 < dx := Real.sqrt_pos_of_pos (by positivity)
    -- Use that |dx * path k| is bounded
    have habs_bound : |dx * (path k : ℝ)| < M := by
      -- |dx * path k| ≤ |dx * path 0| + |dx * (path k - path 0)|
      -- < 1 + (2*t/delta + 2) = 3 + 2*t/delta < M
      have htri : |dx * (path k : ℝ)| ≤ |dx * (path 0 : ℝ)| + |dx * (path k : ℝ) - dx * (path 0 : ℝ)| := by
        have h := abs_add_le (dx * (path 0 : ℝ)) (dx * (path k : ℝ) - dx * (path 0 : ℝ))
        simp only [add_sub_cancel] at h
        exact h
      have hstep1 : |dx * (path 0 : ℝ)| = dx * |(path 0 : ℝ)| := by
        rw [abs_mul, abs_of_pos hdx_pos]
      have hstep2 : |dx * (path 0 : ℝ)| < 1 := by
        rw [hstep1, mul_comm]; exact hpath0_small
      -- The oscillation bound via chaining lemma
      have hosc : |dx * (path k : ℝ) - dx * (path 0 : ℝ)| ≤ 2 * t / delta + 2 := by
        -- Use window size w = ⌊delta * N⌋
        let w := Nat.floor (delta * N)
        have hw_pos : 0 < w := by
          rw [Nat.floor_pos]
          linarith
        have hk_le_N : k ≤ N := min_le_right _ _
        -- The increment bound from S-continuity
        have hincr : ∀ i j : ℕ, i ≤ N → j ≤ N → (i : ℤ) - j ≤ w → (j : ℤ) - i ≤ w →
            |dx * (path i : ℝ) - dx * (path j : ℝ)| < 1 := by
          intro i j hi hj hij hji
          have hfloor_le : (w : ℝ) ≤ delta * N := Nat.floor_le (by positivity : 0 ≤ delta * N)
          have hij' : (i : ℤ) - j ≤ delta * N := by
            have h1 : ((i : ℤ) - j : ℝ) ≤ w := by exact_mod_cast hij
            linarith
          have hji' : (j : ℤ) - i ≤ delta * N := by
            have h1 : ((j : ℤ) - i : ℝ) ≤ w := by exact_mod_cast hji
            linarith
          exact hmod n i j hi hj hij' hji'
        -- Apply the chaining lemma
        have hchain := oscillation_bound_by_chaining path dx hdx_pos N w k hw_pos hk_le_N 1 one_pos hincr
        -- Now show (k/w + 1) * 1 ≤ 2*t/delta + 2
        have hw_pos_real : (0 : ℝ) < w := by exact_mod_cast hw_pos
        have hk_le_tN : (k : ℝ) ≤ t * N := by
          calc (k : ℝ) ≤ Nat.floor (t * N) := by exact_mod_cast min_le_left _ _
            _ ≤ t * N := Nat.floor_le (by positivity)
        -- w ≥ delta * N - 1 ≥ delta * N / 2 (when delta * N > 2)
        have hw_lower : delta * N / 2 ≤ w := by
          have hfloor_ge : (w : ℝ) ≥ delta * N - 1 := by
            have := Nat.sub_one_lt_floor (delta * N)
            linarith
          linarith
        -- (k/w : ℕ) ≤ k/w ≤ t*N / (delta*N/2) = 2*t/delta
        have hdiv_bound : (k / w : ℕ) ≤ 2 * t / delta := by
          have h1 : ((k / w : ℕ) : ℝ) ≤ (k : ℝ) / w := Nat.cast_div_le
          have h2 : (k : ℝ) / w ≤ (t * N) / w := by
            apply div_le_div_of_nonneg_right hk_le_tN (le_of_lt hw_pos_real)
          have h3 : (t * N) / w ≤ (t * N) / (delta * N / 2) := by
            apply div_le_div_of_nonneg_left (by positivity) (by linarith) hw_lower
          have h4 : (t * N) / (delta * N / 2) = 2 * t / delta := by
            have hN_pos : (0 : ℝ) < N := by exact_mod_cast hNpos
            field_simp
          linarith
        calc |dx * (path k : ℝ) - dx * (path 0 : ℝ)|
            ≤ ((k / w : ℕ) + 1 : ℕ) * (1 : ℝ) := hchain
          _ = (k / w : ℕ) + 1 := by simp
          _ ≤ 2 * t / delta + 1 := by linarith
          _ ≤ 2 * t / delta + 2 := by linarith
      calc |dx * (path k : ℝ)|
          ≤ |dx * (path 0 : ℝ)| + |dx * (path k : ℝ) - dx * (path 0 : ℝ)| := htri
        _ < 1 + |dx * (path k : ℝ) - dx * (path 0 : ℝ)| := by linarith
        _ ≤ 1 + (2 * t / delta + 2) := by linarith
        _ < M := by
            have hp : (0 : ℝ) ≤ |(path 0 : ℝ)| := abs_nonneg _
            linarith
    calc -M - 1 < -|dx * (path k : ℝ)| := by linarith
      _ ≤ dx * (path k : ℝ) := neg_abs_le _
  -- Upper bound: hyperfiniteWalkValuePath < M + 1
  · unfold hyperfiniteWalkValuePath
    apply ofSeq_lt_ofSeq.mpr
    apply hN_large.mono
    intro n ⟨hNbig, hpath0_small⟩
    simp only
    set N := Ω.numSteps.toSeq n
    set k := min (Nat.floor (t * N)) N
    set dx := Real.sqrt (1 / N)
    have hNpos : 0 < N := by
      by_contra h; push_neg at h
      have : delta * (N : ℝ) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdelta_pos)
        exact_mod_cast h
      linarith
    have hdx_pos : 0 < dx := Real.sqrt_pos_of_pos (by positivity)
    -- Same bound as above
    have habs_bound : |dx * (path k : ℝ)| < M := by
      have htri : |dx * (path k : ℝ)| ≤ |dx * (path 0 : ℝ)| + |dx * (path k : ℝ) - dx * (path 0 : ℝ)| := by
        have h := abs_add_le (dx * (path 0 : ℝ)) (dx * (path k : ℝ) - dx * (path 0 : ℝ))
        simp only [add_sub_cancel] at h
        exact h
      have hstep1 : |dx * (path 0 : ℝ)| = dx * |(path 0 : ℝ)| := by
        rw [abs_mul, abs_of_pos hdx_pos]
      have hstep2 : |dx * (path 0 : ℝ)| < 1 := by
        rw [hstep1, mul_comm]; exact hpath0_small
      have hosc : |dx * (path k : ℝ) - dx * (path 0 : ℝ)| ≤ 2 * t / delta + 2 := by
        -- Use window size w = ⌊delta * N⌋
        let w := Nat.floor (delta * N)
        have hw_pos : 0 < w := by
          rw [Nat.floor_pos]
          linarith
        have hk_le_N : k ≤ N := min_le_right _ _
        -- The increment bound from S-continuity
        have hincr : ∀ i j : ℕ, i ≤ N → j ≤ N → (i : ℤ) - j ≤ w → (j : ℤ) - i ≤ w →
            |dx * (path i : ℝ) - dx * (path j : ℝ)| < 1 := by
          intro i j hi hj hij hji
          have hfloor_le : (w : ℝ) ≤ delta * N := Nat.floor_le (by positivity : 0 ≤ delta * N)
          have hij' : (i : ℤ) - j ≤ delta * N := by
            have h1 : ((i : ℤ) - j : ℝ) ≤ w := by exact_mod_cast hij
            linarith
          have hji' : (j : ℤ) - i ≤ delta * N := by
            have h1 : ((j : ℤ) - i : ℝ) ≤ w := by exact_mod_cast hji
            linarith
          exact hmod n i j hi hj hij' hji'
        -- Apply the chaining lemma
        have hchain := oscillation_bound_by_chaining path dx hdx_pos N w k hw_pos hk_le_N 1 one_pos hincr
        -- Now show (k/w + 1) * 1 ≤ 2*t/delta + 2
        have hw_pos_real : (0 : ℝ) < w := by exact_mod_cast hw_pos
        have hk_le_tN : (k : ℝ) ≤ t * N := by
          calc (k : ℝ) ≤ Nat.floor (t * N) := by exact_mod_cast min_le_left _ _
            _ ≤ t * N := Nat.floor_le (by positivity)
        -- w ≥ delta * N - 1 ≥ delta * N / 2 (when delta * N > 2)
        have hw_lower : delta * N / 2 ≤ w := by
          have hfloor_ge : (w : ℝ) ≥ delta * N - 1 := by
            have := Nat.sub_one_lt_floor (delta * N)
            linarith
          linarith
        -- (k/w : ℕ) ≤ k/w ≤ t*N / (delta*N/2) = 2*t/delta
        have hdiv_bound : (k / w : ℕ) ≤ 2 * t / delta := by
          have h1 : ((k / w : ℕ) : ℝ) ≤ (k : ℝ) / w := Nat.cast_div_le
          have h2 : (k : ℝ) / w ≤ (t * N) / w := by
            apply div_le_div_of_nonneg_right hk_le_tN (le_of_lt hw_pos_real)
          have h3 : (t * N) / w ≤ (t * N) / (delta * N / 2) := by
            apply div_le_div_of_nonneg_left (by positivity) (by linarith) hw_lower
          have h4 : (t * N) / (delta * N / 2) = 2 * t / delta := by
            have hN_pos : (0 : ℝ) < N := by exact_mod_cast hNpos
            field_simp
          linarith
        calc |dx * (path k : ℝ) - dx * (path 0 : ℝ)|
            ≤ ((k / w : ℕ) + 1 : ℕ) * (1 : ℝ) := hchain
          _ = (k / w : ℕ) + 1 := by simp
          _ ≤ 2 * t / delta + 1 := by linarith
          _ ≤ 2 * t / delta + 2 := by linarith
      calc |dx * (path k : ℝ)|
          ≤ |dx * (path 0 : ℝ)| + |dx * (path k : ℝ) - dx * (path 0 : ℝ)| := htri
        _ < 1 + |dx * (path k : ℝ) - dx * (path 0 : ℝ)| := by linarith
        _ ≤ 1 + (2 * t / delta + 2) := by linarith
        _ < M := by
            have hp : (0 : ℝ) ≤ |(path 0 : ℝ)| := abs_nonneg _
            linarith
    calc dx * (path k : ℝ) ≤ |dx * (path k : ℝ)| := le_abs_self _
      _ < M := habs_bound
      _ < M + 1 := lt_add_one M

/-- The standard part of the hyperfinite walk value at a standard time.
    For S-continuous paths, this is well-defined as a real number.

    **Definition**: st(W*(t)) where W*(t) = dx · path(⌊t·N⌋).

    Note: We use Mathlib's `Hyperreal.st` which returns 0 for infinite values.
    For S-continuous paths, the value is finite, so this gives the actual standard part. -/
noncomputable def standardPartPath (Ω : HyperfinitePathSpace)
    (path : ℕ → ℤ) (t : ℝ) : ℝ :=
  Hyperreal.st (hyperfiniteWalkValuePath Ω path t)

/-- The standard part function agrees with the hyperreal walk value
    up to an infinitesimal, for S-continuous paths. -/
theorem standardPartPath_isSt (Ω : HyperfinitePathSpace)
    (path : ℕ → ℤ) (hS : HyperfiniteWalkPath.is_S_continuous Ω path)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsSt (hyperfiniteWalkValuePath Ω path t) (standardPartPath Ω path t) := by
  have hfin := hyperfiniteWalkValue_finite_of_S_continuous Ω path hS t ht0 ht1
  exact Hyperreal.isSt_st' hfin

/-- The standard part function is continuous for S-continuous paths.
    This is the key property needed for Anderson's theorem.

    **Proof idea**: For any ε > 0, S-continuity gives δ > 0 such that
    |s - t| < δ implies |W*(s) - W*(t)| < ε (approximately). Taking standard
    parts preserves this inequality. -/
theorem standardPartPath_continuous (Ω : HyperfinitePathSpace)
    (path : ℕ → ℤ) (hS : HyperfiniteWalkPath.is_S_continuous Ω path) :
    Continuous (fun t : ↥(Set.Icc (0 : ℝ) 1) => standardPartPath Ω path t) := by
  -- Use the epsilon-delta definition of continuity
  rw [Metric.continuous_iff]
  intro ⟨t, ht0, ht1⟩ eps heps
  -- S-continuity with eps/2 gives delta > 0
  obtain ⟨delta, hdelta_pos, hmod⟩ := hS (eps / 2) (by linarith)
  -- Use delta/4 as our continuity modulus (to handle floor rounding)
  use delta / 4
  constructor
  · linarith
  intro ⟨s, hs0, hs1⟩ hdist
  -- We need to show |standardPartPath ... s - standardPartPath ... t| < eps
  unfold standardPartPath
  -- The hyperfinite walk values at s and t
  set Ws := hyperfiniteWalkValuePath Ω path s
  set Wt := hyperfiniteWalkValuePath Ω path t
  -- Both are finite by S-continuity
  have hWs_fin : ¬Infinite Ws := hyperfiniteWalkValue_finite_of_S_continuous Ω path hS s hs0 hs1
  have hWt_fin : ¬Infinite Wt := hyperfiniteWalkValue_finite_of_S_continuous Ω path hS t ht0 ht1
  -- The difference has standard part equal to the difference of standard parts
  have hst_sub : st Ws - st Wt = st (Ws - Wt) := by
    have h := Hyperreal.st_add hWs_fin (Hyperreal.not_infinite_neg hWt_fin)
    simp only [sub_eq_add_neg, Hyperreal.st_neg] at h ⊢
    exact h.symm
  rw [Real.dist_eq, hst_sub]
  -- Define the sequence for walk value at time u, level n
  let walkSeq (u : ℝ) (n : ℕ) : ℝ :=
    let N := Ω.numSteps.toSeq n
    let k := min (Nat.floor (u * N)) N
    let dx := Real.sqrt (1 / N)
    dx * (path k : ℝ)
  -- Key: Ws = ofSeq (walkSeq s) and Wt = ofSeq (walkSeq t)
  have hWs_eq : Ws = ofSeq (walkSeq s) := rfl
  have hWt_eq : Wt = ofSeq (walkSeq t) := rfl
  -- Extract distance bound on s and t
  have hdist_st : |s - t| < delta / 4 := by
    have : dist s t < delta / 4 := by
      calc dist s t = dist (⟨s, hs0, hs1⟩ : Set.Icc (0 : ℝ) 1) ⟨t, ht0, ht1⟩ := by
            simp only [Subtype.dist_eq]
        _ < delta / 4 := hdist
    rwa [Real.dist_eq] at this
  -- The difference Ws - Wt is bounded by eps/2 eventually
  have hdiff_small : ∀ᶠ n in hyperfilter ℕ, |walkSeq s n - walkSeq t n| < eps / 2 := by
    -- Eventually N is large enough that delta * N > 4
    -- First get N > ceil(4/delta)
    have hN_large : ∀ᶠ n in hyperfilter ℕ, 4 < delta * Ω.numSteps.toSeq n := by
      -- Use that numSteps is infinite
      have hinf := Ω.numSteps_infinite
      -- Get bound on N being eventually > nat_bound
      let nat_bound := Nat.ceil (4 / delta) + 1
      have hev := Foundation.Hypernat.toSeq_eventually_gt_of_infinite Ω.numSteps hinf nat_bound
      apply hev.mono
      intro n hn
      have h1 : (nat_bound : ℝ) < Ω.numSteps.toSeq n := by exact_mod_cast hn
      have h2 : 4 / delta < nat_bound := by
        have hle : 4 / delta ≤ Nat.ceil (4 / delta) := Nat.le_ceil (4 / delta)
        have : (nat_bound : ℝ) = Nat.ceil (4 / delta) + 1 := by simp only [nat_bound]; norm_cast
        linarith
      have h3 : 4 / delta < Ω.numSteps.toSeq n := lt_trans h2 h1
      calc 4 = delta * (4 / delta) := by field_simp
        _ < delta * Ω.numSteps.toSeq n := by
            apply mul_lt_mul_of_pos_left h3 hdelta_pos
    apply hN_large.mono
    intro n hNbig
    simp only [walkSeq]
    set N := Ω.numSteps.toSeq n
    set ks := min (Nat.floor (s * N)) N
    set kt := min (Nat.floor (t * N)) N
    set dx := Real.sqrt (1 / N)
    have hNpos : 0 < N := by
      by_contra h; push_neg at h
      have : delta * (N : ℝ) ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdelta_pos)
        exact_mod_cast h
      linarith
    have hks_le_N : ks ≤ N := min_le_right _ _
    have hkt_le_N : kt ≤ N := min_le_right _ _
    -- The key: |ks - kt| ≤ delta * N when |s - t| < delta/4 and N > 4/delta
    -- |s*N - t*N| < delta*N/4
    have hst_scaled : |s * N - t * N| < delta * N / 4 := by
      have heq : s * N - t * N = (s - t) * N := by ring
      have hNnn : |(N : ℝ)| = N := abs_of_nonneg (Nat.cast_nonneg N)
      rw [heq, abs_mul, hNnn]
      calc |s - t| * N < delta / 4 * N := by
            apply mul_lt_mul_of_pos_right hdist_st
            exact_mod_cast hNpos
        _ = delta * N / 4 := by ring
    -- Key bound: |ks - kt| ≤ delta * N (in ℤ for hmod)
    -- This follows from: |floor(s*N) - floor(t*N)| ≤ |s*N - t*N| + 1 < delta*N/4 + 1 < delta*N/2
    -- and clamping to [0, N] doesn't increase distance
    have hks_kt_diff : |(ks : ℤ) - kt| ≤ delta * N := by
        -- Floor difference bound
        have hs_le : (Nat.floor (s * N) : ℝ) ≤ s * N := Nat.floor_le (by positivity)
        have ht_le : (Nat.floor (t * N) : ℝ) ≤ t * N := Nat.floor_le (by positivity)
        have hs_lt : s * N < Nat.floor (s * N) + 1 := Nat.lt_floor_add_one _
        have ht_lt : t * N < Nat.floor (t * N) + 1 := Nat.lt_floor_add_one _
        -- |floor(s*N) - floor(t*N)| ≤ |s*N - t*N| + 1
        have hfloor_ub : (Nat.floor (s * N) : ℝ) - Nat.floor (t * N) ≤ |s * N - t * N| + 1 := by
          have h := le_abs_self (s * N - t * N); linarith
        have hfloor_lb : (Nat.floor (t * N) : ℝ) - Nat.floor (s * N) ≤ |s * N - t * N| + 1 := by
          have h := neg_le_abs (s * N - t * N); linarith
        -- Bound on floor difference
        have hfloor_bound : |(Nat.floor (s * N) : ℝ) - Nat.floor (t * N)| < delta * N / 2 := by
          rw [abs_lt]
          constructor <;> linarith
        -- Clamping doesn't increase distance: |min a N - min b N| ≤ |a - b|
        -- We prove the real version and convert to ℤ
        have hks_real : (ks : ℝ) = min (Nat.floor (s * N)) N := by simp [ks]
        have hkt_real : (kt : ℝ) = min (Nat.floor (t * N)) N := by simp [kt]
        have hmin_le : |(ks : ℝ) - kt| ≤ |(Nat.floor (s * N) : ℝ) - Nat.floor (t * N)| := by
          -- ks = min (floor(s*N)) N, kt = min (floor(t*N)) N as naturals
          -- We use abs_min_sub_min_le_max: |min a b - min c d| ≤ max |a - c| |b - d|
          -- Cast to ℝ first, then apply the lemma
          have hcast_ks : (ks : ℝ) = min (Nat.floor (s * N) : ℝ) (N : ℝ) := by
            simp only [ks, Nat.cast_min]
          have hcast_kt : (kt : ℝ) = min (Nat.floor (t * N) : ℝ) (N : ℝ) := by
            simp only [kt, Nat.cast_min]
          rw [hcast_ks, hcast_kt]
          -- Apply abs_min_sub_min_le_max with reals
          have h := abs_min_sub_min_le_max (Nat.floor (s * N) : ℝ) (N : ℝ)
              (Nat.floor (t * N) : ℝ) (N : ℝ)
          simp only [sub_self, abs_zero] at h
          exact le_trans h (max_eq_left (abs_nonneg _)).le
        -- Combine bounds
        have hks_kt_real : |(ks : ℝ) - kt| < delta * N := by
          calc |(ks : ℝ) - kt| ≤ |(Nat.floor (s * N) : ℝ) - Nat.floor (t * N)| := hmin_le
            _ < delta * N / 2 := hfloor_bound
            _ ≤ delta * N := by linarith
        -- Convert to ℤ: |(ks : ℤ) - kt| ≤ delta * N
        have hint_bound : (|(ks : ℤ) - kt| : ℝ) ≤ delta * N := by
          -- Use simp to normalize all casts ℕ → ℤ → ℝ to ℕ → ℝ
          simp only [Int.cast_natCast]
          exact le_of_lt hks_kt_real
        exact_mod_cast hint_bound
    -- Apply S-continuity
    -- hks_kt_diff has type (|(ks : ℤ) - kt| : ℝ) ≤ delta * N
    -- We need (ks : ℤ) - kt ≤ delta * N as (ℝ) for hmod
    -- Convert using Int.cast_abs: (|a| : ℝ) = |(a : ℝ)| for a : ℤ
    have hks_kt_diff_real : |((ks : ℤ) : ℝ) - kt| ≤ delta * N := by
      simp only [Int.cast_abs, Int.cast_sub, Int.cast_natCast] at hks_kt_diff
      exact hks_kt_diff
    have h1 : ((ks : ℤ) - kt : ℝ) ≤ delta * N := by
      have h := le_abs_self (((ks : ℤ) : ℝ) - kt)
      simp only [Int.cast_natCast] at h hks_kt_diff_real ⊢
      linarith
    have h2 : ((kt : ℤ) - ks : ℝ) ≤ delta * N := by
      have h := neg_le_abs (((ks : ℤ) : ℝ) - kt)
      simp only [Int.cast_natCast] at h hks_kt_diff_real ⊢
      linarith
    exact hmod n ks kt hks_le_N hkt_le_N h1 h2
  -- The difference Ws - Wt = ofSeq(walkSeq s - walkSeq t) is bounded eventually
  have hWdiff_fin : ¬Infinite (Ws - Wt) := by
    rw [sub_eq_add_neg]
    exact Hyperreal.not_infinite_add hWs_fin (Hyperreal.not_infinite_neg hWt_fin)
  -- Standard part of bounded hyperreal is bounded
  have hWdiff_eq : Ws - Wt = ofSeq (fun n => walkSeq s n - walkSeq t n) := by
    simp only [hWs_eq, hWt_eq, sub_eq_add_neg]
    rfl
  have hst_bound : |st (Ws - Wt)| ≤ eps / 2 := by
    rw [hWdiff_eq]
    have hbound : ∀ᶠ n in hyperfilter ℕ, |walkSeq s n - walkSeq t n| ≤ eps / 2 :=
      hdiff_small.mono fun n hn => le_of_lt hn
    -- Upper bound: ofSeq f ≤ (r : ℝ*) iff f ≤ᶠ r
    -- Note: (r : ℝ*) = ofSeq (fun _ => r) definitionally
    have hub : ofSeq (fun n => walkSeq s n - walkSeq t n) ≤ (eps / 2 : ℝ*) := by
      rw [show (eps / 2 : ℝ*) = ofSeq (fun _ => eps / 2) from rfl]
      apply ofSeq_le_ofSeq.mpr
      apply hbound.mono
      intro n hn
      linarith [le_abs_self (walkSeq s n - walkSeq t n)]
    have hlb : (-(eps / 2) : ℝ*) ≤ ofSeq (fun n => walkSeq s n - walkSeq t n) := by
      rw [show (-(eps / 2) : ℝ*) = ofSeq (fun _ => -(eps / 2)) from rfl]
      apply ofSeq_le_ofSeq.mpr
      apply hbound.mono
      intro n hn
      linarith [neg_le_abs (walkSeq s n - walkSeq t n)]
    have hfin : ¬Infinite (ofSeq (fun n => walkSeq s n - walkSeq t n)) := by
      rw [← hWdiff_eq]; exact hWdiff_fin
    have hst_ub : st (ofSeq (fun n => walkSeq s n - walkSeq t n)) ≤ eps / 2 := by
      have h := Hyperreal.st_le_of_le hfin (Hyperreal.not_infinite_real (eps / 2)) hub
      rwa [Hyperreal.st_id_real] at h
    have hst_lb : -(eps / 2) ≤ st (ofSeq (fun n => walkSeq s n - walkSeq t n)) := by
      have h := Hyperreal.st_le_of_le (Hyperreal.not_infinite_real (-(eps / 2))) hfin hlb
      rwa [Hyperreal.st_id_real] at h
    exact abs_le.mpr ⟨by linarith, hst_ub⟩
  linarith

/-! ## Summary: Path to Anderson's Theorem

The complete proof of Anderson's theorem requires:

1. **Single-time marginals** (infrastructure above):
   - Binomial probabilities converge to Gaussian (local CLT)
   - Loeb probability of cylinder sets equals Wiener measure

2. **Joint distributions**:
   - Extend to cylinder sets at multiple times t₁ < t₂ < ... < tₖ
   - Use Markov property: increments are independent
   - Joint convergence follows from product of marginals

3. **Path continuity**:
   - Show that Loeb-a.a. paths have continuous standard parts
   - Use modulus of continuity estimates for random walks
   - Kolmogorov's criterion for path regularity

4. **Pushforward measure**:
   - The standard part map st : HyperfiniteWalk → C([0,T])
   - Pushforward of Loeb measure under st
   - Equals Wiener measure on C([0,T])

The key insight is that hyperfinite probability theory makes the limiting
arguments trivial: the "limit" is just the standard part of a hyperfinite object.

## References

* Anderson, R. M. "A nonstandard representation for Brownian motion and Itô
  integration" (1976)
* Lindstrøm, T. "Hyperfinite stochastic integration" (1980s)
* Cutland, N. "Loeb Measures in Practice: Recent Advances" (2000)
-/

end SPDE.Nonstandard
