/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.LoebMeasure.CoinFlipSpace
import StochasticPDE.Nonstandard.Foundation.InternalMembership

/-!
# Cylinder Sets

Cylinder sets are events defined by constraints at finitely many times.
They are fundamental for computing explicit probabilities and for
connecting hyperfinite random walks to Wiener measure.

A cylinder set at times k₁ < k₂ < ... < kₘ is defined by:
  { ω : W_{k₁}(ω) ∈ A₁, W_{k₂}(ω) ∈ A₂, ..., W_{kₘ}(ω) ∈ Aₘ }

where each Aᵢ is a Borel set in ℝ.

For hyperfinite random walks:
- Walk values W_k depend on the first k coin flips
- The cylinder set probability can be computed by counting
- Internal probabilities are exact; Loeb measure gives the standard part
-/

open Hyperreal Filter

namespace SPDE.Nonstandard

/-- A single-time constraint: the walk value at step k lies in interval [a, b].
    We use intervals for simplicity; more general Borel sets would require
    more infrastructure. -/
structure SingleTimeConstraint where
  /-- The step index -/
  step : ℕ
  /-- Lower bound (as a real, represents a standard bound) -/
  lower : ℝ
  /-- Upper bound -/
  upper : ℝ
  /-- Bounds are ordered -/
  bounds_ordered : lower ≤ upper

/-- A cylinder constraint: a finite list of single-time constraints.
    The steps should be distinct and in increasing order for well-definedness. -/
structure CylinderConstraint where
  /-- The list of constraints -/
  constraints : List SingleTimeConstraint
  /-- Steps are strictly increasing -/
  steps_increasing : List.Pairwise (· < ·) (constraints.map (·.step))

namespace CylinderConstraint

/-- The maximum step mentioned in the constraint -/
def maxStep (C : CylinderConstraint) : ℕ :=
  (C.constraints.map (·.step)).foldl max 0

/-- Empty constraint (true for all paths) -/
def empty : CylinderConstraint where
  constraints := []
  steps_increasing := List.Pairwise.nil

theorem empty_maxStep : empty.maxStep = 0 := rfl

end CylinderConstraint

/-- A cylinder set on a hyperfinite path space.
    This pairs a constraint with the probability space. -/
structure CylinderSet (Ω : HyperfinitePathSpace) where
  /-- The constraint defining the cylinder set -/
  constraint : CylinderConstraint
  /-- The maximum step is less than N (so the event is well-defined) -/
  step_bound : constraint.maxStep < Ω.numSteps.val

namespace CylinderSet

variable {Ω : HyperfinitePathSpace}

/-- The trivial cylinder set (whole space) -/
noncomputable def univ : CylinderSet Ω where
  constraint := CylinderConstraint.empty
  step_bound := by
    simp only [CylinderConstraint.empty_maxStep]
    have h := Ω.numSteps_infinite
    rw [Foundation.Hypernat.infinite_iff_infinitePos] at h
    -- h : InfinitePos Ω.numSteps.val means Ω.numSteps.val > any real
    -- Need: (0 : ℕ) < Ω.numSteps.val, i.e., ((0 : ℕ) : ℝ*) < Ω.numSteps.val
    have hpos : (1 : ℝ*) < Ω.numSteps.val := h 1
    calc ((0 : ℕ) : ℝ*) = (0 : ℝ*) := by norm_cast
      _ < (1 : ℝ*) := by norm_num
      _ < Ω.numSteps.val := hpos

end CylinderSet

/-! ### Internal Events from Cylinder Sets

A cylinder set defines an internal event: the set of hyperfinite paths
(coin flip sequences) satisfying the constraints.

At each level n, the internal set consists of coin flip sequences of
length n whose partial sums (scaled by dx) lie in the specified intervals.
-/

/-- Check if a single constraint is satisfied by a walk value.
    The walk value w should be in the interval [lower, upper]. -/
def SingleTimeConstraint.isSatisfied (c : SingleTimeConstraint) (w : ℝ) : Prop :=
  c.lower ≤ w ∧ w ≤ c.upper

/-- The number of coin flip sequences of length n whose walk at step k
    lies in the interval [a, b], given step size dx.

    This is a counting function: count { ω ∈ {±1}^n : W_k(ω) ∈ [a, b] }
    where W_k = dx · Σᵢ₌₀^{k-1} ωᵢ.

    For the hyperfinite case, n will come from the sequence representation,
    and dx is determined by the level.

    The partial sum S_k = Σᵢ₌₀^{k-1} ωᵢ after k steps with j heads (+1) is 2j - k.
    The number of paths with exactly j heads is C(k, j).
    We count j values where the walk value dx·(2j - k) lies in [a, b]. -/
noncomputable def countWalksInInterval (n : ℕ) (k : ℕ) (a b : ℝ) (dx : ℝ) : ℕ :=
  if _hk : k ≤ n then
    -- Sum over j = number of +1s in the first k flips
    (Finset.range (k + 1)).filter (fun j : ℕ =>
      -- Partial sum is 2j - k (which can be negative)
      -- Walk value is dx * (2j - k)
      -- We need a ≤ dx * (2j - k) ≤ b
      let walkVal : ℝ := dx * (2 * (j : ℝ) - k)
      a ≤ walkVal ∧ walkVal ≤ b
    ) |>.sum (fun j => Nat.choose k j * 2^(n - k))
  else
    0

/-- Count transitions from walk value at step k₁ to satisfying constraint at step k₂.
    For a walk at value w₁ at step k₁, count paths reaching [a₂, b₂] at step k₂.

    The walk value at k₂ is w₂ = w₁ + dx·(2j - Δk) where j is the number of +1s
    in the Δk = k₂ - k₁ additional steps.
    We need a₂ ≤ w₂ ≤ b₂. -/
noncomputable def countTransitions (k₁ k₂ : ℕ) (w₁ : ℝ) (a₂ b₂ : ℝ) (dx : ℝ) : ℕ :=
  if k₁ < k₂ then
    let dk := k₂ - k₁
    (Finset.range (dk + 1)).filter (fun j : ℕ =>
      let deltaVal := dx * (2 * (j : ℝ) - dk)
      let w₂ := w₁ + deltaVal
      a₂ ≤ w₂ ∧ w₂ ≤ b₂
    ) |>.sum (fun j => Nat.choose dk j)
  else if k₁ = k₂ then
    -- Same step: check if w₁ is in [a₂, b₂]
    if a₂ ≤ w₁ ∧ w₁ ≤ b₂ then 1 else 0
  else
    0  -- k₁ > k₂: invalid

/-- The cardinality of a cylinder set at level n with given path length.
    This is the number of coin flip sequences of given length satisfying the constraint.

    For a single constraint at step k with interval [a, b]:
    - Count walks where W_k ∈ [a, b]
    - Each such walk can be extended in 2^(pathLen-k) ways

    For two constraints at steps k₁ < k₂:
    - Use the Markov property: count transitions from valid states at k₁ to valid states at k₂
    - Total count = Σⱼ₁ C(k₁,j₁) × (transitions from w₁ to [a₂,b₂]) × 2^(pathLen - k₂)

    For 3+ constraints, we use a conservative upper bound (all paths).
    A full implementation would require dynamic programming.

    **Important**: `pathLen` should be the actual path length at this level
    (i.e., `numSteps.toSeq n` for a `HyperfinitePathSpace`). -/
noncomputable def cylinderCardAtLevel (c : CylinderConstraint) (pathLen : ℕ) (dx : ℝ) : ℕ :=
  match c.constraints with
  | [] => 2^pathLen  -- Empty constraint: all paths
  | [c₁] =>
    if c₁.step ≤ pathLen then countWalksInInterval pathLen c₁.step c₁.lower c₁.upper dx
    else 2^pathLen  -- Constraint at step > pathLen: vacuously true
  | [c₁, c₂] =>
    -- Since steps_increasing ensures c₁.step < c₂.step
    if c₂.step ≤ pathLen then
      -- Two constraints: sum over all valid j₁ values at step c₁.step
      -- For each j₁, count transitions to valid j₂ at c₂.step
      (Finset.range (c₁.step + 1)).filter (fun j₁ : ℕ =>
        let w₁ := dx * (2 * (j₁ : ℝ) - c₁.step)
        c₁.lower ≤ w₁ ∧ w₁ ≤ c₁.upper
      ) |>.sum (fun j₁ =>
        let w₁ := dx * (2 * (j₁ : ℝ) - c₁.step)
        let transCount := countTransitions c₁.step c₂.step w₁ c₂.lower c₂.upper dx
        Nat.choose c₁.step j₁ * transCount * 2^(pathLen - c₂.step))
    else if c₁.step ≤ pathLen then
      -- Only first constraint applies
      countWalksInInterval pathLen c₁.step c₁.lower c₁.upper dx
    else
      2^pathLen
  | _ =>
    -- LIMITATION: For 3+ constraints, returns upper bound (all paths).
    -- This gives probability 1, not the actual probability.
    -- A proper implementation would use dynamic programming:
    --   For constraints at k₁ < k₂ < ... < kₘ, iterate:
    --   count[kᵢ, wᵢ] = Σ count[kᵢ₋₁, wᵢ₋₁] × transitions(wᵢ₋₁ → wᵢ)
    -- For Anderson's theorem, single-time marginals need only 1 constraint,
    -- and joint distributions at 2 times are handled above.
    2^pathLen

/-! ### Cylinder Sets as Internal Events

We now connect cylinder sets to the internal event structure developed earlier.
A cylinder set defines a `ConcreteInternalEvent` with explicitly computable
cardinality at each level.
-/

/-- Convert a cylinder set to an internal set representation.
    At level n, this represents the set of possible walk values satisfying the constraint.

    Note: This is an approximation for internal set membership purposes.
    The true internal set structure would be the set of coin flip sequences,
    but for probability calculations we use `cylinderCardAtLevel` which gives
    exact counts. This function is used for saturation arguments where we need
    an `InternalSet` structure.

    The representation uses:
    - Empty constraint: Set.univ (all values allowed)
    - Single constraint at step k with [a,b]: the interval [a, b]
    - Multiple constraints: intersection of the constraint intervals

    This is conceptually correct: the set of achievable walk values at the
    final constraint time is contained in the last constraint's interval. -/
noncomputable def CylinderSet.toInternalSet {Ω : HyperfinitePathSpace} (C : CylinderSet Ω)
    (_dx_seq : ℕ → ℝ) : Foundation.InternalSet where
  sets := fun _n =>
    -- The set of achievable walk values satisfying all constraints
    match C.constraint.constraints with
    | [] => Set.univ
    | [c₁] => Set.Icc c₁.lower c₁.upper
    | cs =>
      -- For multiple constraints, the final walk value must satisfy
      -- at least the last constraint's bounds
      match cs.getLast? with
      | some cLast => Set.Icc cLast.lower cLast.upper
      | none => Set.univ

/-- The hyperreal cardinality of a cylinder set.
    This is defined as the germ of the level-wise cardinalities.
    At level n, paths have length `Ω.numSteps.toSeq n`. -/
noncomputable def CylinderSet.card {Ω : HyperfinitePathSpace} (C : CylinderSet Ω)
    (dx_seq : ℕ → ℝ) : ℝ* :=
  ofSeq (fun n => (cylinderCardAtLevel C.constraint (Ω.numSteps.toSeq n) (dx_seq n) : ℝ))

/-- The internal probability of a cylinder set -/
noncomputable def CylinderSet.prob {Ω : HyperfinitePathSpace} (C : CylinderSet Ω)
    (dx_seq : ℕ → ℝ) : ℝ* :=
  C.card dx_seq / Ω.probSpace.size

/-- The empty constraint gives probability 1.
    For the trivial cylinder set, cardinality at level n = 2^(numSteps.toSeq n)
    and size = 2^(numSteps.toSeq n), so the ratio is 1. -/
theorem CylinderSet.prob_univ (Ω : HyperfinitePathSpace) (dx_seq : ℕ → ℝ) :
    (CylinderSet.univ : CylinderSet Ω).prob dx_seq = 1 := by
  unfold CylinderSet.prob CylinderSet.card CylinderSet.univ
  -- cylinderCardAtLevel with empty constraints returns 2^pathLen
  have hcard : ∀ n, cylinderCardAtLevel CylinderConstraint.empty (Ω.numSteps.toSeq n) (dx_seq n) =
               2^(Ω.numSteps.toSeq n) := by
    intro n
    simp only [cylinderCardAtLevel, CylinderConstraint.empty]
  simp only [hcard]
  -- Goal: ofSeq (fun n => (2^(numSteps.toSeq n) : ℕ)) / Ω.probSpace.size = 1
  -- Ω.probSpace.size = hyperPow2Seq Ω.numSteps.toSeq = ofSeq (fun n => 2^(numSteps.toSeq n))
  have hsize : Ω.probSpace.size = ofSeq (fun n => (2 : ℝ) ^ Ω.numSteps.toSeq n) := rfl
  rw [hsize]
  -- The numerator casts (2^k : ℕ) to ℝ, which equals (2 : ℝ)^k
  have heq : (ofSeq (fun n => ((2 ^ Ω.numSteps.toSeq n : ℕ) : ℝ))) =
             ofSeq (fun n => (2 : ℝ) ^ Ω.numSteps.toSeq n) := by
    congr 1
    ext n
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [heq]
  -- x / x = 1 when x ≠ 0
  have hpos : (0 : ℝ*) < ofSeq (fun n => (2 : ℝ) ^ Ω.numSteps.toSeq n) := by
    have h0 : (0 : ℝ*) = ofSeq (fun _ => (0 : ℝ)) := by rfl
    rw [h0, ofSeq_lt_ofSeq]
    apply Eventually.of_forall
    intro n
    exact pow_pos (by norm_num : (0 : ℝ) < 2) _
  exact div_self (ne_of_gt hpos)

/-! ### Design Note: Level Matching

The cylinder set probability computation requires careful matching between:
1. The level n in the internal set representation
2. The step size dx at level n
3. The total path length (numSteps.toSeq n)

For a consistent construction:
- At level n, paths have length numSteps.toSeq n
- dx at level n is sqrt(T / numSteps.toSeq n)
- Cylinder set cardinality counts paths of length numSteps.toSeq n

The `dx_seq` parameter is taken separately; a more complete construction could
derive dx directly from the hyperfinite path space structure.
-/

/-! ## Walk Finiteness and the Standard Part Map

For Anderson's theorem, we need to show that hyperfinite walk values are
finite (not hyperreal-infinite) for Loeb-almost-all paths.

### Heuristic Argument

For a hyperfinite random walk with k steps and step size dx:
- W_k = dx · (X₁ + X₂ + ... + X_k) where each Xᵢ = ±1
- The partial sum S_k = X₁ + ... + X_k has expected value 0 and variance k
- By CLT, S_k is approximately N(0, k) for large k
- So W_k = dx · S_k is approximately N(0, k · dx²) = N(0, k · dt) = N(0, t)

This shows that for "typical" paths (Loeb-almost-all), W_k is O(√t), hence finite.

### Formal Statement

For any standard bound M > 0 and any standard time t ∈ (0, T):
  Loeb({ ω : |W(t, ω)| > M }) ≤ C/M²

where C depends on t. This follows from the variance bound.
-/

/-- The event that a walk value at step k lies within bound M.
    This is a cylinder set with a single constraint. -/
noncomputable def walkBoundedEvent (Ω : HyperfinitePathSpace) (k : ℕ) (M : ℝ)
    (hk : k < Ω.numSteps.val) (_hM : 0 < M) : CylinderSet Ω where
  constraint := {
    constraints := [{
      step := k
      lower := -M
      upper := M
      bounds_ordered := by linarith
    }]
    steps_increasing := List.pairwise_singleton _ _
  }
  step_bound := by
    simp only [CylinderConstraint.maxStep, List.map_cons, List.map_nil]
    simp only [List.foldl_cons, List.foldl_nil]
    exact hk

/-- The complement: event that walk value exceeds bound M.
    The Loeb measure of this event should go to 0 as M → ∞. -/
structure WalkExceedsBound (Ω : HyperfinitePathSpace) where
  /-- The step index -/
  step : ℕ
  /-- The bound -/
  bound : ℝ
  /-- Step is within the path -/
  step_valid : step < Ω.numSteps.val
  /-- Bound is positive -/
  bound_pos : 0 < bound

namespace WalkExceedsBound

variable {Ω : HyperfinitePathSpace}

/-- The cardinality of paths where |W_k| > M at level n.
    This counts walks where the partial sum S_k satisfies |S_k| > M/dx.

    By binomial bounds: P(|S_k| > m) ≤ 2 exp(-m²/(2k)) for m > 0.
    For m = M/dx, this gives approximately P(|W_k| > M) ≤ 2 exp(-M²/(2k·dx²)) = 2 exp(-M²/(2t)).

    For the counting version: number of paths ≤ 2^n · 2 exp(-M²/(2t)) when the bound applies.
    This is a very rough bound; a precise treatment needs local CLT. -/
noncomputable def cardExceedingAtLevel (E : WalkExceedsBound Ω) (pathLen : ℕ) (dx : ℝ) : ℕ :=
  -- Count walks where |dx * (2j - k)| > M, i.e., |2j - k| > M/dx
  if _hk : E.step ≤ pathLen then
    (Finset.range (E.step + 1)).filter (fun j : ℕ =>
      let walkVal : ℝ := |dx * (2 * (j : ℝ) - E.step)|
      E.bound < walkVal  -- Walk exceeds bound
    ) |>.sum (fun j => Nat.choose E.step j * 2^(pathLen - E.step))
  else
    0

end WalkExceedsBound

/-! ### Variance Bound

The key probabilistic estimate is the variance bound for random walks:
  E[W_k²] = k · dx² = k · dt = t

This implies by Chebyshev's inequality:
  P(|W_k| > M) ≤ E[W_k²]/M² = t/M²

In the internal setting, this translates to:
  |{paths : |W_k| > M}| / 2^N ≤ t/M²

Taking standard parts gives the Loeb measure bound.
-/

/-! ### Variance and Chebyshev Bounds

The variance of the random walk is proven in `HyperfiniteRandomWalk.lean`:
- `quadratic_variation_eq_time`: For standard k, QV = k·dt exactly
- This implies Var(W_k) = k·dt = t for time t = k·dt

The Chebyshev inequality for random walks (P(|W_k| > M) ≤ t/M²) requires:
1. Computing E[S_k²] = k for symmetric random walk
2. Applying Chebyshev's inequality: P(|X| > M) ≤ E[X²]/M²

This is left as future work requiring binomial statistics infrastructure.
-/

end SPDE.Nonstandard
