# Riemann Sum Bound: Detailed Proof Strategy

## Goal
Prove h_upper and h_lower sorrys in `CylinderConvergenceHelpers.lean:1171-1175`:
```
h_upper : S_val ≤ I_val + ε * (b - a) + 2 * M * Δ
h_lower : I_val ≤ S_val + ε * (b - a) + 2 * M * Δ
```

## Context
- `g = gaussianDensitySigma(√t)`, continuous, non-negative, bounded by `M = 1/(√t√(2π))`
- `S_val = Σ_{j ∈ range(k+1)} (if a ≤ x_j ≤ b then g(x_j) * Δ else 0)`
- `I_val = ∫_{[a,b]} g`
- Lattice: `x_j = (2j - k)/√N`, spacing `Δ = 2/√N`
- UC: `∀ x y ∈ [a,b], dist(x,y) < η → dist(g(x),g(y)) < ε`
- Key bounds: `Δ < η` and `3MΔ < δ/2`

## CRITICAL BUG: h_lower with 2MΔ may be FALSE

The correct analysis gives:
- h_upper: `S ≤ I + ε*(b-a) + MΔ` (always true)
- h_lower: `I ≤ S + ε*(b-a+Δ) + MΔ` (always true)

For h_lower to give `I ≤ S + ε*(b-a) + 2MΔ` we need `εΔ ≤ MΔ` i.e. `ε ≤ M`.
Since `ε = δ/(2(b-a+1))` and `M = 1/(√t√(2π))`, this fails when δ is large relative to M*(b-a+1).

### Fix: Ensure Δ ≤ 1

Add `max ... 4` to N₀ so that `N ≥ 4`, giving `√N ≥ 2`, hence `Δ = 2/√N ≤ 1`.

With `Δ ≤ 1`:
- h_lower bound: `ε*(b-a+Δ) + MΔ ≤ ε*(b-a+1) + MΔ`
- For combining step: need `ε*(b-a+1) + MΔ ≤ ε*(b-a+1) + 3MΔ` ✓

### Recommended: Change bounds to

```
h_upper : S_val ≤ I_val + ε * (b - a) + M * Δ
h_lower : I_val ≤ S_val + ε * (b - a + 1) + M * Δ
```

These are always provable (with Δ ≤ 1 for h_lower), and the combining step gives:
```
|S - I| ≤ ε*(b-a+1) + MΔ ≤ ε*(b-a+1) + 3MΔ  ✓
```

---

## Proof of h_upper: S ≤ I + ε*(b-a) + MΔ

### Strategy: Right-bin decomposition

Define J = {j ∈ range(k+1) : a ≤ x_j ≤ b} (lattice points in [a,b]).
Split J into:
- J₁ = {j ∈ J : x_j + Δ ≤ b} (interior: right bin [x_j, x_j+Δ) ⊂ [a,b])
- J₂ = J \ J₁ = {j ∈ J : x_j > b - Δ} (boundary)

**Interior bound** (j ∈ J₁):
- R_j = Set.Ico (x_j) (x_j + Δ) is the "right bin"
- R_j ⊂ [a, b] (since x_j ≥ a from J, x_j + Δ ≤ b from J₁)
- For y ∈ R_j: |y - x_j| < Δ < η and y ∈ [a,b], x_j ∈ [a,b]
- By UC: g(x_j) ≤ g(y) + ε
- So: g(x_j) * Δ = ∫_{R_j} g(x_j) ≤ ∫_{R_j} (g + ε) = ∫_{R_j} g + ε*Δ
- Summing: Σ_{J₁} g(x_j)*Δ ≤ Σ_{J₁} ∫_{R_j} g + ε*|J₁|*Δ

**Key facts about right bins**:
- R_j are pairwise disjoint (for j₁ < j₂: x_{j₂} ≥ x_{j₁} + Δ since spacing = Δ)
- R_j ⊂ [a,b] for j ∈ J₁
- g ≥ 0 everywhere
- Therefore: Σ_{J₁} ∫_{R_j} g ≤ ∫_{[a,b]} g = I (by integral_finset_biUnion + setIntegral_mono_set)
- Also: |J₁|*Δ ≤ b - a (disjoint bins of width Δ inside [a,b])

**Boundary bound** (j ∈ J₂):
- |J₂| ≤ 1 (lattice spacing = Δ, boundary region (b-Δ, b] has length < Δ)
- Each term: g(x_j)*Δ ≤ M*Δ
- Total: Σ_{J₂} g(x_j)*Δ ≤ MΔ

**Combine**: S = Σ_{J₁} + Σ_{J₂} ≤ (I + ε*(b-a)) + MΔ

### Lean proof sketch for h_upper

```lean
-- 1. Filter the sum
-- Rewrite S_val using Finset.sum_filter to get sum over J
-- 2. Split J into J₁ (interior) and J₂ (boundary)
-- Use Finset.filter and sdiff
-- 3. Bound boundary: Σ_{J₂} ≤ MΔ
-- Show |J₂| ≤ 1 via lattice spacing argument
-- Each term ≤ MΔ via hg_le
-- 4. Bound interior: Σ_{J₁} ≤ I + ε*(b-a)
-- Per-bin: g(x_j)*Δ ≤ ∫_{R_j} g + ε*Δ
--   Use setIntegral_mono and setIntegral_const
-- Sum of integrals: Σ ∫_{R_j} g ≤ I
--   Use integral_finset_biUnion (needs: MeasurableSet, PairwiseDisjoint, IntegrableOn)
--   Then setIntegral_mono_set (needs: IntegrableOn, 0 ≤ᵐ f, s ≤ᵐ t)
-- |J₁|*Δ ≤ b-a from disjoint bins
-- 5. Combine with linarith
```

### Key Mathlib lemmas needed

1. `MeasureTheory.integral_finset_biUnion` — decomposes ∫_{∪ A_i} f = Σ ∫_{A_i} f
   Needs: (t : Finset ι), MeasurableSet (s i), PairwiseDisjoint, IntegrableOn
2. `MeasureTheory.setIntegral_mono_set` — ∫_A f ≤ ∫_B f when A ⊆ B and f ≥ 0
   Needs: IntegrableOn f B, 0 ≤ᵐ[restrict B] f, A ≤ᵐ B
3. `MeasureTheory.setIntegral_const` — ∫_s c = μ.real s • c
4. `MeasureTheory.setIntegral_mono` — pointwise f ≤ g → ∫_s f ≤ ∫_s g
   Needs: IntegrableOn f s, IntegrableOn g s, f ≤ g a.e. on s
5. `Real.volume_Ico` (or `MeasureTheory.Measure.real`) for volume of Ico interval

### Disjointness proof

For j₁ ≠ j₂ in J₁: Set.Ico (x_{j₁}) (x_{j₁}+Δ) ∩ Set.Ico (x_{j₂}) (x_{j₂}+Δ) = ∅

Proof: WLOG j₁ < j₂. Then x_{j₂} = x_{j₁} + (j₂-j₁)*Δ ≥ x_{j₁} + Δ.
So the second interval starts at x_{j₂} ≥ x_{j₁} + Δ, which is the right endpoint of the first.
Since Set.Ico is right-open: y < x_{j₁}+Δ ≤ x_{j₂} for y ∈ first bin, so y ∉ second bin.

In Lean: reduce to showing (2*j₂ - k)/√N ≥ (2*j₁ - k)/√N + Δ, i.e.,
2*(j₂ - j₁)/√N ≥ 2/√N, i.e., j₂ - j₁ ≥ 1, i.e., j₂ > j₁ (from j₁ ≠ j₂ and j₁ < j₂).

### |J₂| ≤ 1 proof

J₂ = {j ∈ J : x_j > b - Δ} = {j ∈ range(k+1) : a ≤ x_j ≤ b ∧ x_j > b - Δ}
So x_j ∈ (b-Δ, b]. Length = Δ. Lattice spacing = Δ.
In interval (b-Δ, b] of length Δ with points spaced Δ apart: at most 1 point.
Proof: if j₁, j₂ ∈ J₂ with j₁ < j₂, then x_{j₂} - x_{j₁} ≥ Δ.
But both in (b-Δ, b], so x_{j₂} - x_{j₁} < Δ. Contradiction.
(In Lean: show J₂.card ≤ 1 using Finset.card_le_one)

---

## Proof of h_lower: I ≤ S + ε*(b-a+1) + MΔ (with Δ ≤ 1)

### Strategy: Centered-bin decomposition + gap bound

Define centered bins C_j = Set.Ico (x_j - Δ/2) (x_j + Δ/2) for j ∈ J.

**Decompose [a,b]**:
```
I = ∫_{[a,b]} g = ∫_{[a,b] ∩ ∪C_j} g + ∫_{[a,b] \ ∪C_j} g
```

**Part 1: Covered region**
```
∫_{[a,b] ∩ ∪C_j} g = Σ_{j∈J} ∫_{C_j ∩ [a,b]} g   (disjoint bins)
```
For each j ∈ J, y ∈ C_j ∩ [a,b]:
- |y - x_j| < Δ/2 < Δ < η
- y ∈ [a,b], x_j ∈ [a,b]
- By UC: g(y) ≤ g(x_j) + ε
- So: ∫_{C_j ∩ [a,b]} g ≤ (g(x_j) + ε) * |C_j ∩ [a,b]| ≤ (g(x_j) + ε) * Δ

Summing: Σ ∫_{C_j ∩ [a,b]} g ≤ Σ (g(x_j) + ε)*Δ = S + ε*|J|*Δ

**Bound on |J|*Δ**:
- |J| ≤ ⌊(b-a)/Δ⌋ + 1 ≤ (b-a)/Δ + 1
- |J|*Δ ≤ b - a + Δ ≤ b - a + 1 (using Δ ≤ 1)
- So: ε*|J|*Δ ≤ ε*(b - a + 1)

**Part 2: Gap (uncovered region)**
The gap = [a,b] \ ∪_{j∈J} C_j.

Claim: |gap| ≤ Δ.
Proof: For any y ∈ [a + Δ/2, b - Δ/2], the nearest lattice point x_j has |y - x_j| ≤ Δ/2
(spacing = Δ). And x_j ∈ [y - Δ/2, y + Δ/2] ⊂ [a, b], so j ∈ J and y ∈ C_j.
Therefore gap ⊂ [a, a+Δ/2) ∪ (b-Δ/2, b], which has measure ≤ Δ.

So: ∫_{gap} g ≤ M * Δ.

**Combine**: I ≤ S + ε*(b-a+1) + MΔ

### Lean proof sketch for h_lower

```lean
-- 1. Decompose ∫_{[a,b]} g using covered/gap regions
-- Use MeasureTheory.integral_add_compl or similar
-- 2. Bound covered region
-- Use integral_finset_biUnion for centered bins (needs disjointness)
-- Then Finset.sum_le_sum with per-bin UC bound
-- Use setIntegral_mono for per-bin: ∫_{C_j∩[a,b]} g ≤ (g(x_j)+ε) * Δ
-- 3. Bound |J|*Δ ≤ b-a+1
-- 4. Bound gap measure ≤ Δ, hence gap integral ≤ MΔ
-- 5. Combine with linarith
```

### Centered-bin disjointness

C_j = Set.Ico ((2j-k-1)/√N) ((2j-k+1)/√N)
For j₁ < j₂: upper endpoint of C_{j₁} = (2j₁-k+1)/√N ≤ (2j₂-k-1)/√N = lower endpoint of C_{j₂}
(since j₂ ≥ j₁ + 1 implies 2j₂ - k - 1 ≥ 2j₁ - k + 1)

Same argument as right-bin disjointness.

---

## Required Code Changes

### 1. Modify N₀ (line 1086)

Change:
```lean
refine ⟨max (max (⌈4 / η ^ 2⌉₊ + 1) (⌈144 * M ^ 2 / δ ^ 2⌉₊ + 1)) N₃, fun N hN => ?_⟩
```
To:
```lean
refine ⟨max (max (max (⌈4 / η ^ 2⌉₊ + 1) (⌈144 * M ^ 2 / δ ^ 2⌉₊ + 1)) 4) N₃, fun N hN => ?_⟩
```

### 2. Update N extraction (lines 1090-1094)

```lean
have hN_large₁ : ⌈4 / η ^ 2⌉₊ + 1 ≤ N :=
  le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN))
have hN_large₂ : ⌈144 * M ^ 2 / δ ^ 2⌉₊ + 1 ≤ N :=
  le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN))
have hN_ge4 : 4 ≤ N :=
  le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
have hN₃ : N₃ ≤ N := le_trans (le_max_right _ _) hN
```

### 3. Derive Δ ≤ 1

```lean
have hΔ_le_one : Δ ≤ 1 := by
  rw [hΔ_def, div_le_one hsqN_pos]
  have : (4 : ℝ) ≤ ↑N := by exact_mod_cast hN_ge4
  calc (2 : ℝ) ≤ Real.sqrt 4 := by norm_num
    _ ≤ Real.sqrt ↑N := Real.sqrt_le_sqrt this
```
(Need to check: `Real.sqrt 4 = 2` may need `norm_num` or manual proof.)

### 4. Change h_upper and h_lower bounds

```lean
have h_upper : S_val ≤ I_val + ε * (b - a) + M * Δ := by
  sorry -- right-bin argument
have h_lower : I_val ≤ S_val + ε * (b - a + 1) + M * Δ := by
  sorry -- centered-bin argument + Δ ≤ 1
```

### 5. Adjust combining step

```lean
rw [abs_le]
constructor
· -- -(ε*(b-a+1) + 3MΔ) ≤ S - I, i.e., I - S ≤ ε*(b-a+1) + 3MΔ
  -- From h_lower: I ≤ S + ε*(b-a+1) + MΔ, so I - S ≤ ε*(b-a+1) + MΔ ≤ ... + 3MΔ
  nlinarith [mul_pos hM_pos hΔ_pos]
· -- S - I ≤ ε*(b-a+1) + 3MΔ
  -- From h_upper: S ≤ I + ε*(b-a) + MΔ, so S - I ≤ ε*(b-a) + MΔ ≤ ... + 3MΔ
  nlinarith [mul_pos hM_pos hΔ_pos, hε_pos]
```

---

## Infrastructure needed (not in Mathlib)

### Integral of constant on Ico
```lean
∫ x in Set.Ico a b, (c : ℝ) = c * (b - a)
```
From `setIntegral_const`: ∫ x in s, c = μ.real s • c, plus `volume.real (Set.Ico a b) = b - a`.

### Per-bin integral bound
```lean
-- If ∀ x ∈ S, f(x) ≤ g(x), S measurable, f,g integrable on S:
-- ∫_S f ≤ ∫_S g
```
This is `MeasureTheory.setIntegral_mono` (available in Mathlib).

### Finset cardinality bound for boundary
```lean
-- Lattice points in (c, c+Δ] with spacing Δ: at most 1
-- Proof: any two such points j₁ < j₂ have x_{j₂} - x_{j₁} ≥ Δ > c+Δ - c = Δ. Contradiction.
```

---

## Estimated Complexity

- h_upper proof: ~80-100 lines
  - Filter rewrite: ~10 lines
  - J₁/J₂ split: ~10 lines
  - Disjointness of right bins: ~15 lines
  - Per-bin UC bound: ~15 lines
  - integral_finset_biUnion application: ~15 lines
  - setIntegral_mono_set: ~10 lines
  - |J₂| ≤ 1: ~10 lines
  - Combining: ~5 lines

- h_lower proof: ~80-100 lines (similar structure)

- N₀ modification + Δ ≤ 1: ~15 lines

**Total: ~180-215 lines**

---

## Alternative Approach: Avoid integral_finset_biUnion

If `integral_finset_biUnion` proves too complex to apply, an alternative for
"Σ ∫_{R_j} g ≤ ∫_{[a,b]} g" is:

1. Define step function `h(y) = g(x_j)` on R_j, `h(y) = 0` elsewhere
2. Show `h ≤ g + ε` pointwise on [a,b] (by UC)
3. S = ∫ h ≤ ∫ (g + ε) = I + ε*(b-a)
4. This avoids sum-of-integrals ≤ integral entirely

But defining and integrating the step function `h` may be equally complex in Lean.

## Status
- [x] Analysis complete, bounds verified
- [x] Mathlib lemma signatures checked
- [x] Code change plan written
- [ ] N₀ modification implemented
- [ ] h_upper proof written
- [ ] h_lower proof written
- [ ] File compiles with 0 sorrys in this theorem
