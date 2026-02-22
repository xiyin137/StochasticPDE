# Plan: Completing Anderson's Theorem

## Goal
Eliminate all 9 remaining sorrys in the Nonstandard module. The primary target is **Anderson's theorem**: the pushforward of Loeb measure under the standard part map equals Wiener measure.

## Dependency Graph (updated 2026-02-22)

```
anderson_theorem (PROVEN, delegates to anderson_theorem_cylinder)
  └── anderson_theorem_cylinder (SORRY #1 — AndersonTheorem.lean:516)
        └── cylinder_prob_convergence (SORRY #2 — LocalCLT.lean:1144) ← NEXT TARGET
              ├── scaledProb_eq_walkIntervalProb (PROVEN ✓)
              ├── binomProb_ratio_near_one (PROVEN ✓)
              ├── gaussDensity_Riemann_sum_converges (PROVEN ✓ — 2026-02-22)
              │     └── gaussianDensitySigma_continuous (PROVEN ✓)
              └── binomial_tail_small (PROVEN ✓, Chernoff bounds)

local_clt_error_bound (SORRY #3 — LocalCLT.lean:185, standalone, NOT on critical path)

ito_correspondence       (SORRY #4  — ItoCorrespondence.lean:202)
ito_isometry_standard    (SORRY #5  — ItoCorrespondence.lean:229)
ito_lemma_hyperfinite    (SORRY #6  — ItoCorrespondence.lean:373)
ito_formula              (SORRY #7  — ItoCorrespondence.lean:406)
gbm_explicit_solution    (SORRY #8  — ExplicitSolutions.lean:81)
ou_explicit_solution     (SORRY #9  — ExplicitSolutions.lean:112)
```

**Priority order**: #2 → #1 (critical path), then #4–#7 (Ito chain), then #8–#9 (explicit solutions). #3 can be skipped (superseded by ratio approach).

---

## Phase A: Critical Path (2 remaining sorrys)

### A1. `gaussDensity_Riemann_sum_converges` — PROVEN ✓ (2026-02-22)

**File**: `CylinderConvergenceHelpers.lean:1020-1670` (fully proven, 0 sorrys)

Used Option 1 (direct UC argument). See `riemann_sum_bound.md` for detailed implementation notes. The proof was ~650 lines total including helper infrastructure. Key insight: the h_lower bound required a "crossing zone" argument for gap bins, not just the centered-bin decomposition originally planned.

---

### A2. `cylinder_prob_convergence` (SORRY #2) — NEXT TARGET

**File**: `LocalCLT.lean:1131-1144`

**Statement**: For a single time t and interval [a,b] with a < b:
```
  |scaledProb_N - ∫_{a}^{b} gaussianDensitySigma(√t, x) dx| < ε
```
where scaledProb_N = #{flips : partialSumFin(N,flips,⌊tN⌋)/√N ∈ [a,b]} / 2^N.

**All prerequisites are now PROVEN**:
- `scaledProb_eq_walkIntervalProb` (CylinderConvergenceHelpers.lean:373): scaledProb = walkIntervalProb k a b (1/√N)
  - walkIntervalProb = Σ_{j=0}^{k} walkValInInterval(k, j, a, b, 1/√N)
  - walkValInInterval checks if (2j-k)/√N ∈ [a,b] and returns C(k,j)/2^k
- `binomProb_ratio_near_one` (CylinderConvergenceHelpers.lean:996): for large N, |C(k,j)/2^k / (g(x_j)·Δ) - 1| < δ
- `gaussDensity_Riemann_sum_converges` (CylinderConvergenceHelpers.lean:1020): Σ g(x_j)·Δ → ∫g
- `binomial_tail_small` (CylinderConvergenceHelpers.lean:1884): Chernoff tail bound

**Proof strategy (triangle inequality)**:

The key idea: decompose |scaledProb - ∫g| into two pieces via triangle inequality.

```
scaledProb = walkIntervalProb k a b (1/√N)           [by scaledProb_eq_walkIntervalProb]
           = Σ_{j: x_j ∈ [a,b]} C(k,j)/2^k          [expanding walkValInInterval/binomialWalkProb]

RiemannSum = Σ_{j: x_j ∈ [a,b]} g(x_j) · Δ          [Δ = 2/√N]

|scaledProb - ∫g| ≤ |Σ binom_j - Σ gauss_j·Δ| + |Σ gauss_j·Δ - ∫g|
                    └────── term 1 ──────────┘   └──── term 2 ────┘
```

**Term 2** (Riemann sum error): Directly from `gaussDensity_Riemann_sum_converges` with δ₁ = ε/3.

**Term 1** (pointwise ratio → sum error): By `binomProb_ratio_near_one` with δ' chosen below:
- For each j with x_j ∈ [a,b]: |C(k,j)/2^k / (g(x_j)·Δ) - 1| < δ'
- So |C(k,j)/2^k - g(x_j)·Δ| < δ' · g(x_j) · Δ
- Summing: |Σ binom_j - Σ gauss_j·Δ| ≤ δ' · Σ g(x_j) · Δ
- Bound: Σ g(x_j)·Δ ≤ M·(b-a+2) where M = 1/(√t·√(2π)) is the peak bound
  (at most (b-a)/Δ + 2 terms, each ≤ M·Δ)
- Choose δ' = ε / (3·M·(b-a+2)), then term 1 ≤ ε/3

**Combine**: |scaledProb - ∫g| ≤ ε/3 + ε/3 = 2ε/3 < ε. ✓

**Note**: This does NOT need the tail splitting! The ratio bound + Riemann sum convergence together give everything directly, without needing to separate central/tail regions. This is much simpler than originally planned.

**Required hypothesis**: k ≤ N for `scaledProb_eq_walkIntervalProb`. Since k = ⌊tN⌋, this holds when t ≤ 1. For t > 1, we'd need ⌊tN⌋ > N for large N, making the theorem problematic. **Potential fix**: add hypothesis `ht1 : t ≤ 1` or verify that `partialSumFin N flips k` handles k > N correctly.

**Lean proof outline**:
```lean
intro ε hε
-- Step 1: Get N₁ from binomProb_ratio_near_one with δ' = ε/(3*B) where B = M*(b-a+2)
set B := M * (b - a + 2) with hB_def
have hB_pos : 0 < B := ...
set δ' := ε / (3 * B) with hδ'_def
obtain ⟨N₁, hN₁⟩ := binomProb_ratio_near_one a b t ha ht δ' (by positivity)
-- Step 2: Get N₂ from gaussDensity_Riemann_sum_converges with δ₁ = ε/3
obtain ⟨N₂, hN₂⟩ := gaussDensity_Riemann_sum_converges a b t (le_of_lt ha) ht (ε/3) (by linarith)
-- Step 3: N₀ = max(N₁, N₂, ...) with enough to ensure k ≤ N and 0 < N
refine ⟨max (max N₁ N₂) ..., fun N hN => ?_⟩
-- Step 4: Rewrite scaledProb = walkIntervalProb
have h_sp := scaledProb_eq_walkIntervalProb N k hk a b hN_pos
-- Step 5: Triangle inequality
calc |scaledProb - wienerProb|
    ≤ |walkIntervalProb - RiemannSum| + |RiemannSum - wienerProb| := abs_sub_abs_le_abs_sub ...
    _ < ε/3 + ε/3 := add_lt_add h_term1 h_term2
    _ < ε := ...
```

**Estimated complexity**: ~100-150 lines. The main work is:
1. Unfolding walkIntervalProb and relating it term-by-term to the Riemann sum (~30 lines)
2. Applying binomProb_ratio_near_one per-term and summing (~40 lines)
3. Ensuring k ≤ N and N > 0 (~15 lines)
4. Triangle inequality combining step (~15 lines)

---

### A3. `anderson_theorem_cylinder` (SORRY #1)

**File**: `AndersonTheorem.lean:505-516`

**Statement**: For any `CylinderConstraint n`, the pre-Loeb probability equals `wienerCylinderProb c`.

**What `wienerCylinderProb` is**: Product of single-time Gaussian integrals (for independent increments).

**Proof strategy**:

*Case n = 1 (single constraint)*:
Directly follows from `cylinder_prob_convergence` + the definition of `preLoebMeasure` (standard part of the levelwise probability).

Specifically:
- `preLoebMeasure cylinderEvent = st(hyperProb cylinderEvent)`
- At level N, `hyperProb = #{satisfying flips}/2^N = scaledProb`
- By `cylinder_prob_convergence`, scaledProb → wienerCylinderProb as N → ∞
- Since the hyperreal `st` of a sequence converging to L is L (via `isSt_of_tendsto`), we get equality

*Case n ≥ 2 (multiple constraints)*:
This requires the **independence of increments** for the random walk. The key fact is:

For a random walk with independent coin flips, the increments S_{k₂} - S_{k₁} and S_{k₃} - S_{k₂} are independent. This means the joint distribution factors as a product.

**Steps for n ≥ 2**:
1. Decompose the cylinder constraint into increments: (W_{t₁} ∈ [a₁,b₁]) ∧ (W_{t₂}-W_{t₁} ∈ [a₂',b₂']) ∧ ...
2. By independence of increments, the joint probability = product of marginal probabilities
3. Each marginal converges by the n=1 case (`cylinder_prob_convergence`)
4. Product of limits = limit of products

**Infrastructure needed**:
- Independence of random walk increments (combinatorial fact about coin flips)
- Product decomposition of `wienerCylinderProb` (should follow from definition)

**For n = 1**: ~50 lines (connect `cylinder_prob_convergence` to `preLoebMeasure` via `isSt_of_tendsto`)

**For general n**: Additional ~100 lines for the independence/product argument. Alternatively, could prove just n=1 first and leave n≥2 as a separate step.

**Note**: The current `wienerCylinderProb` definition in `WienerMeasure.lean` may need inspection — for n≥2 it likely uses a product of Gaussian densities for increments.

---

## Phase B: Ito Chain (4 sorrys)

These are independent of Phase A and can be worked on in parallel.

### B1. `ito_correspondence` (SORRY #5)

**Statement**: The hyperfinite Ito integral Σ H_k · ΔW_k is not infinite (i.e., has finite standard part), given S-continuity of the path and boundedness of H.

**Proof idea**:
- |H| ≤ M everywhere (by hypothesis)
- The partial sums Σ_{k<K} ε_k (where ε_k = ±1) have magnitude ≈ √K by the walk structure
- So |Σ H_k · ΔW_k| ≤ M · |Σ ε_k| · dx ≈ M · √K · dx = M · √(tN) / √N = M√t
- This is a standard real, hence not infinite

**Technical approach**: Work at the sequence level (via `Germ.coe_eq`). For each n:
- |Σ_{k<K_n} H(k/N_n) · flip_k| ≤ M · max_{j≤K_n} |Σ_{k<j} flip_k|
- By the S-continuity hypothesis, the walk values are bounded
- Multiply by dx_n = 1/√N_n to get the integral bounded

**Estimated**: ~80 lines.

### B2. `ito_isometry_standard` (SORRY #6)

**Statement**: The quadratic variation of the stochastic integral equals the variance sum, up to infinitesimal.

**Proof idea**: By `HyperfiniteStochasticIntegral.ito_isometry`, we have the exact hyperfinite identity Σ(H·ΔW)² = Σ H²·dt. Taking standard parts preserves this equality (both sides are finite by S-continuity + boundedness of H).

**Estimated**: ~40 lines (mostly connecting existing results).

### B3. `ito_lemma_hyperfinite` (SORRY #7)

**Statement**: f(W_K) - f(W_0) = Σ f'(W_k)·ΔW_k + ½Σ f''(W_k)·dt + infinitesimal.

**Proof idea** (Taylor expansion):
1. Telescoping: f(W_K) - f(W_0) = Σ_{k<K} [f(W_{k+1}) - f(W_k)]
2. Taylor: f(W_{k+1}) - f(W_k) = f'(W_k)·ΔW_k + ½f''(W_k)·(ΔW_k)² + R_k
   where R_k = O(|ΔW_k|³) by Taylor remainder with f ∈ C²
3. Since (ΔW_k)² = dt, the second term gives ½f''(W_k)·dt
4. Remainder: Σ R_k = O(K · dx³) = O(t · dt^{1/2}) which is infinitesimal

**Key infrastructure needed**:
- Taylor remainder bound for C² functions (Mathlib has `taylor_mean_remainder` and related)
- Bound on Σ|ΔW_k|³ = K·dx³ (since |ΔW_k| = dx for all k)
- The walk values st(W_k) stay bounded (from S-continuity), so f', f'' are bounded on the range

**Estimated**: ~150 lines (the most substantial proof in this phase).

### B4. `ito_formula` (SORRY #8)

**Statement**: The hyperfinite Ito integral of f' is not infinite.

**Proof idea**: Same as `ito_correspondence` (B1) with H = deriv f. The boundedness of deriv f on the relevant range is given by hypothesis `hf'_bdd`.

**Estimated**: ~50 lines (similar pattern to B1).

---

## Phase C: Explicit Solutions (2 sorrys)

These depend on Phase B (specifically `ito_lemma_hyperfinite`).

### C1. `gbm_explicit_solution` (SORRY #9)

**Proof**: Apply Ito's lemma to f(x) = log(x) with the GBM SDE dX = μX dt + σX dW.
- f'(x) = 1/x, f''(x) = -1/x²
- d(log X) = (1/X)dX - ½(1/X²)(σX)²dt = (μ - σ²/2)dt + σdW
- Integrate and exponentiate

Depends on: `ito_lemma_hyperfinite` + `standardPart_satisfies_sde`

### C2. `ou_explicit_solution` (SORRY #10)

**Proof**: Apply integrating factor e^{θt} to the OU SDE dX = θ(μ-X)dt + σdW.
- d(e^{θt}X) = θμe^{θt}dt + σe^{θt}dW
- Integrate and divide by e^{θt}

Depends on: `ito_lemma_hyperfinite` + stochastic product rule

---

## Phase D: Cleanup

### D1. `local_clt_error_bound` (SORRY #4) — SKIP

This is superseded by the ratio approach in `binomProb_ratio_near_one`. Could either:
- Delete the theorem statement entirely
- Or prove it from `binomProb_ratio_near_one` as a corollary (straightforward but not needed)

**Recommendation**: Mark with a comment that it's superseded and not on any critical path.

---

## Execution Order (updated 2026-02-22)

```
Phase A (critical path — sequential):
  A1: gaussDensity_Riemann_sum_converges  — DONE ✓ (~650 lines)
  A2: cylinder_prob_convergence           (~100-150 lines) ← NEXT
  A3: anderson_theorem_cylinder           (~50-150 lines depending on n=1 vs general)

Phase B (Ito chain — can start in parallel with A):
  B1: ito_correspondence                  (~80 lines)
  B2: ito_isometry_standard               (~40 lines)
  B3: ito_lemma_hyperfinite               (~150 lines)
  B4: ito_formula                         (~50 lines)

Phase C (depends on B3):
  C1: gbm_explicit_solution               (~60 lines)
  C2: ou_explicit_solution                 (~60 lines)
```

**Total remaining**: ~600-750 lines of proof across 8 sorrys (skipping local_clt_error_bound).

## Key Risk: Riemann Sum Convergence — RESOLVED ✓

This was completed on 2026-02-22. The proof used a direct UC argument (Option 1) and was ~650 lines rather than the estimated ~100. The main difficulty was the h_lower bound which required a novel "crossing zone" argument for gap bins.

## Key Risk: Anderson n ≥ 2

The multi-time case requires factoring the joint distribution into independent increments. This is a combinatorial fact about the random walk (coin flips on disjoint index ranges are independent), but formalizing it requires:
- A notion of independence for finite product spaces
- The increment decomposition S_{k₂} - S_{k₁} depends only on flips in [k₁, k₂)
- Product of marginal probabilities = joint probability

This could add significant infrastructure. **Mitigation**: Prove n=1 first (sufficient for single-time Brownian motion properties), defer n≥2.

## Key Risk: t > 1 in cylinder_prob_convergence

The `scaledProb_eq_walkIntervalProb` theorem requires `k ≤ N`. Since k = ⌊tN⌋, this holds for t ≤ 1 but fails for t > 1 (where ⌊tN⌋ > N for large N). Options:
1. Add hypothesis `t ≤ 1` to `cylinder_prob_convergence`
2. Extend `scaledProb_eq_walkIntervalProb` to handle k > N (where partialSumFin truncates)
3. In `anderson_theorem_cylinder`, ensure all times are in (0,1]

For Anderson's theorem on [0,1], option 1 is sufficient.
