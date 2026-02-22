# Plan: Completing Anderson's Theorem

## Goal
Eliminate all 10 sorrys in the Nonstandard module. The primary target is **Anderson's theorem**: the pushforward of Loeb measure under the standard part map equals Wiener measure.

## Dependency Graph

```
anderson_theorem (PROVEN, delegates to anderson_theorem_cylinder)
  └── anderson_theorem_cylinder (SORRY #1 — AndersonTheorem.lean:516)
        └── cylinder_prob_convergence (SORRY #2 — LocalCLT.lean:1144)
              ├── scaledProb_eq_walkIntervalProb (PROVEN)
              ├── binomProb_ratio_near_one (PROVEN)
              ├── gaussDensity_Riemann_sum_converges (SORRY #3 — CylinderConvergenceHelpers.lean:1034)
              │     └── gaussianDensitySigma_continuous (PROVEN)
              └── binomial_tail_small (PROVEN, Chernoff bounds)

local_clt_error_bound (SORRY #4 — LocalCLT.lean:185, standalone, NOT on critical path)

ito_correspondence       (SORRY #5  — ItoCorrespondence.lean:202)
ito_isometry_standard    (SORRY #6  — ItoCorrespondence.lean:229)
ito_lemma_hyperfinite    (SORRY #7  — ItoCorrespondence.lean:373)
ito_formula              (SORRY #8  — ItoCorrespondence.lean:406)
gbm_explicit_solution    (SORRY #9  — ExplicitSolutions.lean:81)
ou_explicit_solution     (SORRY #10 — ExplicitSolutions.lean:112)
```

**Priority order**: #3 → #2 → #1 (critical path), then #5–#8 (Ito chain), then #9–#10 (explicit solutions). #4 can be skipped (superseded by ratio approach).

---

## Phase A: Critical Path (3 sorrys)

### A1. `gaussDensity_Riemann_sum_converges` (SORRY #3)

**File**: `CylinderConvergenceHelpers.lean:1024-1034`

**Statement**: For continuous Gaussian density g on [a,b], the Riemann sum
```
  Σ_{j : a ≤ x_j ≤ b} g(x_j) · Δx  →  ∫_{a}^{b} g(x) dx
```
where x_j = (2j - k)/√N and Δx = 2/√N, with k = ⌊tN⌋.

**Why it's hard**: The sum is over a *lattice* that shifts as N grows; the number of terms grows like (b-a)√N/2. This isn't a standard textbook Riemann sum because the lattice points and the range of summation both depend on N.

**Available infrastructure**:
- `gaussianDensitySigma_continuous` (proven) — the integrand is continuous
- Mathlib's `BoxIntegral` module has `HasIntegral`, `integrable_of_continuousOn`, and convergence of integral sums along tagged partitions
- Mathlib's `MeasureTheory.integral` and `IntervalIntegral` for the target integral

**Proof strategy (two options)**:

*Option 1: Direct ε-δ from uniform continuity.*
Since g = gaussianDensitySigma(√t, ·) is uniformly continuous on [a,b] (continuous on compact):
1. For any ε > 0, pick δ > 0 from UC of g on [a,b]
2. For N large enough, mesh = 2/√N < δ
3. The Riemann sum differs from ∫g by at most ε·(b-a) + tail correction
4. The "tail correction" is that the lattice {x_j} covers [a,b] up to ±Δx at boundaries — bounded by 2·‖g‖_∞·Δx → 0

The main technical work:
- Partition [a,b] into sub-intervals of width Δx = 2/√N
- On each sub-interval, |g(x_j) - g(x)| < ε by UC
- So |Σ g(x_j)Δx - ∫g| ≤ ε(b-a) + boundary terms
- Boundary terms: at most 2 lattice points near a,b contribute O(Δx) error

*Option 2: Via Mathlib's BoxIntegral.*
Construct a tagged partition of [a,b] from the lattice points and appeal to `integrable_of_continuousOn` + `HasIntegral.tendsto`. This would be cleaner but requires navigating the BoxIntegral API (which uses multi-dimensional boxes even for 1D).

**Recommendation**: Option 1 (direct UC argument) is more self-contained and avoids BoxIntegral API complexity. The proof is ~100 lines: UC setup, lattice-to-partition correspondence, summation error bound.

**Key lemmas to develop**:
- `uniform_continuous_on_of_continuous_compact`: g UC on [a,b] (may exist in Mathlib as `IsCompact.uniformContinuousOn_of_continuous`)
- `lattice_covers_interval`: for large N, the lattice {(2j-k)/√N} covers [a,b] up to boundary terms
- `riemann_sum_error_bound`: |Σ f(x_j)Δx - ∫f| ≤ ω(f,δ)·(b-a) + 2‖f‖_∞·Δx where ω is the modulus of continuity

---

### A2. `cylinder_prob_convergence` (SORRY #2)

**File**: `LocalCLT.lean:1131-1144`

**Statement**: For a single time t and interval [a,b]:
```
  |scaledProb_N - ∫_{a}^{b} gaussianDensitySigma(√t, x) dx| < ε
```
where scaledProb_N = #{flips : S_{⌊tN⌋}/√N ∈ [a,b]} / 2^N.

**Available infrastructure** (all proven):
- `scaledProb_eq_walkIntervalProb`: scaledProb = Σ_{j in range} C(k,j)/2^k (fiber decomposition)
- `binomProb_ratio_near_one`: C(k,j)/2^k ≈ gaussianDensitySigma(√t, x_j) · Δx (pointwise ratio → 1)
- `binomial_tail_small`: tail probability outside [-C√k, C√k] is ≤ 2exp(-C²/2) (Chernoff)
- `gaussDensity_Riemann_sum_converges` (SORRY #3, to be proved first)

**Proof strategy**:

Split the sum into central + tail regions:
```
  scaledProb = Σ_{|x_j| ≤ C√k/√N} C(k,j)/2^k + Σ_{|x_j| > C√k/√N} C(k,j)/2^k
```

1. **Tail is small** (both sides):
   - Binomial tail: Σ_{tail} C(k,j)/2^k ≤ 2exp(-C²/2) < ε/4 for C large
   - Gaussian tail: ∫_{|x|>C} g(x) dx < ε/4 for C large (from `gaussian_tail_bound`)

2. **Central region: pointwise ratio → sum convergence**:
   - By `binomProb_ratio_near_one`: for large N, each C(k,j)/2^k = g(x_j)·Δx·(1 ± δ)
   - So Σ_{central} C(k,j)/2^k = (1 ± δ) · Σ_{central} g(x_j)·Δx
   - By `gaussDensity_Riemann_sum_converges`: Σ_{central} g(x_j)·Δx → ∫_{central} g

3. **Combine**: |scaledProb - ∫g| ≤ ε/4 + ε/4 + δ·∫g + Riemann error < ε

**Key technical steps**:
- Need to relate the `if` conditions in `gaussDensity_Riemann_sum_converges` to the actual binomial sum range
- The central/tail cutoff C should be chosen as a function of ε (C = √(2·log(8/ε)) works)
- The Riemann sum convergence gives the central region match

**Estimated complexity**: ~150 lines. Most of the hard work (local CLT, Chernoff) is already done.

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

## Execution Order

```
Phase A (critical path — sequential):
  A1: gaussDensity_Riemann_sum_converges  (~100 lines)
  A2: cylinder_prob_convergence           (~150 lines)
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

**Total estimated**: ~700-900 lines of proof across 9 sorrys (skipping #4).

## Key Risk: Riemann Sum Convergence

The `gaussDensity_Riemann_sum_converges` proof is the gate for the entire critical path. The main difficulty is that this is a *lattice Riemann sum* (not a standard partition-based sum), so standard Riemann sum theorems may not apply directly. The uniform continuity argument should work but requires careful bookkeeping of the lattice-to-interval correspondence.

If this proves too difficult directly, an alternative is to:
1. Prove a general "lattice Riemann sum converges for UC functions" lemma
2. Apply it to the Gaussian density

This general lemma would be reusable infrastructure.

## Key Risk: Anderson n ≥ 2

The multi-time case requires factoring the joint distribution into independent increments. This is a combinatorial fact about the random walk (coin flips on disjoint index ranges are independent), but formalizing it requires:
- A notion of independence for finite product spaces
- The increment decomposition S_{k₂} - S_{k₁} depends only on flips in [k₁, k₂)
- Product of marginal probabilities = joint probability

This could add significant infrastructure. **Mitigation**: Prove n=1 first (sufficient for single-time Brownian motion properties), defer n≥2.
