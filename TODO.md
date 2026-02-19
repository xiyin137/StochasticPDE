# SPDE Standard Approach - Status and TODO

## PRIORITY: Complete Itô Formula Proof

**3 sorry groups remain on the Itô formula critical path:**

1. **Conditional Itô isometry** (`compensated_sq_setIntegral_zero`)
   - Private sorry in IsometryTheorems.lean:316, also ConditionalIsometry.lean
   - Blocks `stoch_integral_squared_orthogonal` (IsometryTheorems.lean:432)
   - Approach: L² limit from simple processes + abstract compensated square martingale
   - Sub-dependencies in ConditionalIsometry.lean:
     - `simple_compensated_sq_setIntegral_zero` — simple process case via BM independence — **SORRY**
     - `compensated_sq_setIntegral_zero` Step 4 (limit passing) — **SORRY**
     - `sq_L1_tendsto_of_L2` — L¹ convergence of SI² via Cauchy-Schwarz — **PROVEN** ✓
     - `diffusion_integral_L1_tendsto` — L¹ convergence of ∫H² via Cauchy-Schwarz — **PROVEN** ✓

2. **E[Q₁·Z₂] = 0** (`h_part2` in IsometryTheorems.lean:507)
   - Also blocks `stoch_integral_squared_orthogonal`
   - Approach: Approximate Q₁ by F_{s₂}-measurable Q₁_n, use conditional isometry (#1)
   - Depends on #1 being solved

3. **E3 a.e. convergence** (ItoFormulaProof.lean:2672)
   - `∀ᵐ ω, error²(k,ω) → 0` — the last sorry in `si_increment_L2_convergence`
   - E1, E2, E4 convergence PROVEN; only E3 (weighted QV error) remains
   - E3 = Riemann error (UC pattern, same as E1/E2) + weighted QV fluctuation
   - Depends on `stoch_integral_squared_orthogonal` (#1 + #2) via QVConvergence

**Dependency chain:**
```
simple_compensated_sq_setIntegral_zero (CI:221)
  → compensated_sq_setIntegral_zero (IT:316)
  → stoch_integral_squared_orthogonal (IT:432, also needs h_part2 at IT:507)
  → si_compensated_orthogonal_partition (QVC:215)
  → ito_qv_L2_bound (QVC:672)
  → ito_process_discrete_qv_L2_convergence (QVC:984)
  → E3 a.e. convergence (IFP:2672)
  → ito_formula (IFP:1416)
```

**Everything else is NOT on the Itô formula critical path.** Do not work on InnerIntegralIntegrability, BDG, SDE existence, etc. until these sorrys are closed.

---

## Current Sorry Count (as of 2026-02-18)

| File | Sorrys | Key Items |
|------|--------|-----------|
| **StochasticIntegration.lean** | **8** | quadratic_variation, bdg_inequality, sde_existence, sde_uniqueness_law, stratonovich, semimartingale_integral, girsanov, martingale_representation |
| **BrownianMotion.lean** | **5** | time_inversion, eval_unit_is_brownian, Q-Wiener continuous_paths, Q-Wiener regularity_from_trace, levy_characterization |
| **SPDE.lean** | **5** | Generator/semigroup infrastructure |
| **Basic.lean** | **1** | is_martingale_of_bounded (needs uniform integrability) |
| **RegularityStructures.lean** | **1** | Abstract approach (complementary to folder) |
| **Probability/Basic.lean** | **2** | condexp_jensen, doob_maximal_L2 |
| **Helpers/ItoFormulaProof.lean** | **1** | a.e. convergence in si_increment_L2_convergence (line 2672) |
| **Helpers/IsometryTheorems.lean** | **2** | compensated_sq_setIntegral_zero (line 316), h_part2 (line 507) |
| **Helpers/ConditionalIsometry.lean** | **3** | simple_compensated_sq_setIntegral_zero, compensated_sq_setIntegral_zero Step 4, h_part2 (stoch_integral_squared_orthogonal) |
| **Helpers/QuarticBound.lean** | **0** | FULLY PROVEN |
| **Helpers/QVConvergence.lean** | **0** | FULLY PROVEN |
| **Helpers/ItoFormulaDecomposition.lean** | **0** | FULLY PROVEN |
| **Helpers/QuadraticVariation.lean** | **0** | FULLY PROVEN |
| **Helpers/InnerIntegralIntegrability.lean** | **5** | Tonelli/Fubini infrastructure (NOT on ito_formula critical path) |
| **Helpers/** (all other files) | **0** | Fully proven |
| **Probability/IndependenceHelpers.lean** | **0** | Fully proven |
| **Probability/Pythagoras.lean** | **0** | Fully proven |
| **EKMS/** | **16** | Hyperbolicity, InvariantMeasure, TwoSidedMinimizers, OneSidedMinimizers, Basic |
| **Examples/** | **15** | YangMills2D, Phi4, KPZ |
| **Nonstandard/Anderson/** | **10** | ItoCorrespondence, ExplicitSolutions, LocalCLT, AndersonTheorem, CylinderConvergenceHelpers |
| **RegularityStructures/** | **41** | See RegularityStructures/TODO.md |

**Total: ~114 sorrys** (33 SPDE core + 41 RegularityStructures + 16 EKMS + 15 Examples + 10 Nonstandard)
**Critical path: 5 sorrys** (1 in IsometryTheorems + 3 in ConditionalIsometry + 1 in ItoFormulaProof)

---

## Soundness Audit (2026-02-12)

**All files audited for definition soundness and axiom smuggling.**

### Results:
- **StochasticIntegration.lean**: SOUND — all structures properly defined
- **BrownianMotion.lean**: SOUND — all structures properly defined
- **Basic.lean**: SOUND — Filtration, Martingale, LocalMartingale all correct
- **SPDE.lean**: SOUND (after fix) — `PolynomialNonlinearity.leading_nonzero` replaces weak `nontrivial`
- **Probability/Basic.lean**: SOUND — `IsGaussian` correctly includes char_function as defining property
- **Helpers/**: SOUND — 15+ files, no issues
- **No axioms, no .choose in definitions, no True := trivial**

### Fix applied:
- `PolynomialNonlinearity`: replaced `nontrivial : ∃ k, coeff k ≠ 0` with
  `leading_nonzero : coeff ⟨degree, ...⟩ ≠ 0` (proper polynomial of stated degree)
- This eliminated the `sorry` in `renormalized_spde` (leading coeff unchanged by renormalization)
- Old `nontrivial` is now a derived lemma

---

## Reconstruction Theorem — USES SORRY (3 blocking)

`reconstruction_theorem` in `Reconstruction.lean` has a proof term but
**transitively depends on 3 sorry'd lemmas** in the uniqueness argument.
See `RegularityStructures/TODO.md` for full sorry-dependency audit.

**What is proven:**
- `reconstruction_exists` — FULLY PROVEN (explicit construction R(f) = Π_x f(x))
- `extendModelPairing_bound` — FULLY PROVEN
- `reconstruction_pairing_diff_bound` — FULLY PROVEN

**Blocking sorrys (3):**
1. `pairing_eq_of_small_scale_bound` (Reconstruction.lean:399) — Prop 3.19, requires Littlewood-Paley
2. `pairing_eq_of_small_scale_eq` scale > 1 (Reconstruction.lean:427) — scale extension
3. `pairing_eq_of_small_scale_eq` scale ≤ 0 (Reconstruction.lean:430) — domain boundary

**RegularityStructures sorry breakdown:**
- Trees/ — 0 sorrys (fully proven)
- Models/Admissible.lean — 0 sorrys (fully proven)
- Reconstruction.lean — 5 sorrys (3 blocking + 2 corollaries)
- Models/Canonical.lean — 15 sorrys (specific model, not blocking reconstruction)
- FixedPoint.lean — 10 sorrys (downstream application)
- BPHZ.lean — 11 sorrys (downstream renormalization)
- BesovCharacterization.lean — 2 sorrys
- SmoothCutoff.lean — 1 sorry

---

## Ito Formula — Complete Sorry Dependency Audit (updated 2026-02-18)

### The theorem: `ito_formula` at ItoFormulaProof.lean

**Status**: Top-level proof term is COMPLETE. **7 sorrys** remain on the critical path (across 3 files).

**Statement:**
For C^{1,2} function f and Ito process dX_t = mu_t dt + sigma_t dW_t:
```
f(t, X_t) = f(0, X_0) + int_0^t [d_t f + d_x f * mu + 1/2 d^2_x f * sigma^2] ds + M_t
```
where M_t is a martingale (the stochastic integral int_0^t d_x f * sigma dW).

### Critical Path: 5 sorrys blocking `ito_formula`

```
ito_formula -- PROVED, wires to:
  ito_formula_martingale -- PROVED, wires to:
    si_increment_L2_convergence (ItoFormulaProof.lean:1365)
      ito_error_decomposition -- PROVED ✓
      fatou_squeeze_tendsto_zero_ae -- PROVED ✓
      Error bound: 0 ≤ error² ≤ 4*(E1²+E2²+E3²+E4²) -- PROVED ✓
        |E1| ≤ 2*Mft*T (time Riemann) -- PROVED ✓
        |E2| ≤ 2*Mf'*Mμ*T (drift Riemann) -- PROVED ✓
        |E3| ≤ ½Mf''*(Mσ²T+Sk) (QV weighted) -- PROVED ✓
        |E4| ≤ 2*Mf''*Sk (Taylor remainder) -- PROVED ✓
      Dominator g_k → G a.e. -- PROVED ✓
      *** a.e. convergence: error²(k) → 0 (line 2672) -- SORRY [1] ***
        E1,E2,E4 → 0: UC pattern (same as proven cases)
        E3 → 0: Riemann UC error + QV fluctuation
          [needs stoch_integral_squared_orthogonal:]
          stoch_integral_squared_orthogonal (IsometryTheorems.lean)
            compensated_sq_setIntegral_zero (CI) -- uses:
              simple_compensated_sq_setIntegral_zero (CI) -- SORRY [2]
              sq_L1_tendsto_of_L2 (CI) -- PROVED ✓
              diffusion_integral_L1_tendsto (CI) -- PROVED ✓
              Step 4 limit passing (CI) -- SORRY [3]
            h_part2: E[Q₁·Z₂] = 0 (CI) -- SORRY [4]
          [also needs IT:316 private copy] -- SORRY [5]
```

#### Layer 1: ItoFormulaProof.lean (1 sorry, line 2672)

| Line | Goal | Description | Difficulty |
|------|------|-------------|------------|
| 2672 | a.e. convergence | `∀ᵐ ω, error²(k,ω) → 0` in `si_increment_L2_convergence` | High |

**What's proved in si_increment_L2_convergence:**
- Subsequence extraction (tendsto_of_subseq_tendsto + QV a.e. sub-subsequence)
- Error decomposition: error² ≤ 4*(E1²+E2²+E3²+E4²) a.e. ∀ k
- Absolute value bounds on E1, E2, E3, E4 (for domination)
- Dominator g_k defined, g_k ≥ 0, f_k ≤ g_k a.e., g_k → G a.e.
- **Missing**: f_k → 0 a.e. (error² → 0 pointwise for continuous paths)

**Approach for the remaining sorry:**
Need to show each E_i(k,ω) → 0 for a.e. ω (continuous path + QV convergence):
- E1 → 0: Use FTC + uniform continuity of ∂_tf on compact set + path UC
- E2 → 0: Use uniform continuity of f' + path UC + bounded drift
- E3 → 0: Decompose into Riemann error (UC) + QV discrepancy (a.e. convergence)
- E4 → 0: Adapt `taylor_remainders_ae_tendsto_zero` pattern (UC of f'' + QV bounded)

**Available infrastructure:**
- `riemann_sum_L2_convergence` (ItoFormulaDecomposition.lean:559) — L² Riemann convergence
- `taylor_remainders_ae_tendsto_zero` (QuadraticVariation.lean:344) — Taylor a.e. convergence
- Both use `Metric.tendsto_atTop` + `isCompact_Icc.uniformContinuousOn_of_continuous` pattern

#### Layer 2: IsometryTheorems.lean (2 sorrys) + ConditionalIsometry.lean (4 sorrys)

| File | Line | Lemma | Description | Status |
|------|------|-------|-------------|--------|
| IT | 316 | `compensated_sq_setIntegral_zero` | ∫_A [Δ² - ∫σ²] = 0 for A ∈ F_s (private) | SORRY |
| CI | ~635 | `simple_compensated_sq_setIntegral_zero` | Simple process conditional isometry | SORRY |
| CI | ~660 | `compensated_sq_setIntegral_zero` Step 4 | Limit passing from simple to general | SORRY |
| CI | ~738 | `h_part2` | E[Q₁·Z₂] = 0 (approx Q₁ F_{s₂}-measurable) | SORRY |
| CI | 164 | `sq_L1_tendsto_of_L2` | SI_n² → SI² in L¹ (Cauchy-Schwarz) | **PROVEN** ✓ |
| CI | 275 | `diffusion_integral_L1_tendsto` | ∫H_n² → ∫σ² in L¹ (Cauchy-Schwarz) | **PROVEN** ✓ |

**NOTE**: IT:316 and CI:240 are the same result; IT:316 is a private copy used in the orthogonality proof. Architecture needs restructuring — either prove IT:316 directly or move `stoch_integral_squared_orthogonal` to CI.

**Key approach for simple_compensated_sq_setIntegral_zero (CI:221)**:
Inductive/telescoping on partition: M_k = S_k² - V_k where S_k is partial sum of adapted×ΔW terms.
- M_{k+1} - M_k = 2·S_k·h_k·ΔW_k + h_k²·[(ΔW_k)² - Δt_k]
- Both terms have zero set-integral over F_s ⊂ F_{r_k}:
  - First: `setIntegral_adapted_mul_increment_zero` (proven, SimpleIntegralMartingale.lean:53)
  - Second: `setIntegral_sq_of_indep_eq_measure_mul_integral` + `increment_variance` (proven)

**Used by**: QVConvergence.lean:215 (in `si_compensated_orthogonal_partition`)

#### Layer 3: QuarticBound.lean — FULLY PROVEN ✓

#### Layer 3: QVConvergence.lean — FULLY PROVEN ✓

#### Layer 3: ItoFormulaDecomposition.lean — FULLY PROVEN ✓

#### Layer 3: QuadraticVariation.lean — FULLY PROVEN ✓

**Used by**: QuarticBound.lean:1260 (`stoch_integral_increment_L4_integrable_proof`)
-> QVConvergence.lean:276,296,347 -> ito_qv_L2_bound -> ito_process_discrete_qv_L2_convergence

### NOT on critical path (19 sorrys in SPDE core)

| File | Count | Sorrys | Notes |
|------|-------|--------|-------|
| StochasticIntegration.lean | 8 | bdg_inequality, quadratic_variation, sde_existence_uniqueness, sde_uniqueness_law, stratonovich_chain_rule, semimartingale_integral_exists, girsanov, martingale_representation | Independent theorems |
| InnerIntegralIntegrability.lean | 5 | inner_sq_integral_integrable_of_sub_interval, inner_product_integral_integrable, integrableOn_sq_ae_of_square_integrable, integrableOn_ae_of_square_integrable, integrableOn_product_ae_of_square_integrable | Not on ito_formula critical path |
| Probability/Basic.lean | 2 | condexp_jensen, doob_maximal_L2 | Not used by SPDE |
| BrownianMotion.lean | 5 | See separate section below |
| Basic.lean | 1 | is_martingale_of_bounded | Not used by ito_formula |
| SPDE.lean | 4 | Generator/semigroup infrastructure |
| RegularityStructures.lean | 1 | Abstract approach |

### Sorry-free files on the ito_formula critical path

- ItoFormulaDecomposition.lean (0 sorrys)
- ItoFormulaInfrastructure.lean (0 sorrys)
- ItoIntegralProperties.lean (0 sorrys)
- QVConvergence.lean (0 sorrys)
- QuadraticVariation.lean (0 sorrys)
- L2LimitInfrastructure.lean (0 sorrys)
- IsometryAt.lean (0 sorrys)
- TaylorRemainder.lean (0 sorrys)
- All other Helpers/ files (0 sorrys)

### Proven infrastructure (key components)

| Component | Location |
|-----------|----------|
| `ito_formula` top-level wiring | ItoFormulaProof.lean:1416 |
| `ito_formula_martingale` wiring | ItoFormulaProof.lean:1338 |
| `ito_error_decomposition` (telescope+Taylor identity) | ItoFormulaProof.lean:920 |
| `process_L2_increment_bound` | ItoFormulaProof.lean:710 |
| `four_sq_sub_bound` | ItoFormulaProof.lean:694 |
| `si_increment_integrable` | ItoFormulaProof.lean:387 |
| `si_increment_diff_sq_integrable` | ItoFormulaProof.lean:427 |
| `si_increment_martingale_property` | ItoFormulaProof.lean:569 |
| `martingale_setIntegral_eq_of_L2_limit` | L2LimitInfrastructure.lean |
| `ito_integral_martingale_setIntegral` | ItoIntegralProperties.lean |
| `weighted_qv_L2_convergence` | ItoFormulaInfrastructure.lean |
| `ito_process_discrete_qv_L2_convergence` | QVConvergence.lean:984 |
| `ito_qv_L2_bound` | QVConvergence.lean:672 |
| `stoch_integral_isometry` (ItoProcess) | IsometryTheorems.lean:223 |
| `stoch_integral_increment_L4_bound_proof` | QuarticBound.lean:1363 |
| `stoch_integral_increment_L4_integrable_proof` | QuarticBound.lean:1245 |
| `taylor_remainders_ae_tendsto_zero` | ItoFormulaDecomposition.lean |
| `fatou_squeeze_tendsto_zero` | ItoFormulaDecomposition.lean |
| `partition_increment_ae_zero` | QuadraticVariation.lean |
| `inner_integral_quadratic_split_ae` | InnerIntegralIntegrability.lean |

---

## Other Sorrys by File

### StochasticIntegration.lean (8 sorrys)
1. `bdg_inequality` (line 1322) — Burkholder-Davis-Gundy inequality
2. `quadratic_variation` (line 1518) — QV of Ito process (corollary of ito_formula with f(x)=x^2)
3. `sde_existence_uniqueness` (line 1677) — SDE existence via Picard iteration
4. `sde_uniqueness_law` (line 1716) — Pathwise uniqueness via Gronwall
5. `stratonovich_chain_rule` (line 1751) — Stratonovich chain rule
6. `semimartingale_integral_exists` (line 1900) — Semimartingale integral construction
7. `girsanov` (line 1930) — Girsanov theorem
8. `martingale_representation` (line 1956) — Martingale representation theorem

### BrownianMotion.lean (5 sorrys)
1. `time_inversion` (line 595) — t*W(1/t) is BM
2. `eval_unit_is_brownian` (line 648) — Cylindrical Wiener unit evaluation
3. `continuous_paths` (line 744) — Q-Wiener continuous paths
4. `regularity_from_trace` (line 749) — Q-Wiener regularity
5. `levy_characterization` (line 782) — Levy characterization

### Helpers/InnerIntegralIntegrability.lean (5 sorrys — NOT on ito_formula critical path)
1. `inner_sq_integral_integrable_of_sub_interval` (line 82) — ∫₀ᵗ f² integrable from ∫₀ᵀ f² integrable
2. `inner_product_integral_integrable` (line 100) — ∫₀ᵗ fg integrable from ∫₀ᵀ f², g² integrable
3. `integrableOn_sq_ae_of_square_integrable` (line 114) — f² IntegrableOn a.e. (Tonelli)
4. `integrableOn_ae_of_square_integrable` (line 124) — f IntegrableOn a.e. (L²⊂L¹)
5. `integrableOn_product_ae_of_square_integrable` (line 136) — fg IntegrableOn a.e. (AM-GM)

---

## Fully Proven Components

### Helpers/ (13+ files, 0 sorrys)
- **CommonRefinement.lean** — Merged partitions, valueAtTime, joint measurability
- **SimpleProcessLinear.lean** — Linear combination of simple process integrals
- **MergedValueAtTime.lean** — valueAtTime linearity for merged processes
- **SimpleIntegralMartingale.lean** — Simple stochastic integral is martingale
- **SetIntegralHelpers.lean** — Cross-term vanishing, variance factorization on sets
- **L2LimitInfrastructure.lean** — Set integral convergence from L^2 convergence
- **ItoIntegralProperties.lean** — Ito isometry proof, martingale proof
- **IsometryAt.lean** — isometry_at, bilinear_isometry_at
- **ProductL2Convergence.lean** — Product L^2 convergence
- **IteratedProductConvergence.lean** — Iterated integral product convergence
- **SimpleProcessDef.lean** — SimpleProcess structure, stochasticIntegral definitions
- **GronwallForSDE.lean** — Gronwall lemma infrastructure
- **ItoFormulaInfrastructure.lean** — BM QV L^2 convergence, weighted QV convergence
- **ItoFormulaDecomposition.lean** — Taylor remainder, Fatou squeeze, QV L^2 infrastructure
- **QVConvergence.lean** — Compensated SI squared bounds, QV L^2 bound, discrete QV convergence
- **QuadraticVariation.lean** — QV definitions, discrete QV structure
- **TaylorRemainder.lean** — Taylor remainder bounds

### Probability/ (2 files, 0 sorrys)
- **IndependenceHelpers.lean** — Bridge lemmas for independence
- **Pythagoras.lean** — L^2 Pythagoras for orthogonal RVs

### RegularityStructures/Trees/ (3 files, 0 sorrys)
- **Basic.lean** — MultiIndex, TreeSymbol, complexity
- **Homogeneity.lean** — homogeneity_decomposition, FormalSum algebra
- **Operations.lean** — Standard trees for Phi^4/KPZ

### Key Proven Theorems
- **Ito isometry** (simple + L^2 limit): `E[(int H dW)^2] = E[int H^2 ds]`
- **Bilinear Ito isometry**: `E[(int H1 dW)(int H2 dW)] = E[int H1 H2 ds]`
- **Ito integral is martingale**: set-integral property on [0,T]
- **Ito integral linearity**: `I(aH1 + bH2) = aI(H1) + bI(H2)` in L^2
- **BM quadratic variation compensator**: W^2_t - t is martingale
- **BM quadratic variation L^2 convergence**: E[|sum (DeltaW)^2 - t|^2] -> 0
- **Weighted QV convergence**: sum g_i[(DeltaW_i)^2 - Delta t_i] -> 0 in L^2 for adapted bounded g
- **Ito process discrete QV L^2 convergence**: sum (DeltaX_i)^2 -> [X]_t in L^2
- **Ito error decomposition**: SI_n - Rem = E1 + E2 + E3 - E4 with (a+b+c-d)^2 <= 4(a^2+b^2+c^2+d^2)
- **Martingale orthogonality**: int_A Y=0 for all A in F_s, X is F_s-meas => E[X*Y]=0
- **Bilinear isometry at different times**: E[S(t)*S(s)] = E[S(s)^2] for s<=t
- **Simple process increment L^2**: E[|S(t)-S(s)|^2] = E[S(t)^2]-E[S(s)^2]
- **Process L^2 increment bound**: E[(X_t - X_s)^2] <= (2*Mmu^2*T + 2*Msigma^2)*(t-s)
- **BM scaling**: c^{-1/2}W_{ct} is BM
- **BM reflection**: -W is BM
- **Reconstruction exists**: explicit construction R(f) = Pi_x f(x)
