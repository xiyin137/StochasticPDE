# SPDE Standard Approach - Status and TODO

## PRIORITY: Complete Itô Formula Proof

**0 sorrys remain on the Itô formula critical path — FULLY PROVEN!**

1. ~~**Conditional Itô isometry** (`compensated_sq_setIntegral_zero`)~~ — **PROVEN** ✓
   - `simple_compensated_sq_setIntegral_zero` — **PROVEN** ✓ (BM independence + Pythagoras)
   - `compensated_sq_setIntegral_zero` Step 4 (limit passing) — **PROVEN** ✓ (L¹ convergence + `tendsto_setIntegral_of_L1`)
   - ItoCalculus/IsometryTheorems.lean:316 private copy — **PROVEN** ✓ (0 sorrys in IT now)

2. ~~**E[Q₁·Z₂] = 0** (`h_part2` in ItoCalculus/ConditionalIsometry.lean:1515)~~ — **PROVEN** ✓
   - Used `diffusion_adapted` (added to ItoProcess, see below) + Fubini + pointwise orthogonality
   - For each u ∈ [s₁,t₁]: σ²(u,·) is F_{s₂}-measurable → E[σ²(u,·)·Z₂] = 0
   - Fubini swaps ∫_ω ∫_u to ∫_u ∫_ω → each inner integral = 0

3. ~~**E3 a.e. convergence** (ItoCalculus/ItoFormulaProof.lean:~2500)~~ — **PROVEN** ✓
   - E1, E2, E3, E4 convergence all PROVEN
   - `h_B_bound` (line ~2149): **PROVEN** ✓ (2026-02-20) — E[B²] ≤ C_B·T/(n+1), via `weighted_capped_qv_L2_bound` from ItoCalculus/WeightedQVBound.lean
   - Weight ½f''(τᵢ, X(τᵢ)) bounded by Mf''/2, F_{τᵢ}-measurable by composition of continuous f'' with adapted process

**Dependency chain:**
```
simple_compensated_sq_setIntegral_zero (CI) — PROVEN ✓
  → compensated_sq_setIntegral_zero (CI) — PROVEN ✓
  → stoch_integral_squared_orthogonal (CI) — PROVEN ✓
  → si_compensated_orthogonal_partition (QVC:215) — PROVEN ✓
  → ito_qv_L2_bound (QVC:672) — PROVEN ✓
  → ito_process_discrete_qv_L2_convergence (QVC:984) — PROVEN ✓
  → E3 a.e. convergence (IFP:2672) — PROVEN ✓
  → ito_formula (IFP:1416) — PROVEN ✓
```

**The Itô formula critical path is COMPLETE (0 sorrys).** All remaining sorrys are independent theorems.

---

## Current Sorry Count (as of 2026-02-20)

| File | Sorrys | Key Items |
|------|--------|-----------|
| **ItoCalculus/StochasticIntegration.lean** | **8** | quadratic_variation, bdg_inequality, sde_existence, sde_uniqueness_law, stratonovich, semimartingale_integral, girsanov, martingale_representation |
| **ItoCalculus/BrownianMotion.lean** | **5** | time_inversion, eval_unit_is_brownian, Q-Wiener continuous_paths, Q-Wiener regularity_from_trace, levy_characterization |
| **SPDE.lean** | **5** | Generator/semigroup infrastructure |
| **ItoCalculus/Basic.lean** | **1** | is_martingale_of_bounded (needs uniform integrability) |
| **RegularityStructures.lean** | **1** | Abstract approach (complementary to folder) |
| **ItoCalculus/Probability/Basic.lean** | **2** | condexp_jensen, doob_maximal_L2 |
| **ItoCalculus/ItoCalculus/ItoFormulaProof.lean** | **0** | FULLY PROVEN ✓ |
| **ItoCalculus/ItoCalculus/WeightedQVBound.lean** | **0** | FULLY PROVEN ✓ |
| **ItoCalculus/ItoCalculus/IsometryTheorems.lean** | **0** | FULLY PROVEN ✓ |
| **ItoCalculus/ItoCalculus/ConditionalIsometry.lean** | **0** | FULLY PROVEN ✓ |
| **ItoCalculus/ItoCalculus/QuarticBound.lean** | **0** | FULLY PROVEN |
| **ItoCalculus/ItoCalculus/QVConvergence.lean** | **0** | FULLY PROVEN |
| **ItoCalculus/ItoCalculus/ItoFormulaDecomposition.lean** | **0** | FULLY PROVEN |
| **ItoCalculus/ItoCalculus/QuadraticVariation.lean** | **0** | FULLY PROVEN |
| **Helpers/InnerIntegralIntegrability.lean** | **5** | Tonelli/Fubini infrastructure (NOT on ito_formula critical path) |
| **ItoCalculus/** (all other files) | **0** | Fully proven |
| **ItoCalculus/Probability/IndependenceHelpers.lean** | **0** | Fully proven |
| **ItoCalculus/Probability/Pythagoras.lean** | **0** | Fully proven |
| **EKMS/** | **16** | Hyperbolicity, InvariantMeasure, TwoSidedMinimizers, OneSidedMinimizers, Basic |
| **Examples/** | **15** | YangMills2D, Phi4, KPZ |
| **Nonstandard/Anderson/** | **10** | ItoCorrespondence, ExplicitSolutions, LocalCLT, AndersonTheorem, CylinderConvergenceHelpers |
| **RegularityStructures/** | **41** | See RegularityStructures/TODO.md |

**Total: ~108 sorrys** (27 SPDE core + 41 RegularityStructures + 16 EKMS + 15 Examples + 10 Nonstandard)
**Critical path: 0 sorrys — Itô formula FULLY PROVEN** ✓

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

### The theorem: `ito_formula` at ItoCalculus/ItoFormulaProof.lean

**Status**: FULLY PROVEN ✓. **0 sorrys** on the critical path.

**Statement:**
For C^{1,2} function f and Ito process dX_t = mu_t dt + sigma_t dW_t:
```
f(t, X_t) = f(0, X_0) + int_0^t [d_t f + d_x f * mu + 1/2 d^2_x f * sigma^2] ds + M_t
```
where M_t is a martingale (the stochastic integral int_0^t d_x f * sigma dW).

### Critical Path: COMPLETE (0 sorrys)

```
ito_formula -- PROVED ✓
  ito_formula_martingale -- PROVED ✓
    si_increment_L2_convergence (ItoCalculus/ItoFormulaProof.lean:1623) -- PROVED ✓
      ito_error_decomposition -- PROVED ✓
      fatou_squeeze_tendsto_zero_ae -- PROVED ✓
      Error bound: 0 ≤ error² ≤ 4*(E1²+E2²+E3²+E4²) -- PROVED ✓
      Dominator g_k → G a.e. -- PROVED ✓
      a.e. convergence: error²(k) → 0 -- PROVED ✓
        E1,E2,E4 → 0: UC pattern -- PROVED ✓
        E3 → 0: A + B decomposition -- PROVED ✓
          A L² → 0: Fatou squeeze -- PROVED ✓
          B L² → 0: squeeze_zero from h_B_bound -- PROVED ✓
          h_B_bound: E[B²] ≤ C_B·T/(n+1) -- PROVED ✓ (via weighted_capped_qv_L2_bound)
```

#### Layer 1: ItoCalculus/ItoFormulaProof.lean (0 sorrys — FULLY PROVEN ✓)

**What's proved in si_increment_L2_convergence:**
- Subsequence extraction (tendsto_of_subseq_tendsto + QV a.e. sub-subsequence) — PROVEN ✓
- Error decomposition: error² ≤ 4*(E1²+E2²+E3²+E4²) a.e. ∀ k — PROVEN ✓
- E1, E2, E4 → 0 a.e. — PROVEN ✓ (UC patterns)
- E3 = A + B decomposition — PROVEN ✓
- A L² convergence (Fatou squeeze with constant dominator) — PROVEN ✓
- B L² convergence (squeeze_zero from quantitative bound) — PROVEN ✓ (uses h_B_bound)
- L² → a.e. subsequence extraction via L2_zero_ae_subseq — PROVEN ✓
- All measurability/integrability (h_E3_aesm, h_E3_sq_int, h_A_sq_int, h_B_sq_int) — PROVEN ✓
- Final squeeze combining E1-E4 — PROVEN ✓

**0 remaining sorrys.** `h_B_bound` proved 2026-02-20 via `weighted_capped_qv_L2_bound` (ItoCalculus/WeightedQVBound.lean).
Weight = ½f''(τᵢ, X(τᵢ)), C_w = Mf''/2. Three-way decomposition B₁+2B₂+B₃ with:
- B₁ orthogonality via `weighted_compensated_orthogonal_partition`
- B₂ cross terms via isometry + Cauchy-Schwarz
- B₃ drift terms via deterministic bound

#### Layer 2: ItoCalculus/IsometryTheorems.lean (0 sorrys) + ItoCalculus/ConditionalIsometry.lean (0 sorrys) — FULLY PROVEN ✓

| File | Line | Lemma | Description | Status |
|------|------|-------|-------------|--------|
| IT | 316 | `compensated_sq_setIntegral_zero` | ∫_A [Δ² - ∫σ²] = 0 for A ∈ F_s (private) | **PROVEN** ✓ |
| CI | ~906 | `simple_compensated_sq_setIntegral_zero` | Simple process conditional isometry | **PROVEN** ✓ |
| CI | ~1028 | `compensated_sq_setIntegral_zero` Step 4 | Limit passing from simple to general | **PROVEN** ✓ |
| CI | ~1515 | `stoch_integral_squared_orthogonal` | E[Z₁·Z₂] = 0 on disjoint intervals | **PROVEN** ✓ |
| CI | 164 | `sq_L1_tendsto_of_L2` | SI_n² → SI² in L¹ (Cauchy-Schwarz) | **PROVEN** ✓ |
| CI | 275 | `diffusion_integral_L1_tendsto` | ∫H_n² → ∫σ² in L¹ (Cauchy-Schwarz) | **PROVEN** ✓ |
| CI | ~1305 | `tendsto_setIntegral_of_L1` | L¹ → set integral convergence helper | **PROVEN** ✓ |

**h_part2 proof (E[Q₁·Z₂] = 0)**: Uses `diffusion_adapted` (see below) + Fubini swap + pointwise orthogonality.
For each u ∈ [s₁,t₁], σ²(u,·) is F_{s₂}-measurable (diffusion_adapted + monotonicity),
so E[σ²(u,·)·Z₂] = 0 by conditional isometry. Fubini swaps the ω and u integrals.

**Used by**: ItoCalculus/QVConvergence.lean:215 (in `si_compensated_orthogonal_partition`)

#### Layer 3: ItoCalculus/QuarticBound.lean — FULLY PROVEN ✓

#### Layer 3: ItoCalculus/QVConvergence.lean — FULLY PROVEN ✓

#### Layer 3: ItoCalculus/ItoFormulaDecomposition.lean — FULLY PROVEN ✓

#### Layer 3: ItoCalculus/QuadraticVariation.lean — FULLY PROVEN ✓

**Used by**: ItoCalculus/QuarticBound.lean:1260 (`stoch_integral_increment_L4_integrable_proof`)
-> ItoCalculus/QVConvergence.lean:276,296,347 -> ito_qv_L2_bound -> ito_process_discrete_qv_L2_convergence

### NOT on critical path (19 sorrys in SPDE core)

| File | Count | Sorrys | Notes |
|------|-------|--------|-------|
| ItoCalculus/StochasticIntegration.lean | 8 | bdg_inequality, quadratic_variation, sde_existence_uniqueness, sde_uniqueness_law, stratonovich_chain_rule, semimartingale_integral_exists, girsanov, martingale_representation | Independent theorems |
| Helpers/InnerIntegralIntegrability.lean | 5 | inner_sq_integral_integrable_of_sub_interval, inner_product_integral_integrable, integrableOn_sq_ae_of_square_integrable, integrableOn_ae_of_square_integrable, integrableOn_product_ae_of_square_integrable | Not on ito_formula critical path |
| ItoCalculus/Probability/Basic.lean | 2 | condexp_jensen, doob_maximal_L2 | Not used by SPDE |
| ItoCalculus/BrownianMotion.lean | 5 | See separate section below |
| ItoCalculus/Basic.lean | 1 | is_martingale_of_bounded | Not used by ito_formula |
| SPDE.lean | 4 | Generator/semigroup infrastructure |
| RegularityStructures.lean | 1 | Abstract approach |

### Sorry-free files on the ito_formula critical path

- ItoCalculus/ItoFormulaDecomposition.lean (0 sorrys)
- ItoCalculus/ItoFormulaInfrastructure.lean (0 sorrys)
- ItoCalculus/ItoIntegralProperties.lean (0 sorrys)
- ItoCalculus/QVConvergence.lean (0 sorrys)
- ItoCalculus/QuadraticVariation.lean (0 sorrys)
- ItoCalculus/L2LimitInfrastructure.lean (0 sorrys)
- ItoCalculus/IsometryAt.lean (0 sorrys)
- ItoCalculus/TaylorRemainder.lean (0 sorrys)
- All other ItoCalculus/ files (0 sorrys)

### Proven infrastructure (key components)

| Component | Location |
|-----------|----------|
| `ito_formula` top-level wiring | ItoCalculus/ItoFormulaProof.lean:1416 |
| `ito_formula_martingale` wiring | ItoCalculus/ItoFormulaProof.lean:1338 |
| `ito_error_decomposition` (telescope+Taylor identity) | ItoCalculus/ItoFormulaProof.lean:920 |
| `process_L2_increment_bound` | ItoCalculus/ItoFormulaProof.lean:710 |
| `four_sq_sub_bound` | ItoCalculus/ItoFormulaProof.lean:694 |
| `si_increment_integrable` | ItoCalculus/ItoFormulaProof.lean:387 |
| `si_increment_diff_sq_integrable` | ItoCalculus/ItoFormulaProof.lean:427 |
| `si_increment_martingale_property` | ItoCalculus/ItoFormulaProof.lean:569 |
| `martingale_setIntegral_eq_of_L2_limit` | ItoCalculus/L2LimitInfrastructure.lean |
| `ito_integral_martingale_setIntegral` | ItoCalculus/ItoIntegralProperties.lean |
| `weighted_qv_L2_convergence` | ItoCalculus/ItoFormulaInfrastructure.lean |
| `ito_process_discrete_qv_L2_convergence` | ItoCalculus/QVConvergence.lean:984 |
| `ito_qv_L2_bound` | ItoCalculus/QVConvergence.lean:672 |
| `stoch_integral_isometry` (ItoProcess) | ItoCalculus/IsometryTheorems.lean:223 |
| `weighted_capped_qv_L2_bound` | ItoCalculus/WeightedQVBound.lean:267 |
| `stoch_integral_increment_L4_bound_proof` | ItoCalculus/QuarticBound.lean:1363 |
| `stoch_integral_increment_L4_integrable_proof` | ItoCalculus/QuarticBound.lean:1245 |
| `taylor_remainders_ae_tendsto_zero` | ItoCalculus/ItoFormulaDecomposition.lean |
| `fatou_squeeze_tendsto_zero` | ItoCalculus/ItoFormulaDecomposition.lean |
| `partition_increment_ae_zero` | ItoCalculus/QuadraticVariation.lean |
| `inner_integral_quadratic_split_ae` | InnerIntegralIntegrability.lean |

---

## Other Sorrys by File

### ItoCalculus/StochasticIntegration.lean (8 sorrys)
1. `bdg_inequality` (line 1322) — Burkholder-Davis-Gundy inequality
2. `quadratic_variation` (line 1518) — QV of Ito process (corollary of ito_formula with f(x)=x^2)
3. `sde_existence_uniqueness` (line 1677) — SDE existence via Picard iteration
4. `sde_uniqueness_law` (line 1716) — Pathwise uniqueness via Gronwall
5. `stratonovich_chain_rule` (line 1751) — Stratonovich chain rule
6. `semimartingale_integral_exists` (line 1900) — Semimartingale integral construction
7. `girsanov` (line 1930) — Girsanov theorem
8. `martingale_representation` (line 1956) — Martingale representation theorem

### ItoCalculus/BrownianMotion.lean (5 sorrys)
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

### ItoCalculus/ (25+ files, 0 sorrys on critical path)
- **ItoCalculus/Basic.lean** — Filtrations, adapted processes, martingales
- **ItoCalculus/BrownianMotion.lean** — Wiener process, cylindrical Wiener process
- **ItoCalculus/StochasticIntegration.lean** — Itô integral, isometry, SDEs
- **ItoCalculus/Probability/Basic.lean** — Measure-theoretic probability helpers
- **ItoCalculus/Probability/IndependenceHelpers.lean** — Bridge lemmas for independence
- **ItoCalculus/Probability/Pythagoras.lean** — L² Pythagoras for orthogonal RVs
- **ItoCalculus/CommonRefinement.lean** — Merged partitions, valueAtTime, joint measurability
- **ItoCalculus/SimpleProcessLinear.lean** — Linear combination of simple process integrals
- **ItoCalculus/MergedValueAtTime.lean** — valueAtTime linearity for merged processes
- **ItoCalculus/SimpleIntegralMartingale.lean** — Simple stochastic integral is martingale
- **ItoCalculus/SetIntegralHelpers.lean** — Cross-term vanishing, variance factorization on sets
- **ItoCalculus/L2LimitInfrastructure.lean** — Set integral convergence from L² convergence
- **ItoCalculus/ItoIntegralProperties.lean** — Itô isometry proof, martingale proof
- **ItoCalculus/IsometryAt.lean** — isometry_at, bilinear_isometry_at
- **ItoCalculus/ProductL2Convergence.lean** — Product L² convergence
- **ItoCalculus/IteratedProductConvergence.lean** — Iterated integral product convergence
- **ItoCalculus/SimpleProcessDef.lean** — SimpleProcess structure, stochasticIntegral definitions
- **ItoCalculus/GronwallForSDE.lean** — Gronwall lemma infrastructure
- **ItoCalculus/IsometryTheorems.lean** — Itô isometry, bilinear isometry, orthogonal increments, compensated square
- **ItoCalculus/ItoFormulaInfrastructure.lean** — BM QV L² convergence, weighted QV convergence
- **ItoCalculus/ItoFormulaDecomposition.lean** — Taylor remainder, Fatou squeeze, QV L² infrastructure
- **ItoCalculus/QVConvergence.lean** — Compensated SI squared bounds, QV L² bound, discrete QV convergence
- **ItoCalculus/WeightedQVBound.lean** — Weighted QV discrepancy L² bound for Itô formula
- **ItoCalculus/QuadraticVariation.lean** — QV definitions, discrete QV structure
- **ItoCalculus/TaylorRemainder.lean** — Taylor remainder bounds
- **ItoCalculus/ConditionalIsometry.lean** — Conditional Itô isometry
- **ItoCalculus/QuarticBound.lean** — Fourth moment bounds
- **ItoCalculus/ItoFormulaProof.lean** — Complete Itô formula proof (0 sorrys)

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
