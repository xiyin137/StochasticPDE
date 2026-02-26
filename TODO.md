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

### ItoProcess Structural Improvement Phase 2: Remove all derivable fields (2026-02-21)

Per CLAUDE.md rule 16 ("Computational result cannot be assumed in definition or structure"),
`stoch_integral_measurable` and `stoch_integral_sq_integrable` were removed from `ItoProcess`
and derived as theorems. Combined with the earlier removal of `stoch_integral_adapted`, the
ItoProcess structure now contains **zero computational results as fields**.

**Phase 2 changes (this session):**
- **Removed field**: `stoch_integral_measurable` (ambient measurability — now derived)
- **Removed field**: `stoch_integral_sq_integrable` (square integrability — now derived)
- **Added to `stoch_integral_is_L2_limit`**: a.e. pointwise convergence as 7th conjunction
  (construction data from fast L² convergence + Borel-Cantelli, breaks Bochner integral circularity)

**Derived theorems (dependency order, all 0 sorrys):**
```
stoch_integral_is_L2_limit (field, includes a.e. convergence)
  └→ stoch_integral_aestronglyMeasurable (from a.e. convergence via aestronglyMeasurable_of_tendsto_ae)
      ├→ stoch_integral_sq_integrable (Fatou's lemma: ∫⁻ SI² ≤ liminf ∫⁻ SI_n² < ⊤)
      │   └→ stoch_integral_integrable (L² ⊂ L¹ on probability spaces)
      └→ stoch_integral_adapted (indicator trick + measurable_of_tendsto_metrizable + usual conditions)
          └→ stoch_integral_measurable (from F.le_ambient)
```

**Key technique — Fatou chain for `stoch_integral_sq_integrable`:**
enorm → ofReal → Fatou → Bochner conversion → isometry convergence → Tendsto.liminf_eq

**Simplifications:**
- `stoch_integral_adapted`: now uses a.e. convergence directly (eliminated Chebyshev → TendstoInMeasure → subsequence extraction, ~120 lines removed)
- `stoch_integral_initial`: now uses a.e. convergence (SI_n(0)=0 → SI(0)=0 a.e.), removing dependency on `[IsProbabilityMeasure μ]`

**Phase 1 changes (earlier session):**
- **Removed field**: `stoch_integral_adapted` (F_t-measurability — now derived)
- **Added field**: `BM_adapted_to_F` — BM is adapted to working filtration F (standard: Karatzas-Shreve §2.7)
- **Added field**: `usual_conditions` — F is right-continuous and complete (standard assumption)
- **Changed**: `stoch_integral_is_L2_limit` adaptedness from `BM.F.σ_algebra` to `F.σ_algebra`

**Why `process_adapted` and `process_continuous` remain as fields:**
- `process_adapted`: needs progressive measurability of drift (future infrastructure)
- `process_continuous`: KC gives a continuous *modification*, but `integral_form` is a.e. at each t,
  not pathwise — the null set depends on t. Continuity is a choice of version.

**Soundness audit (2026-02-21):** All definitions feeding into the Ito formula have been audited.
No axiom smuggling, no placeholder definitions, no wrong definitions. All structures are mathematically sound.

**Ito formula critical path: still 0 sorrys.** All downstream files (8 files, ~47 call sites) updated and compile successfully.

### Kolmogorov-Chentsov Theorem (NEW — 0 sorrys)

Built from scratch as `ItoCalculus/KolmogorovChentsov/` (4 files, ~1200 lines):
- **DyadicPartition.lean** — Dyadic interval infrastructure
- **MomentToTail.lean** — Markov inequality for p-th moments
- **DyadicIncrement.lean** — Dyadic increment bounds + Borel-Cantelli
- **ContinuousModification.lean** — Main KC theorem: Hölder continuous modification

Derived property infrastructure (4 files):
- **AdaptedLimit.lean** — L² limits of adapted processes preserve adaptedness
- **SIContinuity.lean** — Stochastic integral has continuous modification (applies KC with p=4, q=2)
- **ProcessContinuity.lean** — Itô process has continuous paths (from drift continuity + SI continuity)
- **RemainderIntegrability.lean** — Itô remainder is L¹ and L² integrable (from boundedness)
- **ItoRemainderDef.lean** — Shared definition of itoRemainder (factored to avoid circular imports)

### ito_formula Structural Improvement (2026-02-20)

Removed `hrem_int` and `hrem_sq_int` hypotheses from `ito_formula`. These are now
derived internally from the boundedness hypotheses (`hdiff_bdd`, `hdrift_bdd`, `hf_x_bdd`,
`hf_xx_bdd`, `hf_t_bdd`) and initial condition square-integrability (`hX0_sq`).
Uses `itoRemainder_integrable` and
`itoRemainder_sq_integrable` from `RemainderIntegrability.lean`.
Added `ito_formula_martingale_of_bounds`, which derives the martingale theorem's
`hrem_int`/`hrem_sq_int` hypotheses internally from the same boundedness package.

### ItoProcess Core/Regularity Split (2026-02-25)

Introduced a compatibility-first split of Itô process assumptions:

- Added `ItoProcessCore` and `ItoProcessRegularity` in `ItoCalculus/ItoProcessCore.lean`
- Added roundtrip adapters: `ItoProcess.toCore`, `ItoProcess.toRegularity`,
  `ItoProcessCore.toItoProcess`
- Added core bridge theorems:
  - `ito_formula_core` and `ito_formula_martingale_core` (`ItoFormulaCoreBridge.lean`)
  - Core adapters for quadratic variation and QV convergence
  - Core adapters for process/SI/remainder integrability
- Added split-core adapters for isometry/orthogonality infrastructure:
  `ItoProcessCore.stoch_integral_isometry_core`,
  `ItoProcessCore.stoch_integral_squared_orthogonal_core`, and related
  interval integrability/bound wrappers in `IsometryTheorems.lean`
- Added split-core helper adapters in `QVConvergence.lean` for:
  increment decomposition, drift increment/squared-sum bounds, QV partition split,
  and single compensated increment L² bound
- Rewrote `capped_ito_qv_L2_bound_core` as a direct core proof
  (no `simpa` delegation to the legacy capped theorem body)
- Reworked `ito_qv_L2_bound_core` to derive from
  `capped_ito_qv_L2_bound_core` at `u = T = t`, eliminating the remaining
  legacy theorem-body dependency on the QV endpoint bound
- QV endpoint status: both `capped_ito_qv_L2_bound_core` and
  `ito_qv_L2_bound_core` now avoid direct delegation to legacy theorem bodies
- Rewired core bridges (`ItoFormulaCoreBridge.lean`, `QVConvergence.lean`) to
  use `ItoProcessRegularity.ofSplit` + `toItoProcess`, removing local
  `ItoFormulaAssumptions` rebuilding boilerplate at call sites
- Removed redundant compatibility bundle `ItoFormulaAssumptions` and its
  roundtrip projections from `ItoProcessCore.lean` after full migration to
  split bundles + regularity-first adapters
- Removed redundant coefficient-joint-measurability mini-bundle
  `ItoProcessCoefficientJointMeasurability`; core remainder-integrability
  adapters now take explicit drift/diffusion joint measurability hypotheses
- Added Phase 3 constructor helpers:
  `ItoProcessRegularity.ofSplit`
- Added regularity-first Itô formula bridge entry points:
  `ito_formula_core_ofRegularity` and
  `ito_formula_martingale_core_ofRegularity`
- Added regularity-first core isometry adapters in `IsometryTheorems.lean`
  (`*_core_ofRegularity` wrappers over split-bundle adapters)
- Added regularity-first core QV adapters in `QVConvergence.lean`
  (`*_core_ofRegularity` wrappers for decomposition/bounds/convergence)
- Added regularity-first conditional-isometry adapters in
  `ConditionalIsometry.lean`
  (`compensated_sq_setIntegral_zero_core_ofRegularity`,
   `stoch_integral_squared_orthogonal_core_ofRegularity`)
- Added regularity-first remainder-integrability adapters in
  `RemainderIntegrability.lean`
  (`stoch_integral_integrable_core_ofRegularity`,
   `process_integrable_core_ofRegularity`,
   `process_sq_integrable_core_ofRegularity`,
   `itoRemainder_integrable_core_ofRegularity`,
   `itoRemainder_sq_integrable_core_ofRegularity`)
- Rewired `ItoFormulaCoreBridge.lean` to use regularity-first remainder
  integrability adapters instead of passing split measurability hypotheses
  directly at call sites
- Rewrote `ItoProcessCore.stoch_integral_squared_orthogonal_core`
  as a direct core proof (removed direct delegation to legacy
  `ItoProcess.stoch_integral_squared_orthogonal` theorem body)
- Rewrote `ItoProcessCore.compensated_sq_setIntegral_zero_core`
  as a direct core proof (removed direct delegation to legacy
  `ItoProcess.compensated_sq_setIntegral_zero` theorem body)
- Rewrote QV core helper adapters in `ItoCalculus/QVConvergence.lean`
  (`ito_process_increment_decomp_ae_core`, `drift_increment_bound_core`,
   `drift_sq_sum_bound_core`, `qv_partition_sum_core`,
   `si_compensated_sq_L2_single_core`) as direct core proofs/proof bodies,
  removing direct legacy theorem-body delegation for these helpers
- Reduced assumption load in QV helper interfaces by removing redundant
  split-bundle parameters from:
  `ito_process_increment_decomp_ae_core` (keeps only drift regularity),
  `drift_increment_bound_core`, `drift_sq_sum_bound_core`,
  and `qv_partition_sum_core`
- Rewired key internal steps in `capped_ito_qv_L2_bound_core` to use
  regularity-first core adapters for SI isometry, compensated-integrability,
  and orthogonality (`*_core_ofRegularity`) via a local
  `ItoProcessRegularity.ofSplit` bundle
- Added core-local wrappers for L4 increment bounds/measurability and
  core capped-QV helper lemmas in `QVConvergence.lean`, so
  `capped_ito_qv_L2_bound_core` no longer reconstructs a legacy process
  inside its theorem body
- Rewrote `ito_formula_core` in `ItoFormulaCoreBridge.lean` as a direct
  core proof (using `itoRemainderCore` + `ito_formula_martingale_core`)
  instead of delegating to legacy `ito_formula`
- Rewrote `ito_formula_martingale_core` in `ItoFormulaCoreBridge.lean`
  as a direct L²-limit martingale transfer proof (using
  `martingale_setIntegral_eq_of_L2_limit` and core-derived integrability),
  removing direct delegation to legacy `ito_formula_martingale`
- Normalized local legacy reconstruction in `ItoFormulaCoreBridge.lean`
  and QV wrappers to `ItoProcessRegularity.ofSplit` + `toItoProcess`
  (no remaining `toItoProcessOfSplit` usage in those files)
- Normalized local legacy reconstruction in
  `IsometryTheorems.lean` and `ConditionalIsometry.lean` to
  `ItoProcessRegularity.ofSplit` + `toItoProcess`
  (no remaining `toItoProcessOfSplit` call sites)
- Removed obsolete split reconstruction helper
  `ItoProcessCore.toItoProcessOfSplit` after migration
- Removed unused `bdg_inequality` theorem stub from `StochasticIntegration.lean`

### ItoProcess Phase 3 (next)

Goal: continue removing assumption-heavy entry points while preserving theorem usability.

- [x] Add constructor helpers that derive `ItoProcessRegularity` from standard measurability/integrability hypotheses
- [x] Port remaining bridge theorems to consume `ItoProcessCore` + split regularity bundles directly
- [x] Remove remaining direct legacy theorem-body delegation inside core adapters
- [x] Minimize residual local legacy reconstructions in helper wrappers
  (`IsometryTheorems.lean` / `ConditionalIsometry.lean` migrated)
- [ ] Minimize residual derivable assumptions in legacy `ItoProcess` adapters
  (progress: added `ito_formula_martingale_of_bounds` so the legacy
  martingale theorem can be used without explicit `hrem_int`/`hrem_sq_int`)
- [ ] Keep `ito_formula` and `ito_formula_martingale` statement-compatible and fully sorry-free
- [x] Run full `lake build` after each migration batch to protect existing infrastructure

---

## Current Sorry Count (as of 2026-02-25)

| File | Sorrys | Key Items |
|------|--------|-----------|
| **ItoCalculus/StochasticIntegration.lean** | **7** | quadratic_variation, sde_existence, sde_uniqueness_law, stratonovich, semimartingale_integral, girsanov, martingale_representation |
| **ItoCalculus/BrownianMotion.lean** | **5** | time_inversion, eval_unit_is_brownian, Q-Wiener continuous_paths, Q-Wiener regularity_from_trace, levy_characterization |
| **SPDE.lean** | **5** | Generator/semigroup infrastructure |
| **ItoCalculus/Basic.lean** | **1** | is_martingale_of_bounded (needs uniform integrability) |
| **RegularityStructures.lean** | **1** | Abstract approach (complementary to folder) |
| **ItoCalculus/Probability/Basic.lean** | **2** | condexp_jensen, doob_maximal_L2 |
| **Helpers/InnerIntegralIntegrability.lean** | **5** | Tonelli/Fubini infrastructure (NOT on ito_formula critical path) |
| **ItoCalculus/** (all other files) | **0** | Fully proven |
| **EKMS/** | **16** | Hyperbolicity, InvariantMeasure, TwoSidedMinimizers, OneSidedMinimizers, Basic |
| **Examples/** | **15** | YangMills2D, Phi4, KPZ |
| **Nonstandard/Anderson/AndersonTheorem.lean** | **2** | multi_constraint_convergence_uniform, hT₁ |
| **Nonstandard/Anderson/CylinderConvergenceHelpers.lean** | **1** | riemann_sum_continuous_converges |
| **Nonstandard/Anderson/ExplicitSolutions.lean** | **2** | gbm_explicit_solution, ou_explicit_solution |
| **Nonstandard/Anderson/ItoCorrespondence.lean** | **4** | ito_correspondence, ito_isometry_hyperfinite, ito_lemma_hyperfinite, ito_correspondence_integral_finiteness |
| **Nonstandard/Anderson/LocalCLT.lean** | **1** | local_clt_error_bound |
| **RegularityStructures/** | **41** | See RegularityStructures/TODO.md |

**Total: ~108 sorrys** (26 SPDE core + 41 RegularityStructures + 16 EKMS + 15 Examples + 10 Nonstandard)
**Itô formula critical path: 0 sorrys — FULLY PROVEN** ✓
**Anderson theorem critical path: 3 sorrys** (see below)

---

## Anderson's Theorem — Critical Path (as of 2026-02-22)

**Goal:** `anderson_random_walk_pushforward` — pushforward of Loeb measure under standard part = Wiener measure, proved via cylinder set convergence.

**3 sorrys on critical path.**

### Dependency chain:
```
anderson_random_walk_pushforward
  → multi_constraint_convergence_shifted (induction on n)
    base case (n=0): PROVED ✓
    inductive step (n+1 = m+1):
      → hT₁: |∑ C(k,j)/2^k * W_m(x_j) - ∫ gauss * W_m| → 0     [SORRY]
         → binomial_test_fn_convergence (CylinderConvergenceHelpers)  [PROVED ✓]
            → riemann_sum_continuous_converges                         [SORRY]
      → hT₂: sumForm - T₁ → 0                                       [PROVED ✓]
         → multi_constraint_convergence_uniform (for n = m)            [SORRY]
```

### Blocking sorrys (3):

1. **`riemann_sum_continuous_converges`** (CylinderConvergenceHelpers.lean:2175)
   - Riemann sum convergence for continuous bounded functions on lattice mesh
   - Generalizes `gaussDensity_Riemann_sum_converges` (already proved for Gaussian)
   - Standard analysis: uniform continuity on compact sets → mesh → 0
   - **Difficulty: medium** (infrastructure lemma, no deep math)

2. **`hT₁`** (AndersonTheorem.lean:846)
   - Connects `binomial_test_fn_convergence` to the specific goal
   - Test function is `W_m = wienerNestedIntegral` (continuous, bounded by [0,1])
   - Main subtlety: coordinate alignment (k₁ = ⌊t₁*N⌋ - ⌊p*N⌋ vs ⌊dt*N⌋)
   - **Difficulty: medium** (bookkeeping, `binomial_test_fn_convergence` does the heavy lifting)

3. **`multi_constraint_convergence_uniform`** (AndersonTheorem.lean:560)
   - Uniform-in-prevPos version: ∀ prevPos, |count/2^M - W_n(prevPos)| < ε
   - Needed by hT₂ proof (for suffix constraints after conditioning on x₁)
   - Proof: by induction on n, leveraging equicontinuity of wienerNestedIntegral
   - **Difficulty: hard** (combines induction + uniform convergence + equicontinuity)

### Proved components (Anderson):

| Component | File | Status |
|-----------|------|--------|
| `cylinder_prob_convergence` (n=1, φ=1) | CylinderConvergenceHelpers | PROVED ✓ |
| `binomial_test_fn_convergence` (n=1, general φ) | CylinderConvergenceHelpers | PROVED ✓ |
| `gaussDensity_Riemann_sum_converges` | CylinderConvergenceHelpers | PROVED ✓ |
| `binomProb_ratio_near_one` (local CLT ratio) | CylinderConvergenceHelpers | PROVED ✓ |
| `binomial_tail_small` | CylinderConvergenceHelpers | PROVED ✓ |
| `wienerNestedIntegral_nonneg` | WienerNestedIntegral | PROVED ✓ |
| `wienerNestedIntegral_le_one` | WienerNestedIntegral | PROVED ✓ |
| `wienerNestedIntegral_continuous` | WienerNestedIntegral | PROVED ✓ |
| hT₂ (suffix error → 0) | AndersonTheorem | PROVED ✓ |
| hfiber (count/2^M = sumForm) | AndersonTheorem | PROVED ✓ |
| Nonstandard Foundation (all) | Foundation/ | PROVED ✓ (0 sorrys) |
| Loeb measure + Wiener measure | LoebMeasure/ | PROVED ✓ (0 sorrys) |

### Not on Anderson critical path (7 sorrys):
- `ExplicitSolutions.lean` (2): GBM, OU explicit solutions
- `ItoCorrespondence.lean` (4): hyperfinite Itô correspondence
- `LocalCLT.lean` (1): local_clt_error_bound (Berry-Esseen style)

---

## Soundness Audit (2026-02-21, updated from 2026-02-12)

**All files audited for definition soundness and axiom smuggling.**

### Results:
- **ItoProcess** (StochasticIntegration.lean): SOUND — zero computational results as fields.
  `stoch_integral_measurable`, `stoch_integral_sq_integrable`, `stoch_integral_adapted` all
  derived as theorems. `stoch_integral_is_L2_limit` correctly encodes construction data
  (7 conjunctions including a.e. convergence). No axiom smuggling.
- **BrownianMotion.lean**: SOUND — all fields are characterizing properties
- **Basic.lean**: SOUND — Filtration, Martingale, LocalMartingale, StoppingTime all correct
- **SimpleProcess** (SimpleProcessDef.lean): SOUND — partition data + ambient measurability
- **IsGaussian** (Probability/Basic.lean): SOUND — includes characteristic function
- **usualConditions**: SOUND — right-continuous + complete (standard conditions habituelles)
- **SPDE.lean**: SOUND — `PolynomialNonlinearity.leading_nonzero` replaces weak `nontrivial`
- **Helpers/**: SOUND — 15+ files, no issues
- **No axioms anywhere in ItoCalculus/, no .choose in definitions, no True := trivial**

### Fix history:
- (2026-02-12) `PolynomialNonlinearity`: replaced `nontrivial` with `leading_nonzero`
- (2026-02-21) ItoProcess Phase 1: removed `stoch_integral_adapted` field, added `BM_adapted_to_F` + `usual_conditions`
- (2026-02-21) ItoProcess Phase 2: removed `stoch_integral_measurable` + `stoch_integral_sq_integrable` fields, added a.e. convergence to `stoch_integral_is_L2_limit`

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

### NOT on critical path (see table below)

| File | Count | Sorrys | Notes |
|------|-------|--------|-------|
| ItoCalculus/StochasticIntegration.lean | 7 | quadratic_variation, sde_existence_uniqueness, sde_uniqueness_law, stratonovich_chain_rule, semimartingale_integral_exists, girsanov, martingale_representation | Independent theorems |
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

### ItoCalculus/StochasticIntegration.lean (7 sorrys)
1. `quadratic_variation` (line 1721) — QV of Ito process (corollary of ito_formula with f(x)=x^2)
2. `sde_existence_uniqueness` (line 1881) — SDE existence via Picard iteration
3. `sde_uniqueness_law` (line 1895) — Pathwise uniqueness via Gronwall
4. `stratonovich_chain_rule` (line 1952) — Stratonovich chain rule
5. `semimartingale_integral_exists` (line 2101) — Semimartingale integral construction
6. `girsanov` (line 2129) — Girsanov theorem
7. `martingale_representation` (line 2148) — Martingale representation theorem

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
- **ItoCalculus/KolmogorovChentsov/DyadicPartition.lean** — Dyadic partition infrastructure (0 sorrys)
- **ItoCalculus/KolmogorovChentsov/MomentToTail.lean** — Moment-to-tail bounds (0 sorrys)
- **ItoCalculus/KolmogorovChentsov/DyadicIncrement.lean** — Dyadic increment Borel-Cantelli (0 sorrys)
- **ItoCalculus/KolmogorovChentsov/ContinuousModification.lean** — KC theorem (0 sorrys)
- **ItoCalculus/AdaptedLimit.lean** — Adapted L² limits (0 sorrys)
- **ItoCalculus/SIContinuity.lean** — SI continuous modification (0 sorrys)
- **ItoCalculus/ProcessContinuity.lean** — Itô process path continuity (0 sorrys)
- **ItoCalculus/RemainderIntegrability.lean** — Itô remainder integrability (0 sorrys)
- **ItoCalculus/ItoRemainderDef.lean** — itoRemainder definition (0 sorrys)

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
- **Kolmogorov-Chentsov theorem**: processes with E[|X_t - X_s|^p] ≤ M|t-s|^q (q>1) have Hölder continuous modifications
- **Stochastic integral continuous modification**: SI has continuous paths (KC with p=4, q=2 from quartic bound)
- **Itô remainder integrability**: itoRemainder ∈ L¹ ∩ L² under boundedness hypotheses (derived, not assumed)
- **Reconstruction exists**: explicit construction R(f) = Pi_x f(x)
