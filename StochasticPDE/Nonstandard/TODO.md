# Rigorous Stochastic Differential Equations via Nonstandard Analysis

## Goal

Develop a rigorous theory of **stochastic differential equations (SDEs)** using nonstandard (hyperreal) calculus. The approach follows Anderson's 1976 construction:

1. **Hyperfinite random walk** → Brownian motion via standard part
2. **Hyperfinite stochastic integral** → Itô integral via standard part
3. **Loeb measure** → Wiener measure via pushforward

This provides a rigorous foundation where pathwise stochastic calculus is meaningful: paths are actual functions, integrals are actual sums, and measure theory emerges from counting.

## Current State

**Total: 10 sorrys across 5 files** (3 on Anderson critical path, 1 standalone, 6 for Itô chain)

Mathlib provides minimal hyperreal infrastructure:
- `Hyperreal := Germ (hyperfilter ℕ) ℝ` - ultraproduct construction
- `ofSeq`, `IsSt`, `st`, `Infinitesimal`, `Infinite` - basic operations
- `isSt_of_tendsto` - the key bridge theorem

We have built substantial infrastructure on top of this for SDEs.

## Completed Components

### 1. Foundation Layer (`Foundation/`)

**All files: NO sorries, fully proven**

| File | Key Content |
|------|-------------|
| `Hypernatural.lean` | `Hypernat` type, `omega`, arithmetic, `Infinite` predicate, `timeStepIndex` |
| `HyperfiniteSum.lean` | Sums indexed by hypernaturals, linearity, monotonicity |
| `InternalMembership.lean` | Internal sets, ultrafilter membership, hyperfinite sets |
| `Saturation.lean` | ℵ₁-saturation for countable families of internal sets |
| `Arithmetic.lean` | Integer/real arithmetic helpers for casts, division bounds, index computations |

#### Saturation Theory (`Saturation.lean`)

Key definitions and results:
- `CountableInternalFamily` - A countable family of internal sets indexed by ℕ
- `HasFIP` - Internal-level finite intersection property
- `HasStandardFIP` - Standard-level FIP (for each n, n-th level intersection is nonempty)
- `countable_saturation_standard` - Main theorem: HasStandardFIP implies intersection nonempty
- `IsUniform` - Property for families where level sets are constant
- `uniform_hasFIP_implies_hasStandardFIP` - For uniform families, internal FIP ⇒ standard FIP

#### Arithmetic Helpers (`Arithmetic.lean`)

Key lemmas for integer/real arithmetic used in Local CLT proofs:
- `natCast_intCast_eq` - ((n : ℤ) : ℝ) = (n : ℝ) for naturals
- `int_div2_le_real_div2` - Integer division by 2 ≤ real division
- `int_div2_ge_real_div2_sub_half` - Integer division by 2 ≥ real division - 1/2
- `int_ge_one_of_real_gt_half_nonneg` - Integer with real cast > 1/2 and ≥ 0 implies ≥ 1
- `int_div2_add_ge_one_of_real_gt_one` - Key lemma for index lower bounds
- `int_div2_add_le_n_sub_one_of_real_lt` - Key lemma for index upper bounds

### 2. Hyperfinite Random Walk (`HyperfiniteRandomWalk.lean`)

**NO sorries, fully proven**

Key theorems:
- `quadratic_variation_eq_time`: For standard k, QV = k·dt exactly
- `st_quadratic_variation_eq_time`: For standard time t, st(QV) = t
- `dt_infinitesimal`: Time step is infinitesimal when N is infinite

Note: Walk values can be infinite for pathological coin flip sequences.
Finite-path statements require Loeb measure ("almost surely").

### 3. Hyperfinite Stochastic Integration (`HyperfiniteStochasticIntegral.lean`)

**NO sorries, fully proven**

Key theorems:
- `ito_isometry`: Σ(H·ΔW)² = Σ H²·dt exactly
- `integral_infinitesimal_of_standard`: For standard k, the integral is infinitesimal
- `integral_not_infinite_of_standard`: Consequence of above

### 4. Hyperfinite Integration (`HyperfiniteIntegration.lean`)

**NO sorries, fully proven**

Key theorem:
- `st_hyperfiniteRiemannSum_eq_integral`: Standard part of hyperfinite Riemann sum equals integral

### 5. White Noise (`HyperfiniteWhiteNoise.lean`)

**NO sorries, fully proven**

Key results:
- White noise as normalized increments
- Covariance structure (ξₖ² = 1/dt)
- Quadratic variation of integrals

### 6. Anderson's Theorem Infrastructure (`Anderson/`)

#### RandomWalkMoments.lean - **COMPLETE, no sorries**
- `sum_partialSumFin_sq`: Σ_flips S_k² = k * 2^n
- `chebyshev_count`: #{|S_k| > M} * M² ≤ k * 2^n
- `chebyshev_prob`: P(|S_k| > M) ≤ k/M²

#### MaximalInequality.lean - **COMPLETE, no sorries**
- `maximal_count`: #{max |S_i| > M} * M² ≤ (k+1)² * 2^n
- `maximal_prob`: P(max_{i≤k} |S_i| > M) ≤ (k+1)²/M²
- Uses union bound + Chebyshev (weaker than reflection principle)

#### SContinuity.lean - **COMPLETE, no sorries**
- `sum_windowIncrement_sq`: Σ_flips (S_{k+h} - S_k)² = h * 2^n
- `increment_chebyshev_count`: #{|increment| > M} * M² ≤ h * 2^n
- `modulus_bound_prob`: P(max increment > M) ≤ numWindows * h / M²

#### SContinuityAS.lean - **COMPLETE, no sorries**
- `exp_one_lt_four`: e < 4 (using Mathlib's `Real.exp_one_lt_three`)
- `violationProbGlobalThreshold_bound`: P(violation) ≤ 1/C² (via single-step window analysis)
- `sum_inv_sq_bounded`: Σ 1/k² ≤ 2 (via telescoping lemma)
- `sum_telescope_Ico`: Telescoping sum identity
- `sqrt2_fourthRoot_bound_strict`: Fourth-root calculation for Lévy modulus (tight bound)
- `levyModulus_implies_S_continuous`: Paths with Lévy modulus are S-continuous
- `levyModulus_violation_sum_bound`: Sum of violation probs ≤ 2

#### LocalCLT.lean - **2 sorries remaining (substantial infrastructure proven)**
- `stirling_lower_bound`: **PROVEN** via Mathlib's `Stirling.le_factorial_stirling`
- `stirling_ratio_tendsto_one`: **PROVEN** via Mathlib's `tendsto_stirlingSeq_sqrt_pi`
- `stirling_upper_bound_eventual`: **PROVEN** as consequence of ratio → 1
- `choose_eq_factorial_div`: **PROVEN** binomial in terms of factorials
- `factorial_eq_stirlingSeq`: **PROVEN** n! = stirlingSeq(n) · √(2n) · (n/e)^n
- `stirlingSeq_le_one`: **PROVEN** stirlingSeq(n) ≤ stirlingSeq(1) for n ≥ 1
- `e_sq_le_four_pi`: **PROVEN** e²/(2π) ≤ 2 using numerical bounds
- `central_binomial_asymptotic`: **PROVEN** C(2n,n) ≤ 4^n/√(πn/2) via Stirling
- `gaussian_tail_bound`: **PROVEN** Mill's ratio via comparison argument and `integral_exp_mul_Ioi`
- `sum_exp_boolToInt`: **PROVEN** Σ_b exp(l·boolToInt(b)) = 2·cosh(l)
- `equivFinSuccFun`: **PROVEN** (Fin (n+1) → α) ≃ α × (Fin n → α) via Fin.cons
- `sum_prod_function_eq_prod_sum`: **PROVEN** Σ_flips Π_i f(i, flips i) = Π_i Σ_b f(i, b)
- `exponential_moment_random_walk`: **PROVEN** Σ_flips exp(λ·S_n) = (2·cosh(λ))^n
- `double_factorial_bound`: **PROVEN** (2k)! ≥ 2^k · k! by induction
- `exp_markov_count`: **PROVEN** Exponential Markov inequality for counting
- `partialSumFin_neg_flips`: **PROVEN** Random walk symmetry under flip negation
- `cosh_le_exp_half_sq`: **PROVEN** via Mathlib's `Real.cosh_le_exp_half_sq`
- `hoeffding_random_walk`: **PROVEN** P(|S_n| > t) ≤ 2·exp(-t²/(2n)) via Chernoff method
- `stirlingSeq_bounds`: **PROVEN** √π ≤ stirlingSeq(n) ≤ stirlingSeq(1)
- `factorial_ratio_stirling_bounds`: **PROVEN** n!/(k!(n-k)!) bounded by Stirling expressions
- `local_clt_error_bound`: sorry (standalone, NOT on critical path — superseded by ratio approach in `binomProb_ratio_near_one`)
- `local_clt_central_region`: **PROVEN** (both upper and lower bounds)
  - Upper bound uses `stirling_ratio_decomp`, `exp_factor_le_one`, `s1_prefactor_le_two` from LocalCLTHelpers.lean
  - Lower bound uses `pinsker_excess_crude` from LocalCLTHelpers.lean
- `cylinder_prob_convergence`: sorry (main bridge theorem, needs CylinderConvergenceHelpers)

#### CylinderConvergenceHelpers.lean - **WIP (20+ proven, 1 sorry)**
Infrastructure for `cylinder_prob_convergence`:
- `gaussianDensitySigma_continuous`: **PROVEN**
- `gaussianDensitySigma_nonneg`: **PROVEN**
- `gaussianDensitySigma_le_peak`: **PROVEN**
- `floor_ratio_tendsto`: **PROVEN** ⌊tN⌋/N → t
- `floor_eventually_large`: **PROVEN**
- `partialSumFin_depends_on_prefix`: **PROVEN**
- `countTruesBelow`: **DEFINED** (count of true flips in first k positions)
- `card_filter_lt`: **PROVEN** (#{i : Fin N | i < k} = k, via `Finset.card_bij'` + `Fin.castLE`)
- `partialSumFin_eq_countTrues`: **PROVEN** (S_k = 2·#true - k, partition into true/false)
- `card_bool_trues_eq_choose`: **PROVEN** (#{g : Fin k → Bool | j trues} = C(k,j), via bijection with `powersetCard`)
- `card_prefix_suffix_product`: **PROVEN** (#{f | countTrue = j} = C(k,j)·2^{N-k}, prefix/suffix decomposition)
- `scaledProb_eq_walkIntervalProb`: **PROVEN** (card(filter)/2^N = walkIntervalProb, fiber decomposition)
- `binomProb_ratio_near_one`: **PROVEN** (C(k,j)/2^k ≈ gaussian·Δx, quantitative local CLT ratio)
  - Decomposition: binomP/gaussP = θ × P × Q where θ = Stirling ratio, P = sqrt prefactor, Q = exp factor
  - Each factor shown to be within ε of 1 for large N, using Stirling bounds + entropy excess
  - Helper files: BinomGaussRatioHelpers.lean, RatioConvergenceHelpers.lean (both fully proven)
- `gaussDensity_Riemann_sum_converges`: sorry (Riemann sum → integral, uses continuity of Gaussian density)
- **Chernoff bound chain - ALL PROVEN:**
  - `weighted_exp_markov`: exponential Markov inequality
  - `binomial_mgf`: Σ C(k,j)/2^k exp(λ(2j-k)) = cosh(λ)^k
  - `binomial_chernoff_upper`: Chernoff for positive tail
  - `binomial_chernoff_lower`: Chernoff for negative tail (by symmetry)
  - `binomial_tail_small`: P(|S_k| > C√k) ≤ 2exp(-C²/2)

#### LocalCLTHelpers.lean - **COMPLETE, 0 sorrys**
- Helper lemmas for factor-2 bounds in `local_clt_central_region`:
  - `log_diff_ge_two_v`, `binary_pinsker`: Binary Pinsker inequality infrastructure
  - `exp_factor_le_one`: Pinsker-based bound on exponential factor
  - `e_fourth_lt_sixteen_pi_sq`, `eighty_one_e4_lt_512_pi_sq`: Numerical bounds
  - `e4n2_le_64pi2_kink`: e⁴n² ≤ 64π²k(n-k) for central region
  - `s1_sq_pi_ratio_sq_le_four`: (s₁²/π)² × n²/(4k(n-k)) ≤ 4
  - `s1_prefactor_le_two`: (s₁²/π) × √(n²/(4k(n-k))) ≤ 2
  - `stirling_ratio_decomp`: central/2^n = √(n/(2πk(nk))) × exp_factor
  - `sqrt_prefactor_factoring`: √(n/(2πk(nk))) = √(n²/(4k(nk))) × √(2/(πn))
  - `central_region_s_bound`, `central_region_e4_bound`: Central region bounds
  - `pinsker_excess_crude`: **PROVEN** (derivative nonnegativity for entropy excess bound)
  - `pinsker_excess_crude_abs`: **PROVEN** (absolute value version)
  - `power_product_eq_exp`: **PROVEN** (product of powers as exponential)

#### AndersonTheorem.lean - **WIP (10 theorems proven, 1 sorry on critical path)**
- `LoebPathSpace`: Hyperfinite path space with Loeb probability structure
- `preLoebMeasure`: Standard part of hyperfinite probability
- `preLoebMeasure_nonneg`: **PROVEN** via `st_le_of_le`
- `preLoebMeasure_univ`: **PROVEN** via `dif_neg`, `st_id_real`
- `levyModulusEvent`: **UPDATED** to use variance bound `C√(h/n)` instead of Lévy log formula
  - **Design note**: Anderson's 1976 paper only requires S-continuity (no specific modulus formula)
  - The variance bound is sufficient for S-continuity and avoids degeneracy issues
- `levyModulusEvent_fraction_bound`: **PROVEN** via Doob L² maximal inequality
- `sContinuous_loebMeasure_bound`: **PROVEN**
- `sContinuous_loebMeasure_three_quarters`: **PROVEN** (corollary)
- `sContinuous_loebMeasureOne`: **PROVEN** (uses sContinuous_loebMeasure_bound)
- `WienerMeasureSpec`: Cylinder set probabilities for Wiener measure
- `wienerCylinderProb`: defined (multi-time Wiener probability)
- `standardPartMap'_startsAtZero`: **PROVEN** (calls `standardPartMap_startsAtZero`)
- `anderson_theorem_cylinder`: sorry (Loeb → Wiener cylinder convergence, needs cylinder_prob_convergence)
- `cylinder_hyperfinite_iff_standard`: **PROVEN** (calls `standardPartPath_isSt`)
- `anderson_theorem`: **PROVEN** (calls `anderson_theorem_cylinder`)
- `brownian_paths_continuous_as`: **PROVEN** (calls `sContinuous_loebMeasureOne`)
- `brownian_increments_gaussian`: **PROVEN** by `rfl`

#### ItoCorrespondence.lean - **WIP (definitions complete, soundness issues FIXED)**
- `SimpleProcess`: Step function adapted to filtration
- `ItoIntegrand`: L²-adapted process for Itô integration
- `liftToHyperfinite`: Lift standard process to hyperfinite integrand
- `hyperfiniteItoIntegral`: Hyperfinite stochastic integral Σₖ Hₖ·ΔWₖ
- `ito_correspondence`: sorry - **FIXED**: now requires S-continuity hypothesis
  - Previously claimed deterministic finiteness (unsound)
  - Now correctly requires path to satisfy modulus bound for finiteness
- `ito_isometry_standard`: placeholder
- `ito_linearity`: **PROVEN** (full proof)
- `ito_integral_const`: **PROVEN** (full proof)
- `ito_lemma_hyperfinite`: sorry (Itô's lemma via Taylor)
- `ito_formula`: sorry - **FIXED**: now requires S-continuity and bounded derivative hypotheses

#### HyperfiniteSDE.lean - **COMPLETE (10 theorems proven, 0 sorries)**
- `HyperfiniteSDE`: Hyperfinite SDE structure (drift, diffusion, initial condition)
- `solution`: Euler-Maruyama solution Xₖ₊₁ = Xₖ + a(Xₖ)dt + b(Xₖ)ΔWₖ
- `solutionAtHypernat`: Solution at hypernatural index
- `increment_pm_dx`: **PROVEN** (increment is ±dx)
- `increment_sq`: **PROVEN** (increment² = dt)
- `solution_zero`: **PROVEN** by `rfl`
- `solution_step`: **PROVEN** by `rfl`
- `solution_increment_eq`: **PROVEN** (ring tactic)
- `solutionAtHypernat_zero`: **PROVEN** (using Germ.coe_eq)
- `solution_exists`: **PROVEN** (trivial from definition)
- `solution_s_continuous`: **PROVEN** (one-step bound using boundedness)
- `quadratic_variation_approx`: **PROVEN** (error bound via algebraic manipulation)
- `solution_integral_form`: **PROVEN** by induction (drift + stochastic decomposition)
- Special cases: `geometricBrownianMotion`, `ornsteinUhlenbeck`, `squareRootProcess`

#### SDESolution.lean - **COMPLETE (all theorems proven, 0 sorries)**
- `WellPosedSDE`: Classical SDE well-posedness (Lipschitz, growth bounds)
- `SDE_is_S_continuous`: S-continuity modulus definition for SDE solutions
- `SDE_is_S_continuous_levelN`: Level-n S-continuity for solutionAtHypernat
- `stepIndex_le_numSteps_levelN`: **PROVEN** (step index bounded by numSteps at level n)
- `floor_diff_bound`: **PROVEN** (|⌊a⌋ - ⌊b⌋| ≤ |a - b| + 1)
- `sde_solution_s_continuous`: **PROVEN** (tautology from S-continuity hypothesis)
- `solution_diff_bound`: **PROVEN** (helper: step bound by induction)
- `dx_infinitesimal`: **PROVEN** (helper: dx infinitesimal from dx²=dt)
- `solution_s_continuous_path`: **PROVEN** (S-continuity using telescope bound)
- `solution_finite_at_standard`: **PROVEN** by induction using infinitesimal arithmetic
- `standardPartSolution`: Standard part gives C([0,T], ℝ) solution
- `standardPartSolution_zero`: **PROVEN** using stepIndex and solutionAtHypernat_zero
- `sde_solution_chaining_bound`: **PROVEN** (|X_n(k) - X_n(0)| ≤ (k/w + 1)*B by strong induction)
- `standardPartSolution_continuous`: **PROVEN**
- `drift_integral_correspondence`: **PROVEN** (level-n drift sums bounded by M*t via hyperreal bound extraction)
- `stochastic_integral_correspondence`: **PROVEN** (finite sum of infinitesimals is infinitesimal)
- `standardPart_satisfies_sde`: **PROVEN** (foldl decomposition by induction - key main theorem)
- `uniqueness_hyperfinite`: **PROVEN** by induction
- `standardPart_unique`: **PROVEN** (both solutions equal standardPartSolution)
- `simple_bm_solution`: **PROVEN** by `rfl`
- `variance_evolution`: **PROVEN** by ring tactic
- `expected_value_ode`: **PROVEN** (level-n decomposition by definition)
- Note: `gbm_explicit_solution` and `ou_explicit_solution` moved to ExplicitSolutions.lean

#### PathContinuity.lean - **COMPLETE, no sorries**
- `ofSeq_le_ofSeq`: Comparison of hyperreals via eventually (local lemma)
- `oscillation_bound_by_chaining`: |W(k) - W(0)| ≤ (k/w + 1) · B via strong induction
- `hyperfiniteWalkValue_finite_of_S_continuous`: S-continuous paths have finite values at standard times
- `standardPartPath`: Standard part function f(t) = st(W(⌊t·N⌋))
- `standardPartPath_isSt`: st agrees with hyperreal up to infinitesimal
- `standardPartPath_continuous`: **KEY THEOREM** - f is continuous on [0,1]

### 7. Loeb Measure (`LoebMeasure/`)

**Core files: NO sorries**

What's proven:
- `InternalProbSpace` with probability properties
- `preLoebMeasure` (standard part of internal probability)
- Finite additivity, monotonicity
- `DecreasingConcreteEvents.sigma_additivity` - **σ-additivity proven via saturation**
- `LoebMeasurableSet`, `LoebOuterMeasure`, `LoebInnerMeasure`
- `LoebMeasurable` - sets where inner = outer measure
- Cylinder sets with probability computation
- Binomial probability computations
- Path continuity structures (S-continuity, modulus)
- `SqrtData.mk'` - proves dx = √dt exists

#### WienerMeasure.lean - **WIP, defines path space and Wiener measure**
- `PathSpace`: C([0,1], ℝ) using Mathlib's ContinuousMap
- `CylinderConstraint`: Cylinder sets determined by finite times
- `gaussianDensity`: Gaussian density for Brownian increments
- `standardPartMap`: S-continuous hyperfinite paths → PathSpace **PROVEN**
- `standardPartMap_startsAtZero`: Paths start at 0 **PROVEN**
- `gaussianDensity_integral_eq_one`: **PROVEN** (via Mathlib's `integral_gaussian`)
- `anderson_cylinder_convergence`: Placeholder statement (needs local CLT)

#### MathlibBridge.lean - **Carathéodory measurability COMPLETE (0 sorries)**
- `LevelwiseSet`: Concrete representation of internal sets **PROVEN**
- `LevelwiseSet.preLoeb`: Pre-Loeb measure with properties **PROVEN**
- `preLoeb_add_disjoint`: Finite additivity **PROVEN**
- `cardAtLevel_union_le`: |A ∪ B| ≤ |A| + |B| **PROVEN**
- `hyperProb_le_add`: Subadditivity of hyperProb **PROVEN**
- `preLoeb_le_add`: Subadditivity of preLoeb **PROVEN**
- `LevelwiseCover`: Countable cover structure **DEFINED**
- `loebOuterMeasure'`: Outer measure via covers **DEFINED**
- `loebOuterMeasure'_empty`: μ*(∅) = 0 **PROVEN**
- `loebOuterMeasure'_le_preLoeb`: Upper bound **PROVEN**
- `loebOuterMeasure'_mono`: Monotonicity **PROVEN**
- `inter_diff_disjoint`: (E ∩ A) and (E \ A) disjoint **PROVEN**
- `inter_union_diff`: (E ∩ A) ∪ (E \ A) = E **PROVEN**
- `LoebCaratheodoryMeasurable`: Carathéodory condition **DEFINED**
- `loebCaratheodory_of_internal`: Internal sets Carathéodory measurable **PROVEN**
- `loebOuterMeasureOnCoinFlips`: Placeholder for Mathlib OuterMeasure (needs proper carrier type)

## Roadmap to Complete SDEs

### Phase 1: Loeb Measure (In Progress)
1. ✅ σ-additivity for decreasing sequences (via saturation)
2. ✅ Complete Carathéodory extension (MathlibBridge.lean)
   - ✅ `LevelwiseSet`, `preLoeb`, `preLoeb_add_disjoint` (finite additivity)
   - ✅ `preLoeb_le_add` (subadditivity)
   - ✅ `loebOuterMeasure'`, `loebOuterMeasure'_empty`, `loebOuterMeasure'_mono`
   - ✅ `loebCaratheodory_of_internal` - Internal sets are Carathéodory measurable
   - ⬜ Connect to Mathlib `OuterMeasure.toMeasure` (type-theoretic work)
3. ⬜ Prove Loeb measurable sets form σ-algebra
   - ✅ `loebMeasurable_compl_internal`: Complements measurable
   - ✅ `loebMeasurable_add_disjoint`: Finite unions measurable
   - ⬜ Countable unions (follows from Carathéodory via Mathlib's infrastructure)

### Phase 2: S-Continuity Almost Surely
4. ✅ Chebyshev bounds and maximal inequality
5. ✅ Increment variance and modulus bounds
6. ✅ Fill remaining numerical sorries in SContinuityAS.lean
7. ✅ LocalCLT Stirling infrastructure (via Mathlib's `Stirling.le_factorial_stirling`)
   - ✅ `gaussian_tail_bound` - **PROVEN** Mill's ratio via integration by parts
   - ✅ `cosh_le_exp_half_sq` - **PROVEN** via Mathlib's `Real.cosh_le_exp_half_sq`
   - ✅ `hoeffding_random_walk` - **PROVEN** via Chernoff method (exp Markov + cosh bound)
   - ✅ `central_binomial_asymptotic` - **PROVEN** C(2n,n) ≤ 4^n/√(πn/2) via Stirling
   - ✅ `factorial_ratio_stirling_bounds` - **PROVEN** n!/(k!(n-k)!) Stirling bounds
   - ✅ `stirlingSeq_triple_ratio_near_one` in Arithmetic.lean - **PROVEN**
   - ✅ Chernoff bound chain in CylinderConvergenceHelpers.lean - **ALL PROVEN**
     - `weighted_exp_markov`, `binomial_mgf`, `binomial_chernoff_upper/lower`, `binomial_tail_small`
   - Remaining sorrys on critical path to `anderson_theorem_cylinder` (3 total):
     - `gaussDensity_Riemann_sum_converges` (CylinderConvergenceHelpers.lean:1034) - Riemann sum
     - `cylinder_prob_convergence` (LocalCLT.lean:1144) - main bridge (uses above)
     - `anderson_theorem_cylinder` (AndersonTheorem.lean:516) - uses cylinder_prob_convergence
   - Standalone sorry (not on critical path):
     - `local_clt_error_bound` (LocalCLT.lean:185) - absolute error bound, superseded by ratio approach
   - Recently proven (eliminated 3 sorrys):
     - `pinsker_excess_crude` (LocalCLTHelpers.lean) - **NOW PROVEN**
     - `scaledProb_eq_walkIntervalProb` (CylinderConvergenceHelpers.lean) - **NOW PROVEN**
     - `binomProb_ratio_near_one` (CylinderConvergenceHelpers.lean) - **NOW PROVEN**
       (Stirling decomposition + entropy excess + sqrt prefactor bounds)
   - Non-critical sorrys (6 total, for Itô chain):
     - `ito_correspondence` (ItoCorrespondence.lean:202)
     - `ito_isometry_standard` (ItoCorrespondence.lean:229)
     - `ito_lemma_hyperfinite` (ItoCorrespondence.lean:373)
     - `ito_formula` (ItoCorrespondence.lean:406)
     - `gbm_explicit_solution` (ExplicitSolutions.lean:81)
     - `ou_explicit_solution` (ExplicitSolutions.lean:112)
   - **Critical path dependency chain:**
     ```
     anderson_theorem (PROVEN, calls anderson_theorem_cylinder)
       └── anderson_theorem_cylinder (SORRY)
             └── cylinder_prob_convergence (SORRY)
                   ├── scaledProb_eq_walkIntervalProb (PROVEN)
                   ├── binomProb_ratio_near_one (PROVEN)
                   │     └── local_clt_central_region (PROVEN)
                   │           ├── pinsker_excess_crude (PROVEN)
                   │           └── exp_factor_le_one (PROVEN)
                   ├── gaussDensity_Riemann_sum_converges (SORRY) ◄── NEXT TARGET
                   │     └── gaussianDensitySigma_continuous (PROVEN)
                   └── binomial_tail_small (PROVEN, Chernoff bounds)
     local_clt_error_bound (SORRY, standalone - not on critical path)
     ```

### Phase 3: Standard Part and Path Space
8. ✅ Define standard part function f(t) = st(W(⌊t·N⌋)) for S-continuous paths
   - `standardPartPath` defined in PathContinuity.lean
   - `standardPartPath_isSt` proven (using Mathlib's `isSt_st'`)
   - `hyperfiniteWalkValue_finite_of_S_continuous` - **PROVEN** (uses chaining lemma)
   - `standardPartPath_continuous` - **PROVEN** (ε-δ argument with S-continuity modulus)
9. ✅ Prove oscillation bound (chaining argument using S-continuity)
   - `oscillation_bound_by_chaining` - **PROVEN** via strong induction
10. ✅ Prove f is continuous (uses S-continuity modulus)
   - Key lemmas: `ofSeq_le_ofSeq`, `Int.cast_abs`, `st_le_of_le`, `st_id_real`
11. ✅ Define path space C([0,T]) with Wiener measure
   - `PathSpace` = `C(UnitInterval, ℝ)` using Mathlib's ContinuousMap
   - Cylinder sets and Gaussian density defined
   - `standardPartMap` sends S-continuous paths to PathSpace

### Phase 4: Anderson's Theorem
12. ⏳ Pushforward of Loeb measure under st = Wiener measure
   - Infrastructure in AndersonTheorem.lean (5 theorems proven)
   - Requires: local CLT completion for full proof
   - `anderson_theorem_cylinder`, `anderson_theorem` have sorries
13. ⏳ Itô integral = standard part of hyperfinite stochastic integral
   - ItoCorrespondence.lean created with definitions
   - `hyperfiniteItoIntegral` defined, `ito_correspondence` has sorry
   - `ito_lemma_hyperfinite` stated (Itô's lemma via Taylor)

### Phase 5: SDEs
14. ✅ Solution theory for hyperfinite SDEs: dX = a(X)dt + b(X)dW
   - HyperfiniteSDE.lean complete (10 theorems proven, 0 sorries)
   - `solution` defined via Euler-Maruyama scheme
   - `increment_sq`, `solution_exists`, `solution_integral_form` proven
   - Special cases: GBM, OU, CIR, simple BM
15. ⏳ Standard part gives classical SDE solution
   - SDESolution.lean (16 theorems proven, 0 sorries)
   - `standardPartSolution` defined
   - `solution_finite_at_standard` proven by induction
   - `standardPartSolution_zero` proven
   - `uniqueness_hyperfinite` proven by induction
   - `standardPart_satisfies_sde` **PROVEN** (main result - foldl decomposition)
   - `drift_integral_correspondence` **PROVEN** (hyperreal bound extraction)
   - `stochastic_integral_correspondence` **PROVEN** (infinitesimal sums)
   - `standardPartSolution_continuous` **PROVEN** (0 sorries)
   - `gbm_explicit_solution` and `ou_explicit_solution` in ExplicitSolutions.lean (need Itô lemma)
16. ✅ Existence and uniqueness via Picard iteration (hyperfinitely)
   - `solution_exists` proven (trivial from recursive definition)
   - `uniqueness_hyperfinite` proven

## File Structure

```
Nonstandard/
├── Foundation/
│   ├── Hypernatural.lean        [COMPLETE] hyperfloor_mono, timeStepIndex_mono added
│   ├── HyperfiniteSum.lean      [COMPLETE]
│   ├── InternalMembership.lean  [COMPLETE]
│   ├── Saturation.lean          [COMPLETE]
│   └── Arithmetic.lean          [COMPLETE] Integer/real cast helpers
├── Anderson/
│   ├── RandomWalkMoments.lean   [COMPLETE] E[S_k²]=k, Chebyshev (0 sorries)
│   ├── MaximalInequality.lean   [COMPLETE] P(max |S_i| > M) bound (0 sorries)
│   ├── SContinuity.lean         [COMPLETE] Increment variance, modulus (0 sorries)
│   ├── SContinuityAS.lean       [COMPLETE] Borel-Cantelli, Lévy modulus (0 sorries)
│   ├── LocalCLT.lean            [WIP] Stirling, binomial → Gaussian (2 sorries)
│   ├── LocalCLTHelpers.lean     [COMPLETE] Factor-2 bound helpers (0 sorrys)
│   ├── BinomGaussRatioHelpers.lean [COMPLETE] Stirling decomposition helpers (0 sorrys)
│   ├── RatioConvergenceHelpers.lean [COMPLETE] Product-near-one helpers (0 sorrys)
│   ├── CylinderConvergenceHelpers.lean [WIP] Combinatorial/analytical helpers (1 sorry: Riemann sum)
│   ├── AndersonTheorem.lean     [WIP] st_* μ_L = μ_W (1 sorry: anderson_theorem_cylinder)
│   ├── ItoCorrespondence.lean   [WIP] st(Σ H·dW) = ∫ H dW (4 sorries)
│   ├── HyperfiniteSDE.lean      [COMPLETE] dX = a·dt + b·dW (0 sorries)
│   ├── SDESolution.lean         [COMPLETE] Standard part → SDE solution (0 sorries)
│   └── ExplicitSolutions.lean   [WIP] GBM/OU explicit formulas (2 sorries, need Itô)
├── LoebMeasure/
│   ├── InternalProbSpace.lean   [COMPLETE]
│   ├── SigmaAdditivity.lean     [COMPLETE]
│   ├── LoebMeasurable.lean      [COMPLETE]
│   ├── CylinderSets.lean        [COMPLETE]
│   ├── CoinFlipSpace.lean       [COMPLETE]
│   ├── PathContinuity.lean      [COMPLETE] standardPartPath, continuity proven
│   ├── WienerMeasure.lean       [WIP] Wiener measure (wienerCylinderProb n≥2 placeholder)
│   └── MathlibBridge.lean       [COMPLETE] Carathéodory extension (0 sorries)
├── Anderson.lean                [module file] - imports all Anderson/ files
├── HyperfiniteRandomWalk.lean   [COMPLETE] stepIndex_mono added
├── HyperfiniteWhiteNoise.lean   [COMPLETE]
├── HyperfiniteIntegration.lean  [COMPLETE]
├── HyperfiniteStochasticIntegral.lean [COMPLETE]
├── LoebMeasure.lean             [COMPLETE]
├── Nonstandard.lean             [module file]
└── TODO.md                      [this file]
```

## Key Design Decisions

1. **No axioms**: Everything built from Mathlib's ultraproduct construction
2. **Hypernat as subtype**: `Hypernat := { x : ℝ* // IsHypernat x }` for type safety
3. **toSeq via Classical.choose**: Extract representative sequences non-constructively
4. **Honest about limitations**: Theorems that require Loeb measure are documented, not sorry'd
5. **Rigorous definitions only**: Deleted trivial/circular theorems that claimed more than they proved
6. **Hyperreal sqrt proved**: `SqrtData.mk'` proves √dt exists using eventual positivity
7. **Correct index handling**: `centralBinomialShifted` and `local_clt_*` use `(n/2 : ℤ) + k` (not `k.toNat`) to correctly handle negative k values

## References

1. Anderson, R. M. "A nonstandard representation for Brownian motion and Itô integration" (1976)
2. Loeb, P. "Conversion from nonstandard to standard measure spaces" (1975)
3. Lindstrøm, T. "Hyperfinite stochastic integration" (1980s)
4. Albeverio, S. et al. "Nonstandard Methods in Stochastic Analysis and Mathematical Physics"
5. Goldblatt, R. "Lectures on the Hyperreals" - Chapter 11 on internal sets
