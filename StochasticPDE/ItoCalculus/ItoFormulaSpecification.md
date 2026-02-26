# Ito Formula: Precise Statement and Definition Audit

This document gives a precise description of the Ito formula theorem as it is proved in this codebase, and audits the definitions it depends on.

Primary theorem source:
- `StochasticPDE/ItoCalculus/ItoFormulaProof.lean` (`SPDE.ito_formula`)

## 1. Exact theorem shape (`SPDE.ito_formula`)

The theorem (in Lean form) is:

```lean
theorem ito_formula {F : Filtration Omega R}
    [IsProbabilityMeasure mu]
    (X : ItoProcess F mu)
    (f : R -> R -> R)
    (hf_t : forall x, Differentiable R (fun t => f t x))
    (hf_x : forall t, ContDiff R 2 (fun x => f t x))
    (hdiff_bdd : exists M, forall t w, |X.diffusion t w| <= M)
    (hdrift_bdd : exists M, forall t w, |X.drift t w| <= M)
    (hf_x_bdd : exists M, forall t x, |deriv (fun x => f t x) x| <= M)
    (hf_xx_bdd : exists M, forall t x, |deriv (deriv (fun x => f t x)) x| <= M)
    (hf_t_bdd : exists M, forall t x, |deriv (fun s => f s x) t| <= M)
    (hf_t_cont : Continuous (fun p : R x R => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : R x R => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : R x R => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun w => (X.process 0 w)^2) mu) :
    exists (stoch_int : R -> Omega -> R),
      (forallᵐ w ∂mu, stoch_int 0 w = 0) /\
      (forall s t : R, 0 <= s -> s <= t ->
        forall A : Set Omega, MeasurableSet[F.sigma_algebra s] A ->
        ∫ w in A, stoch_int t w ∂mu = ∫ w in A, stoch_int s w ∂mu) /\
      (forall t : R, t >= 0 -> forallᵐ w ∂mu,
        f t (X.process t w) = f 0 (X.process 0 w) +
          (∫ s in Set.Icc 0 t,
            ( deriv (fun u => f u (X.process s w)) s
            + deriv (fun x => f s x) (X.process s w) * X.drift s w
            + (1/2) * deriv (deriv (fun x => f s x)) (X.process s w) * (X.diffusion s w)^2
            ) ∂volume) +
          stoch_int t w)
```

Interpretation:
- The theorem is existential: it proves there exists a process `stoch_int`.
- The process starts at zero almost surely.
- It satisfies a set-integral martingale property relative to `F_s`.
- The Ito identity holds almost surely for each `t >= 0`.

In the proof, the witness is chosen as `itoRemainder X f`.

## 2. What README shorthand means

README states:

`f(t, X_t) = f(0, X_0) + int_0^t [partial_t f + partial_x f * mu + 1/2 partial_xx f * sigma^2] ds + M_t`

This is mathematically correct shorthand. The formal theorem strengthens this shorthand by explicitly packaging:
- existence of the remainder process,
- its initial condition,
- and its martingale property in set-integral form.

## 3. Definition chain used by Ito formula

## 3.1 Brownian motion (`SPDE.BrownianMotion`)

Defined in `StochasticPDE/ItoCalculus/BrownianMotion.lean`.
Core fields include:
- a filtration `F`,
- an adapted process,
- `W_0 = 0` a.s.,
- a.s. continuous paths,
- independent increments,
- Gaussian increments,
- a nonpositive-time convention (`W_t = 0` a.s. for `t <= 0`).

This is a structural definition, not an axiom.

## 3.2 Ito process (`SPDE.ItoProcess`)

Defined in `StochasticPDE/ItoCalculus/StochasticIntegration.lean`.
It contains:
- dynamics fields: `process`, `drift`, `diffusion`, `BM`, `stoch_integral`,
- decomposition field:
  - `integral_form`:
    `X_t = X_0 + int_0^t drift ds + stoch_integral_t` a.s. for `t >= 0`,
- construction data:
  - `stoch_integral_is_L2_limit` (simple-process approximations, L2 convergence, isometry-limit data, integrand L2 convergence, and a.e. pointwise convergence),
- regularity/measurability fields:
  - drift and diffusion adaptedness/joint measurability/integrability assumptions,
- filtration compatibility:
  - `F_le_BM_F`, `BM_adapted_to_F`, `usual_conditions`,
- path regularity:
  - `process_continuous` a.s.

This is assumption-heavy, but explicit.

## 3.3 Derived (not assumed) stochastic-integral properties

From `stoch_integral_is_L2_limit` + compatibility assumptions, the following are proved as theorems in `StochasticIntegration.lean`:
- `stoch_integral_aestronglyMeasurable`
- `stoch_integral_sq_integrable`
- `stoch_integral_integrable`
- `stoch_integral_adapted`
- `stoch_integral_measurable`
- `stoch_integral_initial`
- `stoch_integral_martingale`

These are not extra structure fields of `ItoProcess`.

## 3.4 Ito remainder definition

Defined in `StochasticPDE/ItoCalculus/ItoRemainderDef.lean`:
- `itoRemainder X f t w`
  is exactly
  `f(t, X_t) - f(0, X_0) - int_0^t [partial_t f + partial_x f * drift + 1/2 partial_xx f * diffusion^2] ds`.

This is the process that becomes the martingale term in Ito formula.

## 4. Immediate theorem dependencies in the proof chain

## 4.1 Martingale step

`SPDE.ito_formula_martingale` proves set-integral martingale property of `itoRemainder`.
It uses:
- L2 convergence of SI-increment approximants to the remainder,
- transfer of set-integral martingale property along L2 limits.

## 4.2 Integrability discharge from bounds

`SPDE.ito_formula_martingale_of_bounds` removes explicit remainder integrability assumptions by deriving them from:
- bounded drift/diffusion,
- bounded derivatives of `f`,
- continuity assumptions on derivative maps,
- `X_0 in L2`.

## 4.3 Final assembly

`SPDE.ito_formula`:
- sets `stoch_int := itoRemainder X f`,
- proves initial value at time `0`,
- imports martingale property from `ito_formula_martingale_of_bounds`,
- and obtains Ito identity by unfolding the definition.

## 5. Core split variant

The file `StochasticPDE/ItoCalculus/ItoProcessCore.lean` provides:
- `ItoProcessCore` (minimal dynamics object),
- split regularity bundles:
  - `ItoProcessConstruction`
  - `ItoProcessDriftRegularity`
  - `ItoProcessDiffusionRegularity`
  - `ItoProcessFiltrationCompatibility`
- assembly/projection adapters.

`StochasticPDE/ItoCalculus/ItoFormulaCoreBridge.lean` proves:
- `ito_formula_martingale_core`,
- `ito_formula_core`,
- and regularity-first variants,
by reconstructing the legacy `ItoProcess` and reusing the established proof infrastructure without changing theorem meaning.

## 6. Soundness status for Ito formula path

Checks performed:
- `#print axioms SPDE.ito_formula`
- `#print axioms SPDE.ito_formula_martingale`
- `#print axioms SPDE.ito_formula_martingale_of_bounds`
- `#print axioms SPDE.ito_formula_core`
- `#print axioms SPDE.ito_formula_martingale_core`

Observed dependencies:
- `propext`, `Classical.choice`, `Quot.sound`

`sorryAx` is not present in these theorem dependencies.

Note:
- There are still `sorry` declarations in other parts of `StochasticIntegration.lean` (for example semimartingale/SDE/Stratonovich sections), but those are outside the Ito-formula critical theorem chain described here.

