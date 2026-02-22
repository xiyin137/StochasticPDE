# Notes on Anderson (1976): A Nonstandard Representation for Brownian Motion and Ito Integration

Bull. Amer. Math. Soc. 82(1), January 1976, pp. 99–101.

## Paper Summary

This is a 3-page announcement (full proofs in a subsequent article). Anderson constructs Brownian motion and Ito integration using Loeb's technique.

## Setup

Let η be an infinite natural number (hypernatural).

- **Sample space**: Ω = {-1, 1}^η (internal coin flips)
- **Internal σ-algebra**: 𝔄 = {internal subsets of Ω}
- **Counting measure**: ν(A) = |A| / 2^η

By Loeb's results, the standard part of ν is countably additive, and by Caratheodory it extends uniquely to the σ-field L(𝔄). This gives the **Loeb space** (Ω, L(𝔄), L(ν)).

## Random Walk

```
χ(t, ω) = Σ_{k < [ηt]} ω_k/√η  +  (ηt - [ηt]) · ω_{[ηt]+1} / √η
```

The second term is a linear interpolation between integer times. Define β: [0,1] × Ω → R by:

```
β(t, ω) = °χ(t, ω)     (standard part)
```

## Main Theorem

**(i)** β is a normalized Brownian motion; hence Brownian motion exists.

**(ii)** For L(ν)-almost all ω, χ(·, ω) is near-standard in *C([0,1]) and β(·, ω) is continuous; hence Wiener measure exists.

**Anderson's claim**: "The proof of this theorem is quite easy compared to the standard proofs of existence and path continuity of Brownian motion."

## Ito Integration

Let f: [0,1] × Ω → R be Ito integrable (in the standard sense) w.r.t. β. Lift f to an internal step function g: *[0,1] × Ω → *R. Then:

**Theorem**: For t ∈ [0,1],
```
∫₀ᵗ f(τ,ω) dβ(τ,ω) = °∫₀ᵗ g(τ,ω) dχ(τ,ω)
```

For L(ν)-almost all ω, the "path" ∫₀ᵗ g(τ,ω) dχ(τ,ω), viewed as a function of t ∈ *[0,1], is near-standard in *C([0,1]); hence the "path" ∫₀ᵗ f(τ,ω) dβ(τ,ω), viewed as a function of t ∈ [0,1], is continuous.

## Ito's Lemma (Sketch)

The key insight: on the nonstandard time interval [i/η, (i+1)/η] with i ∈ *N:
- dt = 1/η
- (dχ)² = (±1/√η)² = 1/η = dt

So **(dβ)² = dt is an exact statement** in the nonstandard theory.

This immediately gives:
```
∫₀ᵗ β(τ,ω) dβ(τ,ω) = °Σ_{k=0}^{[ηt]-1} χ(k/η, ω) · ω_{k+1} · √η
```

A "simple formal manipulation of sums" reduces this to °(½(χ²(t,ω) - t)), hence:
```
∫₀ᵗ β(τ,ω) dβ(τ,ω) = ½(β²(t,ω) - t)
```

---

## Relevance to Our Formalization

### What the paper proves vs. what we need

Anderson's paper *announces* results but doesn't give full proofs. The key gap for us:

1. **Theorem (i)**: "β is normalized Brownian motion" — this means the finite-dimensional distributions are Gaussian. Anderson doesn't give the proof here. **This is exactly our `anderson_theorem_cylinder` sorry.** The proof requires showing that the hyperfinite binomial distribution converges to Gaussian (our local CLT chain).

2. **Theorem (ii)**: "L(ν)-almost all paths are near-standard in *C([0,1])" — this is our S-continuity result. **We have this proven** (`sContinuous_loebMeasureOne`).

3. **Ito integration**: The correspondence theorem and Ito's lemma. **Our sorrys #5-#8 in ItoCorrespondence.lean.**

### Key difference: our walk vs. Anderson's walk

Anderson uses **linear interpolation** between integer steps:
```
χ(t, ω) = Σ_{k<[ηt]} ω_k/√η + (ηt - [ηt]) · ω_{[ηt]+1}/√η
```

Our formalization uses **piecewise constant** (step at ⌊tN⌋):
```
walkValue(t) = dx * Σ_{k<⌊tN⌋} flip_k
```

This difference is **immaterial** for the standard part — both give the same β(t,ω) = °χ(t,ω) since the interpolation term is infinitesimal (it's at most 1/√η).

### What's NOT in the paper that we need

The paper doesn't detail:
- The local CLT proof (binomial → Gaussian convergence)
- The cylinder set probability argument
- The Riemann sum convergence step

These are the "standard" ingredients that Anderson considers routine but which require substantial formalization work. Our critical path sorrys #1-#3 are exactly this gap.

### The (dχ)² = dt insight

This is **already captured** in our formalization:
- `HyperfiniteStochasticIntegral.ito_isometry` proves Σ(H·ΔW)² = Σ H²·dt exactly
- `HyperfiniteWalk.increment_sq` proves (ΔW_k)² = dt

The nonstandard approach makes Ito's lemma "just Taylor expansion" because the quadratic variation identity is exact (not a limit). This is formalized but the sorry in `ito_lemma_hyperfinite` is about carrying through the Taylor remainder bound.
