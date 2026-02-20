/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.BrownianMotion

/-!
# Simple Process Definition

This file defines simple (step) processes and their stochastic integrals.
It is extracted from `StochasticIntegration.lean` to break import cycles:
helper files that prove properties of simple process integrals
(e.g., the martingale property) need to import this file but not the
full `StochasticIntegration.lean`.

## Main Definitions

* `SimpleProcess` — A simple (step) process defined by a finite partition
* `SimpleProcess.stochasticIntegral` — The stochastic integral Σ Hᵢ ΔWᵢ
* `SimpleProcess.stochasticIntegral_at` — Time-parameterized stochastic integral

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Simple Processes -/

/-- A simple (step) process defined by a finite partition -/
structure SimpleProcess (F : Filtration Ω ℝ) where
  /-- Number of partition points -/
  n : ℕ
  /-- The partition times (as a function) -/
  times : Fin n → ℝ
  /-- The values at each interval -/
  values : Fin n → Ω → ℝ
  /-- Partition is increasing -/
  increasing : ∀ i j : Fin n, i < j → times i < times j
  /-- Values are measurable random variables.
      The stronger predictability condition (F_{t_{i-1}}-measurability) and
      BM-adaptedness are passed as explicit hypotheses in the integration theorems. -/
  adapted : ∀ i : Fin n, Measurable (values i)

namespace SimpleProcess

variable {F : Filtration Ω ℝ}

/-- The stochastic integral of a simple process w.r.t. Brownian motion -/
noncomputable def stochasticIntegral (H : SimpleProcess F) (W : BrownianMotion Ω μ) : Ω → ℝ :=
  fun ω =>
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      H.values i ω * (W.process (H.times ⟨i + 1, h⟩) ω - W.process (H.times i) ω)
    else 0

/-- The time-parameterized stochastic integral of a simple process.
    At time t, this includes:
    - Full summands Hᵢ · (W_{t_{i+1}} - W_{t_i}) for completed intervals [t_i, t_{i+1}] ⊂ [0, t]
    - Partial summand H_k · (W_t - W_{t_k}) for the interval containing t

    When t is past the last partition time, this equals `stochasticIntegral`.
    This is needed for the martingale property and L² limit characterization. -/
noncomputable def stochasticIntegral_at (H : SimpleProcess F) (W : BrownianMotion Ω μ)
    (t : ℝ) : Ω → ℝ :=
  fun ω =>
    ∑ i : Fin H.n, if h : (i : ℕ) + 1 < H.n then
      if H.times ⟨i + 1, h⟩ ≤ t then
        H.values i ω * (W.process (H.times ⟨i + 1, h⟩) ω - W.process (H.times i) ω)
      else if H.times i ≤ t then
        H.values i ω * (W.process t ω - W.process (H.times i) ω)
      else 0
    else 0

end SimpleProcess

end SPDE
