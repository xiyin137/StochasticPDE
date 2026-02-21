/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.SIContinuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Ito Process Path Continuity

Under bounded diffusion, the Ito process X_t = X_0 + ∫₀ᵗ μ ds + ∫₀ᵗ σ dW has a
continuous modification on any compact interval [0, T].

## Strategy

1. The drift integral t ↦ ∫₀ᵗ μ(s,ω) ds is continuous in t (from `drift_time_integrable`)
2. The stochastic integral has a continuous modification (from `SIContinuity.lean`)
3. Define X'_t = X_0 + drift_integral + SI'_t and show it's a continuous modification of X

## Main Results

* `drift_integral_continuousOn` — the drift integral is continuous on [0,T]
* `ito_process_continuous_modification` — X has a continuous modification on [0,T]

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Theorem 2.2.8
-/

namespace SPDE

open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Drift integral continuity -/

/-- The drift integral ∫₀ᵗ μ(s,ω) ds is continuous on [0,T] for each ω.
    This uses Mathlib's `continuousOn_primitive_Icc` applied to the
    pathwise integrability from `drift_time_integrable`. -/
theorem drift_integral_continuousOn {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (ω : Ω)
    (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ s in Icc 0 t, X.drift s ω ∂volume) (Icc 0 T) := by
  exact intervalIntegral.continuousOn_primitive_Icc (X.drift_time_integrable ω T hT)

/-! ## Main theorem -/

/-- Under bounded diffusion, the Ito process has a continuous modification on [0, T].
    The modification is constructed as X'_t = X_0 + ∫₀ᵗ μ ds + SI'_t where SI' is
    the continuous modification of the stochastic integral from Kolmogorov-Chentsov. -/
theorem ito_process_continuous_modification {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcess F μ)
    {Mσ : ℝ} (hMσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ)
    (T : ℝ) (hT : 0 < T) :
    ∃ X' : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => X' t ω) (Icc 0 T)) ∧
      (∀ t, t ∈ Icc 0 T → ∀ᵐ ω ∂μ, X' t ω = X.process t ω) := by
  -- Get continuous modification of SI from Kolmogorov-Chentsov
  obtain ⟨SI', hSI_cont, hSI_mod⟩ := stoch_integral_continuous_modification X hMσ T hT
  -- Construct X'_t(ω) = X_0(ω) + ∫₀ᵗ μ(s,ω) ds + SI'_t(ω)
  refine ⟨fun t ω => X.process 0 ω +
    (∫ s in Icc 0 t, X.drift s ω ∂volume) + SI' t ω, ?_, ?_⟩
  · -- Continuity: constant + continuous drift integral + continuous SI'
    filter_upwards [hSI_cont] with ω hSI_cont_ω
    have hdrift_cont := drift_integral_continuousOn X ω T hT.le
    exact (continuousOn_const.add hdrift_cont).add hSI_cont_ω
  · -- Modification: X'_t =ᵃᵉ X_t via integral_form and SI' =ᵃᵉ SI
    intro t ht
    filter_upwards [hSI_mod t ht, X.integral_form t ht.1] with ω hSI hform
    -- hSI : SI' t ω = X.stoch_integral t ω
    -- hform : X.process t ω = X.process 0 ω + drift_int + X.stoch_integral t ω
    linarith

end SPDE
