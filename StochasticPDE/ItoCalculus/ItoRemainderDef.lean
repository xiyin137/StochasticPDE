/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.ItoProcessCore

/-!
# Itô Remainder Definition

The Itô formula remainder `itoRemainder` is the stochastic integral part of the
Itô decomposition:

  M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds

This file contains only the definition, factored out so that both
`RemainderIntegrability.lean` and `ItoFormulaProof.lean` can use it
without circular imports.
-/

namespace SPDE

open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Itô formula remainder (stochastic integral part):
    M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds

    Core version using `ItoProcessCore`. -/
noncomputable def itoRemainderCore {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) (f : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  f t (X.process t ω) - f 0 (X.process 0 ω) -
  ∫ s in Set.Icc 0 t,
    (deriv (fun u => f u (X.process s ω)) s +
     deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
     (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2) ∂volume

/-- The Itô formula remainder (stochastic integral part):
    M_t = f(t, X_t) - f(0, X_0) - ∫₀ᵗ [∂_t f + ∂_x f · μ + ½∂²_x f · σ²] ds

    This is the process that the Itô formula asserts is a martingale. -/
noncomputable def itoRemainder {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  f t (X.process t ω) - f 0 (X.process 0 ω) -
  ∫ s in Set.Icc 0 t,
    (deriv (fun u => f u (X.process s ω)) s +
     deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
     (1/2) * deriv (deriv (fun x => f s x)) (X.process s ω) * (X.diffusion s ω)^2) ∂volume

@[simp] theorem itoRemainder_eq_core {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) (f : ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) :
    itoRemainder X f t ω = itoRemainderCore X.toCore f t ω := rfl

end SPDE
