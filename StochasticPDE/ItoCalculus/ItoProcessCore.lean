/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.StochasticIntegration

/-!
# Ito Process Core/Regularity Split

This module introduces a lightweight core definition for Itô processes and a
separate regularity package. It is an adapter layer for incremental refactoring:

- `ItoProcessCore`: minimal dynamics/decomposition data
- `ItoProcessRegularity`: analytic and construction hypotheses currently used by proofs
- `ItoProcess.toCore` / `ItoProcess.toRegularity`: forget/projection maps
- `ItoProcessCore.toItoProcess`: reconstruction to legacy `ItoProcess`

The goal is to decouple heavy assumptions from the core object without changing
the existing Itô formula proof chain.
-/

namespace SPDE

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Minimal core data for an Itô process: dynamics and decomposition only. -/
structure ItoProcessCore (F : Filtration Ω ℝ) (μ : Measure Ω) where
  process : ℝ → Ω → ℝ
  drift : ℝ → Ω → ℝ
  diffusion : ℝ → Ω → ℝ
  BM : BrownianMotion Ω μ
  stoch_integral : ℝ → Ω → ℝ
  integral_form : ∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
    process t ω = process 0 ω +
      (∫ (s : ℝ) in Set.Icc 0 t, drift s ω ∂volume) +
      stoch_integral t ω
  process_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (process t)

/-- Regularity and construction package used by the current Itô formula infrastructure. -/
structure ItoProcessRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) where
  stoch_integral_is_L2_limit : ∃ (approx : ℕ → SimpleProcess F),
    (∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (F.σ_algebra ((approx n).times i)) _ ((approx n).values i)) ∧
    (∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C) ∧
    (∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
                                     X.stoch_integral t ω)^2 ∂μ)
      Filter.atTop (nhds 0)) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto
      (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω)^2 ∂μ)
      Filter.atTop
      (nhds (∫ ω, (∫ (s : ℝ) in Set.Icc 0 t, (X.diffusion s ω)^2 ∂volume) ∂μ))) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto
      (fun n => ∫ ω, (∫ s in Set.Icc 0 t,
        (SimpleProcess.valueAtTime (approx n) s ω - X.diffusion s ω) ^ 2 ∂volume) ∂μ)
      Filter.atTop (nhds 0)) ∧
    (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n =>
        SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω)
        Filter.atTop (nhds (X.stoch_integral t ω)))
  process_continuous : ∀ᵐ ω ∂μ, Continuous (fun t => X.process t ω)
  drift_time_integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntegrableOn (fun s => X.drift s ω) (Set.Icc 0 t) volume
  drift_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (X.drift t)
  drift_jointly_measurable : Measurable (Function.uncurry X.drift)
  diffusion_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t)
  diffusion_jointly_measurable : Measurable (Function.uncurry X.diffusion)
  diffusion_sq_time_integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntegrableOn (fun s => (X.diffusion s ω)^2) (Set.Icc 0 t) volume
  diffusion_sq_integral_integrable : ∀ (t : ℝ), 0 ≤ t →
    Integrable (fun ω => ∫ s in Set.Icc 0 t, (X.diffusion s ω)^2 ∂volume) μ
  F_le_BM_F : ∀ t, F.σ_algebra t ≤ X.BM.F.σ_algebra t
  BM_adapted_to_F : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (X.BM.process t)
  usual_conditions : F.usualConditions μ

/-- Construction hypotheses for Itô processes on top of core data. -/
structure ItoProcessConstruction {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) where
  stoch_integral_is_L2_limit : ∃ (approx : ℕ → SimpleProcess F),
    (∀ n, ∀ i : Fin (approx n).n,
      @Measurable Ω ℝ (F.σ_algebra ((approx n).times i)) _ ((approx n).values i)) ∧
    (∀ n, ∀ i : Fin (approx n).n, ∃ C : ℝ, ∀ ω, |(approx n).values i ω| ≤ C) ∧
    (∀ n, ∀ i : Fin (approx n).n, 0 ≤ (approx n).times i) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω -
                                     X.stoch_integral t ω)^2 ∂μ)
      Filter.atTop (nhds 0)) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto
      (fun n => ∫ ω, (SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω)^2 ∂μ)
      Filter.atTop
      (nhds (∫ ω, (∫ (s : ℝ) in Set.Icc 0 t, (X.diffusion s ω)^2 ∂volume) ∂μ))) ∧
    (∀ t : ℝ, t ≥ 0 →
    Filter.Tendsto
      (fun n => ∫ ω, (∫ s in Set.Icc 0 t,
        (SimpleProcess.valueAtTime (approx n) s ω - X.diffusion s ω) ^ 2 ∂volume) ∂μ)
      Filter.atTop (nhds 0)) ∧
    (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n =>
        SimpleProcess.stochasticIntegral_at (approx n) X.BM t ω)
        Filter.atTop (nhds (X.stoch_integral t ω)))
  process_continuous : ∀ᵐ ω ∂μ, Continuous (fun t => X.process t ω)

/-- Drift regularity hypotheses for Itô processes on top of core data. -/
structure ItoProcessDriftRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) where
  drift_time_integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntegrableOn (fun s => X.drift s ω) (Set.Icc 0 t) volume
  drift_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (X.drift t)
  drift_jointly_measurable : Measurable (Function.uncurry X.drift)

/-- Diffusion regularity hypotheses for Itô processes on top of core data. -/
structure ItoProcessDiffusionRegularity {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) where
  diffusion_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (X.diffusion t)
  diffusion_jointly_measurable : Measurable (Function.uncurry X.diffusion)
  diffusion_sq_time_integrable : ∀ ω (t : ℝ), 0 ≤ t →
    IntegrableOn (fun s => (X.diffusion s ω)^2) (Set.Icc 0 t) volume
  diffusion_sq_integral_integrable : ∀ (t : ℝ), 0 ≤ t →
    Integrable (fun ω => ∫ s in Set.Icc 0 t, (X.diffusion s ω)^2 ∂volume) μ

/-- Joint measurability of Itô coefficients on top of core data. -/
structure ItoProcessCoefficientJointMeasurability {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) where
  drift_jointly_measurable : Measurable (Function.uncurry X.drift)
  diffusion_jointly_measurable : Measurable (Function.uncurry X.diffusion)

/-- Filtration compatibility hypotheses for Itô processes on top of core data. -/
structure ItoProcessFiltrationCompatibility {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) where
  F_le_BM_F : ∀ t, F.σ_algebra t ≤ X.BM.F.σ_algebra t
  BM_adapted_to_F : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (X.BM.process t)
  usual_conditions : F.usualConditions μ

namespace ItoProcessCoefficientJointMeasurability

/-- Build coefficient joint measurability directly from drift/diffusion
    regularity bundles. -/
def ofDriftDiffusion {F : Filtration Ω ℝ}
    {X : ItoProcessCore F μ}
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X) :
    ItoProcessCoefficientJointMeasurability X where
  drift_jointly_measurable := DR.drift_jointly_measurable
  diffusion_jointly_measurable := D.diffusion_jointly_measurable

end ItoProcessCoefficientJointMeasurability

namespace ItoProcess

/-- Forget heavy regularity fields. -/
def toCore {F : Filtration Ω ℝ} (X : ItoProcess F μ) : ItoProcessCore F μ where
  process := X.process
  drift := X.drift
  diffusion := X.diffusion
  BM := X.BM
  stoch_integral := X.stoch_integral
  integral_form := X.integral_form
  process_adapted := X.process_adapted

/-- Extract the heavy regularity package. -/
def toRegularity {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) : ItoProcessRegularity X.toCore where
  stoch_integral_is_L2_limit := X.stoch_integral_is_L2_limit
  process_continuous := X.process_continuous
  drift_time_integrable := X.drift_time_integrable
  drift_adapted := X.drift_adapted
  drift_jointly_measurable := X.drift_jointly_measurable
  diffusion_adapted := X.diffusion_adapted
  diffusion_jointly_measurable := X.diffusion_jointly_measurable
  diffusion_sq_time_integrable := X.diffusion_sq_time_integrable
  diffusion_sq_integral_integrable := X.diffusion_sq_integral_integrable
  F_le_BM_F := X.F_le_BM_F
  BM_adapted_to_F := X.BM_adapted_to_F
  usual_conditions := X.usual_conditions

end ItoProcess

namespace ItoProcessRegularity

/-- Project to construction assumptions. -/
def toConstruction {F : Filtration Ω ℝ}
    {X : ItoProcessCore F μ}
    (R : ItoProcessRegularity X) : ItoProcessConstruction X where
  stoch_integral_is_L2_limit := R.stoch_integral_is_L2_limit
  process_continuous := R.process_continuous

/-- Project to drift regularity assumptions. -/
def toDriftRegularity {F : Filtration Ω ℝ}
    {X : ItoProcessCore F μ}
    (R : ItoProcessRegularity X) : ItoProcessDriftRegularity X where
  drift_time_integrable := R.drift_time_integrable
  drift_adapted := R.drift_adapted
  drift_jointly_measurable := R.drift_jointly_measurable

/-- Project to diffusion regularity assumptions. -/
def toDiffusionRegularity {F : Filtration Ω ℝ}
    {X : ItoProcessCore F μ}
    (R : ItoProcessRegularity X) : ItoProcessDiffusionRegularity X where
  diffusion_adapted := R.diffusion_adapted
  diffusion_jointly_measurable := R.diffusion_jointly_measurable
  diffusion_sq_time_integrable := R.diffusion_sq_time_integrable
  diffusion_sq_integral_integrable := R.diffusion_sq_integral_integrable

/-- Project to coefficient joint measurability assumptions. -/
def toCoefficientJointMeasurability {F : Filtration Ω ℝ}
    {X : ItoProcessCore F μ}
    (R : ItoProcessRegularity X) : ItoProcessCoefficientJointMeasurability X where
  drift_jointly_measurable := R.drift_jointly_measurable
  diffusion_jointly_measurable := R.diffusion_jointly_measurable

/-- Project to filtration compatibility assumptions. -/
def toFiltrationCompatibility {F : Filtration Ω ℝ}
    {X : ItoProcessCore F μ}
    (R : ItoProcessRegularity X) : ItoProcessFiltrationCompatibility X where
  F_le_BM_F := R.F_le_BM_F
  BM_adapted_to_F := R.BM_adapted_to_F
  usual_conditions := R.usual_conditions

/-- Assemble the full regularity package from split assumptions. -/
def ofSplit {F : Filtration Ω ℝ}
    {X : ItoProcessCore F μ}
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X) :
    ItoProcessRegularity X where
  stoch_integral_is_L2_limit := C.stoch_integral_is_L2_limit
  process_continuous := C.process_continuous
  drift_time_integrable := DR.drift_time_integrable
  drift_adapted := DR.drift_adapted
  drift_jointly_measurable := DR.drift_jointly_measurable
  diffusion_adapted := D.diffusion_adapted
  diffusion_jointly_measurable := D.diffusion_jointly_measurable
  diffusion_sq_time_integrable := D.diffusion_sq_time_integrable
  diffusion_sq_integral_integrable := D.diffusion_sq_integral_integrable
  F_le_BM_F := FC.F_le_BM_F
  BM_adapted_to_F := FC.BM_adapted_to_F
  usual_conditions := FC.usual_conditions

end ItoProcessRegularity

namespace ItoProcessCore

/-- Rebuild the legacy `ItoProcess` from `core + regularity`. -/
def toItoProcess {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) (R : ItoProcessRegularity X) : ItoProcess F μ where
  process := X.process
  drift := X.drift
  diffusion := X.diffusion
  BM := X.BM
  stoch_integral := X.stoch_integral
  stoch_integral_is_L2_limit := R.stoch_integral_is_L2_limit
  integral_form := X.integral_form
  process_adapted := X.process_adapted
  drift_time_integrable := R.drift_time_integrable
  drift_adapted := R.drift_adapted
  drift_jointly_measurable := R.drift_jointly_measurable
  diffusion_adapted := R.diffusion_adapted
  diffusion_jointly_measurable := R.diffusion_jointly_measurable
  diffusion_sq_time_integrable := R.diffusion_sq_time_integrable
  diffusion_sq_integral_integrable := R.diffusion_sq_integral_integrable
  F_le_BM_F := R.F_le_BM_F
  BM_adapted_to_F := R.BM_adapted_to_F
  usual_conditions := R.usual_conditions
  process_continuous := R.process_continuous

@[simp] theorem toCore_toItoProcess {F : Filtration Ω ℝ}
    (X : ItoProcessCore F μ) (R : ItoProcessRegularity X) :
    (X.toItoProcess R).toCore = X := by
  rfl

end ItoProcessCore

@[simp] theorem ItoProcess.toItoProcess_toCore {F : Filtration Ω ℝ}
    (X : ItoProcess F μ) :
    X.toCore.toItoProcess X.toRegularity = X := by
  cases X
  rfl

end SPDE
