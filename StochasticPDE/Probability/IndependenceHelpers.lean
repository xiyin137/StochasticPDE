/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Basic
import StochasticPDE.Probability.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Independence Bridge Lemmas

This file provides lemmas bridging between σ-algebra independence (`Indep`) and
random variable independence (`IndepFun`), which is needed to connect Brownian motion's
`independent_increments` property to Mathlib's integral factorization lemmas.

## Main Results

* `indepFun_of_measurable_and_indep` - If X is m₁-measurable and Indep m₁ σ(Y),
  then IndepFun X Y
* `indepFun_of_earlier_adapted` - If X is F_s-measurable and ΔW is independent of F_t
  for s ≤ t, then IndepFun X ΔW
* `measurable_mul_of_measurable` - Product of m-measurable functions is m-measurable

## Application

These are the key lemmas for proving the Itô isometry: they allow us to conclude
that E[Hᵢ·ΔWᵢ · ΔWⱼ] = E[Hᵢ·ΔWᵢ] · E[ΔWⱼ] when i < j, using the fact that
Hᵢ·ΔWᵢ is adapted (hence F_{t_j}-measurable) while ΔWⱼ is independent of F_{t_j}.

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Chapter 3
-/

namespace SPDE.Probability

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-! ## From σ-algebra independence to random variable independence -/

/-- If X is m₁-measurable and m₁ is independent of comap(Y), then IndepFun X Y.

This is the fundamental bridge lemma. The proof uses:
1. `comap_le_of_measurable'`: X is m₁-measurable → comap X ≤ m₁
2. `indep_of_indep_of_le_left`: Indep m₁ m₂ and m₃ ≤ m₁ → Indep m₃ m₂
3. `IndepFun_iff_Indep`: IndepFun X Y ↔ Indep (comap X) (comap Y) -/
theorem indepFun_of_measurable_and_indep
    {m₁ : MeasurableSpace Ω}
    {X Y : Ω → ℝ}
    (hX : @Measurable Ω ℝ m₁ _ X)
    (hindep : @Indep Ω m₁ (MeasurableSpace.comap Y inferInstance) m₀ μ) :
    IndepFun X Y μ := by
  rw [IndepFun_iff_Indep]
  -- Need: Indep (comap X) (comap Y)
  -- We have: Indep m₁ (comap Y)
  -- And: comap X ≤ m₁ (since X is m₁-measurable)
  have hle : MeasurableSpace.comap X inferInstance ≤ m₁ := by
    exact MeasurableSpace.comap_le_iff_le_map.mpr (fun _ hs => hX hs)
  exact indep_of_indep_of_le_left hindep hle

/-- If X is F_s-measurable and ΔW is independent of F_t with s ≤ t,
    then IndepFun X ΔW.

    This combines filtration monotonicity with the bridge lemma above. -/
theorem indepFun_of_earlier_adapted
    {F : SPDE.Filtration Ω ℝ}
    {X ΔW : Ω → ℝ} {s t : ℝ}
    (hX : @Measurable Ω ℝ (F.σ_algebra s) _ X)
    (hst : s ≤ t)
    (hindep : @Indep Ω (F.σ_algebra t)
              (MeasurableSpace.comap ΔW inferInstance) m₀ μ) :
    IndepFun X ΔW μ := by
  -- X is F_s-measurable, and F_s ≤ F_t, so X is F_t-measurable
  have hX_t : @Measurable Ω ℝ (F.σ_algebra t) _ X :=
    hX.mono (F.mono s t hst) le_rfl
  exact indepFun_of_measurable_and_indep hX_t hindep

/-- Product of m-measurable ℝ-valued functions is m-measurable.
    This is needed to show that Hᵢ·ΔWᵢ·Hⱼ is F_{t_j}-measurable. -/
theorem measurable_mul_of_measurable
    {m : MeasurableSpace Ω}
    {f g : Ω → ℝ}
    (hf : @Measurable Ω ℝ m _ f) (hg : @Measurable Ω ℝ m _ g) :
    @Measurable Ω ℝ m _ (fun ω => f ω * g ω) :=
  hf.mul hg

/-- Subtraction of m-measurable ℝ-valued functions is m-measurable. -/
theorem measurable_sub_of_measurable
    {m : MeasurableSpace Ω}
    {f g : Ω → ℝ}
    (hf : @Measurable Ω ℝ m _ f) (hg : @Measurable Ω ℝ m _ g) :
    @Measurable Ω ℝ m _ (fun ω => f ω - g ω) :=
  hf.sub hg

/-- Square of an m-measurable function is m-measurable. -/
theorem measurable_sq_of_measurable
    {m : MeasurableSpace Ω}
    {f : Ω → ℝ}
    (hf : @Measurable Ω ℝ m _ f) :
    @Measurable Ω ℝ m _ (fun ω => (f ω)^2) :=
  hf.pow_const 2

/-! ## Integral factorization via independence -/

/-- Key factorization: if X is m₁-measurable, Y generates comap Y, and Indep m₁ σ(Y),
    then E[X·Y] = E[X] · E[Y].

    This combines the bridge lemma with Mathlib's `IndepFun.integral_mul_eq_mul_integral`. -/
theorem integral_mul_of_indep_sigma_algebra
    {m₁ : MeasurableSpace Ω}
    (_hm₁ : m₁ ≤ m₀)
    {X Y : Ω → ℝ}
    (hX_meas : @Measurable Ω ℝ m₁ _ X)
    (hX_int : Integrable X μ)
    (hY_int : Integrable Y μ)
    (hindep : @Indep Ω m₁ (MeasurableSpace.comap Y inferInstance) m₀ μ)
    [IsProbabilityMeasure μ] :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) := by
  have hIndepFun : IndepFun X Y μ := indepFun_of_measurable_and_indep hX_meas hindep
  exact hIndepFun.integral_mul_eq_mul_integral
    hX_int.aestronglyMeasurable hY_int.aestronglyMeasurable

/-- Corollary: if X is m₁-measurable, E[Y] = 0, and Indep m₁ σ(Y),
    then E[X·Y] = 0.

    This is the key lemma for cross-term vanishing in the Itô isometry. -/
theorem integral_mul_zero_of_indep_zero_mean
    {m₁ : MeasurableSpace Ω}
    (hm₁ : m₁ ≤ m₀)
    {X Y : Ω → ℝ}
    (hX_meas : @Measurable Ω ℝ m₁ _ X)
    (hX_int : Integrable X μ)
    (hY_int : Integrable Y μ)
    (hindep : @Indep Ω m₁ (MeasurableSpace.comap Y inferInstance) m₀ μ)
    (hY_mean : ∫ ω, Y ω ∂μ = 0)
    [IsProbabilityMeasure μ] :
    ∫ ω, X ω * Y ω ∂μ = 0 := by
  rw [integral_mul_of_indep_sigma_algebra hm₁ hX_meas hX_int hY_int hindep, hY_mean, mul_zero]

/-! ## Adapted process measurability helpers -/

/-- If a process is adapted to F, then its value at time t is
    measurable w.r.t. the ambient σ-algebra. -/
theorem adapted_measurable_ambient
    {F : SPDE.Filtration Ω ℝ}
    {X : SPDE.AdaptedProcess F ℝ} (t : ℝ) :
    Measurable (X.process t) :=
  (X.adapted t).mono (F.le_ambient t) le_rfl

/-- An F_s-measurable function is also F_t-measurable for s ≤ t. -/
theorem measurable_of_le
    {F : SPDE.Filtration Ω ℝ}
    {f : Ω → ℝ} {s t : ℝ}
    (hf : @Measurable Ω ℝ (F.σ_algebra s) _ f)
    (hst : s ≤ t) :
    @Measurable Ω ℝ (F.σ_algebra t) _ f :=
  hf.mono (F.mono s t hst) le_rfl

end SPDE.Probability
