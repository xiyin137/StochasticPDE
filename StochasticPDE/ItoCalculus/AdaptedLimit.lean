/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.Basic

/-!
# Adaptedness under Usual Conditions

Under the usual conditions (right-continuous + complete filtration), a function that is
a.e. equal to an F_t-measurable function is itself F_t-measurable. This is the key
result for upgrading AEMeasurable to Measurable in the filtration setting.

## Main Results

* `Filtration.measurable_of_ae_eq` — a.e. equal to F_t-measurable implies F_t-measurable
* `Filtration.adapted_modification` — a modification of an adapted process is adapted

## Application

When the Kolmogorov-Chentsov theorem produces a modification Y with Y(t) =ᵐ X(t),
if X is adapted and the filtration satisfies usual conditions, then Y is adapted.
-/

namespace SPDE

open MeasureTheory Filter Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace Filtration

/-- Under usual conditions, a function that is a.e. equal to an F_t-measurable function
    is itself F_t-measurable. This uses the completeness part of usual conditions:
    null sets are measurable at every level. -/
theorem measurable_of_ae_eq
    {F : Filtration Ω ℝ} (huc : F.usualConditions μ) {t : ℝ}
    {g g' : Ω → ℝ} (hg' : @Measurable Ω ℝ (F.σ_algebra t) _ g')
    (hae : g =ᵐ[μ] g') :
    @Measurable Ω ℝ (F.σ_algebra t) _ g := by
  -- N = {ω | g ω ≠ g' ω} has measure 0
  set N := {ω : Ω | g ω ≠ g' ω}
  have hN_null : μ N = 0 := ae_iff.mp hae
  -- Under usual conditions, N is F_t-measurable
  have hN_meas : @MeasurableSet Ω (F.σ_algebra t) N := huc.2 t N hN_null
  -- Show g is measurable: for every Borel set s, g⁻¹'(s) is F_t-measurable
  intro s hs
  -- Decompose: g⁻¹'(s) = (g⁻¹'(s) ∩ N) ∪ (g⁻¹'(s) ∩ Nᶜ)
  rw [← inter_union_compl (g ⁻¹' s) N]
  apply MeasurableSet.union
  · -- g⁻¹'(s) ∩ N ⊆ N has measure 0, hence F_t-measurable
    exact huc.2 t _ (measure_mono_null inter_subset_right hN_null)
  · -- On Nᶜ, g = g', so g⁻¹'(s) ∩ Nᶜ = g'⁻¹'(s) ∩ Nᶜ
    have h_eq : g ⁻¹' s ∩ Nᶜ = g' ⁻¹' s ∩ Nᶜ := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_setOf, N, ne_eq,
        not_not]
      exact and_congr_left fun h => by rw [h]
    rw [h_eq]
    exact (hg' hs).inter hN_meas.compl

/-- Under usual conditions, if X is adapted and Y(t) =ᵐ X(t) for all t,
    then Y is adapted. This is the key result for the Kolmogorov-Chentsov
    modification: the modification of an adapted process remains adapted. -/
theorem adapted_modification
    {F : Filtration Ω ℝ} (huc : F.usualConditions μ)
    {X Y : ℝ → Ω → ℝ}
    (hX_adapted : ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (X t))
    (hmod : ∀ t : ℝ, Y t =ᵐ[μ] X t) :
    ∀ t : ℝ, @Measurable Ω ℝ (F.σ_algebra t) _ (Y t) :=
  fun t => measurable_of_ae_eq huc (hX_adapted t) (hmod t)

end Filtration

end SPDE
