/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Grönwall's Inequality for SDE Uniqueness

This file provides an integral version of Grönwall's inequality suitable for
proving uniqueness of SDE solutions:

If φ : ℝ → ℝ is continuous, nonneg, φ(0) = 0, and
  φ(t) ≤ C * ∫₀ᵗ φ(s) ds for all t ∈ [0, T],
then φ ≡ 0 on [0, T].

The proof uses Mathlib's ODE Gronwall inequality applied to the antiderivative
F(t) = ∫₀ᵗ φ(s) ds, which satisfies F'(t) = φ(t) ≤ C * F(t), F(0) = 0.

## Main Results

* `integral_gronwall_zero` — The zero-initial Grönwall vanishing result
* `ae_eq_zero_of_integral_sq_zero` — If E[f²] = 0 then f = 0 a.e.
-/

open MeasureTheory Set Filter Topology intervalIntegral

/-- Nonneg continuous function with integral bound φ(t) ≤ C ∫₀ᵗ φ ds vanishes.

    Uses the ODE Gronwall inequality on F(t) = ∫₀ᵗ f(s)ds. -/
theorem integral_gronwall_zero {f : ℝ → ℝ} {C T : ℝ}
    (hf_cont : ContinuousOn f (Icc 0 T))
    (hf_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (_hf0 : f 0 = 0)
    (hT : 0 ≤ T)
    (_hC : 0 ≤ C)
    (h_bound : ∀ t ∈ Icc 0 T,
      f t ≤ C * ∫ s in Icc 0 t, f s ∂volume) :
    ∀ t ∈ Icc 0 T, f t = 0 := by
  -- Define F(t) = ∫ u in 0..t, f u (interval integral)
  set F : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, f u with hF_def
  -- f is interval integrable on [0, T]
  have hf_integ : IntervalIntegrable f volume 0 T :=
    hf_cont.intervalIntegrable_of_Icc hT
  -- F is continuous on [0, T]
  have hF_cont : ContinuousOn F (Icc 0 T) := by
    have := continuousOn_primitive_interval' hf_integ left_mem_uIcc
    rwa [uIcc_of_le hT] at this
  -- F(0) = 0
  have hF_zero : F 0 = 0 := integral_same
  -- Relate set integral and interval integral: ∫ in Icc = ∫ in a..b
  have hF_eq_set : ∀ x ∈ Icc 0 T, F x = ∫ s in Icc 0 x, f s ∂volume := by
    intro x ⟨hx0, hxT⟩
    simp only [hF_def]
    rw [integral_Icc_eq_integral_Ioc, ← integral_of_le hx0]
  -- F is nonneg on [0, T] (since f ≥ 0)
  have hF_nonneg : ∀ x ∈ Icc 0 T, 0 ≤ F x := by
    intro x hx
    rw [hF_eq_set x hx]
    exact setIntegral_nonneg measurableSet_Icc
      fun s hs => hf_nonneg s ⟨hs.1, le_trans hs.2 hx.2⟩
  -- F has right derivative f(x) at each x ∈ [0, T)
  have hF_deriv : ∀ x ∈ Ico 0 T, HasDerivWithinAt F (f x) (Ici x) x := by
    intro x ⟨hx0, hxT⟩
    have hf_int_x : IntervalIntegrable f volume 0 x :=
      (hf_cont.mono (Icc_subset_Icc_right (le_of_lt hxT))).intervalIntegrable_of_Icc hx0
    have h_mem : Icc 0 T ∈ 𝓝[>] x :=
      mem_of_superset (Icc_mem_nhdsGT hxT) (Icc_subset_Icc hx0 le_rfl)
    exact integral_hasDerivWithinAt_right hf_int_x
      ⟨Icc 0 T, h_mem, hf_cont.aestronglyMeasurable measurableSet_Icc⟩
      ((hf_cont x ⟨hx0, le_of_lt hxT⟩).mono_of_mem_nhdsWithin h_mem)
  -- ‖f(x)‖ ≤ C * ‖F(x)‖ for x ∈ [0, T)
  have hF_bound : ∀ x ∈ Ico 0 T, ‖f x‖ ≤ C * ‖F x‖ := by
    intro x hx
    have hx' : x ∈ Icc 0 T := Ico_subset_Icc_self hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x hx'),
        Real.norm_eq_abs, abs_of_nonneg (hF_nonneg x hx')]
    calc f x ≤ C * ∫ s in Icc 0 x, f s ∂volume := h_bound x hx'
      _ = C * F x := by rw [hF_eq_set x hx']
  -- Apply Gronwall: F ≡ 0 on [0, T]
  have hF_eq_zero : ∀ x ∈ Icc 0 T, F x = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hF_cont hF_deriv hF_zero hF_bound
  -- Conclude: f(t) = 0
  intro t ht
  have h1 : f t ≤ 0 := by
    calc f t ≤ C * ∫ s in Icc 0 t, f s ∂volume := h_bound t ht
      _ = C * F t := by rw [hF_eq_set t ht]
      _ = C * 0 := by rw [hF_eq_zero t ht]
      _ = 0 := by ring
  linarith [hf_nonneg t ht]

/-- If ∫ f² dμ = 0 and f is AEStronglyMeasurable, then f = 0 a.e. -/
theorem ae_eq_zero_of_integral_sq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ}
    (_hf : AEStronglyMeasurable f μ)
    (h_sq_int : Integrable (fun ω => (f ω)^2) μ)
    (h_zero : ∫ ω, (f ω)^2 ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  -- ∫ f² = 0 with f² ≥ 0 implies f² = 0 a.e., hence f = 0 a.e.
  have h_nonneg : 0 ≤ᵐ[μ] fun ω => (f ω) ^ 2 :=
    Eventually.of_forall (fun ω => sq_nonneg (f ω))
  have h_sq_zero : (fun ω => (f ω)^2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_sq_int).mp h_zero
  filter_upwards [h_sq_zero] with ω hω
  exact_mod_cast sq_eq_zero_iff.mp hω
