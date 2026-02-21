/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Moment-to-Tail Bounds

This file provides the p-th moment Markov inequality and its corollary for
the Kolmogorov-Chentsov theorem.

## Main Results

* `moment_markov_real` — ε^p * μ.real {|X| ≥ ε} ≤ E[|X|^p] (real measure version)
* `moment_tail_bound` — μ {|X| ≥ ε} ≤ ENNReal.ofReal (E[|X|^p] / ε^p)
* `moment_tail_bound_of_le` — tail bound given an upper bound on E[|X|^p]

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Lemma 2.2.7
-/

namespace KolmogorovChentsov

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Set equality: power monotonicity -/

omit [MeasurableSpace Ω] in
/-- For ε ≥ 0, the set {ε ≤ |X|} equals {ε^p ≤ |X|^p} (natural number power) -/
theorem setOf_le_abs_eq_setOf_le_pow {X : Ω → ℝ} {ε : ℝ} (hε : 0 ≤ ε) {p : ℕ} (hp : 0 < p) :
    {ω | ε ≤ |X ω|} = {ω | ε ^ p ≤ |X ω| ^ p} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h; exact pow_le_pow_left₀ hε h p
  · intro h; exact le_of_pow_le_pow_left₀ hp.ne' (abs_nonneg _) h

/-! ## Real-valued Markov inequality for p-th moments -/

/-- p-th moment Markov inequality (real measure version):
    ε^p * μ.real {|X| ≥ ε} ≤ E[|X|^p].
    This follows from the basic Markov inequality applied to f = |X|^p. -/
theorem moment_markov_real {p : ℕ} (hp : 0 < p)
    {X : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hint : Integrable (fun ω => |X ω| ^ p) μ) :
    ε ^ p * μ.real {ω | ε ≤ |X ω|} ≤ ∫ ω, |X ω| ^ p ∂μ := by
  rw [setOf_le_abs_eq_setOf_le_pow hε.le hp]
  exact mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (fun ω => pow_nonneg (abs_nonneg _) p)) hint (ε ^ p)

/-! ## ENNReal tail bound -/

/-- p-th moment Markov inequality (ENNReal version for finite measures):
    μ {|X| ≥ ε} ≤ ENNReal.ofReal (E[|X|^p] / ε^p).
    Requires finite measure (automatic for probability measures). -/
theorem moment_tail_bound [IsFiniteMeasure μ] {p : ℕ} (hp : 0 < p)
    {X : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hint : Integrable (fun ω => |X ω| ^ p) μ) :
    μ {ω | ε ≤ |X ω|} ≤ ENNReal.ofReal ((∫ ω, |X ω| ^ p ∂μ) / ε ^ p) := by
  have hep : 0 < ε ^ p := pow_pos hε p
  have h_fin : μ {ω | ε ≤ |X ω|} ≠ ⊤ := measure_ne_top μ _
  -- Real Markov bound
  have h_markov := moment_markov_real hp hε hint
  -- Divide by ε^p: μ.real S ≤ ∫ |X|^p / ε^p
  have h_div : (μ {ω | ε ≤ |X ω|}).toReal ≤ (∫ ω, |X ω| ^ p ∂μ) / ε ^ p := by
    rw [← Measure.real_def]
    rwa [le_div_iff₀ hep, mul_comm]
  -- Convert to ENNReal
  calc μ {ω | ε ≤ |X ω|}
      = ENNReal.ofReal ((μ {ω | ε ≤ |X ω|}).toReal) := (ENNReal.ofReal_toReal h_fin).symm
    _ ≤ ENNReal.ofReal ((∫ ω, |X ω| ^ p ∂μ) / ε ^ p) := ENNReal.ofReal_le_ofReal h_div

/-- Tail bound given an upper bound on the p-th moment:
    If E[|X|^p] ≤ C then μ {|X| ≥ ε} ≤ ENNReal.ofReal (C / ε^p). -/
theorem moment_tail_bound_of_le [IsFiniteMeasure μ] {p : ℕ} (hp : 0 < p)
    {X : Ω → ℝ} {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hint : Integrable (fun ω => |X ω| ^ p) μ)
    (hbound : (∫ ω, |X ω| ^ p ∂μ) ≤ C) :
    μ {ω | ε ≤ |X ω|} ≤ ENNReal.ofReal (C / ε ^ p) := by
  calc μ {ω | ε ≤ |X ω|}
      ≤ ENNReal.ofReal ((∫ ω, |X ω| ^ p ∂μ) / ε ^ p) := moment_tail_bound hp hε hint
    _ ≤ ENNReal.ofReal (C / ε ^ p) := by
        apply ENNReal.ofReal_le_ofReal
        exact div_le_div_of_nonneg_right hbound (pow_pos hε p).le

/-- Strict inequality version for Phase 3 (dyadic increments use strict inequality).
    μ {|X| > δ} ≤ μ {|X| ≥ δ} ≤ bound -/
theorem moment_tail_bound_strict [IsFiniteMeasure μ] {p : ℕ} (hp : 0 < p)
    {X : Ω → ℝ} {δ : ℝ} (hδ : 0 < δ) {C : ℝ}
    (hint : Integrable (fun ω => |X ω| ^ p) μ)
    (hbound : (∫ ω, |X ω| ^ p ∂μ) ≤ C) :
    μ {ω | δ < |X ω|} ≤ ENNReal.ofReal (C / δ ^ p) := by
  calc μ {ω | δ < |X ω|}
      ≤ μ {ω | δ ≤ |X ω|} := by
        apply measure_mono
        intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; exact le_of_lt hω
    _ ≤ ENNReal.ofReal (C / δ ^ p) := moment_tail_bound_of_le hp hδ hint hbound

end KolmogorovChentsov
