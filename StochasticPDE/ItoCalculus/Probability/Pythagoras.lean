/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# L² Pythagorean Theorem

The L² Pythagorean theorem: if E[aᵢ·aⱼ] = 0 for i ≠ j (orthogonality),
then E[(Σ aᵢ)²] = Σ E[aᵢ²].

This is the algebraic core of the Itô isometry.

## Main Results

* `sum_sq_integral_eq_sum_integral_sq` — L² Pythagoras for finite sums
-/

open MeasureTheory Finset

namespace SPDE.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- L² Pythagoras: if E[aᵢ·aⱼ] = 0 for i ≠ j, then E[(Σ aᵢ)²] = Σ E[aᵢ²].

    Proof: expand (Σ aᵢ)² = Σᵢ Σⱼ aᵢ·aⱼ, pull integral inside double sum,
    then extract diagonal (off-diagonal terms vanish by orthogonality). -/
theorem sum_sq_integral_eq_sum_integral_sq {n : ℕ}
    (a : Fin n → Ω → ℝ)
    (h_cross_int : ∀ i j : Fin n, Integrable (fun ω => a i ω * a j ω) μ)
    (h_orthog : ∀ i j : Fin n, i ≠ j → ∫ ω, a i ω * a j ω ∂μ = 0) :
    ∫ ω, (∑ i : Fin n, a i ω) ^ 2 ∂μ =
    ∑ i : Fin n, ∫ ω, (a i ω) ^ 2 ∂μ := by
  -- Step 1: (Σ aᵢ)² = Σᵢ Σⱼ aᵢ·aⱼ
  have hexpand : ∀ ω, (∑ i : Fin n, a i ω) ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, a i ω * a j ω := by
    intro ω; simp [sq, sum_mul_sum]
  simp_rw [hexpand]
  -- Step 2: Pull integral inside the double sum
  have h_inner_int : ∀ i : Fin n,
      Integrable (fun ω => ∑ j : Fin n, a i ω * a j ω) μ :=
    fun i => integrable_finset_sum _ (fun j _ => h_cross_int i j)
  rw [integral_finset_sum _ (fun i _ => h_inner_int i)]
  simp_rw [integral_finset_sum _ (fun j _ => h_cross_int _ j)]
  -- Step 3: Extract diagonal, zero out cross terms
  congr 1; ext i
  rw [← add_sum_erase _ _ (mem_univ i)]
  have hoff : ∑ j ∈ univ.erase i, ∫ ω, a i ω * a j ω ∂μ = 0 :=
    sum_eq_zero (fun j hj => h_orthog i j (ne_of_mem_erase hj).symm)
  rw [hoff, add_zero]
  congr 1; ext ω; ring

end SPDE.Probability
