/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# C² Taylor Remainder Bound

Bounds on the second-order Taylor remainder for C² functions,
used in the proof of the Itô formula.

## Main result

* `c2_taylor_remainder_bound` - For C² function g, the remainder
    R₂ = g(x+h) - g(x) - g'(x)h - ½g''(x)h² satisfies |R₂| ≤ C · h²
    where C bounds the oscillation of g'' near x.
-/

open Set

/-- Helper: if z ∈ uIcc x (x + h) then |z - x| ≤ |h|. -/
lemma abs_sub_le_of_mem_uIcc {x h z : ℝ} (hz : z ∈ uIcc x (x + h)) :
    |z - x| ≤ |h| := by
  rw [mem_uIcc] at hz
  rcases hz with ⟨hxz, hzxh⟩ | ⟨hxhz, hzx⟩
  · have h1 : 0 ≤ z - x := by linarith
    have h2 : z - x ≤ h := by linarith
    rw [abs_of_nonneg h1]
    exact le_trans h2 (le_abs_self h)
  · have h1 : z - x ≤ 0 := by linarith
    have h2 : -(z - x) ≤ -h := by linarith
    rw [abs_of_nonpos h1]
    exact le_trans h2 (neg_le_abs h)

/-! ## C² Taylor remainder bound -/

/-- For a C² function g, the second-order Taylor remainder is bounded by
    the oscillation of g'' times h². -/
theorem c2_taylor_remainder_bound {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (x h : ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hC_bound : ∀ y ∈ uIcc x (x + h),
      |deriv (deriv g) y - deriv (deriv g) x| ≤ C) :
    |g (x + h) - g x - deriv g x * h - (1/2) * deriv (deriv g) x * h ^ 2| ≤
    C * h ^ 2 := by
  by_cases hh : h = 0
  · simp [hh]
  -- C² gives differentiability
  have hg_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hg'_diff : Differentiable ℝ (deriv g) := by
    have h := (contDiff_succ_iff_deriv (n := 1)).mp hg
    exact h.2.2.differentiable (by norm_num)
  -- Useful: derivative of (y - x) is 1
  have h_yx : ∀ z : ℝ, HasDerivAt (fun y => y - x) 1 z := fun z => by
    have h := (hasDerivAt_id z).sub (hasDerivAt_const z x)
    rwa [sub_zero] at h
  -- Step 1: G(y) = g'(y) - g'(x) - g''(x)(y-x), G'(z) = g''(z) - g''(x)
  have hG_deriv : ∀ z ∈ uIcc x (x + h), HasDerivAt
      (fun y => deriv g y - deriv g x - deriv (deriv g) x * (y - x))
      (deriv (deriv g) z - deriv (deriv g) x) z := by
    intro z _
    have hd1 : HasDerivAt (fun y => deriv g y - deriv g x)
        (deriv (deriv g) z) z := by
      have h := (hg'_diff z).hasDerivAt.sub (hasDerivAt_const z (deriv g x))
      rwa [sub_zero] at h
    have hd2 : HasDerivAt (fun y => deriv (deriv g) x * (y - x))
        (deriv (deriv g) x) z := by
      have h := (hasDerivAt_const z (deriv (deriv g) x)).mul (h_yx z)
      simp only [zero_mul, zero_add, mul_one] at h
      exact h
    exact hd1.sub hd2
  -- MVT on G: |G(y)| ≤ C·|y-x|
  have hG_bound : ∀ y ∈ uIcc x (x + h),
      ‖(deriv g y - deriv g x) - deriv (deriv g) x * (y - x)‖ ≤ C * |y - x| := by
    intro y hy
    rw [show (deriv g y - deriv g x) - deriv (deriv g) x * (y - x) =
        (fun y => deriv g y - deriv g x - deriv (deriv g) x * (y - x)) y -
        (fun y => deriv g y - deriv g x - deriv (deriv g) x * (y - x)) x from by ring_nf]
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hG_deriv z hz).hasDerivWithinAt)
      (fun z hz => by rw [Real.norm_eq_abs]; exact hC_bound z hz)
      (show Convex ℝ (uIcc x (x + h)) from convex_uIcc x (x + h))
      (left_mem_uIcc) hy
    exact hmvt
  -- Step 2: F(y) = g(y) - g(x) - g'(x)(y-x) - ½g''(x)(y-x)²
  -- F'(z) = g'(z) - g'(x) - g''(x)(z-x) = G(z)
  have hF_deriv : ∀ z ∈ uIcc x (x + h), HasDerivAt
      (fun y => g y - g x - deriv g x * (y - x) - (1/2) * deriv (deriv g) x * (y - x) ^ 2)
      ((deriv g z - deriv g x) - deriv (deriv g) x * (z - x)) z := by
    intro z _
    have hd1 : HasDerivAt (fun y => g y - g x) (deriv g z) z := by
      have h := (hg_diff z).hasDerivAt.sub (hasDerivAt_const z (g x))
      rwa [sub_zero] at h
    have hd2 : HasDerivAt (fun y => deriv g x * (y - x)) (deriv g x) z := by
      have h := (hasDerivAt_const z (deriv g x)).mul (h_yx z)
      simp only [zero_mul, zero_add, mul_one] at h
      exact h
    -- (y-x)*(y-x) has derivative 2*(z-x) via product rule
    have hd_sq : HasDerivAt (fun y => (y - x) * (y - x)) (2 * (z - x)) z := by
      have h := (h_yx z).mul (h_yx z)
      have heq : 1 * (z - x) + (z - x) * 1 = 2 * (z - x) := by ring
      rwa [heq] at h
    -- ½g''(x)*(y-x)*(y-x) has derivative g''(x)*(z-x)
    have hd3 : HasDerivAt (fun y => (1/2 : ℝ) * deriv (deriv g) x * ((y - x) * (y - x)))
        (deriv (deriv g) x * (z - x)) z := by
      have h := (hasDerivAt_const z ((1/2 : ℝ) * deriv (deriv g) x)).mul hd_sq
      simp only [zero_mul, zero_add] at h
      have heq : 1 / 2 * deriv (deriv g) x * (2 * (z - x)) =
          deriv (deriv g) x * (z - x) := by ring
      rwa [heq] at h
    -- Combine
    have h12 := hd1.sub hd2
    have hcomb := h12.sub hd3
    -- Convert (y-x)*(y-x) to (y-x)^2 in the function
    have hfun_eq : (fun y => (fun y => g y - g x) y - (fun y => deriv g x * (y - x)) y -
        (fun y => 1 / 2 * deriv (deriv g) x * ((y - x) * (y - x))) y) =
        (fun y => g y - g x - deriv g x * (y - x) - 1 / 2 * deriv (deriv g) x * (y - x) ^ 2) := by
      ext y; ring
    rwa [show (fun y => g y - g x - deriv g x * (y - x) -
        1 / 2 * deriv (deriv g) x * (y - x) ^ 2) =
        (fun y => (fun y => g y - g x) y - (fun y => deriv g x * (y - x)) y -
        (fun y => 1 / 2 * deriv (deriv g) x * ((y - x) * (y - x))) y) from by ext y; ring]
  rw [show g (x + h) - g x - deriv g x * h - 1 / 2 * deriv (deriv g) x * h ^ 2 =
    (fun y => g y - g x - deriv g x * (y - x) - (1/2) * deriv (deriv g) x * (y - x) ^ 2)
      (x + h) -
    (fun y => g y - g x - deriv g x * (y - x) - (1/2) * deriv (deriv g) x * (y - x) ^ 2)
      x from by ring_nf]
  calc ‖(fun y => g y - g x - deriv g x * (y - x) -
        1 / 2 * deriv (deriv g) x * (y - x) ^ 2) (x + h) -
        (fun y => g y - g x - deriv g x * (y - x) -
        1 / 2 * deriv (deriv g) x * (y - x) ^ 2) x‖
      ≤ (C * |h|) * ‖(x + h) - x‖ := by
        apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun z hz => (hF_deriv z hz).hasDerivWithinAt)
          (fun z hz => by
            rw [Real.norm_eq_abs]
            calc |((deriv g z - deriv g x) - deriv (deriv g) x * (z - x))|
                ≤ C * |z - x| := by
                  rw [← Real.norm_eq_abs]; exact hG_bound z hz
              _ ≤ C * |h| := by
                  exact mul_le_mul_of_nonneg_left (abs_sub_le_of_mem_uIcc hz) hC)
          (show Convex ℝ (uIcc x (x + h)) from convex_uIcc x (x + h))
          (left_mem_uIcc) (right_mem_uIcc)
    _ = C * h ^ 2 := by
        rw [Real.norm_eq_abs, show (x + h) - x = h from by ring, mul_assoc,
            abs_mul_abs_self]
        ring
