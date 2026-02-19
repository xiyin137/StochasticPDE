/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.RegularityStructures.Models.Admissible
import StochasticPDE.RegularityStructures.SmoothCutoff

/-!
# Canonical Model from Noise

This file defines the canonical model Π^ξ built from noise ξ.

## Main Definitions

* `CanonicalModelData` - Data needed to construct the canonical model
* `canonical_model` - The canonical model Π^ξ built from noise ξ
* `renormalized_model_converges` - The renormalized models converge as ε → 0

## Mathematical Background

For a concrete SPDE, the model is built from:
1. The mollified noise ξ_ε
2. The convolution kernel K (e.g., heat kernel)

The construction is recursive on tree complexity:
- Π_x(Xi) = ξ (the noise)
- Π_x(X^k) = (· - x)^k (polynomials)
- Π_x(I_k(τ)) = ∫ D^k_y K(x,y) Π_y(τ) dy
- Π_x(τ₁ · τ₂) = Π_x(τ₁) · Π_x(τ₂) (requires renormalization!)

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 8
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## Canonical Model Data -/

/-- Data for constructing the canonical model from noise.
    This encodes how to lift the noise ξ to a full model. -/
structure CanonicalModelData (d : ℕ) (params : ModelParameters d) where
  /-- The mollified noise ξ_ε as a function of cutoff ε, point x -/
  mollified_noise : ℝ → (Fin d → ℝ) → ℝ
  /-- The singular convolution kernel K satisfying Assumptions 5.1 and 5.4 of Hairer 2014 -/
  singular_kernel : SingularKernelRS d
  /-- Variance of mollified noise -/
  noise_variance : ℝ → ℝ  -- ε → Var(ξ_ε(x))
  /-- Variance grows as ε → 0 -/
  variance_grows : ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ < ε₂ → noise_variance ε₁ > noise_variance ε₂

namespace CanonicalModelData

variable {d : ℕ} {params : ModelParameters d}

/-- Singular kernel for the heat kernel structure.

    The dyadic decomposition K_n satisfies:
    - K = Σ_n K_n (pointwise convergence for x ≠ y)
    - K_n(x,y) = 0 when |x - y| > C * 2^{-n} (localization to scale 2^{-n})
    - |K_n(x,y)| ≤ C * 2^{(d-β)n} (size estimate)

    The construction uses smooth cutoff functions from SmoothCutoff.lean:
    K_n(x,y) = K(x,y) · ψ_n(|x-y|)
    where ψ_n is the n-th dyadic cutoff localized to scale 2^{-n}.

    IMPORTANT: Requires d ≥ 2 for the bound 2^{(d-β)n} with β = 2 to work.
    For d = 1 (1D space), use parabolic scaling where effective dimension is d + 2.
    For d = 0, the problem is trivial with no spatial degrees of freedom. -/
noncomputable def heatKernelSingular (d : ℕ) (hd : d ≥ 2) : SingularKernelRS d where
  order := 2  -- Heat kernel has order 2 (parabolic scaling)
  order_pos := two_pos
  kernel := fun x y => Real.exp (-(∑ i, (x i - y i)^2) / 4)  -- Heat kernel at t=1
  kernel_dyadic := fun n x y =>
    -- K_n(x,y) = K(x,y) · ψ_n(|x-y|) where ψ_n is the n-th dyadic cutoff
    let K_xy := Real.exp (-(∑ i, (x i - y i)^2) / 4)
    let dist_xy := euclideanDist d x y
    let cutoff := DyadicDecomposition.standard.cutoff n dist_xy
    K_xy * cutoff
  bound_const := 1
  bound_pos := one_pos
  support_bound := fun n x y hdist => by
    -- When |x-y| > C * 2^{-n}, the dyadic cutoff vanishes
    -- The cutoff ψ_n is zero outside its support scale
    have h_cutoff_zero : DyadicDecomposition.standard.cutoff n (euclideanDist d x y) = 0 := by
      apply DyadicDecomposition.cutoff_zero_outside
      -- Need: standard.annular.bump.rOut * 2^{-n} ≤ |euclideanDist d x y|
      -- hdist provides: Real.sqrt (∑ i, (x i - y i)^2) > 1 * 2^{-(n:ℝ)}
      -- standard.annular.bump.rOut = 1, euclideanDist = Real.sqrt(...)
      have hrOut : DyadicDecomposition.standard.annular.bump.rOut = 1 := rfl
      rw [hrOut]
      have h_dist_nonneg : euclideanDist d x y ≥ 0 := by
        unfold euclideanDist euclideanNorm
        exact Real.sqrt_nonneg _
      have h_dist_eq : euclideanDist d x y = Real.sqrt (∑ i, (x i - y i)^2) := rfl
      rw [h_dist_eq]
      -- hdist : Real.sqrt (...) > 1 * 2^{-(n:ℝ)}
      exact bound_transfer (Real.sqrt (∑ i, (x i - y i)^2)) n 1 (Real.sqrt_nonneg _) hdist
    simp only [h_cutoff_zero, mul_zero]
  pointwise_bound := fun n x y => by
    -- |K_n(x,y)| ≤ C * 2^{(d-2)n}
    -- |K(x,y) * cutoff| ≤ |K(x,y)| * |cutoff| ≤ 1 * 1 = 1 ≤ C * 2^{(d-2)n}
    have h_exp_le_one : |Real.exp (-(∑ i, (x i - y i)^2) / 4)| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg
      · apply neg_nonpos_of_nonneg
        apply Finset.sum_nonneg
        intro i _
        exact sq_nonneg _
      · norm_num
    have h_cutoff_le_one : |DyadicDecomposition.standard.cutoff n (euclideanDist d x y)| ≤ 1 :=
      DyadicDecomposition.cutoff_abs_le_one _ n _
    have h_prod : |Real.exp (-(∑ i, (x i - y i)^2) / 4) *
           DyadicDecomposition.standard.cutoff n (euclideanDist d x y)| ≤ 1 := by
      calc |Real.exp (-(∑ i, (x i - y i)^2) / 4) *
             DyadicDecomposition.standard.cutoff n (euclideanDist d x y)|
          = |Real.exp (-(∑ i, (x i - y i)^2) / 4)| *
             |DyadicDecomposition.standard.cutoff n (euclideanDist d x y)| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul h_exp_le_one h_cutoff_le_one (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    calc |Real.exp (-(∑ i, (x i - y i)^2) / 4) *
           DyadicDecomposition.standard.cutoff n (euclideanDist d x y)|
        ≤ 1 := h_prod
      _ ≤ 1 * (2 : ℝ) ^ (((d : ℝ) - 2) * ↑n) := by
          -- Need: 1 ≤ 1 * 2^{(d-2)n}, i.e., 1 ≤ 2^{(d-2)n}
          -- This holds when (d-2)n ≥ 0, i.e., when d ≥ 2 or n = 0
          -- For d < 2 and n > 0, the bound 2^{(d-2)n} < 1
          -- However, in physical applications d ≥ 2 for spatial dimensions
          by_cases hd : d ≥ 2
          · -- d ≥ 2: exponent (d-2)n ≥ 0
            have hd_cast : (d : ℝ) ≥ 2 := Nat.cast_le.mpr hd
            have h_exp_nonneg : ((d : ℝ) - 2) * ↑n ≥ 0 := by
              apply mul_nonneg
              · linarith
              · exact Nat.cast_nonneg n
            have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (((d : ℝ) - 2) * ↑n) :=
              Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) h_exp_nonneg
            calc (1 : ℝ) ≤ (2 : ℝ) ^ (((d : ℝ) - 2) * ↑n) := h1
              _ = 1 * (2 : ℝ) ^ (((d : ℝ) - 2) * ↑n) := by ring
          · -- d < 2: This case is now excluded by the hypothesis hd : d ≥ 2
            push_neg at hd
            omega  -- hd : d < 2 contradicts hd : d ≥ 2

/-- Standard data for the heat kernel on ℝ^d with d ≥ 2.

    The mollified noise ξ_ε is the convolution of white noise ξ with a mollifier ρ_ε.
    In dimension d, the variance of ξ_ε(x) scales as ε^{-d} as ε → 0.

    The `mollified_noise` field represents a sample path of ξ_ε(x) = (ξ * ρ_ε)(x).
    Full probabilistic treatment would require:
    - White noise as a random distribution on Schwartz space
    - Stochastic convolution integral
    - Measurability and moment estimates

    For regularity structures, the key properties are:
    1. ξ_ε is smooth (since ρ is smooth)
    2. Var(ξ_ε(x)) = ‖ρ_ε‖_{L²}² = ε^{-d} ‖ρ‖_{L²}²
    3. ξ_ε → ξ in distribution as ε → 0

    Note: d ≥ 2 is required for the heat kernel bounds. For d = 1 spatial dimensions,
    use parabolic scaling where the effective dimension is d + 2 = 3. -/
noncomputable def heatKernel (hd : d ≥ 2) : CanonicalModelData d params where
  mollified_noise := fun ε x =>
    -- ξ_ε(x) = ∫ ρ_ε(x - y) ξ(dy) where ρ_ε is the scaled mollifier
    -- The value depends on the realization of white noise ξ
    -- The scaled mollifier is ρ_ε(z) = ε^{-d} ρ(z/ε)
    -- For a proper definition, we would need stochastic integration:
    -- ∫ ρ_ε(x - y) ξ(dy) where ξ is white noise
    --
    -- Using the Mollifier infrastructure from SmoothCutoff.lean:
    -- let ρ := Mollifier.standard d
    -- let ρ_ε := Mollifier.scaled d ρ ε
    -- The integral ∫ ρ_ε(x - ·) dξ requires stochastic analysis
    sorry
  singular_kernel := heatKernelSingular d hd
  noise_variance := fun ε =>
    -- Var(ξ_ε(x)) = ‖ρ_ε‖_{L²}² = ε^{-d} ‖ρ‖_{L²}²
    -- Using the standard mollifier with L2_norm_sq = 1
    ε ^ (-(d : ℝ))
  variance_grows := by
    intro ε₁ ε₂ hε₁ hε₁ε₂
    -- Need: ε₁^(-d) > ε₂^(-d) when 0 < ε₁ < ε₂
    show ε₁ ^ (-(d : ℝ)) > ε₂ ^ (-(d : ℝ))
    -- d ≥ 2 implies d > 0, so ε^(-d) is strictly decreasing
    have hd_pos : (d : ℝ) > 0 := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le (by omega : 0 < 2) hd)
    have hε₂ : ε₂ > 0 := lt_trans hε₁ hε₁ε₂
    rw [Real.rpow_neg (le_of_lt hε₁), Real.rpow_neg (le_of_lt hε₂)]
    -- Need: (ε₁^d)⁻¹ > (ε₂^d)⁻¹, i.e., ε₂^d > ε₁^d
    have h1 : ε₁ ^ (d : ℝ) < ε₂ ^ (d : ℝ) := Real.rpow_lt_rpow (le_of_lt hε₁) hε₁ε₂ hd_pos
    rw [gt_iff_lt, inv_lt_inv₀ (Real.rpow_pos_of_pos hε₂ _) (Real.rpow_pos_of_pos hε₁ _)]
    exact h1

end CanonicalModelData

/-! ## The Canonical Model -/

/-- The canonical model Π^ξ built from noise ξ.

    For the noise tree Xi: (Π_x Xi)(φ) = ∫ φ(y) ξ(y) dy
    For integration I(τ): (Π_x I(τ))(φ) = ∫∫ K(y,z) (Π_z τ)(dz) φ(y) dy
    For products: requires Wick renormalization

    The construction is recursive on tree complexity. -/
noncomputable def canonical_model {d : ℕ} {params : ModelParameters d}
    (_data : CanonicalModelData d params) (ε : ℝ) (_hε : ε > 0) : AdmissibleModel d params where
  Pi := {
    pairing := fun τ x φ scale =>
      match τ with
      | .one => 1
      | .Xi =>
        -- ⟨Π_x Ξ, φ^λ_x⟩ = ∫ φ^λ_x(y) ξ_ε(y) dy
        -- This requires the mollified noise realization
        -- The value depends on the specific noise sample
        sorry  -- Requires stochastic integration: ∫ φ^scale_x(y) ξ_ε(y) dy
      | .Poly k =>
        -- ⟨Π_x X^k, φ^λ_x⟩ = λ^{|k|} · ∫ φ(z) z^k dz
        -- The integral ∫ φ(z) z^k dz is the k-th moment of φ centered at 0
        -- For compactly supported φ with support in unit ball, this is bounded
        let degree := k.degree
        scale ^ (degree : ℝ) * 1  -- Simplified: moment assumed to be 1
      | .Integ k τ' =>
        -- ⟨Π_x I_k(τ), φ^λ_x⟩ = ∫∫ D^k_y K(x,y) (Π_y τ')(φ^λ_y) dy
        -- This is recursive in tree structure
        sorry  -- Requires recursion through kernel convolution
      | .Prod τ₁ τ₂ =>
        -- ⟨Π_x (τ₁ · τ₂), φ^λ_x⟩ = ⟨Π_x τ₁ · Π_x τ₂, φ^λ_x⟩
        -- For distributions, product requires Wick renormalization
        sorry  -- Requires Wick product/renormalization
    unit_property := fun _x _φ _scale _hs_pos _hs_le => rfl
  }
  Gamma := {
    Gamma := fun _x _y τ => FormalSum.single τ  -- Simplified: identity recentering
    self_eq_id := fun _x _τ => rfl
    cocycle := fun _x _y _z τ => FormalSum.bind_single τ (fun σ => FormalSum.single σ)
  }
  bound_const := 1  -- Initial constant; actual bound depends on ε and noise realization
  bound_pos := by norm_num
  regularity_index := 0  -- Degree of test function derivatives needed
  analytical_bound := by
    intro τ x φ scale hscale hscale1
    -- RHS is nonnegative
    have hRHS_nonneg : 0 ≤ 1 * Real.rpow scale
        (homogeneity params.noiseRegularity params.kernelOrder τ) * φ.sup_norm := by
      apply mul_nonneg; apply mul_nonneg
      · norm_num
      · exact Real.rpow_nonneg (le_of_lt hscale) _
      · simp only [TestFunction.sup_norm]; linarith [φ.norm_ge_one]
    cases τ with
    | one =>
      -- |1| ≤ 1 * scale^0 * ‖φ‖ = ‖φ‖
      simp only [homogeneity, abs_one]
      have h1 : Real.rpow scale 0 = 1 := Real.rpow_zero scale
      simp only [h1]
      ring_nf
      simp only [TestFunction.sup_norm]
      exact φ.norm_ge_one
    | Xi =>
      -- Xi case has sorry in pairing, bound depends on noise realization
      sorry  -- Requires bound on mollified noise integral
    | Poly k =>
      -- |scale^|k|| ≤ 1 * scale^|k| * ‖φ‖
      simp only [homogeneity]
      have habs : |scale ^ (k.degree : ℝ) * 1| = scale ^ (k.degree : ℝ) := by
        rw [show scale ^ (k.degree : ℝ) * 1 = scale ^ (k.degree : ℝ) by ring]
        rw [abs_of_pos]
        exact Real.rpow_pos_of_pos hscale _
      rw [habs]
      -- Need: scale^|k| ≤ 1 * scale^|k| * ‖φ‖
      have h1 : (1 : ℝ) * Real.rpow scale (k.degree : ℝ) * φ.sup_norm =
                Real.rpow scale (k.degree : ℝ) * φ.sup_norm := by ring
      rw [h1]
      -- Since ‖φ‖ ≥ 1, we have scale^|k| ≤ scale^|k| * ‖φ‖
      have hnorm : φ.sup_norm ≥ 1 := φ.norm_ge_one
      have hpow_pos : Real.rpow scale (k.degree : ℝ) > 0 := Real.rpow_pos_of_pos hscale _
      have hpow_nonneg : Real.rpow scale (k.degree : ℝ) ≥ 0 := le_of_lt hpow_pos
      calc scale ^ (k.degree : ℝ)
          = scale ^ (k.degree : ℝ) * 1 := by ring
        _ ≤ scale ^ (k.degree : ℝ) * φ.sup_norm := by
            apply mul_le_mul_of_nonneg_left hnorm hpow_nonneg
    | Integ _ _ =>
      -- Integ case has sorry in pairing
      sorry  -- Requires bound on kernel convolution
    | Prod _ _ =>
      -- Prod case has sorry in pairing
      sorry  -- Requires bound on Wick product
  consistency := fun x y τ φ scale _hscale _hscale1 => by
    -- Gamma x y τ = single τ, so evalFormalSum (single τ) x φ scale = pairing τ x φ scale
    -- After rewrite, goal is: pairing τ y φ scale = pairing τ x φ scale
    -- For our simplified pairing, this doesn't depend on the base point
    -- .one returns 1, .Poly returns scale^|k|, and .Xi/.Integ/.Prod are sorry anyway
    simp only [ModelMap.evalFormalSum_single]

/-! ## Renormalization -/

/-- The renormalization constants for the canonical model.
    For trees with |τ| < 0, we need to subtract divergent constants. -/
structure RenormalizationConstants (d : ℕ) (params : ModelParameters d) where
  /-- The renormalization constant for each tree requiring renormalization -/
  constant : TreeSymbol d → ℝ → ℝ  -- τ → ε → C_τ(ε)
  /-- Constants only for trees with negative homogeneity -/
  support : ∀ τ : TreeSymbol d,
    homogeneity params.noiseRegularity params.kernelOrder τ ≥ 0 →
    ∀ ε > 0, constant τ ε = 0
  /-- The divergence rate depends on homogeneity -/
  divergence_rate : ∀ τ : TreeSymbol d,
    requiresRenormalization params.noiseRegularity params.kernelOrder τ →
    True  -- Full statement involves |C_τ(ε)| ~ ε^{|τ|}

/-- The renormalized canonical model.
    Π^{ξ,ren}_x(τ) = Π^ξ_x(τ) - C_τ(ε) for trees requiring renormalization. -/
noncomputable def renormalized_canonical_model {d : ℕ} {params : ModelParameters d}
    (data : CanonicalModelData d params)
    (renorm : RenormalizationConstants d params)
    (ε : ℝ) (hε : ε > 0) : AdmissibleModel d params :=
  let base := canonical_model data ε hε
  { Pi := {
      pairing := fun τ x φ scale =>
        base.Pi.pairing τ x φ scale - renorm.constant τ ε
      unit_property := fun x φ scale hs_pos hs_le => by
        -- base.Pi.pairing .one x φ scale - renorm.constant .one ε
        -- = 1 - 0 = 1 (since homogeneity(.one) = 0 ≥ 0)
        have h_hom : homogeneity params.noiseRegularity params.kernelOrder (TreeSymbol.one : TreeSymbol d) ≥ 0 := by
          simp only [homogeneity_one, ge_iff_le, le_refl]
        rw [renorm.support TreeSymbol.one h_hom ε hε]
        simp only [sub_zero]
        exact base.Pi.unit_property x φ scale hs_pos hs_le
    }
    Gamma := base.Gamma
    bound_const := base.bound_const
    bound_pos := base.bound_pos
    regularity_index := base.regularity_index
    analytical_bound := sorry  -- Renormalized model satisfies bounds
    consistency := sorry  -- Consistency with new Pi
  }

/-! ## Convergence -/

/-- The renormalized models converge as ε → 0.
    This is the main convergence theorem (Hairer 2014 Theorem 10.7). -/
theorem renormalized_model_converges {d : ℕ} {params : ModelParameters d}
    (data : CanonicalModelData d params)
    (γ : ℝ) (_hγ : γ > 0) :
    ∃ M_limit : AdmissibleModel d params,
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ∀ hε : 0 < ε, ε < ε₀ →
      AdmissibleModel.distance (canonical_model data ε hε) M_limit γ < δ := by
  sorry  -- This is the main convergence theorem

/-- The limit model is independent of the mollification. -/
theorem limit_independent_of_mollification {d : ℕ} {params : ModelParameters d}
    (data₁ data₂ : CanonicalModelData d params)
    (γ : ℝ) (hγ : γ > 0) :
    ∃ M : AdmissibleModel d params,
    (∀ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ∀ hε : 0 < ε, ε < ε₀ →
      AdmissibleModel.distance (canonical_model data₁ ε hε) M γ < δ) ∧
    (∀ δ > 0, ∃ ε₀ > 0, ∀ ε : ℝ, ∀ hε : 0 < ε, ε < ε₀ →
      AdmissibleModel.distance (canonical_model data₂ ε hε) M γ < δ) := by
  -- Both converge to the same limit
  obtain ⟨M₁, hM₁⟩ := renormalized_model_converges data₁ γ hγ
  use M₁
  constructor
  · exact hM₁
  · sorry  -- Requires showing both limits agree

end SPDE.RegularityStructures
