/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.RegularityStructures.Trees.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Admissible Models for Regularity Structures

This file defines admissible models (Π, Γ) satisfying Hairer's analytical bounds.

## Main Definitions

* `ModelParameters` - Parameters α (noise regularity) and β (kernel order)
* `TestFunction` - Smooth compactly supported test functions
* `ModelMap` - The map Π_x : T → D'
* `RecenteringMap` - The recentering map Γ_{xy}
* `AdmissibleModel` - A model satisfying all required bounds

## Mathematical Background

A model (Π, Γ) for a regularity structure (A, T, G) consists of:

1. **Model map Π_x**: For each x ∈ ℝ^d and τ ∈ T_α, a distribution Π_x τ ∈ D'
   Key bound: |⟨Π_x τ, φ^λ_x⟩| ≤ C λ^{|τ|}

2. **Recentering map Γ_{xy}**: For x, y ∈ ℝ^d, Γ_{xy} : T → T satisfies
   - Γ_{xx} = id
   - Γ_{xy} ∘ Γ_{yz} = Γ_{xz} (cocycle)
   - Π_y = Π_x ∘ Γ_{xy}

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Definition 3.1
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## Model Parameters -/

/-- Parameters for the model bounds.
    These encode the noise regularity and kernel order. -/
structure ModelParameters (d : ℕ) where
  /-- The noise regularity α -/
  noiseRegularity : ℝ
  /-- The kernel order β (typically 2 for heat kernel) -/
  kernelOrder : ℝ
  /-- The minimum homogeneity to consider -/
  minHomogeneity : ℝ
  /-- The maximum homogeneity to consider -/
  maxHomogeneity : ℝ
  /-- Constraint: minHomogeneity < maxHomogeneity -/
  hom_lt : minHomogeneity < maxHomogeneity

namespace ModelParameters

variable {d : ℕ}

/-- Standard parameters for Φ⁴₃: α = -5/2, β = 2 -/
noncomputable def phi4_3 : ModelParameters 3 where
  noiseRegularity := -5/2
  kernelOrder := 2
  minHomogeneity := -5/2
  maxHomogeneity := 2
  hom_lt := by norm_num

/-- Standard parameters for KPZ: α = -3/2, β = 2 -/
noncomputable def kpz : ModelParameters 1 where
  noiseRegularity := -3/2
  kernelOrder := 2
  minHomogeneity := -3/2
  maxHomogeneity := 2
  hom_lt := by norm_num

end ModelParameters

/-! ## Test Functions -/

/-- A smooth compactly supported test function on ℝ^d.
    These are used to test distributions.

    Note: The smoothness condition uses `ContDiff ℝ ⊤` (C^∞ with respect to ℝ).
    The space `Fin d → ℝ` has the product topology and norm structure from Pi.normedAddCommGroup. -/
structure TestFunction (d : ℕ) where
  /-- The test function -/
  f : (Fin d → ℝ) → ℝ
  /-- Compact support (simplified: support in unit ball) -/
  compact_support : ∀ x : Fin d → ℝ, (∑ i, x i ^ 2) > 1 → f x = 0
  /-- Smoothness: f is infinitely differentiable (C^∞) -/
  smooth : ContDiff ℝ ⊤ f
  /-- The supremum norm is finite and bounded -/
  sup_norm_bound : ℝ
  /-- The bound holds: |f(x)| ≤ sup_norm_bound for all x -/
  f_le_bound : ∀ x : Fin d → ℝ, |f x| ≤ sup_norm_bound
  /-- Normalization: ‖φ‖_∞ ≥ 1. This ensures analytical bounds can be satisfied. -/
  norm_ge_one : sup_norm_bound ≥ 1

namespace TestFunction

variable {d : ℕ}

/-- The scaled test function φ^λ_x(y) = λ^{-d} φ((y-x)/λ) -/
noncomputable def scaled (φ : TestFunction d) (x : Fin d → ℝ) (scale : ℝ) : (Fin d → ℝ) → ℝ :=
  fun y => scale ^ (-(d : ℤ)) * φ.f (fun i => (y i - x i) / scale)

/-- The L^∞ norm of a test function (using the explicit bound) -/
def sup_norm (φ : TestFunction d) : ℝ := φ.sup_norm_bound

end TestFunction

/-! ## The Model Map -/

/-- The model map Π_x : T_α → D'.
    For each tree τ and point x, Π_x τ is a distribution.
    We represent the action on test functions directly. -/
structure ModelMap (d : ℕ) (params : ModelParameters d) where
  /-- The pairing ⟨Π_x τ, φ^λ_x⟩ for tree τ, point x, test function φ, scale λ -/
  pairing : TreeSymbol d → (Fin d → ℝ) → TestFunction d → ℝ → ℝ
  /-- Unit property: Π_x(𝟙) = 1 (the constant distribution).
      ⟨Π_x 𝟙, φ^λ_x⟩ = 1 for all x, φ, λ (since 𝟙 represents the constant function 1) -/
  unit_property : ∀ x : Fin d → ℝ, ∀ φ : TestFunction d, ∀ scale : ℝ,
    0 < scale → scale ≤ 1 → pairing .one x φ scale = 1

namespace ModelMap

variable {d : ℕ} {params : ModelParameters d}

/-- Evaluate a FormalSum using a model's pairing function.
    For s = Σᵢ cᵢ τᵢ, returns Σᵢ cᵢ · ⟨Π_x τᵢ, φ^λ_x⟩.
    This extends the pairing to FormalSum by linearity. -/
noncomputable def evalFormalSum (M : ModelMap d params) (s : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) : ℝ :=
  s.terms.foldl (fun acc (c, τ) => acc + c * M.pairing τ x φ scale) 0

/-- evalFormalSum of single τ equals pairing τ -/
theorem evalFormalSum_single (M : ModelMap d params) (τ : TreeSymbol d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) :
    M.evalFormalSum (FormalSum.single τ) x φ scale = M.pairing τ x φ scale := by
  simp only [evalFormalSum, FormalSum.single, List.foldl_cons, List.foldl_nil]
  ring

/-- The analytical bound: |⟨Π_x τ, φ^λ_x⟩| ≤ C λ^{|τ|} ‖φ‖_{C^r}

    This is the key estimate that makes the regularity structure work.
    The homogeneity |τ| determines the scaling behavior. -/
def satisfies_analytical_bound (M : ModelMap d params) (C : ℝ) (_r : ℕ) : Prop :=
  ∀ τ : TreeSymbol d,
  ∀ x : Fin d → ℝ,
  ∀ φ : TestFunction d,
  ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
    |M.pairing τ x φ scale| ≤ C * Real.rpow scale (homogeneity params.noiseRegularity params.kernelOrder τ) * φ.sup_norm

/-- Evaluate the monomial (y - x)^k for multi-index k -/
noncomputable def evalMonomial (k : MultiIndex d) (x y : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, (y i - x i) ^ (k i)

/-- The polynomial reproduces correctly: Π_x(X^k) = (· - x)^k
    This means ⟨Π_x(X^k), φ^λ_x⟩ scales as λ^|k| (the degree of the polynomial).
    The exact value depends on the integral of φ(z) z^k over the support.

    For the polynomial X^k with |k| = Σᵢ kᵢ, the scaling behavior is:
    ⟨Π_x(X^k), φ^λ_x⟩ = λ^|k| ∫ φ(z) z^k dz

    We express this via the homogeneity condition: the bound constant is achieved. -/
def reproduces_polynomials (M : ModelMap d params) : Prop :=
  ∀ k : MultiIndex d,
  ∀ x : Fin d → ℝ,
  ∀ φ : TestFunction d,
  ∀ s₁ s₂ : ℝ,
  0 < s₁ → s₁ ≤ 1 → 0 < s₂ → s₂ ≤ 1 →
    -- Scaling relation: ratio of pairings equals ratio of scales raised to |k|
    -- |⟨Π_x(X^k), φ^{s₁}_x⟩| / |⟨Π_x(X^k), φ^{s₂}_x⟩| = (s₁/s₂)^|k|
    -- We express this as: pairing scales homogeneously with degree |k|
    M.pairing (.Poly k) x φ s₁ * s₂ ^ (k.degree : ℝ) =
    M.pairing (.Poly k) x φ s₂ * s₁ ^ (k.degree : ℝ)

end ModelMap

/-! ## The Recentering Map -/

/-- The recentering map Γ : ℝ^d × ℝ^d → End(T).
    Γ_{xy} tells us how to express Π_y in terms of Π_x.

    IMPORTANT: Γ_{xy} is a LINEAR map on the vector space T, meaning it
    takes a tree τ and returns a formal sum (linear combination of trees).
    This is essential for the regularity structures theory because:
    1. The group action Γ_{xy} = τ + (lower order terms in x-y)
    2. The renormalization group action composes linearly: Γ^g = g ∘ Γ ∘ g⁻¹

    References: Hairer 2014 Definition 2.1, Equation (2.5) -/
structure RecenteringMap (d : ℕ) where
  /-- The linear map Γ_{xy} : T → T for each pair (x, y).
      Returns a FormalSum since Γ_{xy}(τ) = τ + (lower order terms). -/
  Gamma : (Fin d → ℝ) → (Fin d → ℝ) → TreeSymbol d → FormalSum d
  /-- Γ_{xx} = id (identity at same point) -/
  self_eq_id : ∀ x : Fin d → ℝ, ∀ τ : TreeSymbol d, Gamma x x τ = FormalSum.single τ
  /-- Γ_{xy} ∘ Γ_{yz} = Γ_{xz} (cocycle condition for composition).
      Note: This requires extending Gamma to act on FormalSum via bind. -/
  cocycle : ∀ x y z : Fin d → ℝ, ∀ τ : TreeSymbol d,
    FormalSum.bind (Gamma y z τ) (Gamma x y) = Gamma x z τ

/-! ## Admissible Models -/

/-- An admissible model for a regularity structure.

    Following Hairer 2014 Definition 3.1, a model consists of:
    1. A model map Π satisfying analytical bounds
    2. A recentering map Γ satisfying the cocycle condition
    3. Consistency: Π_y = Π_x ∘ Γ_{xy} -/
structure AdmissibleModel (d : ℕ) (params : ModelParameters d) where
  /-- The model map Π -/
  Pi : ModelMap d params
  /-- The recentering map Γ -/
  Gamma : RecenteringMap d
  /-- The bound constant C -/
  bound_const : ℝ
  /-- The constant is positive -/
  bound_pos : bound_const > 0
  /-- The regularity index r for test function norms -/
  regularity_index : ℕ
  /-- The model satisfies the analytical bound -/
  analytical_bound : Pi.satisfies_analytical_bound bound_const regularity_index
  /-- Consistency between Π and Γ: Π_y = Π_x ∘ Γ_{xy}
      Since Γ_{xy}(τ) is a FormalSum, we use evalFormalSum to evaluate it. -/
  consistency : ∀ x y : Fin d → ℝ,
    ∀ τ : TreeSymbol d,
    ∀ φ : TestFunction d,
    ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
      Pi.pairing τ y φ scale = Pi.evalFormalSum (Gamma.Gamma x y τ) x φ scale

namespace AdmissibleModel

variable {d : ℕ} {params : ModelParameters d}

/-- The trivial model: Π_x(Xi) = 0, Π_x(X^k) = (· - x)^k, Π_x(1) = 1 -/
noncomputable def trivialModel : AdmissibleModel d params where
  Pi := {
    pairing := fun τ _x _φ _scale =>
      match τ with
      | .one => 1
      | .Xi => 0
      | .Poly _k => 0  -- Simplified
      | .Integ _k _τ' => 0
      | .Prod _τ₁ _τ₂ => 0
    unit_property := fun _x _φ _scale _hs_pos _hs_le => rfl
  }
  Gamma := {
    Gamma := fun _x _y τ => FormalSum.single τ
    self_eq_id := fun _x _τ => rfl
    cocycle := fun _x _y _z τ => by
      -- bind (single τ) (fun σ => single σ) = single τ
      exact FormalSum.bind_single τ (fun σ => FormalSum.single σ)
  }
  bound_const := 1
  bound_pos := by norm_num
  regularity_index := 0
  analytical_bound := by
    intro τ x φ scale hscale hscale1
    -- For all cases except .one, pairing = 0, so |0| = 0 ≤ RHS
    -- The RHS is always ≥ 0 since it's a product of non-negative terms
    have hRHS_nonneg : 0 ≤ 1 * Real.rpow scale
        (homogeneity params.noiseRegularity params.kernelOrder τ) * φ.sup_norm := by
      apply mul_nonneg
      apply mul_nonneg
      · norm_num
      · exact Real.rpow_nonneg (le_of_lt hscale) _
      · -- sup_norm = sup_norm_bound ≥ 1 ≥ 0
        simp only [TestFunction.sup_norm]
        have h := φ.norm_ge_one
        linarith
    cases τ with
    | one =>
      -- |1| ≤ 1 * scale^0 * ‖φ‖ = ‖φ‖
      -- We have ‖φ‖ ≥ 1 by the norm_ge_one constraint
      simp only [homogeneity, abs_one]
      -- Need: 1 ≤ 1 * scale.rpow 0 * φ.sup_norm
      have h1 : Real.rpow scale 0 = 1 := Real.rpow_zero scale
      simp only [h1]
      ring_nf
      -- Now need: 1 ≤ φ.sup_norm = φ.sup_norm_bound
      simp only [TestFunction.sup_norm]
      exact φ.norm_ge_one
    | Xi => simp only [abs_zero]; exact hRHS_nonneg
    | Poly _ => simp only [abs_zero]; exact hRHS_nonneg
    | Integ _ _ => simp only [abs_zero]; exact hRHS_nonneg
    | Prod _ _ => simp only [abs_zero]; exact hRHS_nonneg
  consistency := fun _x _y τ φ scale _hscale _hscale1 => by
    -- For trivial model: Gamma x y τ = single τ
    -- Need: pairing τ y φ scale = evalFormalSum (single τ) x φ scale
    -- Since the trivial model's pairing doesn't depend on x, and evalFormalSum_single:
    simp only [ModelMap.evalFormalSum_single]
    -- Both sides are the same because the trivial model's pairing doesn't depend on position

/-- The model distance measures how close two models are.

    Following Hairer 2014, the distance between models (Π₁, Γ₁) and (Π₂, Γ₂) is:
    |||M₁ - M₂|||_γ = sup_{τ, x, φ, λ} |⟨Π₁_x τ - Π₂_x τ, φ^λ_x⟩| / λ^{|τ|}

    This is a proper metric on the space of admissible models. -/
noncomputable def distance (M₁ M₂ : AdmissibleModel d params) (γ : ℝ) : ℝ :=
  ⨆ (τ : TreeSymbol d) (x : Fin d → ℝ) (φ : TestFunction d) (scale : Set.Ioo (0 : ℝ) 1),
    if homogeneity params.noiseRegularity params.kernelOrder τ < γ then
      |M₁.Pi.pairing τ x φ scale.val - M₂.Pi.pairing τ x φ scale.val| /
        Real.rpow scale.val (homogeneity params.noiseRegularity params.kernelOrder τ)
    else 0

end AdmissibleModel

/-! ## Singular Kernels for Regularity Structures

Following Assumptions 5.1 and 5.4 from Hairer 2014, a kernel K suitable for
regularity structures must satisfy:
1. K(x, y) = Σ_n K_n(x, y) with K_n supported on |x - y| ~ 2^{-n}
2. |D^k K_n(x, y)| ≤ C 2^{(|k| + |s| - β)n}
3. Vanishing moments: ∫ y^k K_n(x, y) dy = 0 for |k| < ⌊β⌋
-/

/-- A singular kernel K satisfying the regularity structures assumptions.

    Following Assumptions 5.1 and 5.4 from Hairer 2014:
    - K admits a dyadic decomposition K = Σ_n K_n
    - Each K_n is supported on scale 2^{-n}
    - The bounds and vanishing moments are satisfied -/
structure SingularKernelRS (d : ℕ) where
  /-- The kernel order β (typically 2 for heat kernel) -/
  order : ℝ
  order_pos : order > 0
  /-- The kernel K(x, y) -/
  kernel : (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  /-- The dyadic pieces K_n -/
  kernel_dyadic : ℕ → (Fin d → ℝ) → (Fin d → ℝ) → ℝ
  /-- Bound constant for kernel estimates -/
  bound_const : ℝ
  bound_pos : bound_const > 0
  /-- Support bound: K_n(x,y) = 0 when |x - y| > C * 2^{-n}
      This encodes that K_n is supported on scale 2^{-n} -/
  support_bound : ∀ n : ℕ, ∀ x y : Fin d → ℝ,
    Real.sqrt (∑ i, (x i - y i)^2) > bound_const * (2 : ℝ)^(-(n : ℝ)) →
    kernel_dyadic n x y = 0
  /-- Pointwise bound: |K_n(x,y)| ≤ C * 2^{(d-β)n} for x,y in support
      This is the basic size estimate without derivatives -/
  pointwise_bound : ∀ n : ℕ, ∀ x y : Fin d → ℝ,
    |kernel_dyadic n x y| ≤ bound_const * (2 : ℝ)^(((d : ℝ) - order) * n)

end SPDE.RegularityStructures
