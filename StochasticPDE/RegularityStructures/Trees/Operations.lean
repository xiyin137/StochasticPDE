/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.RegularityStructures.Trees.Homogeneity

/-!
# Tree Operations for Regularity Structures

This file defines the key operations on decorated trees:
- I_k: Integration operator
- Polynomial symbols X^k

## Main Definitions

* `I_Xi` - The integrated noise I(Ξ)
* `I_Xi_squared`, `I_Xi_cubed` - Powers for Φ⁴
* `I_I_Xi_squared` - Second-order Picard iteration

## Mathematical Background

The integration operator I_k corresponds to convolution with the kernel:
  I_k(τ) represents ∫ D^k_y K(x,y) Π_y(τ) dy

For the heat kernel K, we have β = 2, so:
  |I_k(τ)| = |τ| + 2 - |k|

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 3.1
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## Standard Trees for Φ⁴ and KPZ

We define the standard trees that appear in singular SPDEs.
-/

variable {d : ℕ}

/-- The integrated noise I(Ξ) = ∫ K(x,y) ξ(y) dy.
    This represents the solution to the linear stochastic heat equation.
    Homogeneity: |I(Ξ)| = α + β -/
def I_Xi : TreeSymbol d := Integ MultiIndex.zero Xi

/-- Homogeneity of I(Ξ) is α + β -/
theorem homogeneity_I_Xi (α β : ℝ) :
    homogeneity α β (I_Xi : TreeSymbol d) = α + β := by
  simp [I_Xi, homogeneity, MultiIndex.degree_zero]

/-- The tree I(Ξ)² representing the square of the linear solution.
    For Φ⁴₃: |I(Ξ)²| = 2(α + β) = 2(-5/2 + 2) = -1 < 0
    This requires renormalization! -/
def I_Xi_squared : TreeSymbol d := Prod I_Xi I_Xi

/-- Homogeneity of I(Ξ)² is 2(α + β) -/
theorem homogeneity_I_Xi_squared (α β : ℝ) :
    homogeneity α β (I_Xi_squared : TreeSymbol d) = 2 * (α + β) := by
  simp [I_Xi_squared, homogeneity_Prod, homogeneity_I_Xi]
  ring

/-- The tree I(Ξ)³ for Φ⁴.
    For Φ⁴₃: |I(Ξ)³| = 3(α + β) = 3(-1/2) = -3/2 < 0
    This also requires renormalization! -/
def I_Xi_cubed : TreeSymbol d := Prod I_Xi (Prod I_Xi I_Xi)

/-- Homogeneity of I(Ξ)³ -/
theorem homogeneity_I_Xi_cubed (α β : ℝ) :
    homogeneity α β (I_Xi_cubed : TreeSymbol d) = 3 * (α + β) := by
  simp [I_Xi_cubed, homogeneity_Prod, homogeneity_I_Xi]
  ring

/-- The tree I(I(Ξ)²) - second-order Picard iteration.
    Homogeneity: |I(I(Ξ)²)| = |I(Ξ)²| + β = 2(α + β) + β = 2α + 3β -/
def I_I_Xi_squared : TreeSymbol d := Integ MultiIndex.zero I_Xi_squared

/-- Homogeneity of I(I(Ξ)²) -/
theorem homogeneity_I_I_Xi_squared (α β : ℝ) :
    homogeneity α β (I_I_Xi_squared : TreeSymbol d) = 2 * α + 3 * β := by
  simp [I_I_Xi_squared, homogeneity, homogeneity_I_Xi_squared, MultiIndex.degree_zero]
  ring

/-! ## Trees Requiring Renormalization for Φ⁴₃

In 3D with space-time white noise: α = -5/2 - ε, β = 2
So |I(Ξ)| = -1/2 - ε < 0
-/

/-- In Φ⁴₃, I(Ξ) has negative homogeneity -/
theorem I_Xi_negative_hom_phi4 :
    homogeneity (-5/2 : ℝ) (2 : ℝ) (I_Xi : TreeSymbol 3) < 0 := by
  simp [homogeneity_I_Xi]
  norm_num

/-- In Φ⁴₃, I(Ξ)² has negative homogeneity -/
theorem I_Xi_squared_negative_hom_phi4 :
    homogeneity (-5/2 : ℝ) (2 : ℝ) (I_Xi_squared : TreeSymbol 3) < 0 := by
  simp [homogeneity_I_Xi_squared]
  norm_num

/-- In Φ⁴₃, I(Ξ)³ has negative homogeneity -/
theorem I_Xi_cubed_negative_hom_phi4 :
    homogeneity (-5/2 : ℝ) (2 : ℝ) (I_Xi_cubed : TreeSymbol 3) < 0 := by
  simp [homogeneity_I_Xi_cubed]
  norm_num

/-! ## Polynomial Operations

The polynomial symbols X^k represent monomials (x - x₀)^k centered at the base point.
-/

/-- The coordinate polynomial X_i (just the i-th variable) -/
def X_coord (i : Fin d) : TreeSymbol d := Poly (MultiIndex.unit i)

/-- Homogeneity of X_i is 1 -/
theorem homogeneity_X_coord (α β : ℝ) (i : Fin d) :
    homogeneity α β (X_coord i : TreeSymbol d) = 1 := by
  simp [X_coord, homogeneity, MultiIndex.degree_unit]

/-- The constant polynomial X^0 = 1 (this is different from `one`) -/
def X_zero : TreeSymbol d := Poly MultiIndex.zero

/-- Homogeneity of X^0 is 0 -/
theorem homogeneity_X_zero (α β : ℝ) :
    homogeneity α β (X_zero : TreeSymbol d) = 0 := by
  simp [X_zero, homogeneity, MultiIndex.degree_zero]

/-! ## Integration with Derivatives

I_k(τ) represents ∫ D^k_y K(x,y) Π_y(τ) dy
-/

/-- Integration with first derivative in direction i:
    I_{e_i}(τ) = ∫ ∂_{y_i} K(x,y) Π_y(τ) dy -/
def I_deriv (i : Fin d) (τ : TreeSymbol d) : TreeSymbol d :=
  Integ (MultiIndex.unit i) τ

/-- Homogeneity of I_{e_i}(τ) is |τ| + β - 1 -/
theorem homogeneity_I_deriv (α β : ℝ) (i : Fin d) (τ : TreeSymbol d) :
    homogeneity α β (I_deriv i τ) = homogeneity α β τ + β - 1 := by
  simp [I_deriv, homogeneity, MultiIndex.degree_unit]

/-! ## KPZ Trees

For KPZ: α = -3/2 - ε, β = 2, so |I(Ξ)| = 1/2 - ε
The problematic tree is I(∂I(Ξ))² which appears in (∇h)²
-/

/-- The derivative of integrated noise: ∂_i I(Ξ) -/
def deriv_I_Xi (i : Fin d) : TreeSymbol d := I_deriv i Xi

/-- Homogeneity of ∂_i I(Ξ) is α + β - 1 -/
theorem homogeneity_deriv_I_Xi (α β : ℝ) (i : Fin d) :
    homogeneity α β (deriv_I_Xi i : TreeSymbol d) = α + β - 1 := by
  simp [deriv_I_Xi, homogeneity_I_deriv, homogeneity_Xi]

/-- For KPZ in 1D, ∂I(Ξ) has homogeneity -1/2 -/
theorem deriv_I_Xi_hom_kpz :
    homogeneity (-3/2 : ℝ) (2 : ℝ) (deriv_I_Xi 0 : TreeSymbol 1) = -1/2 := by
  simp [homogeneity_deriv_I_Xi]
  norm_num

end SPDE.RegularityStructures
