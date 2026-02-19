/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Decorated Trees for Regularity Structures

This file defines the decorated rooted trees that form the basis of regularity structures,
following Hairer's original 2014 paper "A theory of regularity structures".

## Main Definitions

* `MultiIndex` - Multi-indices for polynomial decorations
* `TreeSymbol` - The abstract symbols Ξ (noise), X^k (polynomials), I_k (integration)

## Mathematical Background

In regularity structures, the space T is spanned by decorated trees. Each tree τ
represents a term in the formal expansion of the solution. The key symbols are:

1. **Unit 𝟙**: The multiplicative identity
2. **Noise symbol Ξ**: Represents the driving noise ξ
3. **Polynomial symbols X^k**: Represent monomials (x - x₀)^k
4. **Integration I_k(τ)**: Represents ∫ D^k K(x,y) τ(y) dy
5. **Product τ₁ · τ₂**: Pointwise product

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 3
* Hairer, "Introduction to regularity structures" (Brazilian J. Prob. Stat. 2015)
-/

namespace SPDE.RegularityStructures

open Finset BigOperators

/-! ## Multi-indices -/

/-- A multi-index in d dimensions. Represents exponents (k₁, ..., k_d) for monomials x^k. -/
abbrev MultiIndex (d : ℕ) := Fin d → ℕ

namespace MultiIndex

variable {d : ℕ}

/-- The degree (order) of a multi-index: |k| = Σᵢ kᵢ -/
def degree (k : MultiIndex d) : ℕ := ∑ i, k i

/-- The zero multi-index -/
def zero : MultiIndex d := fun _ => 0

theorem degree_zero : (zero : MultiIndex d).degree = 0 := by
  simp [degree, zero]

/-- Add two multi-indices componentwise -/
def add (k₁ k₂ : MultiIndex d) : MultiIndex d := fun i => k₁ i + k₂ i

theorem degree_add (k₁ k₂ : MultiIndex d) :
    (add k₁ k₂).degree = k₁.degree + k₂.degree := by
  simp [degree, add, Finset.sum_add_distrib]

/-- The i-th unit multi-index e_i -/
def unit (i : Fin d) : MultiIndex d := fun j => if i = j then 1 else 0

theorem degree_unit (i : Fin d) : (unit i : MultiIndex d).degree = 1 := by
  simp only [degree, unit]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_univ]

/-- Factorial of a multi-index: k! = ∏ᵢ (kᵢ)! -/
noncomputable def factorial (k : MultiIndex d) : ℕ := ∏ i, Nat.factorial (k i)

/-- Less than or equal for multi-indices: k ≤ l iff kᵢ ≤ lᵢ for all i -/
def le (k l : MultiIndex d) : Prop := ∀ i, k i ≤ l i

instance : LE (MultiIndex d) := ⟨le⟩

end MultiIndex

/-! ## Abstract Tree Symbols

We define trees inductively. The key symbols are:
- `one`: The unit element 𝟙
- `Xi`: The noise symbol Ξ
- `Poly k`: The polynomial symbol X^k
- `Integ k τ`: The integration symbol I_k(τ)
- `Prod τ₁ τ₂`: The product τ₁ · τ₂
-/

/-- The basic tree symbols for regularity structures.

    Following Hairer 2014 Section 3.1, the symbols are:
    - `one`: The unit element 𝟙 (homogeneity 0)
    - `Xi`: The noise symbol Ξ (homogeneity α = noise regularity)
    - `Poly k`: The polynomial X^k (homogeneity |k|)
    - `Integ k τ`: Integration I_k(τ) = ∫ D^k_y K(x,y) τ(y) dy (homogeneity |τ| + β - |k|)
    - `Prod τ₁ τ₂`: Product τ₁ · τ₂ (homogeneity |τ₁| + |τ₂|)

    The parameter `d` is the spatial dimension. -/
inductive TreeSymbol (d : ℕ) : Type where
  /-- The unit element 𝟙 -/
  | one : TreeSymbol d
  /-- The noise symbol Ξ -/
  | Xi : TreeSymbol d
  /-- Polynomial symbol X^k for multi-index k -/
  | Poly : MultiIndex d → TreeSymbol d
  /-- Integration: I_k(τ) where k is the derivative multi-index -/
  | Integ : MultiIndex d → TreeSymbol d → TreeSymbol d
  /-- Product of two trees -/
  | Prod : TreeSymbol d → TreeSymbol d → TreeSymbol d
  deriving DecidableEq

namespace TreeSymbol

variable {d : ℕ}

/-- Notation for products -/
instance : Mul (TreeSymbol d) where
  mul := Prod

/-- The unit is a multiplicative identity (stated, proof requires more structure) -/
theorem one_mul (τ : TreeSymbol d) : one * τ = Prod one τ := rfl

theorem mul_one (τ : TreeSymbol d) : τ * one = Prod τ one := rfl

/-! ## Tree Complexity

The complexity of a tree bounds the recursion depth. Used for termination proofs. -/

/-- The complexity (size) of a tree. Used for termination of recursive definitions. -/
def complexity : TreeSymbol d → ℕ
  | one => 0
  | Xi => 1
  | Poly _ => 1
  | Integ _ τ => 1 + complexity τ
  | Prod τ₁ τ₂ => 1 + complexity τ₁ + complexity τ₂

/-- Complexity of Integ is greater than its argument -/
theorem complexity_Integ_lt (k : MultiIndex d) (τ : TreeSymbol d) :
    complexity τ < complexity (Integ k τ) := by
  simp only [complexity]
  omega

/-- Complexity of Prod is greater than its arguments -/
theorem complexity_Prod_left_lt (τ₁ τ₂ : TreeSymbol d) :
    complexity τ₁ < complexity (Prod τ₁ τ₂) := by
  simp only [complexity]
  omega

theorem complexity_Prod_right_lt (τ₁ τ₂ : TreeSymbol d) :
    complexity τ₂ < complexity (Prod τ₁ τ₂) := by
  simp only [complexity]
  omega

/-- The number of noise symbols Ξ in a tree -/
def noiseCount : TreeSymbol d → ℕ
  | one => 0
  | Xi => 1
  | Poly _ => 0
  | Integ _ τ => noiseCount τ
  | Prod τ₁ τ₂ => noiseCount τ₁ + noiseCount τ₂

/-- The number of integration symbols in a tree -/
def integCount : TreeSymbol d → ℕ
  | one => 0
  | Xi => 0
  | Poly _ => 0
  | Integ _ τ => 1 + integCount τ
  | Prod τ₁ τ₂ => integCount τ₁ + integCount τ₂

/-- Noise count is bounded by complexity -/
theorem noiseCount_le_complexity (τ : TreeSymbol d) : τ.noiseCount ≤ τ.complexity := by
  induction τ with
  | one => simp [noiseCount, complexity]
  | Xi => simp [noiseCount, complexity]
  | Poly _ => simp [noiseCount, complexity]
  | Integ _ τ ih =>
    simp only [noiseCount, complexity]
    omega
  | Prod τ₁ τ₂ ih1 ih2 =>
    simp only [noiseCount, complexity]
    omega

/-- Integration count is bounded by complexity -/
theorem integCount_le_complexity (τ : TreeSymbol d) : τ.integCount ≤ τ.complexity := by
  induction τ with
  | one => simp [integCount, complexity]
  | Xi => simp [integCount, complexity]
  | Poly _ => simp [integCount, complexity]
  | Integ _ τ ih =>
    simp only [integCount, complexity]
    omega
  | Prod τ₁ τ₂ ih1 ih2 =>
    simp only [integCount, complexity]
    omega

end TreeSymbol

end SPDE.RegularityStructures
