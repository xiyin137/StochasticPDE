/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.RegularityStructures.FixedPoint
import StochasticPDE.RegularityStructures.Models.Canonical

/-!
# BPHZ Renormalization for Regularity Structures

This file formalizes the BPHZ (Bogoliubov-Parasiuk-Hepp-Zimmermann) renormalization
procedure for regularity structures (Hairer 2014, Section 8).

## Main Definitions

* `RenormalizationGroupRS` - The renormalization group acting on models
* `BPHZCharacter` - The BPHZ character computing renormalization constants
* `RenormalizedModel` - The renormalized model Π^{ren}

## Mathematical Background

The BPHZ procedure in regularity structures works as follows:

1. **Identify divergent trees**: Trees τ with |τ| < 0 have divergent expectations
2. **Renormalization group**: G acts on models by Π_x^g τ = Π_x (g · τ)
3. **BPHZ formula**: The renormalization element g ∈ G is computed recursively
   by subtracting divergences from each tree

The key insight (connecting to classical QFT renormalization) is that:
- Trees correspond to Feynman diagrams
- Negative homogeneity corresponds to UV divergence
- The recursive BPHZ formula is the same as in perturbative QFT

Unlike the BHZ (Bruned-Hairer-Zambotti) approach using Hopf algebras, we use
the direct recursive formula from Hairer 2014.

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 8
* Bruned, Hairer, Zambotti, "Algebraic renormalisation of regularity structures" (2019)
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## The Renormalization Group

The structure group G acts on models. Renormalization is achieved by
choosing the right element g ∈ G such that Π^g has finite limits.
-/

/-- The renormalization group for a regularity structure.

    Elements M ∈ G are linear maps M : T → T such that:
    - M preserves the unit: M(1) ≡ 1 (up to coefficient equivalence)
    - M preserves homogeneity sectors: M(T_α) ⊆ ⊕_{β ≤ α} T_β
    - M acts triangularly: (M τ)_α = τ_α + lower order terms

    The group operation is composition. -/
structure RenormGroupElement (d : ℕ) where
  /-- The linear map M : T → T -/
  M : TreeSymbol d → FormalSum d
  /-- Unit preservation (coefficient form): M(1) has coefficient 1 at 1, and 0 elsewhere.
      This is equivalent to M(1) ≡ 1 for evaluation purposes. -/
  unit_preserved_coeff : (M .one).coeff .one = 1
  unit_preserved_other : ∀ τ : TreeSymbol d, τ ≠ .one → (M .one).coeff τ = 0
  /-- Triangularity: The coefficient of τ in M(τ) is 1.
      This means M(τ) = τ + (lower order terms). -/
  triangular : ∀ τ : TreeSymbol d, (M τ).coeff τ = 1
  /-- Off-diagonal constraint: M(σ) has non-zero coefficient at τ ≠ σ only when τ = .one.
      This encodes that M(T_α) ⊆ T_α ⊕ T_0 (only τ and unit terms appear in M τ).
      Combined with triangularity, this means M τ = τ + c • 1 for some constant c.
      This constraint is closed under composition and required for mul.triangular. -/
  off_diagonal : ∀ σ τ : TreeSymbol d, σ ≠ τ → τ ≠ .one → (M σ).coeff τ = 0

namespace RenormGroupElement

variable {d : ℕ}

/-- The identity element -/
def one : RenormGroupElement d where
  M := fun τ => FormalSum.single τ
  unit_preserved_coeff := FormalSum.coeff_single_self .one
  unit_preserved_other := fun τ hτ => FormalSum.coeff_single_ne .one τ hτ
  triangular := fun τ => FormalSum.coeff_single_self τ
  off_diagonal := fun σ τ hστ _hτ => FormalSum.coeff_single_ne σ τ hστ.symm

/-- Composition of renormalization group elements.
    (g * h).M(τ) = g.M applied linearly to h.M(τ)
    If h.M(τ) = Σᵢ cᵢ σᵢ, then (g * h).M(τ) = Σᵢ cᵢ · g.M(σᵢ) -/
noncomputable def mul (g h : RenormGroupElement d) : RenormGroupElement d where
  M := fun τ => FormalSum.bind (h.M τ) g.M
  unit_preserved_coeff := by
    -- (g * h).M(.one) = bind (h.M .one) g.M
    -- Need: coeff .one (bind (h.M .one) g.M) = 1
    -- h.M .one has coeff 1 at .one and 0 elsewhere
    -- By coeff_bind_unit_like, result = (g.M .one).coeff .one = 1
    rw [FormalSum.coeff_bind_unit_like (h.M .one) g.M .one .one
        h.unit_preserved_coeff h.unit_preserved_other]
    exact g.unit_preserved_coeff
  unit_preserved_other := fun τ hτ => by
    -- coeff τ (bind (h.M .one) g.M) = 0 for τ ≠ .one
    -- By coeff_bind_unit_like, result = (g.M .one).coeff τ = 0 (by g.unit_preserved_other)
    rw [FormalSum.coeff_bind_unit_like (h.M .one) g.M .one τ
        h.unit_preserved_coeff h.unit_preserved_other]
    exact g.unit_preserved_other τ hτ
  triangular := fun τ => by
    -- Need: (bind (h.M τ) g.M).coeff τ = 1
    -- Using coeff_bind: the sum Σ_σ (h.M τ).coeff σ * (g.M σ).coeff τ
    -- Key insight: (g.M σ).coeff τ = 0 for ALL σ ≠ τ when τ ≠ .one:
    --   - If σ = .one: (g.M .one).coeff τ = 0 by g.unit_preserved_other
    --   - If σ ≠ .one and σ ≠ τ: (g.M σ).coeff τ = 0 by g.off_diagonal
    -- So the sum simplifies to (h.M τ).coeff τ * (g.M τ).coeff τ = 1 * 1 = 1
    by_cases hτ : τ = .one
    · -- τ = .one case: use unit properties
      subst hτ
      rw [FormalSum.coeff_bind_unit_like (h.M .one) g.M .one .one
          h.unit_preserved_coeff h.unit_preserved_other]
      exact g.triangular .one
    · -- τ ≠ .one case: (g.M σ).coeff τ = 0 for all σ ≠ τ
      have hg_vanish : ∀ σ, σ ≠ τ → (g.M σ).coeff τ = 0 := fun σ hστ => by
        by_cases hσone : σ = .one
        · -- σ = .one: use unit_preserved_other
          subst hσone
          exact g.unit_preserved_other τ hτ
        · -- σ ≠ .one and σ ≠ τ: use off_diagonal
          exact g.off_diagonal σ τ hστ hτ
      -- Now use: sumByTree f g = f.coeff τ * g(τ) when g(σ) = 0 for σ ≠ τ
      rw [FormalSum.coeff_bind]
      -- The foldl computes Σ c * (g.M σ).coeff τ, which equals (coeff τ) * (g.M τ).coeff τ
      have heq : (h.M τ).terms.foldl (fun acc (p : ℝ × TreeSymbol d) =>
          acc + p.1 * (g.M p.2).coeff τ) 0 =
          FormalSum.sumByTree (h.M τ) (fun σ => (g.M σ).coeff τ) := rfl
      rw [heq]
      -- Use foldl_mul_split with g' σ = (g.M σ).coeff τ, which is 0 for σ ≠ τ
      -- foldl_mul_split says: if coeff ρ = 0 for ρ ≠ τ IN THE FORMAL SUM,
      -- then sumByTree = coeff τ * g τ
      -- But we have: g(ρ) = 0 for ρ ≠ τ in the FUNCTION
      -- We need the dual: sumByTree f g = f.coeff τ * g τ when g vanishes off τ
      -- Direct computation: each term (c, σ) contributes c * g(σ)
      -- If σ ≠ τ: c * g(σ) = c * 0 = 0
      -- If σ = τ: c * g(τ)
      -- Sum = Σ_{σ = τ} c * g(τ) = (Σ_{σ = τ} c) * g(τ) = coeff τ * g(τ)
      -- Direct proof: sumByTree f g = f.coeff τ * g τ when g vanishes off τ
      -- We prove: foldl (acc + c * g σ) 0 l = foldl (acc + c when σ=τ) 0 l * g τ
      have hsum : FormalSum.sumByTree (h.M τ) (fun σ => (g.M σ).coeff τ) =
          (h.M τ).coeff τ * (g.M τ).coeff τ := by
        -- Key: g(σ) = 0 for σ ≠ τ, so each term c * g(σ) = c * g(τ) when σ = τ, else 0
        -- Prove by showing both foldls agree via a more direct argument
        -- Use the fact that sumByTree can be rewritten when g is zero off one point
        -- Define the helper with τ as a parameter to keep it in scope
        let τ' := τ  -- Capture τ for use in nested proofs
        have hkey : ∀ l : List (ℝ × TreeSymbol d),
            l.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * (g.M p.2).coeff τ') 0 =
            l.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ' then acc + p.1 else acc) 0 *
              (g.M τ').coeff τ' := by
          intro l
          induction l with
          | nil => simp only [List.foldl_nil, zero_mul]
          | cons hd tl ih =>
            simp only [List.foldl_cons]
            by_cases hσ : hd.2 = τ'
            · -- hd.2 = τ': (g.M τ').coeff τ' appears
              simp only [hσ, ite_true]
              -- LHS: foldl (...) (0 + hd.1 * (g.M τ').coeff τ') tl
              -- RHS: foldl (if σ = τ' ...) (0 + hd.1) tl * (g.M τ').coeff τ'
              -- Use that foldl with init x = x + foldl with init 0
              have hshift1 : ∀ (l' : List (ℝ × TreeSymbol d)) (x : ℝ),
                  l'.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * (g.M p.2).coeff τ') x =
                  x + l'.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * (g.M p.2).coeff τ') 0 := by
                intro l' x
                induction l' generalizing x with
                | nil => simp
                | cons h' t' ih' =>
                  simp only [List.foldl_cons]
                  rw [ih' (x + h'.1 * (g.M h'.2).coeff τ'), ih' (0 + h'.1 * (g.M h'.2).coeff τ')]
                  ring
              have hshift2 : ∀ (l' : List (ℝ × TreeSymbol d)) (x : ℝ),
                  l'.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ' then acc + p.1 else acc) x =
                  x + l'.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ' then acc + p.1 else acc) 0 := by
                intro l' x
                induction l' generalizing x with
                | nil => simp
                | cons h' t' ih' =>
                  simp only [List.foldl_cons]
                  by_cases hh : h'.2 = τ'
                  · simp only [hh, ite_true]
                    rw [ih' (x + h'.1), ih' (0 + h'.1)]
                    ring
                  · simp only [hh, ite_false]
                    exact ih' x
              rw [hshift1, hshift2, ih]
              ring
            · -- hd.2 ≠ τ': (g.M hd.2).coeff τ' = 0
              have hz : (g.M hd.2).coeff τ' = 0 := hg_vanish hd.2 hσ
              rw [hz, mul_zero, add_zero]
              simp only [hσ, ite_false]
              exact ih
        exact hkey (h.M τ').terms
      rw [hsum, h.triangular τ, g.triangular τ]
      ring
  off_diagonal := fun σ τ hστ hτone => by
    -- Need: (bind (h.M σ) g.M).coeff τ = 0 when σ ≠ τ and τ ≠ .one
    -- Strategy: Use sumByTree_g_unique. The function ρ ↦ (g.M ρ).coeff τ is:
    --   - 1 at ρ = τ (by g.triangular)
    --   - 0 at ρ ≠ τ when ρ ≠ .one (by g.off_diagonal)
    --   - 0 at ρ = .one when τ ≠ .one (by g.unit_preserved_other)
    -- So it's non-zero only at τ. By sumByTree_g_unique:
    --   sumByTree (h.M σ) (ρ ↦ (g.M ρ).coeff τ) = (h.M σ).coeff τ * (g.M τ).coeff τ
    -- By h.off_diagonal (σ ≠ τ, τ ≠ .one): (h.M σ).coeff τ = 0
    rw [FormalSum.coeff_bind_as_sumByTree]
    -- Show that ρ ↦ (g.M ρ).coeff τ is zero everywhere except at τ
    have hg_zero : ∀ ρ ≠ τ, (g.M ρ).coeff τ = 0 := by
      intro ρ hρτ
      by_cases hρone : ρ = .one
      · rw [hρone]; exact g.unit_preserved_other τ hτone
      · exact g.off_diagonal ρ τ hρτ hτone
    rw [FormalSum.sumByTree_g_unique (h.M σ) τ (fun ρ => (g.M ρ).coeff τ) hg_zero]
    -- Now we have: (h.M σ).coeff τ * (g.M τ).coeff τ
    have hcoeff_zero : (h.M σ).coeff τ = 0 := h.off_diagonal σ τ hστ hτone
    rw [hcoeff_zero, zero_mul]

/-- The lower-order part of a renormalization group element.
    If M(τ) = τ + L(τ), returns L(τ). -/
noncomputable def lowerOrderPart (g : RenormGroupElement d) (τ : TreeSymbol d) : FormalSum d :=
  g.M τ - FormalSum.single τ

/-- Apply the lower-order part n times (L^n) -/
noncomputable def lowerOrderPower (g : RenormGroupElement d) : ℕ → TreeSymbol d → FormalSum d
  | 0, τ => FormalSum.single τ
  | n + 1, τ => FormalSum.bind (lowerOrderPower g n τ) (lowerOrderPart g)

/-- Inverse element using Neumann series truncated at complexity bound.
    For a triangular operator M(τ) = τ + L(τ) where L has strictly lower homogeneity,
    the inverse is M⁻¹ = Id - L + L² - L³ + ... (Neumann series).
    Since L is nilpotent on finite-complexity trees, this terminates.

    We truncate at n = complexity(τ) + 1 since L^n(τ) = 0 for n > complexity(τ). -/
noncomputable def inv (g : RenormGroupElement d) : RenormGroupElement d where
  M := fun τ =>
    -- M⁻¹(τ) = Σₙ (-1)^n L^n(τ)
    -- Truncate at complexity(τ) + 1
    let bound := τ.complexity + 1
    (List.range bound).foldl
      (fun acc n =>
        acc + (if n % 2 = 0 then (1 : ℝ) else (-1 : ℝ)) • lowerOrderPower g n τ)
      FormalSum.zero
  unit_preserved_coeff := by
    -- For τ = .one, complexity = 0, so bound = 1
    -- Only the n=0 term contributes: 1 * L^0(.one) = single(.one)
    simp only [TreeSymbol.complexity]
    -- List.range 1 = [0]
    simp only [List.range_succ, List.range_zero, List.nil_append]
    simp only [List.foldl_cons, List.foldl_nil]
    -- Goal: (FormalSum.zero + (if 0 % 2 = 0 then 1 else -1) • lowerOrderPower g 0 .one).coeff .one = 1
    simp only [ite_true, lowerOrderPower]
    -- Goal: (FormalSum.zero + 1 • FormalSum.single .one).coeff .one = 1
    rw [FormalSum.coeff_add, FormalSum.coeff_smul]
    simp only [FormalSum.zero, FormalSum.coeff, List.foldl_nil]
    -- Goal: 0 + 1 * (single .one).coeff .one = 1
    -- (single .one).terms = [(1, .one)]
    simp only [FormalSum.single, List.foldl_cons, List.foldl_nil, ite_true]
    ring
  unit_preserved_other := fun τ hτ => by
    -- For τ ≠ .one, coeff τ in inv.M(.one) = 0
    -- Since complexity(.one) = 0, bound = 1, only n=0 term: single(.one)
    simp only [TreeSymbol.complexity]
    simp only [List.range_succ, List.range_zero, List.nil_append]
    simp only [List.foldl_cons, List.foldl_nil]
    simp only [ite_true, lowerOrderPower]
    rw [FormalSum.coeff_add, FormalSum.coeff_smul]
    simp only [FormalSum.zero, FormalSum.coeff, List.foldl_nil]
    -- (single .one).coeff τ = 0 when τ ≠ .one
    simp only [FormalSum.single, List.foldl_cons, List.foldl_nil]
    -- The condition is .one = τ, which is false since τ ≠ .one
    simp only [hτ.symm, ite_false]
    ring
  triangular := fun τ => by
    -- The n=0 term is L^0(τ) = single τ with coefficient 1
    -- Higher n terms: L^n(τ) for n ≥ 1 has coeff 0 at τ (L lowers homogeneity)
    -- So total coeff at τ is 1*1 = 1
    -- Full proof requires lemmas about coeff, smul, foldl interaction
    sorry
  off_diagonal := fun σ τ hστ hτone => by
    -- The inverse preserves the off-diagonal property
    -- inv.M σ = Σₙ (-1)^n L^n(σ)
    -- For each term L^n(σ), we need to show coeff τ = 0 when σ ≠ τ and τ ≠ .one
    -- L^0(σ) = single σ, so coeff τ = 0 when τ ≠ σ
    -- L^n(σ) for n ≥ 1 involves only σ and .one terms (by g.off_diagonal)
    -- So coeff τ = 0 for τ ≠ σ and τ ≠ .one
    sorry  -- Requires induction on Neumann series

instance : One (RenormGroupElement d) := ⟨one⟩
noncomputable instance : Mul (RenormGroupElement d) := ⟨mul⟩
noncomputable instance : Inv (RenormGroupElement d) := ⟨inv⟩

/-- Right identity: g * 1 = g -/
theorem mul_one (g : RenormGroupElement d) : mul g one = g := by
  simp only [mul, one]
  -- (mul g one).M τ = bind (one.M τ) g.M = bind (single τ) g.M
  -- We need: bind (single τ) g.M = g.M τ
  congr 1
  ext τ
  exact FormalSum.bind_single τ g.M

/-- Left identity: 1 * g = g -/
theorem one_mul (g : RenormGroupElement d) : mul one g = g := by
  simp only [mul, one]
  -- (mul one g).M τ = bind (g.M τ) one.M = bind (g.M τ) single
  -- We need: bind (g.M τ) single = g.M τ
  congr 1
  ext τ
  exact FormalSum.bind_single_right (g.M τ)

end RenormGroupElement

/-! ## Action of G on Models

The renormalization group acts on models by:
  Π^g_x τ = Π_x (g · τ)

This changes the model while preserving its analytical structure.
-/

/-- Evaluate a FormalSum using a model's pairing function.
    For s = Σᵢ cᵢ τᵢ, returns Σᵢ cᵢ · ⟨Π_x τᵢ, φ^λ_x⟩ -/
noncomputable def evalFormalSum {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (s : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) : ℝ :=
  s.terms.foldl (fun acc (c, τ) => acc + c * model.Pi.pairing τ x φ scale) 0

/-- Evaluation of single gives the pairing value -/
theorem evalFormalSum_single {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (τ : TreeSymbol d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) :
    evalFormalSum model (FormalSum.single τ) x φ scale = model.Pi.pairing τ x φ scale := by
  simp only [evalFormalSum, FormalSum.single, List.foldl_cons, List.foldl_nil]
  ring

/-- Helper: the eval foldl function is shift-invariant -/
private theorem evalFoldl_shift {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ)
    (l : List (ℝ × TreeSymbol d)) (init : ℝ) :
    l.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * model.Pi.pairing p.2 x φ scale) init =
    init + l.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * model.Pi.pairing p.2 x φ scale) 0 := by
  induction l generalizing init with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    simp only [List.foldl_cons]
    rw [ih (init + hd.1 * model.Pi.pairing hd.2 x φ scale)]
    rw [ih (0 + hd.1 * model.Pi.pairing hd.2 x φ scale)]
    ring

/-- Evaluation distributes over addition -/
theorem evalFormalSum_add {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (s₁ s₂ : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) :
    evalFormalSum model (s₁ + s₂) x φ scale =
    evalFormalSum model s₁ x φ scale + evalFormalSum model s₂ x φ scale := by
  unfold evalFormalSum
  show (s₁ + s₂).terms.foldl _ 0 = s₁.terms.foldl _ 0 + s₂.terms.foldl _ 0
  have heq : (s₁ + s₂).terms = s₁.terms ++ s₂.terms := rfl
  rw [heq, List.foldl_append]
  rw [evalFoldl_shift]

/-- Evaluation of scalar multiple -/
theorem evalFormalSum_smul {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (c : ℝ) (s : FormalSum d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ) :
    evalFormalSum model (c • s) x φ scale = c * evalFormalSum model s x φ scale := by
  unfold evalFormalSum
  have heq : (c • s).terms = s.terms.map (fun (a, τ) => (c * a, τ)) := rfl
  rw [heq]
  induction s.terms with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [evalFoldl_shift _ _ _ _ _ (0 + c * hd.1 * _)]
    rw [evalFoldl_shift _ _ _ _ _ (0 + hd.1 * _)]
    rw [ih]
    ring

/-- evalFormalSum gives g σ when f is "unit-like" at σ: coeff σ = 1, coeff τ = 0 for τ ≠ σ.
    Combined with model.Pi.unit_property, this proves evalFormalSum respects the unit. -/
theorem evalFormalSum_unit_like {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params) (f : FormalSum d) (σ : TreeSymbol d)
    (x : Fin d → ℝ) (φ : TestFunction d) (scale : ℝ)
    (hσ : f.coeff σ = 1) (h0 : ∀ τ ≠ σ, f.coeff τ = 0) :
    evalFormalSum model f x φ scale = model.Pi.pairing σ x φ scale := by
  -- The key is that evalFormalSum f g = Σ_τ (coeff τ f) * g(τ) when grouped by tree
  -- Since coeff σ = 1 and coeff τ = 0 for τ ≠ σ, we get 1 * g(σ) = g(σ)
  unfold evalFormalSum
  -- We use the fact that sumByTree f g = Σ_τ (coeff τ) * g(τ)
  -- and this is exactly what we need to show
  have heq : f.terms.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      acc + p.1 * model.Pi.pairing p.2 x φ scale) 0 =
      FormalSum.sumByTree f (fun τ => model.Pi.pairing τ x φ scale) := rfl
  rw [heq]
  exact FormalSum.sumByTree_eq_single' f σ _ hσ h0

/-- The action of the renormalization group on models.

    Given g ∈ G and a model (Π, Γ), the renormalized model is:
    - Π^g_x τ = Π_x (M_g · τ)  (evaluate g.M(τ) using the original model)
    - Γ^g_{xy} = M_g ∘ Γ_{xy} ∘ M_g⁻¹  (composition of linear maps)

    For the Gamma action, since all maps are linear:
    - First apply g⁻¹ to τ: g.inv.M τ gives a FormalSum
    - Then apply original Γ_{xy} to each tree in the sum (via bind)
    - Then apply g to the result (via bind)

    Reference: Hairer 2014, Section 8 -/
noncomputable def renormAction {d : ℕ} {params : ModelParameters d}
    (g : RenormGroupElement d) (model : AdmissibleModel d params) :
    AdmissibleModel d params where
  Pi := {
    pairing := fun τ x φ scale =>
      -- Π^g_x τ = Σᵢ cᵢ · ⟨Π_x σᵢ, φ⟩ where g.M(τ) = Σᵢ cᵢ σᵢ
      evalFormalSum model (g.M τ) x φ scale
    unit_property := fun x φ scale hs_pos hs_le => by
      -- evalFormalSum model (g.M .one) x φ scale = 1
      -- Using: g.unit_preserved_coeff : (g.M .one).coeff .one = 1
      --        g.unit_preserved_other : ∀ τ ≠ .one, (g.M .one).coeff τ = 0
      --        model.Pi.unit_property : model.Pi.pairing .one x φ scale = 1
      rw [evalFormalSum_unit_like model (g.M .one) .one x φ scale
          g.unit_preserved_coeff g.unit_preserved_other]
      exact model.Pi.unit_property x φ scale hs_pos hs_le
  }
  Gamma := {
    Gamma := fun x y τ =>
      -- Γ^g_{xy}(τ) = M_g(Γ_{xy}(M_g⁻¹(τ)))
      -- Step 1: Apply g⁻¹ to τ to get g.inv.M τ : FormalSum d
      -- Step 2: Extend Γ_{xy} to FormalSum by linearity (via bind)
      -- Step 3: Apply g.M to the result (via bind)
      let invApplied := g.inv.M τ                            -- FormalSum d
      let gammaApplied := FormalSum.bind invApplied (model.Gamma.Gamma x y)  -- FormalSum d
      FormalSum.bind gammaApplied g.M                        -- FormalSum d
    self_eq_id := fun x τ => by
      -- Need: bind (bind (g.inv.M τ) (Γ_xx)) g.M = single τ
      -- Since Γ_xx τ = single τ (identity), and g * g⁻¹ = id
      -- First unfold the let bindings
      simp only []
      -- Step 1: bind (g.inv.M τ) (Γ_xx) = bind (g.inv.M τ) single = g.inv.M τ
      have h1 : FormalSum.bind (g.inv.M τ) (model.Gamma.Gamma x x) =
                FormalSum.bind (g.inv.M τ) FormalSum.single := by
        congr 1
        ext σ
        exact model.Gamma.self_eq_id x σ
      rw [h1, FormalSum.bind_single_right]
      -- Need: bind (g.inv.M τ) g.M = single τ
      -- This is g * g⁻¹ = id applied to τ
      sorry  -- Requires: mul g (inv g) = one, i.e., g * g⁻¹ = id
    cocycle := fun x y z τ => by
      -- Cocycle condition: bind (bind (inv τ) (Γ_yz)) g.M composed with Γ_xy
      -- equals direct Γ_xz application
      -- This follows from the cocycle property of the original Γ
      sorry  -- Requires careful tracking of compositions
  }
  bound_const := model.bound_const
  bound_pos := model.bound_pos
  regularity_index := model.regularity_index
  analytical_bound := sorry  -- Renormalized model still satisfies bounds
  consistency := sorry

/-! ## Trees Requiring Renormalization

A tree τ requires renormalization if |τ| < 0. For such trees, the
naive model Π_x τ has divergent expectations that must be subtracted.
-/

/-- The set of trees requiring renormalization at level n.
    These are trees with:
    - Negative homogeneity: |τ| < 0
    - Complexity at most n -/
def treesRequiringRenorm (d : ℕ) (params : ModelParameters d) (n : ℕ) :
    Set (TreeSymbol d) :=
  { τ | τ.complexity ≤ n ∧
        homogeneity params.noiseRegularity params.kernelOrder τ < 0 }

/-! ## The BPHZ Character

The BPHZ character computes the renormalization constants recursively.
For each tree τ with |τ| < 0, we compute the counterterm:

  g_τ = -E[Π^{ren}_x τ] + (lower order corrections)

This is the direct approach from Hairer 2014, without Hopf algebras.
-/

/-- The BPHZ character g : T → ℝ.

    For each tree τ, g(τ) is the renormalization constant. The character
    is computed recursively:
    - g(1) = 0 (unit needs no renormalization)
    - g(Ξ) = 0 (noise is already normalized)
    - g(X^k) = 0 (polynomials need no renormalization)
    - g(τ) = -E[Π_0 τ] + (recursive corrections) for |τ| < 0 -/
structure BPHZCharacter (d : ℕ) (params : ModelParameters d) where
  /-- The character value g(τ) for each tree -/
  g : TreeSymbol d → ℝ
  /-- Unit: g(1) = 0 -/
  unit_zero : g .one = 0
  /-- Noise: g(Ξ) = 0 -/
  noise_zero : g .Xi = 0
  /-- Polynomial: g(X^k) = 0 -/
  poly_zero : ∀ k : MultiIndex d, g (.Poly k) = 0
  /-- Subcritical trees: g(τ) = 0 when |τ| ≥ 0 -/
  subcritical_zero : ∀ τ : TreeSymbol d,
    homogeneity params.noiseRegularity params.kernelOrder τ ≥ 0 → g τ = 0

namespace BPHZCharacter

variable {d : ℕ} {params : ModelParameters d}

/-- The renormalization element in G induced by the BPHZ character.
    This element g ∈ G is defined by M_g τ = τ + g(τ) · 1 -/
noncomputable def toGroupElement (char : BPHZCharacter d params) : RenormGroupElement d where
  M := fun τ => FormalSum.single τ + (char.g τ) • FormalSum.single .one
  unit_preserved_coeff := by
    -- coeff .one (single .one + g(.one) • single .one)
    -- = coeff .one (single .one) + g(.one) * coeff .one (single .one)
    -- = 1 + 0 * 1 = 1 (since char.unit_zero)
    rw [FormalSum.coeff_add, FormalSum.coeff_smul, FormalSum.coeff_single_self,
        char.unit_zero]
    ring
  unit_preserved_other := fun τ hτ => by
    -- coeff τ (single .one + g(.one) • single .one) = 0 for τ ≠ .one
    rw [FormalSum.coeff_add, FormalSum.coeff_smul,
        FormalSum.coeff_single_ne .one τ hτ]
    ring
  triangular := fun τ => by
    -- coeff τ (single τ + g(τ) • single 1) = coeff τ (single τ) + coeff τ (g(τ) • single 1)
    rw [FormalSum.coeff_add, FormalSum.coeff_smul, FormalSum.coeff_single_self]
    -- = 1 + g(τ) * coeff τ (single 1)
    by_cases hτ : τ = .one
    · -- τ = 1: coeff 1 (single 1) = 1, but char.g 1 = 0
      subst hτ
      rw [FormalSum.coeff_single_self, char.unit_zero]
      ring
    · -- τ ≠ 1: coeff τ (single 1) = 0
      rw [FormalSum.coeff_single_ne .one τ hτ]
      ring
  off_diagonal := fun σ τ hστ hτone => by
    -- M σ = single σ + g(σ) • single .one
    -- coeff τ (M σ) = coeff τ (single σ) + g(σ) * coeff τ (single .one)
    -- = 0 + g(σ) * 0 = 0 (since τ ≠ σ and τ ≠ .one)
    rw [FormalSum.coeff_add, FormalSum.coeff_smul,
        FormalSum.coeff_single_ne σ τ hστ.symm,
        FormalSum.coeff_single_ne .one τ hτone]
    ring

/-- Coefficient structure of BPHZ character's group element.
    For τ ≠ .one: coeff σ (M τ) = 1 if σ = τ, g(τ) if σ = .one, 0 otherwise -/
theorem toGroupElement_coeff_structure (char : BPHZCharacter d params) (τ σ : TreeSymbol d) :
    (char.toGroupElement.M τ).coeff σ =
      if σ = τ then 1
      else if σ = .one then char.g τ
      else 0 := by
  simp only [toGroupElement]
  rw [FormalSum.coeff_add, FormalSum.coeff_smul]
  by_cases hστ : σ = τ
  · subst hστ
    simp only [ite_true, FormalSum.coeff_single_self]
    by_cases hσone : σ = .one
    · subst hσone
      simp only [FormalSum.coeff_single_self, char.unit_zero]
      ring
    · simp only [FormalSum.coeff_single_ne (TreeSymbol.one) σ hσone, mul_zero, add_zero]
  · simp only [hστ, ite_false]
    have hne : σ ≠ τ := hστ
    rw [FormalSum.coeff_single_ne τ σ hne, zero_add]
    by_cases hσone : σ = .one
    · subst hσone
      simp only [ite_true, FormalSum.coeff_single_self]
      ring
    · simp only [hσone, ite_false, FormalSum.coeff_single_ne (TreeSymbol.one) σ hσone, mul_zero]

/-- Key property: for BPHZ characters, coeff τ (g.M σ) = 0 when σ ≠ τ and τ ≠ .one.
    This is crucial for proving multiplication preserves triangularity. -/
theorem toGroupElement_coeff_off_diagonal (char : BPHZCharacter d params)
    (σ τ : TreeSymbol d) (hστ : σ ≠ τ) (hτone : τ ≠ .one) :
    (char.toGroupElement.M σ).coeff τ = 0 := by
  rw [toGroupElement_coeff_structure]
  simp only [hστ.symm, ite_false, hτone, ite_false]

/-- The lower-order part for BPHZ characters has the form g(τ) • single .one (in coefficient sense) -/
theorem toGroupElement_lowerOrderPart_coeff (char : BPHZCharacter d params) (τ σ : TreeSymbol d) :
    (RenormGroupElement.lowerOrderPart char.toGroupElement τ).coeff σ =
    ((char.g τ) • FormalSum.single TreeSymbol.one).coeff σ := by
  -- Compute RHS: (g(τ) • single 1).coeff σ = g(τ) * (single 1).coeff σ
  rw [FormalSum.coeff_smul]
  -- Compute LHS: lowerOrderPart = M τ - single τ
  unfold RenormGroupElement.lowerOrderPart
  simp only [toGroupElement]
  -- (single τ + g(τ) • single 1 - single τ).coeff σ
  -- Use Sub instance which is defined as add f (neg g)
  have hsub : (FormalSum.single τ + char.g τ • FormalSum.single TreeSymbol.one -
               FormalSum.single τ).coeff σ =
              (FormalSum.single τ + char.g τ • FormalSum.single TreeSymbol.one).coeff σ +
              (-(FormalSum.single τ)).coeff σ := by
    show (FormalSum.sub _ _).coeff σ = _
    simp only [FormalSum.sub]
    exact FormalSum.coeff_add _ _ σ
  rw [hsub, FormalSum.coeff_add, FormalSum.coeff_smul]
  -- Compute coeff of negation
  have hneg : (FormalSum.neg (FormalSum.single τ)).coeff σ = -((FormalSum.single τ).coeff σ) := by
    simp only [FormalSum.neg, FormalSum.coeff, FormalSum.single]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    -- Goal: (if τ = σ then -1 else 0) = -(if τ = σ then 1 else 0)
    by_cases h : τ = σ
    · simp only [h, ite_true]; ring
    · simp only [h, ite_false]; ring
  show (FormalSum.single τ).coeff σ + char.g τ * (FormalSum.single TreeSymbol.one).coeff σ +
       (FormalSum.neg (FormalSum.single τ)).coeff σ = char.g τ * (FormalSum.single TreeSymbol.one).coeff σ
  rw [hneg]
  by_cases hστ : σ = τ
  · subst hστ
    rw [FormalSum.coeff_single_self]
    by_cases hσone : σ = TreeSymbol.one
    · subst hσone; rw [FormalSum.coeff_single_self, char.unit_zero]; ring
    · rw [FormalSum.coeff_single_ne (TreeSymbol.one) σ hσone]; ring
  · rw [FormalSum.coeff_single_ne τ σ hστ]
    by_cases hσone : σ = TreeSymbol.one
    · subst hσone; rw [FormalSum.coeff_single_self]; ring
    · rw [FormalSum.coeff_single_ne (TreeSymbol.one) σ hσone]; ring

/-- The inverse formula for BPHZ characters: inv.M τ = single τ - g(τ) • single .one
    This follows from the Neumann series truncating at n=1 due to g(.one) = 0. -/
theorem toGroupElement_inv_formula (char : BPHZCharacter d params) (τ : TreeSymbol d) :
    ∀ σ : TreeSymbol d, (char.toGroupElement.inv.M τ).coeff σ =
      if σ = τ then 1
      else if σ = .one then -(char.g τ)
      else 0 := by
  -- The Neumann series: inv.M τ = Σ_n (-1)^n L^n(τ)
  -- For BPHZ: L τ = M τ - single τ = g(τ) • single .one
  -- L^0 τ = single τ
  -- L^1 τ = g(τ) • single .one
  -- L^n τ = 0 for n ≥ 2 (since g(.one) = 0)
  -- So: inv.M τ = single τ - g(τ) • single .one
  intro σ
  -- This requires showing the foldl over range gives the expected result
  -- The proof involves:
  -- 1. lowerOrderPart g τ = g(τ) • single .one
  -- 2. lowerOrderPower g 0 τ = single τ
  -- 3. lowerOrderPower g 1 τ = g(τ) • single .one
  -- 4. lowerOrderPower g n τ = 0 for n ≥ 2
  sorry

/-- Verification that inv is a right inverse for BPHZ characters (coefficient form):
    The bind of inv.M τ with M has the same coefficients as single τ.

    coeff σ (bind (inv.M τ) M) = coeff σ (single τ)

    This is the key property needed for renormalization. -/
theorem toGroupElement_mul_inv_eq_id_coeff (char : BPHZCharacter d params) (τ σ : TreeSymbol d) :
    (FormalSum.bind (char.toGroupElement.inv.M τ) char.toGroupElement.M).coeff σ =
    (FormalSum.single τ).coeff σ := by
  -- Use coeff_bind: coeff σ (bind f g) = Σ_ρ (f.coeff ρ) * (g ρ).coeff σ
  rw [FormalSum.coeff_bind]
  -- RHS: (single τ).coeff σ = 1 if σ = τ, 0 otherwise
  by_cases hστ : σ = τ
  · -- Case σ = τ: need to show the sum equals 1
    subst hστ
    rw [FormalSum.coeff_single_self]
    -- The sum is: Σ_ρ (inv.M τ).coeff ρ * (M ρ).coeff τ
    -- Using inv_formula: (inv.M τ).coeff τ = 1, (inv.M τ).coeff 1 = -g(τ), others = 0
    -- (M τ).coeff τ = 1, (M 1).coeff τ = 0 (since τ ≠ 1 generally, or g(1) = 0)
    -- So sum = 1 * 1 + (-g(τ)) * 0 = 1
    sorry
  · -- Case σ ≠ τ: need to show the sum equals 0
    rw [FormalSum.coeff_single_ne τ σ hστ]
    -- The sum is: Σ_ρ (inv.M τ).coeff ρ * (M ρ).coeff σ
    -- For σ = 1: sum = 1 * g(τ) + (-g(τ)) * 1 = 0
    -- For σ ≠ 1, σ ≠ τ: all terms are 0
    sorry

end BPHZCharacter

/-! ## The Renormalized Model

The BPHZ renormalization produces a model Π^{ren} that:
1. Agrees with Π on subcritical trees (|τ| ≥ 0)
2. Has finite limits on critical trees (|τ| < 0)
3. Is universal: independent of the mollification

This is Theorem 8.3 from Hairer 2014.
-/

/-- The renormalized model Π^{ren} = Π^g where g is the BPHZ element.

    Key properties:
    - Π^{ren}_x τ = Π_x τ for subcritical τ
    - E[Π^{ren}_x τ] = 0 for critical τ (divergences subtracted)
    - Π^{ren} has a finite limit as ε → 0 -/
noncomputable def renormalizedModel {d : ℕ} {params : ModelParameters d}
    (model : AdmissibleModel d params)
    (char : BPHZCharacter d params) : AdmissibleModel d params :=
  renormAction (char.toGroupElement) model

/-- The BPHZ renormalization theorem (Hairer 2014, Theorem 8.3).

    For the canonical model Π^ε built from mollified noise ξ_ε:
    1. There exists a BPHZ character g_ε
    2. The renormalized model Π^{ε,ren} = Π^{ε,g_ε} has a limit as ε → 0
    3. The limit is independent of the mollification (universality) -/
theorem bphz_renormalization {d : ℕ} {params : ModelParameters d}
    (data : CanonicalModelData d params) (γ : ℝ) (hγ : γ > 0) :
    -- For each ε > 0, there exists a BPHZ character
    ∀ ε > 0, ∃ char_ε : BPHZCharacter d params,
    -- Such that the renormalized models converge
    ∃ model_limit : AdmissibleModel d params,
    ∀ δ > 0, ∃ ε₀ > 0, ∀ ε' : ℝ, ∀ hε' : 0 < ε', ε' < ε₀ →
      -- The distance between renormalized model and limit is less than δ
      AdmissibleModel.distance (renormalizedModel (canonical_model data ε' hε') char_ε) model_limit γ < δ := by
  sorry  -- This is the main renormalization theorem

/-! ## Explicit BPHZ Formula

The BPHZ character is computed recursively. For a tree τ with |τ| < 0:

  g(τ) = -E[Π_0(τ - Σ_{σ ⊂ τ, |σ| < 0} g(σ) · τ/σ)]

where the sum is over divergent subtrees σ of τ, and τ/σ denotes the
contraction of σ in τ.
-/

/-- The recursive BPHZ formula for the character.

    For a tree τ with |τ| < 0:
    g(τ) = -E[Π_0(τ)] + (sum over divergent subtrees)

    This is computed recursively in order of increasing complexity.
    The key property is that g(τ) depends only on g(σ) for subtrees σ ⊊ τ
    with |σ| < 0 (divergent proper subtrees). -/
theorem bphz_recursive_formula {d : ℕ} {params : ModelParameters d}
    (char : BPHZCharacter d params)
    (τ : TreeSymbol d)
    (hτ : homogeneity params.noiseRegularity params.kernelOrder τ < 0) :
    -- The BPHZ character g(τ) is determined by a recursive formula
    -- involving only trees of strictly smaller complexity
    ∀ τ' : TreeSymbol d,
      τ'.complexity < τ.complexity →
      homogeneity params.noiseRegularity params.kernelOrder τ' < 0 →
      -- The character at τ depends on characters at smaller trees
      -- This expresses the recursive structure of BPHZ renormalization
      |char.g τ| ≤ |char.g τ'| + τ.complexity := by
  sorry  -- Requires subtree enumeration and recursive bound analysis

/-! ## Φ⁴₃ Renormalization

For the 3D Φ⁴ model, the trees requiring renormalization are:
- I(Ξ)² with |τ| = -1
- I(Ξ)³ with |τ| = -3/2
- I(I(Ξ)² · Ξ) with |τ| = -1/2

Each gives a divergent counterterm (mass renormalization).
-/

/-- The renormalization constants for Φ⁴₃.

    The key divergent trees are:
    - τ₁ = I(Ξ)² : gives mass counterterm δm²
    - τ₂ = I(Ξ)³ : finite in 3D
    - τ₃ = I(I(Ξ)² · Ξ) : gives coupling counterterm -/
structure Phi4RenormConstants where
  /-- Mass counterterm δm²(ε) -/
  mass_counterterm : ℝ → ℝ
  /-- Logarithmic divergence coefficient -/
  log_coeff : ℝ
  /-- Logarithmic divergence: |δm²(ε) - c log(1/ε)| is bounded as ε → 0 -/
  log_divergence : ∃ M : ℝ, ∀ ε > 0,
    |mass_counterterm ε - log_coeff * Real.log (1/ε)| ≤ M
  /-- Coupling counterterm (finite in 3D) -/
  coupling_counterterm : ℝ → ℝ
  /-- Coupling has a finite limit -/
  coupling_finite : ∃ limit : ℝ, Filter.Tendsto coupling_counterterm
    (nhdsWithin 0 (Set.Ioi 0)) (nhds limit)

/-! ## KPZ Renormalization

For the KPZ equation in 1D, the divergent tree is I(∂I(Ξ))²
corresponding to the (∇h)² nonlinearity. The renormalization
gives a single divergent constant (energy counterterm).
-/

/-- The renormalization constants for KPZ.

    The key divergent tree is τ = I((∂I(Ξ))²) with |τ| = 0.
    This is at the boundary and requires a single counterterm. -/
structure KPZRenormConstants where
  /-- The counterterm C(ε) -/
  counterterm : ℝ → ℝ
  /-- Linear divergence coefficient -/
  linear_coeff : ℝ
  /-- Linear divergence: |C(ε) - c/ε| is bounded as ε → 0 -/
  linear_divergence : ∃ M : ℝ, ∀ ε > 0,
    |counterterm ε - linear_coeff / ε| ≤ M

end SPDE.RegularityStructures
