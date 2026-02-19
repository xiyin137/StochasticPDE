/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.RegularityStructures.Trees.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Homogeneity for Decorated Trees

This file defines the homogeneity assignment |τ| ∈ ℝ for each decorated tree τ.

## Main Definitions

* `TreeSymbol.homogeneity` - The homogeneity |τ| ∈ ℝ for tree τ
* `isSubcritical` - Predicate for trees with |τ| > 0
* `requiresRenormalization` - Predicate for trees with |τ| < 0
* `IndexSetRS` - The index set A containing all possible homogeneities

## Mathematical Background

The homogeneity |τ| determines the regularity of Π_x τ as a distribution.
The key rules are:
- |𝟙| = 0
- |Ξ| = α (noise regularity)
- |X^k| = |k| (polynomial degree)
- |I_k(τ)| = |τ| + β - |k| (integration adds regularity β)
- |τ₁ · τ₂| = |τ₁| + |τ₂| (product is additive)

## References

* Hairer, "A theory of regularity structures" (Inventiones 2014), Section 3.1
-/

namespace SPDE.RegularityStructures

open TreeSymbol

/-! ## Homogeneity Assignment -/

namespace TreeSymbol

variable {d : ℕ}

/-- The homogeneity of a tree symbol.

    Parameters:
    - `α`: The noise regularity (typically -(d+2)/2 + ε for space-time white noise)
    - `β`: The kernel order (typically 2 for the heat kernel)

    The homogeneity determines the regularity of Π_x τ as a distribution. -/
noncomputable def homogeneity (α β : ℝ) : TreeSymbol d → ℝ
  | one => 0
  | Xi => α
  | Poly k => (k.degree : ℝ)
  | Integ k τ => homogeneity α β τ + β - (k.degree : ℝ)
  | Prod τ₁ τ₂ => homogeneity α β τ₁ + homogeneity α β τ₂

/-- Homogeneity of unit is 0 -/
theorem homogeneity_one (α β : ℝ) : homogeneity α β (one : TreeSymbol d) = 0 := rfl

/-- Homogeneity of noise is α -/
theorem homogeneity_Xi (α β : ℝ) : homogeneity α β (Xi : TreeSymbol d) = α := rfl

/-- Homogeneity of polynomial is the degree -/
theorem homogeneity_Poly (α β : ℝ) (k : MultiIndex d) :
    homogeneity α β (Poly k : TreeSymbol d) = (k.degree : ℝ) := rfl

/-- Homogeneity of integration -/
theorem homogeneity_Integ (α β : ℝ) (k : MultiIndex d) (τ : TreeSymbol d) :
    homogeneity α β (Integ k τ) = homogeneity α β τ + β - (k.degree : ℝ) := rfl

/-- Homogeneity of product is additive -/
theorem homogeneity_Prod (α β : ℝ) (τ₁ τ₂ : TreeSymbol d) :
    homogeneity α β (Prod τ₁ τ₂) = homogeneity α β τ₁ + homogeneity α β τ₂ := rfl

/-! ## Subcriticality -/

/-- A tree is subcritical (well-defined as a distribution) if its homogeneity is positive -/
def isSubcritical (α β : ℝ) (τ : TreeSymbol d) : Prop :=
  homogeneity α β τ > 0

/-- A tree requires renormalization if its homogeneity is negative -/
def requiresRenormalization (α β : ℝ) (τ : TreeSymbol d) : Prop :=
  homogeneity α β τ < 0

/-- The unit has homogeneity exactly 0 (boundary case) -/
theorem one_homogeneity_zero (α β : ℝ) : homogeneity α β (one : TreeSymbol d) = 0 := rfl

end TreeSymbol

/-! ## The Vector Space of Trees

The regularity structure T is the free vector space spanned by trees.
-/

/-- A formal linear combination of trees with real coefficients.
    Elements of T are finite formal sums Σᵢ cᵢ τᵢ. -/
structure FormalSum (d : ℕ) where
  /-- The trees appearing in the sum with their coefficients -/
  terms : List (ℝ × TreeSymbol d)

namespace FormalSum

variable {d : ℕ}

/-- The zero element -/
def zero : FormalSum d := ⟨[]⟩

/-- A single tree with coefficient 1 -/
def single (τ : TreeSymbol d) : FormalSum d := ⟨[((1 : ℝ), τ)]⟩

/-- Scalar multiplication -/
def smul (c : ℝ) (f : FormalSum d) : FormalSum d :=
  ⟨f.terms.map (fun (a, τ) => (c * a, τ))⟩

/-- Addition of formal sums -/
def add (f g : FormalSum d) : FormalSum d :=
  ⟨f.terms ++ g.terms⟩

instance : Zero (FormalSum d) := ⟨zero⟩
instance : Add (FormalSum d) := ⟨add⟩
instance : SMul ℝ (FormalSum d) := ⟨smul⟩

/-- The maximum homogeneity appearing in the sum -/
noncomputable def maxHomogeneity (α β : ℝ) (f : FormalSum d) : ℝ :=
  f.terms.foldl (fun acc (_, τ) => max acc (TreeSymbol.homogeneity α β τ)) (0 : ℝ)

/-- Negation -/
def neg (f : FormalSum d) : FormalSum d :=
  ⟨f.terms.map (fun (a, τ) => (-a, τ))⟩

instance : Neg (FormalSum d) := ⟨neg⟩

/-- Subtraction -/
def sub (f g : FormalSum d) : FormalSum d := f + (-g)

instance : Sub (FormalSum d) := ⟨sub⟩

/-- Monadic bind: apply a function to each tree and combine results.
    This is the key operation for composing renormalization group elements.
    Given f = Σᵢ cᵢ τᵢ and g : TreeSymbol d → FormalSum d,
    bind f g = Σᵢ cᵢ · g(τᵢ) -/
def bind (f : FormalSum d) (g : TreeSymbol d → FormalSum d) : FormalSum d :=
  ⟨f.terms.flatMap (fun (c, τ) => (g τ).terms.map (fun (a, σ) => (c * a, σ)))⟩

/-- Get the coefficient sum for a specific tree in the formal sum.
    If τ appears multiple times, their coefficients are summed. -/
def coeff (f : FormalSum d) (τ : TreeSymbol d) : ℝ :=
  f.terms.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0

/-- A single tree with given coefficient -/
def singleWithCoeff (c : ℝ) (τ : TreeSymbol d) : FormalSum d := ⟨[(c, τ)]⟩

/-- The formal sum has only finitely many nonzero terms by construction -/
theorem terms_finite (f : FormalSum d) : f.terms.length < f.terms.length + 1 :=
  Nat.lt_succ_self _

/-- Zero element property -/
theorem add_zero (f : FormalSum d) : f + 0 = f := by
  show FormalSum.add f zero = f
  simp only [add, zero, List.append_nil]

/-- Zero element property -/
theorem zero_add (f : FormalSum d) : 0 + f = f := by
  show FormalSum.add zero f = f
  simp only [add, zero, List.nil_append]

/-- Coefficient of τ in single τ is 1 -/
theorem coeff_single_self (τ : TreeSymbol d) : (single τ).coeff τ = 1 := by
  simp only [coeff, single, List.foldl_cons, List.foldl_nil, ite_true]
  ring

/-- Coefficient of σ in single τ is 0 when σ ≠ τ -/
theorem coeff_single_ne (τ σ : TreeSymbol d) (h : σ ≠ τ) : (single τ).coeff σ = 0 := by
  simp only [coeff, single, List.foldl_cons, List.foldl_nil, h.symm, ite_false]

/-- Helper: foldl with conditional add is additive over append -/
private theorem coeff_foldl_append (l₁ l₂ : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d) (init : ℝ) :
    List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) init (l₁ ++ l₂) =
    List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc)
      (List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) init l₁) l₂ := by
  rw [List.foldl_append]

/-- Helper: foldl for coeff starting from x equals x + foldl starting from 0 -/
private theorem coeff_foldl_shift (l : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d) (x : ℝ) :
    List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) x l =
    x + List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0 l := by
  induction l generalizing x with
  | nil => simp [List.foldl_nil]
  | cons h t ih =>
    simp only [List.foldl_cons]
    by_cases hσ : h.2 = τ
    · simp only [hσ, ite_true]
      rw [ih (x + h.1), ih (0 + h.1)]
      ring
    · simp only [hσ, ite_false]
      exact ih x

/-- Coefficient distributes over addition -/
theorem coeff_add (f g : FormalSum d) (τ : TreeSymbol d) :
    (f + g).coeff τ = f.coeff τ + g.coeff τ := by
  unfold coeff
  show List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0
         (FormalSum.add f g).terms =
       List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 f.terms +
       List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 g.terms
  simp only [FormalSum.add, List.foldl_append]
  rw [coeff_foldl_shift]

/-- Helper: coeff of smul via map scales the foldl result -/
private theorem coeff_smul_foldl (c : ℝ) (l : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0
      (l.map (fun (a, σ) => (c * a, σ))) =
    c * List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 l := by
  induction l with
  | nil => simp [List.foldl_nil, List.map_nil]
  | cons h t ih =>
    simp only [List.map_cons, List.foldl_cons]
    by_cases hσ : h.2 = τ
    · simp only [hσ, ite_true]
      -- Goal: foldl ... (0 + c * h.1) (map ...) = c * foldl ... (0 + h.1) t
      conv_lhs => rw [show (0 : ℝ) + c * h.1 = c * h.1 by ring]
      conv_rhs => rw [show (0 : ℝ) + h.1 = h.1 by ring]
      rw [coeff_foldl_shift (t.map _) τ (c * h.1)]
      rw [coeff_foldl_shift t τ h.1]
      rw [ih]
      ring
    · simp only [hσ, ite_false]
      exact ih

/-- Coefficient of scalar multiple -/
theorem coeff_smul (c : ℝ) (f : FormalSum d) (τ : TreeSymbol d) :
    (c • f).coeff τ = c * f.coeff τ := by
  unfold coeff
  show List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0
         (FormalSum.smul c f).terms =
       c * List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 f.terms
  simp only [FormalSum.smul]
  exact coeff_smul_foldl c f.terms τ

/-- Single is mapped correctly by bind -/
theorem bind_single (τ : TreeSymbol d) (g : TreeSymbol d → FormalSum d) :
    bind (single τ) g = g τ := by
  simp only [bind, single, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  show ⟨(g τ).terms.map (fun (a, σ) => (1 * a, σ))⟩ = g τ
  congr 1
  conv_rhs => rw [← List.map_id (g τ).terms]
  apply List.map_congr_left
  intro ⟨a, σ⟩ _
  simp only [id_eq, Prod.mk.injEq, and_true]
  ring

/-- Binding with single is identity: bind s single = s -/
theorem bind_single_right (s : FormalSum d) : bind s single = s := by
  simp only [bind, single]
  congr 1
  induction s.terms with
  | nil => rfl
  | cons h t ih =>
    simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.singleton_append]
    rw [List.cons_eq_cons]
    refine ⟨?_, ?_⟩
    · exact Prod.ext (mul_one h.1) rfl
    · convert ih using 1

/-- Coefficient of bind for single: coeff (bind (single σ) g) τ = coeff (g σ) τ -/
theorem coeff_bind_single (σ : TreeSymbol d) (g : TreeSymbol d → FormalSum d) (τ : TreeSymbol d) :
    (bind (single σ) g).coeff τ = (g σ).coeff τ := by
  rw [bind_single]

/-- Helper: coeff of mapped list with scalar -/
private theorem coeff_map_scalar (c : ℝ) (l : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0
      (l.map (fun (a, σ) => (c * a, σ))) =
    c * List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 l := by
  induction l with
  | nil => simp only [List.map_nil, List.foldl_nil, mul_zero]
  | cons hd t ih =>
    simp only [List.map_cons, List.foldl_cons]
    by_cases hτ : hd.2 = τ
    · simp only [hτ, ite_true]
      rw [coeff_foldl_shift, ih]
      conv_rhs => rw [coeff_foldl_shift]
      ring
    · simp only [hτ, ite_false]
      exact ih

/-- Helper: foldl shift for the mul-coeff pattern (expanded form) -/
private theorem coeff_mul_foldl_shift' (l : List (ℝ × TreeSymbol d)) (x : ℝ)
    (g : TreeSymbol d → FormalSum d) (τ : TreeSymbol d) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      acc + p.1 * List.foldl (fun acc' (q : ℝ × TreeSymbol d) =>
        if q.2 = τ then acc' + q.1 else acc') 0 (g p.2).terms) x l =
    x + List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      acc + p.1 * List.foldl (fun acc' (q : ℝ × TreeSymbol d) =>
        if q.2 = τ then acc' + q.1 else acc') 0 (g p.2).terms) 0 l := by
  induction l generalizing x with
  | nil =>
    simp only [List.foldl_nil]
    ring
  | cons hd t ih =>
    simp only [List.foldl_cons]
    rw [ih (x + _), ih (0 + _)]
    ring

/-- General coefficient of bind:
    coeff (bind f g) τ = Σ_{(c,σ)∈f.terms} c * coeff (g σ) τ -/
theorem coeff_bind (f : FormalSum d) (g : TreeSymbol d → FormalSum d) (τ : TreeSymbol d) :
    (bind f g).coeff τ =
    f.terms.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * (g p.2).coeff τ) 0 := by
  simp only [bind, coeff]
  induction f.terms with
  | nil => rfl
  | cons hd t ih =>
    simp only [List.flatMap_cons]
    rw [coeff_foldl_append, coeff_foldl_shift, ih, coeff_map_scalar]
    simp only [List.foldl_cons]
    -- LHS: hd.1 * coeff_g_hd + foldl 0 t
    -- RHS: foldl (0 + hd.1 * coeff_g_hd) t
    -- Use shift lemma: foldl x t = x + foldl 0 t, so foldl (0 + a) t = (0 + a) + foldl 0 t = a + foldl 0 t
    conv_rhs => rw [coeff_mul_foldl_shift' t _ g τ]
    -- Now RHS = (0 + hd.1 * ...) + foldl 0 t
    ring

/-- The norm at a specific homogeneity level ℓ.
    This sums |cᵢ| over all terms with homogeneity(τᵢ) = ℓ. -/
noncomputable def normAtLevel (α β : ℝ) (f : FormalSum d) (ℓ : ℝ) : ℝ :=
  f.terms.foldl
    (fun acc (c, τ) =>
      if TreeSymbol.homogeneity α β τ = ℓ then acc + |c| else acc)
    0

/-- The total norm: sum of |cᵢ| over all terms. -/
noncomputable def totalNorm (f : FormalSum d) : ℝ :=
  f.terms.foldl (fun acc (c, _) => acc + |c|) 0

/-- Apply a linear map to each tree in the sum. -/
def mapTrees (f : FormalSum d) (g : TreeSymbol d → TreeSymbol d) : FormalSum d :=
  ⟨f.terms.map (fun (c, τ) => (c, g τ))⟩

/-- mapTrees distributes over addition:
    mapTrees (f + g) h = mapTrees f h + mapTrees g h -/
theorem mapTrees_add (f g : FormalSum d) (h : TreeSymbol d → TreeSymbol d) :
    mapTrees (f + g) h = mapTrees f h + mapTrees g h := by
  unfold mapTrees
  show ⟨((FormalSum.add f g).terms).map (fun (c, τ) => (c, h τ))⟩ =
       FormalSum.add ⟨f.terms.map _⟩ ⟨g.terms.map _⟩
  simp only [FormalSum.add, List.map_append]

/-- mapTrees commutes with negation:
    mapTrees (-f) h = -(mapTrees f h) -/
theorem mapTrees_neg (f : FormalSum d) (h : TreeSymbol d → TreeSymbol d) :
    mapTrees (FormalSum.neg f) h = FormalSum.neg (mapTrees f h) := by
  simp only [mapTrees, FormalSum.neg, List.map_map]
  -- Need to show the two compositions give the same result
  -- LHS: (c, τ) ↦ (c, h τ) ∘ (c, τ) ↦ (-c, τ) = (c, τ) ↦ (-c, h τ)
  -- RHS: (c, τ) ↦ (-c, τ) ∘ (c, τ) ↦ (c, h τ) = (c, τ) ↦ (-c, h τ)
  rfl

/-- mapTrees preserves subtraction:
    mapTrees (f - g) h = mapTrees f h - mapTrees g h -/
theorem mapTrees_sub (f g : FormalSum d) (h : TreeSymbol d → TreeSymbol d) :
    mapTrees (FormalSum.sub f g) h = FormalSum.sub (mapTrees f h) (mapTrees g h) := by
  simp only [FormalSum.sub]
  rw [mapTrees_add]
  -- Need to show: mapTrees f h + mapTrees (neg g) h = add (mapTrees f h) (neg (mapTrees g h))
  congr 1
  exact mapTrees_neg g h

/-- Check if all trees in the sum have homogeneity less than γ. -/
noncomputable def allHomogeneityLt (α β γ : ℝ) (f : FormalSum d) : Bool :=
  f.terms.all (fun (_, τ) => decide (TreeSymbol.homogeneity α β τ < γ))

/-- totalNorm is nonnegative: ‖f‖ ≥ 0.
    Proof: Each term contributes |cᵢ| ≥ 0, sum of nonnegatives is nonnegative. -/
theorem totalNorm_nonneg (f : FormalSum d) : totalNorm f ≥ 0 := by
  unfold totalNorm
  -- Induction on the list: sum of |cᵢ| starting from 0 is ≥ 0
  have : ∀ (l : List (ℝ × TreeSymbol d)) (init : ℝ), init ≥ 0 →
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) init l ≥ 0 := by
    intro l
    induction l with
    | nil => intro init h; simp only [List.foldl_nil]; exact h
    | cons h t ih =>
      intro init hinit
      simp only [List.foldl_cons]
      apply ih
      have habs : |h.1| ≥ 0 := abs_nonneg h.1
      linarith
  exact this f.terms 0 (le_refl 0)

/-- Helper lemma: foldl with + is shift-invariant. -/
theorem foldl_add_shift (l : List (ℝ × TreeSymbol d)) (x : ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) x l =
    x + List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 l := by
  induction l generalizing x with
  | nil => simp [List.foldl_nil]
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih (x + |h.1|)]
    conv_rhs => rw [ih (0 + |h.1|)]
    ring

/-- Triangle inequality for totalNorm: ‖f + g‖ ≤ ‖f‖ + ‖g‖.
    Proof: (f + g).terms = f.terms ++ g.terms by definition,
    so totalNorm(f + g) = Σ|cᵢ| over f.terms ++ g.terms
                        = Σ|cᵢ| over f.terms + Σ|cᵢ| over g.terms
                        = totalNorm(f) + totalNorm(g).
    Thus equality holds (which implies ≤). -/
theorem totalNorm_add_le (f g : FormalSum d) :
    totalNorm (f + g) ≤ totalNorm f + totalNorm g := by
  unfold totalNorm
  -- (f + g).terms = f.terms ++ g.terms by definition of Add instance
  show List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 (FormalSum.add f g).terms ≤ _
  simp only [FormalSum.add]
  rw [List.foldl_append, foldl_add_shift]

/-- Homogeneity of totalNorm: ‖c • f‖ = |c| * ‖f‖.
    Proof: (c • f).terms.map fst = c * f.terms.map fst,
    so Σ|c * aᵢ| = Σ|c| * |aᵢ| = |c| * Σ|aᵢ|. -/
theorem totalNorm_smul (c : ℝ) (f : FormalSum d) :
    totalNorm (c • f) = |c| * totalNorm f := by
  unfold totalNorm
  -- (c • f).terms = f.terms.map (fun (a, τ) => (c * a, τ)) by definition of SMul instance
  show List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 (FormalSum.smul c f).terms =
       |c| * List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 f.terms
  simp only [FormalSum.smul]
  -- Need to show foldl over mapped list = |c| * foldl over original
  have h : ∀ (l : List (ℝ × TreeSymbol d)),
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0
        (l.map (fun (a, τ) => (c * a, τ))) =
      |c| * List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 l := by
    intro l
    induction l with
    | nil => simp [List.foldl_nil]
    | cons hd t ih =>
      simp only [List.map_cons, List.foldl_cons]
      -- LHS: foldl ... |c * hd.1| (map ... t)
      -- RHS: |c| * foldl ... |hd.1| t
      rw [foldl_add_shift]
      -- LHS: |c * hd.1| + foldl ... 0 (map ... t)
      rw [ih]
      -- LHS: |c * hd.1| + |c| * foldl ... 0 t
      -- RHS: |c| * foldl ... |hd.1| t = |c| * (|hd.1| + foldl ... 0 t)
      conv_rhs => rw [foldl_add_shift]
      simp only [abs_mul]
      ring
  exact h f.terms

/-- bind distributes over addition on the left:
    bind (f + g) h = bind f h + bind g h -/
theorem bind_add (f g : FormalSum d) (h : TreeSymbol d → FormalSum d) :
    bind (f + g) h = bind f h + bind g h := by
  show bind (FormalSum.add f g) h = FormalSum.add (bind f h) (bind g h)
  simp only [bind, FormalSum.add, List.flatMap_append]

/-- Helper: flatMap over mapped list with scalar -/
private theorem flatMap_map_smul (c : ℝ) (l : List (ℝ × TreeSymbol d))
    (h : TreeSymbol d → FormalSum d) :
    List.flatMap (fun x => List.map (fun y => (x.1 * y.1, y.2)) (h x.2).terms)
      (l.map (fun (a, τ) => (c * a, τ))) =
    List.map (fun (a, τ) => (c * a, τ))
      (List.flatMap (fun x => List.map (fun y => (x.1 * y.1, y.2)) (h x.2).terms) l) := by
  induction l with
  | nil => rfl
  | cons hd t ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map]
    rw [ih]
    congr 1
    apply List.map_congr_left
    intro ⟨a, σ⟩ _
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    ring

/-- bind commutes with scalar multiplication:
    bind (c • f) h = c • bind f h -/
theorem bind_smul (c : ℝ) (f : FormalSum d) (h : TreeSymbol d → FormalSum d) :
    bind (c • f) h = c • bind f h := by
  show bind (FormalSum.smul c f) h = FormalSum.smul c (bind f h)
  simp only [bind, FormalSum.smul]
  congr 1
  exact flatMap_map_smul c f.terms h

/-- bind zero gives zero: bind 0 h = 0 -/
theorem bind_zero (h : TreeSymbol d → FormalSum d) : bind (0 : FormalSum d) h = 0 := rfl

/-- Helper: flatMap over mapped list with negation -/
private theorem flatMap_map_neg (l : List (ℝ × TreeSymbol d))
    (h : TreeSymbol d → FormalSum d) :
    List.flatMap (fun x => List.map (fun y => (x.1 * y.1, y.2)) (h x.2).terms)
      (l.map (fun (a, τ) => (-a, τ))) =
    List.map (fun (a, τ) => (-a, τ))
      (List.flatMap (fun x => List.map (fun y => (x.1 * y.1, y.2)) (h x.2).terms) l) := by
  induction l with
  | nil => rfl
  | cons hd t ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append, List.map_map]
    rw [ih]
    congr 1
    apply List.map_congr_left
    intro ⟨a, σ⟩ _
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    ring

/-- bind with neg: bind (-f) h = -(bind f h) -/
theorem bind_neg (f : FormalSum d) (h : TreeSymbol d → FormalSum d) :
    bind (neg f) h = neg (bind f h) := by
  simp only [bind, neg]
  congr 1
  exact flatMap_map_neg f.terms h

/-- bind distributes over subtraction:
    bind (f - g) h = bind f h - bind g h -/
theorem bind_sub (f g : FormalSum d) (h : TreeSymbol d → FormalSum d) :
    bind (f - g) h = bind f h - bind g h := by
  show bind (FormalSum.sub f g) h = FormalSum.sub (bind f h) (bind g h)
  simp only [FormalSum.sub]
  rw [bind_add]
  -- -g uses Neg instance, which is neg g
  change FormalSum.add (bind f h) (bind (neg g) h) = FormalSum.add (bind f h) (neg (bind g h))
  rw [bind_neg]

/-- Negation distributes over addition: neg (f + g) = neg f + neg g -/
theorem neg_add (f g : FormalSum d) : neg (f + g) = neg f + neg g := by
  show neg (FormalSum.add f g) = FormalSum.add (neg f) (neg g)
  simp only [neg, FormalSum.add, List.map_append]

/-- totalNorm of negation: ‖-f‖ = ‖f‖ -/
theorem totalNorm_neg (f : FormalSum d) : totalNorm (neg f) = totalNorm f := by
  simp only [totalNorm, neg]
  -- Need to show foldl over mapped list = foldl over original
  have : ∀ (l : List (ℝ × TreeSymbol d)),
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0
        (l.map (fun (a, τ) => (-a, τ))) =
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 l := by
    intro l
    induction l with
    | nil => rfl
    | cons hd t ih =>
      simp only [List.map_cons, List.foldl_cons, abs_neg]
      rw [foldl_add_shift]
      conv_rhs => rw [foldl_add_shift]
      rw [ih]
  exact this f.terms

/-- totalNorm of subtraction bounded by sum:
    ‖f - g‖ ≤ ‖f‖ + ‖g‖ -/
theorem totalNorm_sub_le (f g : FormalSum d) :
    totalNorm (f - g) ≤ totalNorm f + totalNorm g := by
  show totalNorm (FormalSum.sub f g) ≤ totalNorm f + totalNorm g
  simp only [FormalSum.sub]
  calc totalNorm (f + neg g)
      ≤ totalNorm f + totalNorm (neg g) := totalNorm_add_le f (neg g)
    _ = totalNorm f + totalNorm g := by rw [totalNorm_neg]

/-- Helper: foldl for totalNorm is additive over append -/
private theorem totalNorm_foldl_append (l₁ l₂ : List (ℝ × TreeSymbol d)) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 (l₁ ++ l₂) =
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 l₁ +
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 l₂ := by
  rw [List.foldl_append, foldl_add_shift]

/-- totalNorm is commutative over addition: ‖f + g‖ = ‖g + f‖ -/
theorem totalNorm_add_comm (f g : FormalSum d) :
    totalNorm (f + g) = totalNorm (g + f) := by
  show totalNorm (FormalSum.add f g) = totalNorm (FormalSum.add g f)
  simp only [totalNorm, FormalSum.add]
  rw [totalNorm_foldl_append, totalNorm_foldl_append]
  ring

/-- totalNorm is associative: ‖(f + g) + h‖ = ‖f + (g + h)‖ -/
theorem totalNorm_add_assoc (f g h : FormalSum d) :
    totalNorm ((f + g) + h) = totalNorm (f + (g + h)) := by
  show totalNorm (FormalSum.add (FormalSum.add f g) h) =
       totalNorm (FormalSum.add f (FormalSum.add g h))
  simp only [totalNorm, FormalSum.add, List.append_assoc]

/-- Helper: totalNorm of sub equals sum of totalNorms -/
theorem totalNorm_sub_eq (f g : FormalSum d) :
    totalNorm (FormalSum.sub f g) = totalNorm f + totalNorm g := by
  -- FormalSum.sub f g has terms = f.terms ++ (neg g).terms
  have hterms : (FormalSum.sub f g).terms = f.terms ++ (neg g).terms := by
    simp only [FormalSum.sub, neg]
    rfl
  simp only [totalNorm]
  rw [hterms, totalNorm_foldl_append]
  -- Now need: foldl 0 (neg g).terms = foldl 0 g.terms
  have h2 : List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 (neg g).terms =
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 g.terms := by
    have := totalNorm_neg g
    simp only [totalNorm, neg] at this
    exact this
  rw [h2]

/-- Helper for addition of totalNorms -/
theorem totalNorm_add_eq (f g : FormalSum d) :
    totalNorm (FormalSum.add f g) = totalNorm f + totalNorm g := by
  simp only [totalNorm, FormalSum.add, totalNorm_foldl_append]

/-- Key algebraic identity for Hölder regularity:
    totalNorm ((a + b) - (c + d)) = totalNorm ((a - c) + (b - d))
    This holds because both expressions have the same multiset of (absolute) coefficients. -/
theorem totalNorm_add_sub_add (a b c e : FormalSum d) :
    totalNorm (FormalSum.sub (FormalSum.add a b) (FormalSum.add c e)) =
    totalNorm (FormalSum.add (FormalSum.sub a c) (FormalSum.sub b e)) := by
  -- Both sides equal totalNorm a + totalNorm b + totalNorm c + totalNorm e
  rw [totalNorm_sub_eq, totalNorm_add_eq, totalNorm_add_eq]
  rw [totalNorm_add_eq, totalNorm_sub_eq, totalNorm_sub_eq]
  ring

/-- Sum by tree: computes Σ c_i * g(τ_i) over terms of f.
    This is the key computational pattern for evaluating bind operations. -/
def sumByTree (f : FormalSum d) (g : TreeSymbol d → ℝ) : ℝ :=
  f.terms.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0

/-- Helper: foldl with + p.1 * g(p.2) is shift-invariant -/
theorem foldl_mul_tree_shift (l : List (ℝ × TreeSymbol d)) (x : ℝ) (g : TreeSymbol d → ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) x l =
    x + List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0 l := by
  induction l generalizing x with
  | nil => simp [List.foldl_nil]
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih (x + h.1 * g h.2), ih (0 + h.1 * g h.2)]
    ring

/-- sumByTree of single gives the value at that tree -/
theorem sumByTree_single (τ : TreeSymbol d) (g : TreeSymbol d → ℝ) :
    sumByTree (single τ) g = g τ := by
  simp only [sumByTree, single, List.foldl_cons, List.foldl_nil]
  ring

/-- sumByTree distributes over addition -/
theorem sumByTree_add (f₁ f₂ : FormalSum d) (g : TreeSymbol d → ℝ) :
    sumByTree (f₁ + f₂) g = sumByTree f₁ g + sumByTree f₂ g := by
  simp only [sumByTree]
  show List.foldl _ 0 (FormalSum.add f₁ f₂).terms = _
  simp only [FormalSum.add, List.foldl_append]
  rw [foldl_mul_tree_shift]

/-- sumByTree commutes with scalar multiplication -/
theorem sumByTree_smul (c : ℝ) (f : FormalSum d) (g : TreeSymbol d → ℝ) :
    sumByTree (c • f) g = c * sumByTree f g := by
  simp only [sumByTree]
  show List.foldl _ 0 (FormalSum.smul c f).terms = _
  simp only [FormalSum.smul]
  induction f.terms with
  | nil => simp [List.foldl_nil]
  | cons h t ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [foldl_mul_tree_shift, ih]
    conv_rhs => rw [foldl_mul_tree_shift]
    ring

/-- sumByTree of singleWithCoeff -/
theorem sumByTree_singleWithCoeff (c : ℝ) (τ : TreeSymbol d) (g : TreeSymbol d → ℝ) :
    sumByTree (singleWithCoeff c τ) g = c * g τ := by
  simp only [sumByTree, singleWithCoeff, List.foldl_cons, List.foldl_nil]
  ring

/-- Bound on |sumByTree f g| when each |g τ| is bounded.
    |sumByTree f g| ≤ B * totalNorm f when ∀ τ, |g τ| ≤ B. -/
theorem sumByTree_abs_le (f : FormalSum d) (g : TreeSymbol d → ℝ) (B : ℝ)
    (hB : ∀ τ : TreeSymbol d, |g τ| ≤ B) (hB_nonneg : B ≥ 0) :
    |sumByTree f g| ≤ B * totalNorm f := by
  unfold sumByTree totalNorm
  induction f.terms with
  | nil =>
    simp only [List.foldl_nil, abs_zero]
    exact mul_nonneg hB_nonneg (le_refl 0)
  | cons hd t ih =>
    simp only [List.foldl_cons]
    -- Separate first term using shift lemma
    have hza1 : (0 : ℝ) + hd.1 * g hd.2 = hd.1 * g hd.2 := by ring
    have hza2 : (0 : ℝ) + |hd.1| = |hd.1| := by ring
    have hshift1 : List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2)
        (0 + hd.1 * g hd.2) t =
        hd.1 * g hd.2 + List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0 t := by
      conv_lhs => rw [hza1]
      exact foldl_mul_tree_shift t (hd.1 * g hd.2) g
    have hshift2 : List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|)
        (0 + |hd.1|) t =
        |hd.1| + List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + |p.1|) 0 t := by
      conv_lhs => rw [hza2]
      exact foldl_add_shift t |hd.1|
    rw [hshift1, hshift2]
    -- |first_term + rest| ≤ |first_term| + |rest| (triangle inequality)
    have htri : |hd.1 * g hd.2 + List.foldl (fun acc p => acc + p.1 * g p.2) 0 t| ≤
        |hd.1 * g hd.2| + |List.foldl (fun acc p => acc + p.1 * g p.2) 0 t| :=
      abs_add_le _ _
    have habs_mul : |hd.1 * g hd.2| = |hd.1| * |g hd.2| := abs_mul hd.1 _
    have hbound1 : |hd.1| * |g hd.2| ≤ |hd.1| * B :=
      mul_le_mul_of_nonneg_left (hB hd.2) (abs_nonneg hd.1)
    calc |hd.1 * g hd.2 + List.foldl (fun acc p => acc + p.1 * g p.2) 0 t|
        ≤ |hd.1 * g hd.2| + |List.foldl (fun acc p => acc + p.1 * g p.2) 0 t| := htri
      _ = |hd.1| * |g hd.2| + |List.foldl (fun acc p => acc + p.1 * g p.2) 0 t| := by rw [habs_mul]
      _ ≤ |hd.1| * |g hd.2| + B * List.foldl (fun acc p => acc + |p.1|) 0 t := by
          -- a + x ≤ a + y follows from x ≤ y using add_le_add with le_refl
          exact add_le_add (le_refl _) ih
      _ ≤ |hd.1| * B + B * List.foldl (fun acc p => acc + |p.1|) 0 t := by
          -- x + b ≤ y + b follows from x ≤ y using add_le_add with le_refl
          exact add_le_add hbound1 (le_refl _)
      _ = B * (|hd.1| + List.foldl (fun acc p => acc + |p.1|) 0 t) := by ring

/-- coeff_bind expressed as sumByTree -/
theorem coeff_bind_as_sumByTree (f : FormalSum d) (g : TreeSymbol d → FormalSum d) (τ : TreeSymbol d) :
    (bind f g).coeff τ = sumByTree f (fun σ => (g σ).coeff τ) := by
  rw [coeff_bind]
  rfl

/-- Key lemma: sumByTree factors by tree coefficients.
    For a formal sum where all terms have the same tree σ:
    sumByTree f g = f.coeff σ * g σ when all terms are at σ. -/
theorem sumByTree_all_same_tree (l : List (ℝ × TreeSymbol d)) (σ : TreeSymbol d) (g : TreeSymbol d → ℝ)
    (h_all : ∀ p ∈ l, p.2 = σ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0 l =
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = σ then acc + p.1 else acc) 0 l * g σ := by
  induction l with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    have hhd : hd.2 = σ := h_all hd List.mem_cons_self
    have h_all_t : ∀ p ∈ t, p.2 = σ := fun p hp => h_all p (List.mem_cons_of_mem hd hp)
    simp only [List.foldl_cons, hhd, ite_true]
    rw [foldl_mul_tree_shift, coeff_foldl_shift, ih h_all_t]
    ring

/-- sumByTree of single -/
theorem sumByTree_single' (τ : TreeSymbol d) (g : TreeSymbol d → ℝ) :
    sumByTree (single τ) g = g τ := sumByTree_single τ g

-- sumByTree_eq_single and sumByTree_congr are defined later, after foldl_mul_split

/-- Helper: foldl (acc + p.1) is shift-invariant -/
private theorem foldl_sum_shift (l : List (ℝ × TreeSymbol d)) (x : ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1) x l =
    x + List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1) 0 l := by
  induction l generalizing x with
  | nil => simp [List.foldl_nil]
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih (x + h.1), ih (0 + h.1)]
    ring

/-- Helper: all terms at the same tree give coeff * g -/
theorem foldl_mul_same_tree (l : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d) (g : TreeSymbol d → ℝ)
    (h_all : ∀ p ∈ l, p.2 = τ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0 l =
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1) 0 l * g τ := by
  induction l with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    have hhd : hd.2 = τ := h_all hd (List.mem_cons.mpr (.inl rfl))
    have ht : ∀ p ∈ t, p.2 = τ := fun p hp => h_all p (List.mem_cons_of_mem hd hp)
    simp only [List.foldl_cons]
    rw [foldl_mul_tree_shift, foldl_sum_shift, ih ht, hhd]
    ring

/-- Helper: shift for conditional foldl over trees ≠ τ -/
private theorem foldl_cond_ne_shift (l : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d)
    (g : TreeSymbol d → ℝ) (x : ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 ≠ τ then acc + p.1 * g p.2 else acc) x l =
    x + List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 ≠ τ then acc + p.1 * g p.2 else acc) 0 l := by
  induction l generalizing x with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    simp only [List.foldl_cons]
    by_cases heq : hd.2 ≠ τ
    · -- heq : hd.2 ≠ τ, so the if-condition is true
      simp only [if_pos heq]
      rw [ih (x + hd.1 * g hd.2), ih (0 + hd.1 * g hd.2)]
      ring
    · -- heq : ¬(hd.2 ≠ τ), so the if-condition is false
      simp only [if_neg heq]
      exact ih x

/-- Helper: conditional sum with two conditions (≠ σ and ≠ τ) -/
private theorem foldl_cond_ne_two_shift (l : List (ℝ × TreeSymbol d)) (σ τ : TreeSymbol d)
    (g : TreeSymbol d → ℝ) (x : ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      if p.2 ≠ σ ∧ p.2 ≠ τ then acc + p.1 * g p.2 else acc) x l =
    x + List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      if p.2 ≠ σ ∧ p.2 ≠ τ then acc + p.1 * g p.2 else acc) 0 l := by
  induction l generalizing x with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    simp only [List.foldl_cons]
    by_cases hcond : hd.2 ≠ σ ∧ hd.2 ≠ τ
    · simp only [if_pos hcond]
      rw [ih (x + hd.1 * g hd.2), ih (0 + hd.1 * g hd.2)]
      ring
    · simp only [if_neg hcond]
      exact ih x

/-- The conditional sum is 0 when all terms have tree = σ -/
private theorem foldl_cond_ne_zero_of_all_eq {l : List (ℝ × TreeSymbol d)} {σ : TreeSymbol d}
    {g : TreeSymbol d → ℝ} (h : ∀ p ∈ l, p.2 = σ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 ≠ σ then acc + p.1 * g p.2 else acc) 0 l = 0 := by
  induction l with
  | nil => simp
  | cons hd t ih =>
    simp only [List.foldl_cons]
    have hhd : hd.2 = σ := h hd (List.mem_cons.mpr (.inl rfl))
    simp only [hhd, ne_eq, not_true_eq_false, ite_false]
    apply ih
    intro p hp
    exact h p (List.mem_cons_of_mem hd hp)

/-- Helper: the two-condition sum over l equals the one-condition sum over the filtered list -/
private theorem foldl_cond_two_eq_filter (l : List (ℝ × TreeSymbol d)) (σ τ : TreeSymbol d)
    (g : TreeSymbol d → ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 ≠ σ ∧ p.2 ≠ τ then acc + p.1 * g p.2 else acc) 0 l =
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 ≠ σ then acc + p.1 * g p.2 else acc) 0
      (l.filter (fun p => decide (p.2 ≠ τ))) := by
  induction l with
  | nil => simp
  | cons hd t ih =>
    simp only [List.foldl_cons, List.filter_cons]
    by_cases hτ : hd.2 = τ
    · -- hd.2 = τ, hd is filtered out
      have hdec : decide (hd.2 ≠ τ) = false := by simp [hτ]
      simp only [hdec]
      have hcond : ¬(hd.2 ≠ σ ∧ hd.2 ≠ τ) := by simp [hτ]
      simp only [if_neg hcond]
      exact ih
    · -- hd.2 ≠ τ, hd is kept in filter
      have hdec : decide (hd.2 ≠ τ) = true := by simp [hτ]
      simp only [hdec, ite_true, List.foldl_cons]
      by_cases hσ : hd.2 = σ
      · -- hd.2 = σ, so the two-condition is false
        have hcond : ¬(hd.2 ≠ σ ∧ hd.2 ≠ τ) := by simp [hσ]
        simp only [hσ, ne_eq, not_true_eq_false, ite_false]
        exact ih
      · -- Both conditions true
        have hcond : hd.2 ≠ σ ∧ hd.2 ≠ τ := ⟨hσ, hτ⟩
        simp only [hσ, ne_eq, not_false_eq_true, ite_true, true_and, hτ]
        rw [foldl_cond_ne_two_shift, foldl_cond_ne_shift, ih]

/-- Coefficient at τ in the filtered list (filtering out ρ) equals coefficient in original
    when τ ≠ ρ -/
private theorem coeff_filter_ne_eq {l : List (ℝ × TreeSymbol d)} {τ ρ : TreeSymbol d} (hne : τ ≠ ρ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0
      (l.filter (fun p => decide (p.2 ≠ ρ))) =
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 l := by
  induction l with
  | nil => simp
  | cons hd t ih =>
    simp only [List.filter_cons, List.foldl_cons]
    by_cases hρ : hd.2 = ρ
    · -- hd.2 = ρ, so hd is filtered out
      have hdec : decide (hd.2 ≠ ρ) = false := by simp [hρ]
      simp only [hdec]
      have hτ_ne : hd.2 ≠ τ := by rw [hρ]; exact hne.symm
      rw [if_neg hτ_ne]
      exact ih
    · -- hd.2 ≠ ρ, hd is kept in filter
      have hdec : decide (hd.2 ≠ ρ) = true := by simp [hρ]
      simp only [hdec, ite_true, List.foldl_cons]
      by_cases hτ : hd.2 = τ
      · simp only [hτ, ite_true]
        -- Goal: foldl f (0 + hd.1) (filter ...) = foldl f (0 + hd.1) t
        conv_lhs => rw [coeff_foldl_shift, ih]
        conv_rhs => rw [coeff_foldl_shift]
      · simp only [hτ, ite_false]
        exact ih

/-- Coefficient at ρ in the filtered list (filtering out ρ) is 0 -/
private theorem coeff_filter_self_eq_zero {l : List (ℝ × TreeSymbol d)} {ρ : TreeSymbol d} :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = ρ then acc + p.1 else acc) 0
      (l.filter (fun p => decide (p.2 ≠ ρ))) = 0 := by
  induction l with
  | nil => simp
  | cons hd t ih =>
    simp only [List.filter_cons]
    by_cases hρ : hd.2 = ρ
    · -- hd.2 = ρ, so hd is filtered out
      have hdec : decide (hd.2 ≠ ρ) = false := by simp [hρ]
      simp only [hdec]
      exact ih
    · -- hd.2 ≠ ρ, hd is kept but contributes 0 since hd.2 ≠ ρ
      have hdec : decide (hd.2 ≠ ρ) = true := by simp [hρ]
      simp only [hdec, ite_true, List.foldl_cons, hρ, ite_false]
      exact ih

/-- Length of filtered list is at most length of original -/
private theorem filter_length_le (l : List (ℝ × TreeSymbol d)) (p : ℝ × TreeSymbol d → Bool) :
    (l.filter p).length ≤ l.length := List.length_filter_le p l

/-- If some element satisfies ¬p, filtered list is strictly shorter -/
private theorem filter_length_lt {l : List (ℝ × TreeSymbol d)} {ρ : TreeSymbol d}
    (hex : ∃ q ∈ l, q.2 = ρ) :
    (l.filter (fun p => decide (p.2 ≠ ρ))).length < l.length := by
  obtain ⟨q, hq_mem, hq_eq⟩ := hex
  induction l with
  | nil => simp at hq_mem
  | cons hd t ih =>
    simp only [List.filter_cons]
    by_cases hhd : hd.2 = ρ
    · -- hd is filtered out, so filter is at most t.filter
      have hdec : decide (hd.2 ≠ ρ) = false := by simp [hhd]
      simp only [hdec]
      calc (t.filter (fun p => decide (p.2 ≠ ρ))).length
          ≤ t.length := List.length_filter_le _ t
        _ < t.length + 1 := Nat.lt_succ_self _
        _ = (hd :: t).length := by simp
    · -- hd is kept
      have hdec : decide (hd.2 ≠ ρ) = true := by simp [hhd]
      simp only [hdec, ite_true, List.length_cons]
      -- q is in hd :: t and q.2 = ρ, but hd.2 ≠ ρ, so q ∈ t
      have hq_in_t : q ∈ t := by
        cases List.mem_cons.mp hq_mem with
        | inl heq => rw [heq] at hq_eq; exact absurd hq_eq hhd
        | inr ht => exact ht
      have := ih hq_in_t
      omega

/-- Helper: sumProd minus coeff contribution at one tree.
    sumProd l g - coeff τ l * g τ = sumProd of terms where tree ≠ τ. -/
private theorem sumProd_minus_coeff (l : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d) (g : TreeSymbol d → ℝ) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0 l -
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 l * g τ =
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 ≠ τ then acc + p.1 * g p.2 else acc) 0 l := by
  induction l with
  | nil => simp [List.foldl_nil]
  | cons hd t ih =>
    simp only [List.foldl_cons]
    by_cases heq : hd.2 = τ
    · -- hd.2 = τ: contribution cancels
      rw [foldl_mul_tree_shift, coeff_foldl_shift]
      simp only [heq, ite_true, ne_eq, not_true_eq_false, ite_false]
      calc (0 : ℝ) + hd.1 * g τ + List.foldl (fun acc p => acc + p.1 * g p.2) 0 t -
             (0 + hd.1 + List.foldl (fun acc p => if p.2 = τ then acc + p.1 else acc) 0 t) * g τ
           = List.foldl (fun acc p => acc + p.1 * g p.2) 0 t -
             List.foldl (fun acc p => if p.2 = τ then acc + p.1 else acc) 0 t * g τ := by ring
         _ = List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
               if p.2 ≠ τ then acc + p.1 * g p.2 else acc) 0 t := ih
    · -- hd.2 ≠ τ: term contributes to the remaining sum
      have hne : hd.2 ≠ τ := heq
      rw [foldl_mul_tree_shift]
      simp only [hne, ne_eq, not_false_eq_true, ite_true, ite_false]
      rw [foldl_cond_ne_shift, ← ih]
      ring

/-- Extraction identity: CS(l,σ) = coeff(τ,l)*g(τ) + CS2(l,σ,τ) where τ ≠ σ.
    This allows extracting the contribution of one tree from the conditional sum. -/
private theorem foldl_cond_ne_extract (l : List (ℝ × TreeSymbol d)) (σ τ : TreeSymbol d)
    (g : TreeSymbol d → ℝ) (hne : τ ≠ σ) :
    List.foldl (fun acc (q : ℝ × TreeSymbol d) => if q.2 ≠ σ then acc + q.1 * g q.2 else acc) 0 l =
    List.foldl (fun acc (q : ℝ × TreeSymbol d) => if q.2 = τ then acc + q.1 else acc) 0 l * g τ +
    List.foldl (fun acc (q : ℝ × TreeSymbol d) => if q.2 ≠ σ ∧ q.2 ≠ τ then acc + q.1 * g q.2 else acc) 0 l := by
  induction l with
  | nil => simp
  | cons hd t iht =>
    simp only [List.foldl_cons]
    by_cases hσ' : hd.2 = σ
    · -- hd.2 = σ, so hd doesn't contribute to the conditional sum
      have hτ' : hd.2 ≠ τ := by rw [hσ']; exact hne.symm
      have hcond : ¬(hd.2 ≠ σ ∧ hd.2 ≠ τ) := by simp [hσ']
      rw [if_neg (by simp [hσ'] : ¬(hd.2 ≠ σ)), if_neg (by simp [hτ'] : ¬(hd.2 = τ)),
          if_neg hcond]
      exact iht
    · by_cases hτ' : hd.2 = τ
      · -- hd.2 = τ, contributes to coeff sum
        have hcond : ¬(hd.2 ≠ σ ∧ hd.2 ≠ τ) := by simp [hτ']
        rw [if_pos (by exact hσ' : hd.2 ≠ σ), if_pos hτ', if_neg hcond]
        rw [foldl_cond_ne_shift, coeff_foldl_shift, iht, hτ']
        ring
      · -- hd.2 ≠ σ and hd.2 ≠ τ, contributes to two-condition sum
        have hcond : hd.2 ≠ σ ∧ hd.2 ≠ τ := ⟨hσ', hτ'⟩
        rw [if_pos (by exact hσ' : hd.2 ≠ σ), if_neg hτ', if_pos hcond]
        rw [foldl_cond_ne_shift, foldl_cond_ne_two_shift, iht]
        ring

/-- Key helper: the conditional sum CS(l, σ) = 0 when all coefficients at trees ≠ σ are 0.
    Proved by strong induction on the list length using filtering. -/
private theorem foldl_cond_ne_zero_aux (n : ℕ) :
    ∀ (l : List (ℝ × TreeSymbol d)), l.length ≤ n →
    ∀ (σ : TreeSymbol d) (g : TreeSymbol d → ℝ),
    (∀ τ, τ ≠ σ → List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      if p.2 = τ then acc + p.1 else acc) 0 l = 0) →
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 ≠ σ then acc + p.1 * g p.2 else acc) 0 l = 0 := by
  induction n with
  | zero =>
    intro l hl σ g _
    have hl_nil : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    simp [hl_nil]
  | succ n ih =>
    intro l hl σ g hz
    by_cases hall : ∀ p ∈ l, p.2 = σ
    · exact foldl_cond_ne_zero_of_all_eq hall
    · push_neg at hall
      obtain ⟨elem, helem_mem, helem_ne⟩ := hall
      let τ := elem.2
      have hcoeff : List.foldl (fun acc (q : ℝ × TreeSymbol d) =>
          if q.2 = τ then acc + q.1 else acc) 0 l = 0 := hz τ helem_ne
      have hlen : (l.filter (fun q => decide (q.2 ≠ τ))).length < l.length :=
        filter_length_lt ⟨elem, helem_mem, rfl⟩
      have hlen' : (l.filter (fun q => decide (q.2 ≠ τ))).length ≤ n :=
        Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlen hl)
      have hz' : ∀ ρ, ρ ≠ σ → List.foldl (fun acc (q : ℝ × TreeSymbol d) =>
          if q.2 = ρ then acc + q.1 else acc) 0 (l.filter (fun q => decide (q.2 ≠ τ))) = 0 := by
        intro ρ hρ
        by_cases hρτ : ρ = τ
        · rw [hρτ]; exact coeff_filter_self_eq_zero
        · rw [coeff_filter_ne_eq hρτ]; exact hz ρ hρ
      rw [foldl_cond_ne_extract l σ τ g helem_ne, hcoeff, zero_mul]
      rw [foldl_cond_two_eq_filter]
      have := ih _ hlen' σ g hz'
      linarith

/-- Helper: the foldl Σ c * g(τ) over a list can be split by tree.
    If we track the partial coefficient sums for each tree, the total
    is Σ_τ (partial coeff at τ) * g(τ).

    Mathematical proof sketch:
    Σᵢ cᵢ * g(τᵢ) = Σ_ρ (Σ_{τᵢ = ρ} cᵢ) * g(ρ) = Σ_ρ coeff(ρ) * g(ρ)
    If coeff(ρ) = 0 for all ρ ≠ σ, then = coeff(σ) * g(σ). -/
theorem foldl_mul_split (l : List (ℝ × TreeSymbol d)) (σ : TreeSymbol d) (g : TreeSymbol d → ℝ)
    (hz : ∀ τ ≠ σ, List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      if p.2 = τ then acc + p.1 else acc) 0 l = 0) :
    List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0 l =
    List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      if p.2 = σ then acc + p.1 else acc) 0 l * g σ := by
  -- Use sumProd_minus_coeff: sumProd - coeff σ * g σ = conditional sum over τ ≠ σ
  have h := sumProd_minus_coeff l σ g
  -- The conditional sum equals 0 when all terms with τ ≠ σ have zero total coefficient
  suffices hsuff : List.foldl (fun acc (p : ℝ × TreeSymbol d) =>
      if p.2 ≠ σ then acc + p.1 * g p.2 else acc) 0 l = 0 by
    linarith [h]
  exact foldl_cond_ne_zero_aux l.length l (le_refl _) σ g hz

/-- Key lemma: if f has coeff c at σ and 0 at all other trees,
    then sumByTree f g = c * g σ. This is the regrouping property. -/
theorem sumByTree_coeff_unique (f : FormalSum d) (σ : TreeSymbol d) (c a : ℝ)
    (g : TreeSymbol d → ℝ)
    (hσ : f.coeff σ = c) (h0 : ∀ τ ≠ σ, f.coeff τ = 0) (hg : g σ = a) :
    sumByTree f g = c * a := by
  unfold sumByTree coeff at *
  rw [foldl_mul_split f.terms σ g h0, hσ, hg]

/-- Corollary: bind of a "unit-like" formal sum.
    If f has coeff 1 at σ and 0 elsewhere, then (bind f g).coeff τ = (g σ).coeff τ. -/
theorem coeff_bind_unit_like (f : FormalSum d) (g : TreeSymbol d → FormalSum d)
    (σ τ : TreeSymbol d)
    (hσ : f.coeff σ = 1) (h0 : ∀ ρ ≠ σ, f.coeff ρ = 0) :
    (bind f g).coeff τ = (g σ).coeff τ := by
  rw [coeff_bind_as_sumByTree]
  have := sumByTree_coeff_unique f σ 1 ((g σ).coeff τ) (fun ρ => (g ρ).coeff τ) hσ h0 rfl
  rw [this]
  ring

/-- For a FormalSum that equals single σ (in coefficient sense):
    coeff σ = 1 and coeff τ = 0 for τ ≠ σ implies sumByTree gives g σ. -/
theorem sumByTree_eq_single' (f : FormalSum d) (σ : TreeSymbol d) (g : TreeSymbol d → ℝ)
    (hσ : f.coeff σ = 1) (h0 : ∀ τ ≠ σ, f.coeff τ = 0) :
    sumByTree f g = g σ := by
  have := sumByTree_coeff_unique f σ 1 (g σ) g hσ h0 rfl
  rw [this]
  ring

/-- Dual of sumByTree_coeff_unique: if g is non-zero only at τ, then sumByTree f g = f.coeff τ * g τ.
    This is useful when we know g vanishes except at one point. -/
theorem sumByTree_g_unique (f : FormalSum d) (τ : TreeSymbol d) (g : TreeSymbol d → ℝ)
    (hg0 : ∀ ρ ≠ τ, g ρ = 0) :
    sumByTree f g = f.coeff τ * g τ := by
  unfold sumByTree
  -- The key is that for any term (c, ρ), if ρ ≠ τ then c * g(ρ) = c * 0 = 0
  -- So only terms with tree = τ contribute, giving coeff τ * g τ
  have hkey : ∀ l : List (ℝ × TreeSymbol d),
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => acc + p.1 * g p.2) 0 l =
      List.foldl (fun acc (p : ℝ × TreeSymbol d) => if p.2 = τ then acc + p.1 else acc) 0 l * g τ := by
    intro l
    induction l with
    | nil => simp [List.foldl_nil]
    | cons hd tl ih =>
      simp only [List.foldl_cons]
      by_cases hρτ : hd.2 = τ
      · -- hd.2 = τ
        simp only [hρτ, ite_true]
        rw [foldl_mul_tree_shift, ih]
        conv_rhs => rw [coeff_foldl_shift]
        ring
      · -- hd.2 ≠ τ
        simp only [hρτ, ite_false]
        have hz : g hd.2 = 0 := hg0 hd.2 hρτ
        simp only [hz, mul_zero]
        conv_lhs => arg 2; rw [show (0 : ℝ) + 0 = 0 by ring]
        exact ih
  rw [hkey f.terms]
  unfold coeff
  rfl

/-- The set of distinct trees appearing in a formal sum -/
def distinctTrees (f : FormalSum d) : Finset (TreeSymbol d) :=
  (f.terms.map Prod.snd).toFinset

/-- A tree not in distinctTrees has zero coefficient -/
theorem coeff_eq_zero_of_not_in_distinctTrees (f : FormalSum d) (τ : TreeSymbol d)
    (h : τ ∉ distinctTrees f) : f.coeff τ = 0 := by
  unfold coeff distinctTrees at *
  simp only [List.mem_toFinset, List.mem_map] at h
  push_neg at h
  -- h : ∀ a ∈ f.terms, a.2 ≠ τ
  have hkey : ∀ (l : List (ℝ × TreeSymbol d)),
      (∀ a ∈ l, a.2 ≠ τ) →
      List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0 l = 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons hd tl ih =>
      intro hall
      have hne : hd.2 ≠ τ := hall hd (List.mem_cons.mpr (.inl rfl))
      have htl : ∀ a ∈ tl, a.2 ≠ τ := fun a ha => hall a (List.mem_cons.mpr (.inr ha))
      simp only [List.foldl_cons, hne, ite_false]
      exact ih htl
  exact hkey f.terms h

/-- Helper: sumByTree over empty list is zero -/
theorem sumByTree_nil (g : TreeSymbol d → ℝ) :
    sumByTree (⟨[]⟩ : FormalSum d) g = 0 := rfl

/-- Helper: sumByTree over a single term -/
theorem sumByTree_cons_eq (c : ℝ) (τ : TreeSymbol d) (tl : List (ℝ × TreeSymbol d))
    (g : TreeSymbol d → ℝ) :
    sumByTree (⟨(c, τ) :: tl⟩ : FormalSum d) g =
    c * g τ + sumByTree (⟨tl⟩ : FormalSum d) g := by
  unfold sumByTree
  simp only [List.foldl_cons]
  rw [foldl_mul_tree_shift]
  ring

/-- sumByTree is linear in g restricted to trees not in the terms list -/
theorem sumByTree_eq_when_g_eq_on_terms (f : FormalSum d) (g₁ g₂ : TreeSymbol d → ℝ)
    (heq : ∀ p ∈ f.terms, g₁ p.2 = g₂ p.2) :
    sumByTree f g₁ = sumByTree f g₂ := by
  unfold sumByTree
  have hkey : ∀ (l : List (ℝ × TreeSymbol d)),
      (∀ p ∈ l, g₁ p.2 = g₂ p.2) →
      List.foldl (fun acc p => acc + p.1 * g₁ p.2) 0 l =
      List.foldl (fun acc p => acc + p.1 * g₂ p.2) 0 l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons hd tl ih =>
      intro hall
      have hhd : g₁ hd.2 = g₂ hd.2 := hall hd (List.mem_cons.mpr (.inl rfl))
      have htl : ∀ p ∈ tl, g₁ p.2 = g₂ p.2 := fun p hp => hall p (List.mem_cons.mpr (.inr hp))
      simp only [List.foldl_cons]
      -- LHS: foldl ... (0 + hd.1 * g₁ hd.2) tl
      -- RHS: foldl ... (0 + hd.1 * g₂ hd.2) tl
      rw [foldl_mul_tree_shift (g := g₁), foldl_mul_tree_shift (g := g₂), hhd, ih htl]
  exact hkey f.terms heq

/-- Helper: coefficient of τ in a cons list -/
private theorem coeff_cons_eq (c : ℝ) (σ τ : TreeSymbol d) (tl : List (ℝ × TreeSymbol d)) :
    List.foldl (fun acc (c', σ') => if σ' = τ then acc + c' else acc) 0 ((c, σ) :: tl) =
    (if σ = τ then c else 0) + List.foldl (fun acc (c', σ') => if σ' = τ then acc + c' else acc) 0 tl := by
  simp only [List.foldl_cons]
  by_cases h : σ = τ
  · simp only [h, ite_true]
    rw [coeff_foldl_shift]
    ring
  · simp only [h, ite_false]
    ring

/-- Helper: coefficient is zero for trees not in a list -/
private theorem coeff_zero_of_not_in_list (l : List (ℝ × TreeSymbol d)) (τ : TreeSymbol d)
    (h : ∀ a ∈ l, a.2 ≠ τ) :
    List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0 l = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd.2 ≠ τ := h hd (List.mem_cons.mpr (.inl rfl))
    have htl : ∀ a ∈ tl, a.2 ≠ τ := fun a ha => h a (List.mem_cons.mpr (.inr ha))
    simp only [List.foldl_cons, hne, ite_false]
    exact ih htl

/-- Key decomposition: sumByTree equals Finset.sum over distinct trees.
    This uses the existing sumByTree_g_unique lemma which shows that
    sumByTree depends on coefficients, not term representation. -/
theorem sumByTree_eq_finset_sum (f : FormalSum d) (g : TreeSymbol d → ℝ) :
    sumByTree f g = (distinctTrees f).sum (fun τ => f.coeff τ * g τ) := by
  -- Use the regrouping property from sumByTree_g_unique
  -- For each τ ∈ distinctTrees f, the contribution to sumByTree f g is (coeff τ f) * g τ
  -- For τ ∉ distinctTrees f, coeff τ f = 0 so the contribution is 0
  unfold sumByTree distinctTrees coeff
  -- Need to show: foldl (acc + p.1 * g p.2) 0 l = Finset.sum over distinct trees
  -- This follows from regrouping: Σ_i c_i * g(τ_i) = Σ_τ (Σ_{i:τ_i=τ} c_i) * g(τ)
  -- The inner sum is exactly coeff τ
  induction f.terms with
  | nil => rfl
  | cons hd tl ih =>
    -- Expand foldl over (hd :: tl) to get hd.1 * g hd.2 + foldl over tl
    have hexpand : List.foldl (fun acc p => acc + p.1 * g p.2) 0 ((hd.1, hd.2) :: tl) =
        hd.1 * g hd.2 + List.foldl (fun acc p => acc + p.1 * g p.2) 0 tl := by
      simp only [List.foldl_cons]
      rw [foldl_mul_tree_shift]
      ring
    rw [hexpand]
    simp only [List.map_cons, List.toFinset_cons]
    by_cases hmem : hd.2 ∈ (tl.map Prod.snd).toFinset
    · -- hd.2 already in tl
      rw [Finset.insert_eq_of_mem hmem]
      -- Split the sum and use ih
      have hkey : (tl.map Prod.snd).toFinset.sum (fun τ =>
          List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0 ((hd.1, hd.2) :: tl) * g τ) =
          hd.1 * g hd.2 + (tl.map Prod.snd).toFinset.sum (fun τ =>
            List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0 tl * g τ) := by
        -- Each coefficient in (hd :: tl) = coefficient in tl + (hd.1 if τ = hd.2 else 0)
        conv_lhs =>
          arg 2
          ext τ
          rw [coeff_cons_eq hd.1 hd.2 τ tl, add_mul]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single hd.2]
        · simp only [ite_true]
        · intro τ _ hne; simp only [hne.symm, ite_false, zero_mul]
        · intro habs; exact absurd hmem habs
      rw [hkey, ih]
    · -- hd.2 is new
      rw [Finset.sum_insert hmem]
      -- Coefficient at hd.2 in tl is 0
      have hcoeff_new : List.foldl (fun acc (c, σ) => if σ = hd.2 then acc + c else acc) 0 tl = 0 := by
        simp only [List.mem_toFinset, List.mem_map] at hmem
        push_neg at hmem
        exact coeff_zero_of_not_in_list tl hd.2 hmem
      -- Coefficient at hd.2 in full list = hd.1
      have hcoeff_full :
          List.foldl (fun acc (c, σ) => if σ = hd.2 then acc + c else acc) 0 ((hd.1, hd.2) :: tl) = hd.1 := by
        rw [coeff_cons_eq, if_pos rfl, hcoeff_new]
        ring
      rw [hcoeff_full]
      -- For the sum, coefficients at τ ≠ hd.2 are unchanged
      have hsum_eq : (tl.map Prod.snd).toFinset.sum (fun τ =>
          List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0 ((hd.1, hd.2) :: tl) * g τ) =
          (tl.map Prod.snd).toFinset.sum (fun τ =>
            List.foldl (fun acc (c, σ) => if σ = τ then acc + c else acc) 0 tl * g τ) := by
        apply Finset.sum_congr rfl
        intro τ hτ
        simp only [List.mem_toFinset, List.mem_map] at hτ hmem
        have hne : τ ≠ hd.2 := by
          intro heq
          rw [heq] at hτ
          push_neg at hmem
          obtain ⟨a, ha, haeq⟩ := hτ
          exact hmem a ha haeq
        rw [coeff_cons_eq, if_neg (Ne.symm hne)]
        ring
      rw [hsum_eq, ih]

/-- Stronger form: sumByTree f g depends only on the coeff function.
    If two formal sums have the same coefficients, they give the same sumByTree.

    Note: This theorem is conceptually true because sumByTree f g = Σ_τ (coeff τ f) * g(τ)
    when the sum is taken over all trees with non-zero coefficient. The formal proof
    requires showing that the foldl computation gives the same result when regrouped
    by tree, which is captured by the foldl_mul_split theorem.

    For practical use in this codebase, the more specific sumByTree_coeff_unique
    is typically sufficient. -/
theorem sumByTree_congr (f f' : FormalSum d) (g : TreeSymbol d → ℝ)
    (h : ∀ τ, f.coeff τ = f'.coeff τ) :
    sumByTree f g = sumByTree f' g := by
  -- Express both as Finset sums over a common superset
  rw [sumByTree_eq_finset_sum f g, sumByTree_eq_finset_sum f' g]
  -- Use that coefficients outside distinctTrees are zero
  let S := distinctTrees f ∪ distinctTrees f'
  have hf_sub : distinctTrees f ⊆ S := Finset.subset_union_left
  have hf'_sub : distinctTrees f' ⊆ S := Finset.subset_union_right
  -- Extend sums to the common superset S
  have hf_sum : (distinctTrees f).sum (fun τ => f.coeff τ * g τ) =
      S.sum (fun τ => f.coeff τ * g τ) := by
    apply Finset.sum_subset hf_sub
    intro τ _ hτ_not_in
    rw [coeff_eq_zero_of_not_in_distinctTrees f τ hτ_not_in, zero_mul]
  have hf'_sum : (distinctTrees f').sum (fun τ => f'.coeff τ * g τ) =
      S.sum (fun τ => f'.coeff τ * g τ) := by
    apply Finset.sum_subset hf'_sub
    intro τ _ hτ_not_in
    rw [coeff_eq_zero_of_not_in_distinctTrees f' τ hτ_not_in, zero_mul]
  rw [hf_sum, hf'_sum]
  -- Now both sums are over S with equal summands
  apply Finset.sum_congr rfl
  intro τ _
  rw [h τ]

end FormalSum

/-! ## The Index Set

The index set A ⊆ ℝ contains all homogeneities that can appear.

### Mathematical Background (Hairer 2014, Section 2)

For a regularity structure, the index set A must satisfy:
- A is a locally finite subset of ℝ (bounded below, finitely many elements in any bounded interval)
- 0 ∈ A (since 𝟙 has homogeneity 0)

For subcritical SPDEs, the index set is determined by:
1. The noise regularity α (determines |Ξ|)
2. The kernel order β (determines the gain from integration)
3. A homogeneity cutoff γ > 0 (only trees with |τ| < γ are included)

The subcriticality condition ensures that for fixed α, β and cutoff γ,
only finitely many trees have homogeneity less than γ.
-/

/-- Parameters for computing tree homogeneities. -/
structure HomogeneityParams where
  /-- The noise regularity α (e.g., -(d+2)/2 + ε for space-time white noise in d spatial dimensions) -/
  noiseRegularity : ℝ
  /-- The kernel order β (typically 2 for the heat kernel) -/
  kernelOrder : ℝ

/-- The index set A_γ for a regularity structure with homogeneity cutoff γ.
    This consists of all homogeneities |τ| where |τ| < γ.

    By Hairer's subcriticality analysis, this set is finite when:
    - β > 0 (integration improves regularity)
    - α + β > 0 (noise + one integration is positive)
-/
structure IndexSetRS (d : ℕ) where
  /-- The homogeneity parameters -/
  params : HomogeneityParams
  /-- The homogeneity cutoff γ. Only trees with |τ| < γ are included. -/
  cutoff : ℝ
  /-- Subcriticality: β > 0 (integration improves regularity) -/
  kernelOrder_pos : params.kernelOrder > 0
  /-- The cutoff must be positive (to include at least the unit) -/
  cutoff_pos : cutoff > 0

namespace IndexSetRS

variable {d : ℕ}

/-- Total derivative degree in a tree (sum of all |k| in I_k nodes). -/
def totalDerivDegree : TreeSymbol d → ℕ
  | .one => 0
  | .Xi => 0
  | .Poly _ => 0
  | .Integ k τ => k.degree + totalDerivDegree τ
  | .Prod τ₁ τ₂ => totalDerivDegree τ₁ + totalDerivDegree τ₂

/-- Sum of polynomial degrees in a tree. -/
def polyDegreeSum : TreeSymbol d → ℕ
  | .one => 0
  | .Xi => 0
  | .Poly k => k.degree
  | .Integ _ τ => polyDegreeSum τ
  | .Prod τ₁ τ₂ => polyDegreeSum τ₁ + polyDegreeSum τ₂

/-- Homogeneity formula in terms of counts and degrees.
    This is the key lemma for proving bounds. -/
theorem homogeneity_decomposition (α β : ℝ) (τ : TreeSymbol d) :
    TreeSymbol.homogeneity α β τ = τ.noiseCount * α + τ.integCount * β +
      (polyDegreeSum τ : ℝ) - (totalDerivDegree τ : ℝ) := by
  induction τ with
  | one => simp [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
                 polyDegreeSum, totalDerivDegree]
  | Xi => simp [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
                polyDegreeSum, totalDerivDegree]
  | Poly k =>
    simp [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
          polyDegreeSum, totalDerivDegree]
  | Integ k τ ih =>
    simp only [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
               polyDegreeSum, totalDerivDegree]
    rw [ih]
    push_cast
    ring
  | Prod τ₁ τ₂ ih1 ih2 =>
    simp only [TreeSymbol.homogeneity, TreeSymbol.noiseCount, TreeSymbol.integCount,
               polyDegreeSum, totalDerivDegree]
    rw [ih1, ih2]
    push_cast
    ring

/-- A tree is in the index set if its homogeneity is below the cutoff. -/
def isInIndexSet (A : IndexSetRS d) (τ : TreeSymbol d) : Prop :=
  TreeSymbol.homogeneity A.params.noiseRegularity A.params.kernelOrder τ < A.cutoff

/-- Check if a homogeneity value is in the index set. -/
def containsHomogeneity (A : IndexSetRS d) (h : ℝ) : Prop :=
  ∃ τ : TreeSymbol d, isInIndexSet A τ ∧
    TreeSymbol.homogeneity A.params.noiseRegularity A.params.kernelOrder τ = h

/-- The unit 𝟙 is always in the index set (since |𝟙| = 0 < γ). -/
theorem one_in_indexSet (A : IndexSetRS d) : isInIndexSet A .one := by
  simp only [isInIndexSet, TreeSymbol.homogeneity_one]
  exact A.cutoff_pos

/-- Helper: n * x ≥ c * min(x, 0) when n ≤ c and n ≥ 0 and c ≥ 0. -/
theorem nat_mul_ge_max_mul_min (n c : ℕ) (x : ℝ) (hn : n ≤ c) :
    (n : ℝ) * x ≥ (c : ℝ) * min x 0 := by
  by_cases hx : x ≥ 0
  · simp only [min_eq_right hx, mul_zero]
    exact mul_nonneg (Nat.cast_nonneg n) hx
  · push_neg at hx
    simp only [min_eq_left (le_of_lt hx)]
    have hn' : (n : ℝ) ≤ c := Nat.cast_le.mpr hn
    have hc : (c : ℝ) ≥ 0 := Nat.cast_nonneg c
    exact mul_le_mul_of_nonpos_right hn' (le_of_lt hx)

/-- The homogeneity of any tree is bounded below by its structural parameters.
    This is used to prove the index set is locally finite. -/
theorem homogeneity_lower_bound (A : IndexSetRS d) (τ : TreeSymbol d) :
    TreeSymbol.homogeneity A.params.noiseRegularity A.params.kernelOrder τ ≥
    τ.noiseCount * min A.params.noiseRegularity 0 +
    τ.integCount * min A.params.kernelOrder 0 -
    (totalDerivDegree τ : ℝ) := by
  rw [homogeneity_decomposition]
  have h1 : (τ.noiseCount : ℝ) * A.params.noiseRegularity ≥
      (τ.noiseCount : ℝ) * min A.params.noiseRegularity 0 := by
    by_cases hα : A.params.noiseRegularity ≥ 0
    · simp only [min_eq_right hα, mul_zero]
      exact mul_nonneg (Nat.cast_nonneg _) hα
    · push_neg at hα
      simp only [min_eq_left (le_of_lt hα)]
      exact le_refl _
  have h2 : (τ.integCount : ℝ) * A.params.kernelOrder ≥
      (τ.integCount : ℝ) * min A.params.kernelOrder 0 := by
    have hβ : A.params.kernelOrder > 0 := A.kernelOrder_pos
    simp only [min_eq_right (le_of_lt hβ), mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt hβ)
  have h3 : (polyDegreeSum τ : ℝ) ≥ 0 := Nat.cast_nonneg _
  linarith

/-- The index set for Φ⁴₃: α = -(3+2)/2 + ε ≈ -5/2, β = 2.
    For Φ⁴₃ theory in d=3 spatial dimensions, the cutoff γ = 0 suffices
    for the local subcritical solution theory. -/
noncomputable def phi4_3 : IndexSetRS 3 where
  params := ⟨(-5 : ℝ)/2, 2⟩
  cutoff := 1  -- γ = 1 includes trees up to homogeneity < 1
  kernelOrder_pos := by norm_num
  cutoff_pos := by norm_num

/-- The index set for KPZ: α = -(1+2)/2 + ε ≈ -3/2, β = 2.
    For KPZ equation in d=1 spatial dimension. -/
noncomputable def kpz : IndexSetRS 1 where
  params := ⟨(-3 : ℝ)/2, 2⟩
  cutoff := 1
  kernelOrder_pos := by norm_num
  cutoff_pos := by norm_num

end IndexSetRS

end SPDE.RegularityStructures
