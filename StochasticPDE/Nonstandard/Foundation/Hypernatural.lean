/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Real.Hyperreal

/-!
# Hypernatural Numbers

This file develops the hypernatural numbers ℕ* as part of the foundation for
nonstandard analysis.

## Main Definitions

* `Hypernat` - The type of hypernatural numbers
* `Hypernat.ofNatSeq` - Lift a sequence ℕ → ℕ to a hypernatural
* `Hypernat.ofNat'` - The embedding ℕ → ℕ*
* `Hypernat.omega` - The canonical infinite hypernatural

## References

* Goldblatt, "Lectures on the Hyperreals", Chapter 5
-/

open Hyperreal Filter Set

namespace SPDE.Nonstandard.Foundation

/-! ## Definition of Hypernatural Numbers -/

/-- A hyperreal is a hypernatural if it can be represented by a sequence of natural numbers. -/
def IsHypernat (x : ℝ*) : Prop :=
  ∃ f : ℕ → ℕ, x = ofSeq (fun n => (f n : ℝ))

/-- The type of hypernatural numbers. -/
def Hypernat : Type := { x : ℝ* // IsHypernat x }

namespace Hypernat

/-- Coercion to hyperreal -/
def toHyperreal (N : Hypernat) : ℝ* := N.val

instance : CoeOut Hypernat ℝ* := ⟨toHyperreal⟩

/-- The coercion to hyperreal is injective -/
theorem val_injective : Function.Injective (Subtype.val : Hypernat → ℝ*) :=
  Subtype.val_injective

/-- Extensionality for hypernaturals -/
@[ext]
theorem ext {N M : Hypernat} (h : N.val = M.val) : N = M :=
  Subtype.ext h

/-! ## Constructors -/

/-- Construct a hypernatural from a sequence of naturals -/
noncomputable def ofNatSeq (f : ℕ → ℕ) : Hypernat :=
  ⟨ofSeq (fun n => (f n : ℝ)), f, rfl⟩

theorem ofNatSeq_val (f : ℕ → ℕ) : (ofNatSeq f).val = ofSeq (fun n => (f n : ℝ)) := rfl

/-- The representing sequence (choice of representative) -/
noncomputable def toSeq (N : Hypernat) : ℕ → ℕ := Classical.choose N.2

theorem ofSeq_toSeq (N : Hypernat) : ofSeq (fun n => (N.toSeq n : ℝ)) = N.val :=
  (Classical.choose_spec N.2).symm

/-- Embed a standard natural number as a hypernatural -/
noncomputable def ofNat' (n : ℕ) : Hypernat :=
  ofNatSeq (fun _ => n)

/-- The value of ofNat' as a hyperreal -/
theorem ofNat'_val (n : ℕ) : (ofNat' n).val = (n : ℝ*) := rfl

/-- For a standard natural n, toSeq (ofNat' n) equals n almost everywhere.
    This follows from the defining property of toSeq. -/
theorem toSeq_ofNat'_ae (n : ℕ) : ∀ᶠ k in hyperfilter ℕ, (ofNat' n).toSeq k = n := by
  -- toSeq is chosen so that ofSeq (toSeq) = val
  -- For ofNat' n, val = ofSeq (fun _ => n) = n
  -- So ofSeq (fun k => toSeq k) = ofSeq (fun _ => n)
  -- By Germ.coe_eq, this means toSeq k = n almost everywhere
  have hspec : ofSeq (fun k => ((ofNat' n).toSeq k : ℝ)) = (ofNat' n).val := ofSeq_toSeq (ofNat' n)
  rw [ofNat'_val] at hspec
  -- Now we have ofSeq (fun k => toSeq k : ℝ) = (n : ℝ*)
  -- (n : ℝ*) = ofSeq (fun _ => n : ℝ) by definition
  -- Both sides are Germs, so we can use Germ.coe_eq
  have heq : (fun k => ((ofNat' n).toSeq k : ℝ)) =ᶠ[hyperfilter ℕ] (fun _ => (n : ℝ)) := by
    unfold ofSeq at hspec
    exact Germ.coe_eq.mp hspec
  exact heq.mono (fun k h => Nat.cast_injective h)

/-- The canonical infinite hypernatural: ω = [0, 1, 2, 3, ...] -/
noncomputable def omega : Hypernat :=
  ofNatSeq id

/-- omega as hyperreal equals Hyperreal.omega -/
theorem omega_val : omega.val = Hyperreal.omega := rfl

/-! ## Order Structure -/

/-- Less than or equal for hypernaturals -/
protected def le (N M : Hypernat) : Prop := N.val ≤ M.val

/-- Less than for hypernaturals -/
protected def lt (N M : Hypernat) : Prop := N.val < M.val

instance : LE Hypernat := ⟨Hypernat.le⟩
instance : LT Hypernat := ⟨Hypernat.lt⟩

theorem le_def' {N M : Hypernat} : N ≤ M ↔ N.val ≤ M.val := Iff.rfl
theorem lt_def' {N M : Hypernat} : N < M ↔ N.val < M.val := Iff.rfl

instance : Preorder Hypernat where
  le_refl := fun N => le_refl N.val
  le_trans := fun _ _ _ hNM hMK => le_def'.mpr (le_trans (le_def'.mp hNM) (le_def'.mp hMK))
  lt_iff_le_not_ge := fun N M => by
    simp only [lt_def', le_def']
    exact lt_iff_le_not_ge

instance : PartialOrder Hypernat where
  le_antisymm := fun _ _ hNM hMN => ext (le_antisymm (le_def'.mp hNM) (le_def'.mp hMN))

/-- If N ≤ M as hypernaturals, then toSeq N ≤ toSeq M almost everywhere -/
theorem toSeq_le_of_le {N M : Hypernat} (hle : N ≤ M) :
    ∀ᶠ n in hyperfilter ℕ, N.toSeq n ≤ M.toSeq n := by
  rw [le_def'] at hle
  -- N.val = ofSeq (toSeq N) and M.val = ofSeq (toSeq M)
  rw [← N.ofSeq_toSeq, ← M.ofSeq_toSeq] at hle
  -- hle : ofSeq (toSeq N) ≤ ofSeq (toSeq M)
  -- By ofSeq_le_ofSeq, this is equivalent to toSeq N n ≤ toSeq M n a.e.
  unfold ofSeq at hle
  have h := Germ.coe_le.mp hle
  -- h : ∀ᶠ n in hyperfilter ℕ, (N.toSeq n : ℝ) ≤ (M.toSeq n : ℝ)
  exact h.mono (fun n hle => Nat.cast_le.mp hle)

/-- Every hypernatural is non-negative -/
theorem zero_le (N : Hypernat) : (0 : ℝ*) ≤ N.val := by
  obtain ⟨f, hf⟩ := N.2
  rw [hf]
  have h : ∀ n, (0 : ℝ) ≤ f n := fun n => Nat.cast_nonneg (f n)
  -- ofSeq is coercion to Germ, use Germ.coe_le
  unfold ofSeq
  exact Germ.coe_le.mpr (Eventually.of_forall h)

theorem nonneg (N : Hypernat) : 0 ≤ N.val := zero_le N

/-! ## Arithmetic Operations -/

/-- Addition of hypernaturals -/
noncomputable def add (N M : Hypernat) : Hypernat :=
  ofNatSeq (fun n => N.toSeq n + M.toSeq n)

noncomputable instance : Add Hypernat := ⟨add⟩

theorem add_def (N M : Hypernat) : N + M = add N M := rfl

theorem add_val (N M : Hypernat) : (N + M).val = N.val + M.val := by
  change (add N M).val = N.val + M.val
  unfold add ofNatSeq
  rw [← N.ofSeq_toSeq, ← M.ofSeq_toSeq]
  -- Need to show: ofSeq (fun n => (N.toSeq n + M.toSeq n : ℝ)) = ofSeq f_N + ofSeq f_M
  -- Use that ofSeq is a homomorphism via Germ.coe_add
  unfold ofSeq
  -- The key: ↑(f + g) = ↑f + ↑g for functions, via Germ.coe_add
  have h : (fun n => (N.toSeq n : ℝ) + (M.toSeq n : ℝ)) =
           (fun n => (N.toSeq n : ℝ)) + (fun n => (M.toSeq n : ℝ)) := by
    funext n; rfl
  simp only [Nat.cast_add, h, Germ.coe_add]

/-- Multiplication of hypernaturals -/
noncomputable def mul (N M : Hypernat) : Hypernat :=
  ofNatSeq (fun n => N.toSeq n * M.toSeq n)

noncomputable instance : Mul Hypernat := ⟨mul⟩

theorem mul_def (N M : Hypernat) : N * M = mul N M := rfl

theorem mul_val (N M : Hypernat) : (N * M).val = N.val * M.val := by
  change (mul N M).val = N.val * M.val
  unfold mul ofNatSeq
  rw [← N.ofSeq_toSeq, ← M.ofSeq_toSeq]
  unfold ofSeq
  have h : (fun n => (N.toSeq n : ℝ) * (M.toSeq n : ℝ)) =
           (fun n => (N.toSeq n : ℝ)) * (fun n => (M.toSeq n : ℝ)) := by
    funext n; rfl
  simp only [Nat.cast_mul, h, Germ.coe_mul]

/-- Zero hypernatural -/
noncomputable def zero : Hypernat := ofNat' 0

noncomputable instance : Zero Hypernat := ⟨zero⟩

theorem zero_def : (0 : Hypernat) = zero := rfl

theorem zero_val : (0 : Hypernat).val = 0 := by
  change zero.val = 0
  unfold zero ofNat' ofNatSeq ofSeq
  simp only [Nat.cast_zero]
  exact Germ.coe_zero

/-- One hypernatural -/
noncomputable def one : Hypernat := ofNat' 1

noncomputable instance : One Hypernat := ⟨one⟩

theorem one_def : (1 : Hypernat) = one := rfl

theorem one_val : (1 : Hypernat).val = 1 := by
  change one.val = 1
  unfold one ofNat' ofNatSeq ofSeq
  simp only [Nat.cast_one]
  exact Germ.coe_one

/-! ## Basic Algebraic Properties -/

theorem add_comm (N M : Hypernat) : N + M = M + N := by
  apply ext
  rw [add_val, add_val, _root_.add_comm]

theorem add_assoc (N M K : Hypernat) : N + M + K = N + (M + K) := by
  apply ext
  rw [add_val, add_val, add_val, add_val, _root_.add_assoc]

theorem mul_comm (N M : Hypernat) : N * M = M * N := by
  apply ext
  rw [mul_val, mul_val, _root_.mul_comm]

theorem mul_assoc (N M K : Hypernat) : N * M * K = N * (M * K) := by
  apply ext
  rw [mul_val, mul_val, mul_val, mul_val, _root_.mul_assoc]

theorem add_zero (N : Hypernat) : N + 0 = N := by
  apply ext
  rw [add_val, zero_val, _root_.add_zero]

theorem zero_add (N : Hypernat) : 0 + N = N := by
  rw [add_comm, add_zero]

theorem mul_one (N : Hypernat) : N * 1 = N := by
  apply ext
  rw [mul_val, one_val, _root_.mul_one]

theorem one_mul (N : Hypernat) : 1 * N = N := by
  rw [mul_comm, mul_one]

theorem mul_zero (N : Hypernat) : N * 0 = 0 := by
  apply ext
  simp only [mul_val, zero_val, MulZeroClass.mul_zero]

theorem zero_mul (N : Hypernat) : 0 * N = 0 := by
  rw [mul_comm, mul_zero]

/-! ## Infinite Hypernaturals -/

/-- A hypernatural is infinite if it exceeds all standard naturals -/
def Infinite (N : Hypernat) : Prop := Hyperreal.Infinite N.val

/-- Equivalent: N is infinite iff it's infinitely positive (since N ≥ 0) -/
theorem infinite_iff_infinitePos (N : Hypernat) :
    Infinite N ↔ Hyperreal.InfinitePos N.val := by
  constructor
  · intro hN
    cases hN with
    | inl hp => exact hp
    | inr hn =>
      exfalso
      have h0 : N.val < 0 := hn 0
      exact not_lt.mpr (nonneg N) h0
  · intro hp
    left; exact hp

/-- omega is infinite -/
theorem omega_infinite : Infinite omega := by
  rw [Infinite, omega_val]
  exact Hyperreal.infinite_omega

/-- Standard naturals are finite -/
theorem ofNat'_not_infinite (n : ℕ) : ¬Infinite (ofNat' n) := by
  rw [Infinite, ofNat'_val]
  exact Hyperreal.not_infinite_real n

/-- If f : ℕ → ℕ tends to infinity, then ofNatSeq f is infinite -/
theorem ofNatSeq_infinite (f : ℕ → ℕ) (hf : Tendsto (fun n => (f n : ℝ)) atTop atTop) :
    Infinite (ofNatSeq f) := by
  rw [infinite_iff_infinitePos, ofNatSeq_val]
  intro M
  have hev : ∀ᶠ n in atTop, M < f n := hf.eventually_gt_atTop M
  have hcofin : {n | M < f n}ᶜ.Finite := by
    rw [eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine (finite_lt_nat N).subset ?_
    intro n hn
    simp only [mem_compl_iff, mem_setOf_eq, not_lt] at hn
    simp only [mem_setOf_eq]
    by_contra hge
    exact not_lt.mpr hn (hN n (Nat.not_lt.mp hge))
  exact ofSeq_lt_ofSeq.mpr (mem_hyperfilter_of_finite_compl hcofin)

/-- For infinite N, the set {n | b < N.toSeq n} is in the hyperfilter for any bound b.
    This is the correct ultrafilter-based statement - we do NOT claim pointwise convergence,
    only "almost everywhere" in the ultrafilter sense. -/
theorem toSeq_eventually_gt_of_infinite (N : Hypernat) (hN : Infinite N) (b : ℕ) :
    ∀ᶠ n in hyperfilter ℕ, b < N.toSeq n := by
  rw [infinite_iff_infinitePos] at hN
  have hgt : (b : ℝ*) < N.val := hN b
  rw [← N.ofSeq_toSeq] at hgt
  unfold ofSeq at hgt
  have hae : ∀ᶠ n in hyperfilter ℕ, (b : ℝ) < (N.toSeq n : ℝ) := Germ.coe_lt.mp hgt
  exact hae.mono (fun n h => Nat.cast_lt.mp h)

/-- Successor of hypernatural -/
noncomputable def succ (N : Hypernat) : Hypernat := N + 1

theorem succ_val (N : Hypernat) : N.succ.val = N.val + 1 := by
  unfold succ
  rw [add_val, one_val]

/-- N < N + 1 -/
theorem lt_succ (N : Hypernat) : N < N.succ := by
  rw [lt_def', succ_val]
  exact lt_add_of_pos_right N.val (by norm_num : (0 : ℝ*) < 1)

/-! ## Comparison with Standard Naturals -/

/-- Every standard natural is less than any infinite hypernatural -/
theorem ofNat'_lt_of_infinite (n : ℕ) (N : Hypernat) (hN : Infinite N) : ofNat' n < N := by
  rw [lt_def', ofNat'_val]
  rw [infinite_iff_infinitePos] at hN
  exact hN n

/-! ## Hyperfinite Range -/

/-- The hyperfinite range {0, 1, ..., N-1} represented as data -/
structure HyperfiniteRange where
  /-- The upper bound (exclusive) -/
  bound : Hypernat
  /-- The bound is positive -/
  bound_pos : (0 : ℝ*) < bound.val

namespace HyperfiniteRange

/-- The cardinality of the range -/
def card (R : HyperfiniteRange) : Hypernat := R.bound

/-- Check if a hypernatural is in the range -/
def inRange (R : HyperfiniteRange) (k : Hypernat) : Prop :=
  k < R.bound

instance : Membership Hypernat HyperfiniteRange where
  mem := fun (R : HyperfiniteRange) (k : Hypernat) => k < R.bound

theorem mem_iff (R : HyperfiniteRange) (k : Hypernat) : k ∈ R ↔ k < R.bound :=
  Iff.rfl

end HyperfiniteRange

/-! ## Standard Part for Bounded Hypernaturals -/

/-- The standard part of a bounded hypernatural is a natural number -/
noncomputable def stNat (N : Hypernat) (_hbdd : ∃ M : ℕ, N.val ≤ M) : ℕ :=
  Nat.floor (st N.val)

/-- A bounded hypernatural is not infinite -/
theorem not_infinite_of_bdd (N : Hypernat) (hbdd : ∃ M : ℕ, N.val ≤ M) :
    ¬Hyperreal.Infinite N.val := by
  obtain ⟨M, hM⟩ := hbdd
  rw [not_infinite_iff_exist_lt_gt]
  refine ⟨-1, M + 1, ?_, ?_⟩
  · calc (-1 : ℝ*) < 0 := by norm_num
      _ ≤ N.val := nonneg N
  · calc N.val ≤ (M : ℝ*) := hM
      _ < M + 1 := by exact_mod_cast Nat.lt_succ_self M

/-- The standard part of a nonnegative finite hyperreal is nonnegative -/
theorem st_nonneg' {x : ℝ*} (hx : 0 ≤ x) (hni : ¬Hyperreal.Infinite x) : 0 ≤ st x := by
  have h0 : ¬Hyperreal.Infinite (0 : ℝ*) := not_infinite_real 0
  rw [← st_id_real 0]
  exact st_le_of_le h0 hni hx

theorem stNat_spec (N : Hypernat) (hbdd : ∃ M : ℕ, N.val ≤ M) :
    (stNat N hbdd : ℝ) ≤ st N.val ∧ st N.val < stNat N hbdd + 1 := by
  constructor
  · exact Nat.floor_le (st_nonneg' (nonneg N) (not_infinite_of_bdd N hbdd))
  · exact Nat.lt_floor_add_one (st N.val)

/-! ## Hypernatural Floor Function -/

/-- Floor of a nonnegative hyperreal as a hypernatural.
    For x = ofSeq f with f n ≥ 0, we define floor(x) = ofNatSeq (fun n => ⌊f n⌋₊).
    This satisfies floor(x).val ≤ x < floor(x).val + 1 (almost everywhere). -/
noncomputable def hyperfloor (x : ℝ*) (_hx : 0 ≤ x) : Hypernat :=
  ofNatSeq (fun n => Nat.floor (Classical.choose (ofSeq_surjective x) n))

/-- The hyperfloor satisfies floor(x) ≤ x.
    Proof: For the chosen representative f of x, we have ⌊f n⌋₊ ≤ f n when f n ≥ 0.
    Since x ≥ 0, we have f n ≥ 0 almost everywhere, so the result follows. -/
theorem hyperfloor_le (x : ℝ*) (hx : 0 ≤ x) : (hyperfloor x hx).val ≤ x := by
  unfold hyperfloor ofNatSeq ofSeq
  have hspec := Classical.choose_spec (ofSeq_surjective x)
  conv_rhs => rw [← hspec]
  unfold ofSeq
  apply Germ.coe_le.mpr
  -- x ≥ 0 means the representative sequence is ≥ 0 almost everywhere
  have hpos : ∀ᶠ n in hyperfilter ℕ, 0 ≤ Classical.choose (ofSeq_surjective x) n := by
    rw [← hspec] at hx
    unfold ofSeq at hx
    exact Germ.coe_le.mp hx
  exact hpos.mono (fun n hn => Nat.floor_le hn)

/-- The hyperfloor satisfies x < floor(x) + 1. -/
theorem lt_hyperfloor_succ (x : ℝ*) (_hx : 0 ≤ x) : x < (hyperfloor x _hx).val + 1 := by
  unfold hyperfloor ofNatSeq ofSeq
  have hspec := Classical.choose_spec (ofSeq_surjective x)
  conv_lhs => rw [← hspec]
  unfold ofSeq
  rw [← Germ.coe_one, ← Germ.coe_add]
  apply Germ.coe_lt.mpr
  apply Filter.Eventually.of_forall
  intro n
  exact Nat.lt_floor_add_one _

/-- Hyperfloor is monotone: if x ≤ y then floor(x) ≤ floor(y). -/
theorem hyperfloor_mono {x y : ℝ*} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    hyperfloor x hx ≤ hyperfloor y hy := by
  rw [le_def']
  -- Need: (hyperfloor x).val ≤ (hyperfloor y).val
  -- hyperfloor x = ofNatSeq (fun n => Nat.floor (rep_x n))
  -- hyperfloor y = ofNatSeq (fun n => Nat.floor (rep_y n))
  -- Since x ≤ y, we have rep_x n ≤ rep_y n almost everywhere
  -- By Nat.floor_le_floor, floor(rep_x n) ≤ floor(rep_y n) almost everywhere
  unfold hyperfloor ofNatSeq ofSeq
  apply Germ.coe_le.mpr
  -- Get the representative sequences
  have hspec_x := Classical.choose_spec (ofSeq_surjective x)
  have hspec_y := Classical.choose_spec (ofSeq_surjective y)
  -- The inequality x ≤ y becomes rep_x ≤ rep_y almost everywhere
  have hrep_le : ∀ᶠ n in hyperfilter ℕ,
      Classical.choose (ofSeq_surjective x) n ≤ Classical.choose (ofSeq_surjective y) n := by
    rw [← hspec_x, ← hspec_y] at hxy
    unfold ofSeq at hxy
    exact Germ.coe_le.mp hxy
  -- Also need 0 ≤ rep_x n almost everywhere (for floor to be well-defined)
  have hrep_nn : ∀ᶠ n in hyperfilter ℕ, 0 ≤ Classical.choose (ofSeq_surjective x) n := by
    rw [← hspec_x] at hx
    unfold ofSeq at hx
    exact Germ.coe_le.mp hx
  -- Combine and apply Nat.floor_le_floor
  apply Filter.Eventually.mono (hrep_le.and hrep_nn)
  intro n ⟨hle, hnn⟩
  exact Nat.cast_le.mpr (Nat.floor_le_floor hle)

/-- Given a positive standard real t and a positive hyperreal N (typically infinite),
    compute the hypernatural k such that k * (1/N) ≈ t.
    This is useful for finding the time step index. -/
noncomputable def timeStepIndex (t : ℝ) (ht : 0 ≤ t) (N : Hypernat) (hNpos : 0 < N.val) : Hypernat :=
  hyperfloor ((t : ℝ*) * N.val) (by
    apply mul_nonneg
    · exact_mod_cast ht
    · exact le_of_lt hNpos)

/-- The time step index satisfies k * dt ≤ t -/
theorem timeStepIndex_mul_dt_le (t : ℝ) (ht : 0 ≤ t) (N : Hypernat) (hNpos : 0 < N.val) :
    (timeStepIndex t ht N hNpos).val * (1 / N.val) ≤ t := by
  unfold timeStepIndex
  have hfloor := hyperfloor_le ((t : ℝ*) * N.val) (by
    apply mul_nonneg
    · exact_mod_cast ht
    · exact le_of_lt hNpos)
  -- hfloor: (hyperfloor (t * N.val) _).val ≤ t * N.val
  -- Need: (hyperfloor (t * N.val) _).val * (1 / N.val) ≤ t
  have hNpos' : N.val ≠ 0 := ne_of_gt hNpos
  calc (hyperfloor ((t : ℝ*) * N.val) _).val * (1 / N.val)
      = (hyperfloor ((t : ℝ*) * N.val) _).val / N.val := by ring
    _ ≤ ((t : ℝ*) * N.val) / N.val := by
        apply div_le_div_of_nonneg_right hfloor (le_of_lt hNpos)
    _ = (t : ℝ*) := by field_simp

/-- The time step index satisfies t < (k+1) * dt -/
theorem lt_timeStepIndex_succ_mul_dt (t : ℝ) (ht : 0 ≤ t) (N : Hypernat) (hNpos : 0 < N.val) :
    (t : ℝ*) < ((timeStepIndex t ht N hNpos).val + 1) * (1 / N.val) := by
  unfold timeStepIndex
  have hfloor := lt_hyperfloor_succ ((t : ℝ*) * N.val) (by
    apply mul_nonneg
    · exact_mod_cast ht
    · exact le_of_lt hNpos)
  -- hfloor: t * N.val < (hyperfloor (t * N.val) _).val + 1
  -- Need: t < ((hyperfloor (t * N.val) _).val + 1) * (1 / N.val)
  have hNpos' : N.val ≠ 0 := ne_of_gt hNpos
  calc (t : ℝ*) = ((t : ℝ*) * N.val) / N.val := by field_simp
    _ < ((hyperfloor ((t : ℝ*) * N.val) _).val + 1) / N.val := by
        apply div_lt_div_of_pos_right hfloor hNpos
    _ = ((hyperfloor ((t : ℝ*) * N.val) _).val + 1) * (1 / N.val) := by ring

/-- timeStepIndex is monotone in the time parameter -/
theorem timeStepIndex_mono {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s ≤ t)
    (N : Hypernat) (hNpos : 0 < N.val) :
    timeStepIndex s hs N hNpos ≤ timeStepIndex t ht N hNpos := by
  unfold timeStepIndex
  apply hyperfloor_mono
  -- (s : ℝ*) * N.val ≤ (t : ℝ*) * N.val
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hst
  · exact le_of_lt hNpos

end Hypernat

end SPDE.Nonstandard.Foundation
