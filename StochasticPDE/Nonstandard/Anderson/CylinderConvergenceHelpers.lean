/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.Nonstandard.Anderson.LocalCLT
import StochasticPDE.Nonstandard.Anderson.BinomGaussRatioHelpers
import StochasticPDE.Nonstandard.Anderson.RatioConvergenceHelpers
import StochasticPDE.Nonstandard.Foundation.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.ContinuousOn

/-!
# Cylinder Convergence Helpers

Infrastructure for proving `cylinder_prob_convergence`, the key bridge between
the hyperfinite random walk and Wiener measure.

## Main Results

* `gaussianDensitySigma_continuous` - continuity of the Gaussian density
* `scaledProb_eq_walkIntervalProb` - combinatorial rewrite of the scaled probability
* `binomProb_ratio_near_one` - ratio convergence for the local CLT

## Strategy

The proof of `cylinder_prob_convergence` proceeds by:
1. Rewriting scaledProb as a sum of binomial probabilities (combinatorial step)
2. Showing each binomial probability is close to the Gaussian density × mesh width
3. Showing the Riemann sum converges to the integral
-/

open Real Finset MeasureTheory

namespace SPDE.Nonstandard

/-! ## Continuity of Gaussian Density -/

/-- The Gaussian density gaussianDensitySigma(σ, ·) is continuous for σ > 0. -/
theorem gaussianDensitySigma_continuous {σ : ℝ} (hσ : 0 < σ) :
    Continuous (gaussianDensitySigma σ) := by
  unfold gaussianDensitySigma
  simp only [hσ, ↓reduceIte]
  apply Continuous.mul
  · exact continuous_const
  · exact continuous_exp.comp ((continuous_neg.comp (continuous_pow 2)).div_const _)

/-- The Gaussian density is nonneg -/
theorem gaussianDensitySigma_nonneg {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    0 ≤ gaussianDensitySigma σ x := by
  unfold gaussianDensitySigma
  simp only [hσ, ↓reduceIte]
  apply mul_nonneg
  · apply div_nonneg zero_le_one
    apply mul_nonneg (le_of_lt hσ)
    exact Real.sqrt_nonneg _
  · exact le_of_lt (Real.exp_pos _)

/-- The Gaussian density is bounded above by its peak value at x=0. -/
theorem gaussianDensitySigma_le_peak {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    gaussianDensitySigma σ x ≤ 1 / (σ * Real.sqrt (2 * Real.pi)) := by
  unfold gaussianDensitySigma
  simp only [hσ, ↓reduceIte]
  have hσ_sqrt : 0 < σ * Real.sqrt (2 * Real.pi) := by positivity
  apply mul_le_of_le_one_right (div_nonneg one_pos.le (le_of_lt hσ_sqrt))
  rw [Real.exp_le_one_iff]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos.mpr (sq_nonneg x)
  · positivity

/-! ## Floor/Ceiling Ratio Convergence

For k = ⌊tN⌋, the ratio k/(tN) → 1 as N → ∞.
-/

/-- For t > 0, the floor ⌊tN⌋/N → t as N → ∞. -/
theorem floor_ratio_tendsto (t : ℝ) (ht : 0 < t) :
    Filter.Tendsto (fun N : ℕ => (Nat.floor (t * N) : ℝ) / N) Filter.atTop (nhds t) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- For N ≥ N₀, 1/N < ε, so |⌊tN⌋/N - t| ≤ 1/N < ε
  use Nat.ceil (2 / ε)
  intro N hN
  rw [Real.dist_eq]
  -- N ≥ ⌈2/ε⌉ ≥ 2/ε > 1/ε > 0
  have hNε : (2 / ε : ℝ) ≤ N := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  have hN_pos : (0 : ℝ) < N := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hε]
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have h_floor_le : (Nat.floor (t * N) : ℝ) ≤ t * N := Nat.floor_le (by positivity)
  have h_floor_ge : t * N - 1 ≤ (Nat.floor (t * N) : ℝ) := by
    have := Nat.lt_floor_add_one (t * N)
    push_cast at this ⊢
    linarith [Nat.floor_le (show 0 ≤ t * N by positivity)]
  -- |⌊tN⌋/N - t| ≤ 1/N < ε
  -- Upper: ⌊tN⌋/N ≤ t (floor ≤ original)
  have hup : ↑⌊t * ↑N⌋₊ / ↑N ≤ t := by
    rw [div_le_iff₀ hN_pos]; linarith
  -- Lower: t - 1/N ≤ ⌊tN⌋/N (floor > original - 1)
  have hlow : t - 1 / ↑N ≤ ↑⌊t * ↑N⌋₊ / ↑N := by
    rw [le_div_iff₀ hN_pos]
    have : (t - 1 / ↑N) * ↑N = t * ↑N - 1 := by field_simp
    linarith
  -- 1/N < ε since N ≥ 2/ε, so εN ≥ 2 > 1
  have h1N_lt_ε : 1 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hN_pos]
    have : ε * ↑N ≥ ε * (2 / ε) := by nlinarith
    have : ε * (2 / ε) = 2 := by field_simp
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- For t > 0 and N large enough, k = ⌊tN⌋ ≥ some threshold. -/
theorem floor_eventually_large (t : ℝ) (ht : 0 < t) (M : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, M ≤ Nat.floor (t * N) := by
  use Nat.ceil ((M + 1) / t)
  intro N hN
  have htN : (M : ℝ) < t * N := by
    calc (M : ℝ) < M + 1 := by linarith
      _ = t * ((M + 1) / t) := by field_simp
      _ ≤ t * Nat.ceil ((M + 1) / t) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt ht)
          exact Nat.le_ceil _
      _ ≤ t * N := by nlinarith [show (Nat.ceil ((↑M + 1) / t) : ℝ) ≤ N from by exact_mod_cast hN]
  exact Nat.le_floor (le_of_lt htN)

/-! ## Combinatorial Decomposition

Show that scaledProb (counting over Fin N → Bool) equals
a sum of binomial coefficients (walkIntervalProb).

The key fact: partialSumFin N flips k depends only on the first k flips,
so the remaining N-k flips contribute a factor of 2^(N-k).
-/

/-- partialSumFin only depends on flips with index < k.
    If two flip sequences agree on indices < k, they have the same partial sum. -/
theorem partialSumFin_depends_on_prefix (N : ℕ) (f g : Fin N → Bool) (k : ℕ)
    (hagree : ∀ i : Fin N, i.val < k → f i = g i) :
    partialSumFin N f k = partialSumFin N g k := by
  unfold partialSumFin
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  congr 1
  exact hagree i hi

/-- Count of true values among the first k positions of a flip sequence. -/
def countTruesBelow (N : ℕ) (f : Fin N → Bool) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < k ∧ f i = true)).card

/-- The set of indices < k in Fin N has cardinality k when k ≤ N. -/
theorem card_filter_lt (N k : ℕ) (hk : k ≤ N) :
    ((Finset.univ : Finset (Fin N)).filter (fun i : Fin N => i.val < k)).card = k := by
  have hbij : ((Finset.univ : Finset (Fin N)).filter (fun i : Fin N => i.val < k)).card =
      (Finset.univ : Finset (Fin k)).card :=
    Finset.card_bij'
      (fun a ha => ⟨a.val, (Finset.mem_filter.mp ha).2⟩)
      (fun b _ => Fin.castLE hk b)
      (fun _ _ => Finset.mem_univ _)
      (fun b _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩)
      (fun _ _ => Fin.ext rfl)
      (fun _ _ => Fin.ext rfl)
  rw [hbij, Finset.card_univ, Fintype.card_fin]

/-- partialSumFin equals 2 * countTruesBelow - k (as integers).
    Since each true contributes +1 and each false contributes -1,
    the sum is #true - #false = #true - (k - #true) = 2·#true - k. -/
theorem partialSumFin_eq_countTrues (N : ℕ) (f : Fin N → Bool) (k : ℕ) (hk : k ≤ N) :
    (partialSumFin N f k : ℤ) = 2 * ↑(countTruesBelow N f k) - ↑k := by
  unfold partialSumFin countTruesBelow
  set s := (Finset.univ : Finset (Fin N)).filter (fun i : Fin N => i.val < k) with hs_def
  have hcard_s : s.card = k := card_filter_lt N k hk
  -- Decompose s into true and false parts
  have hcover : (s.filter (fun i => f i = true) ∪
      s.filter (fun a => ¬(f a = true))) = s :=
    Finset.filter_union_filter_not_eq (p := fun i => f i = true) s
  have hdisj : Disjoint (s.filter (fun i => f i = true))
      (s.filter (fun a => ¬(f a = true))) :=
    Finset.disjoint_filter_filter_not s s (fun i => f i = true)
  -- Rewrite sum using the partition
  conv_lhs => rw [← hcover]
  rw [Finset.sum_union hdisj]
  -- On true part, boolToInt = 1
  have htrue_val : ∀ i ∈ s.filter (fun i => f i = true), boolToInt (f i) = (1 : ℤ) := by
    intro i hi; rw [Finset.mem_filter] at hi
    unfold boolToInt; simp [hi.2]
  -- On false part, boolToInt = -1
  have hfalse_val : ∀ i ∈ s.filter (fun a => ¬(f a = true)),
      boolToInt (f i) = (-1 : ℤ) := by
    intro i hi; rw [Finset.mem_filter] at hi
    unfold boolToInt; simp [hi.2]
  rw [Finset.sum_congr rfl htrue_val, Finset.sum_congr rfl hfalse_val]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg_one]
  -- Card computation
  have hcard_union : (s.filter (fun i => f i = true)).card +
      (s.filter (fun a => ¬(f a = true))).card = k := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hcover] at h; rw [← h, hcard_s]
  -- True card equals countTruesBelow
  suffices htrue : (s.filter (fun i => f i = true)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun i => i.val < k ∧ f i = true)).card by
    rw [htrue] at hcard_union ⊢; omega
  congr 1; ext i
  constructor
  · intro hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, ⟨(Finset.mem_filter.mp hi.1).2, hi.2⟩⟩
  · intro hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2.1⟩, hi.2.2⟩

/-- Number of boolean functions on Fin k with exactly j trues equals C(k,j).
    Uses bijection with Finset.powersetCard j univ. -/
theorem card_bool_trues_eq_choose (k j : ℕ) (_hj : j ≤ k) :
    ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun g => (Finset.univ.filter (fun i => g i = true)).card = j)).card = Nat.choose k j := by
  -- Rewrite RHS as card of powersetCard
  rw [show Nat.choose k j = ((Finset.univ : Finset (Fin k)).powersetCard j).card from by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]]
  -- Bijection with powersetCard j univ via g ↦ {i | g i = true}
  exact Finset.card_bij'
    (fun g _ => Finset.univ.filter (fun i => g i = true))
    (fun S _ => fun i => decide (i ∈ S))
    (fun g hg => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      exact Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hg⟩)
    (fun S hS => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.mem_powersetCard] at hS
      have : Finset.univ.filter (fun i => decide (i ∈ S) = true) = S := by
        ext i; simp [Finset.mem_filter, decide_eq_true_eq]
      rw [show (Finset.univ.filter (fun i => (fun i => decide (i ∈ S)) i = true)).card =
          S.card from by rw [this]]; exact hS.2)
    (fun g _ => by ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    decide_eq_true_eq]; cases g i <;> simp)
    (fun S _ => by ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                    decide_eq_true_eq])

/-- countTruesBelow equals the cardinality of a filter over the prefix type Fin k. -/
private lemma countTruesBelow_eq_filter_prefix {N k : ℕ} (f : Fin N → Bool) (hk : k ≤ N) :
    countTruesBelow N f k =
    ((Finset.univ : Finset (Fin k)).filter
      (fun i => f ⟨i.val, i.isLt.trans_le hk⟩ = true)).card := by
  unfold countTruesBelow
  exact Finset.card_bij'
    (fun a ha => ⟨a.val, (Finset.mem_filter.mp ha).2.1⟩)
    (fun b _ => ⟨b.val, b.isLt.trans_le hk⟩)
    (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩)
    (fun b hb => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨b.isLt, (Finset.mem_filter.mp hb).2⟩⟩)
    (fun _ _ => Fin.ext rfl)
    (fun _ _ => Fin.ext rfl)

/-- Product counting: #{f : Fin N → Bool | countTruesBelow f k = j} = C(k,j) × 2^(N-k).
    Each choice of prefix (j trues among k) combines with any suffix. -/
theorem card_prefix_suffix_product (N k j : ℕ) (hk : k ≤ N) (hj : j ≤ k) :
    ((Finset.univ : Finset (Fin N → Bool)).filter
      (fun f => countTruesBelow N f k = j)).card = Nat.choose k j * 2 ^ (N - k) := by
  -- Define the target set
  let prefixSet := (Finset.univ : Finset (Fin k → Bool)).filter
    (fun g => (Finset.univ.filter (fun i => g i = true)).card = j)
  let suffixSet := (Finset.univ : Finset (Fin (N - k) → Bool))
  let target := prefixSet ×ˢ suffixSet
  -- Define forward and backward maps
  let fwd : (Fin N → Bool) → (Fin k → Bool) × (Fin (N - k) → Bool) :=
    fun f => (fun i => f ⟨i.val, i.isLt.trans_le hk⟩, fun i => f ⟨k + i.val, by omega⟩)
  let bwd : (Fin k → Bool) × (Fin (N - k) → Bool) → (Fin N → Bool) :=
    fun p => fun i => if hlt : i.val < k then p.1 ⟨i.val, hlt⟩
                      else p.2 ⟨i.val - k, by omega⟩
  -- Step 1: card(source) = card(target) via bijection
  let source := (Finset.univ : Finset (Fin N → Bool)).filter
    (fun f => countTruesBelow N f k = j)
  suffices hsuff : source.card = target.card by
    rw [hsuff, Finset.card_product, card_bool_trues_eq_choose k j hj]
    congr 1
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  -- Step 2: Establish bijection using card_bij'
  show source.card = target.card
  apply Finset.card_bij'
    (fun f _ => fwd f) (fun p _ => bwd p)
  · -- hi: forward maps source into target
    intro f hf
    simp only [source, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [target, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
               suffixSet]
    refine ⟨?_, trivial⟩
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← countTruesBelow_eq_filter_prefix f hk]; exact hf
  · -- hj_mem: backward maps target into source
    intro p hp
    simp only [target, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
               suffixSet] at hp
    simp only [source, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [countTruesBelow_eq_filter_prefix (bwd p) hk]
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [← hp.1]; congr 1
    refine Finset.filter_congr (fun i _ => ?_)
    dsimp only [bwd]; rw [dif_pos i.isLt]
  · -- left_inv: bwd (fwd f) = f
    intro f _; ext ⟨i, hi⟩
    show bwd (fwd f) ⟨i, hi⟩ = f ⟨i, hi⟩
    dsimp only [fwd, bwd]
    split
    · next hlt => rfl
    · next hlt =>
        simp only [show k + (i - k) = i from by omega]
  · -- right_inv: fwd (bwd p) = p
    intro p _
    show fwd (bwd p) = p
    ext ⟨i, hi⟩
    · -- First component
      show (fwd (bwd p)).1 ⟨i, hi⟩ = p.1 ⟨i, hi⟩
      simp only [fwd, bwd, show (i : ℕ) < k from hi, ↓reduceDIte]
    · -- Second component
      show (fwd (bwd p)).2 ⟨i, hi⟩ = p.2 ⟨i, hi⟩
      dsimp only [fwd, bwd]
      simp only [show ¬((k + ↑i : ℕ) < k) from by omega, ↓reduceDIte,
                 show k + (i : ℕ) - k = i from by omega]

/-- countTruesBelow is at most k -/
private lemma countTruesBelow_le_k (N k : ℕ) (f : Fin N → Bool) (hk : k ≤ N) :
    countTruesBelow N f k ≤ k := by
  unfold countTruesBelow
  calc ((Finset.univ.filter (fun i : Fin N => i.val < k ∧ f i = true)).card)
      ≤ ((Finset.univ.filter (fun i : Fin N => i.val < k)).card) := by
        apply Finset.card_le_card
        intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact And.left
    _ = k := card_filter_lt N k hk

/-- Card of walk filter equals sum of fiber cardinalities (ℕ identity). -/
private lemma card_walk_filter_eq_sum (N k : ℕ) (hk : k ≤ N) (a b dx : ℝ) :
    ((Finset.univ : Finset (Fin N → Bool)).filter
      (fun f => a ≤ dx * (2 * ↑(countTruesBelow N f k) - ↑k) ∧
                dx * (2 * ↑(countTruesBelow N f k) - ↑k) ≤ b)).card =
    (Finset.range (k + 1)).sum (fun j =>
      if a ≤ dx * (2 * (j : ℝ) - ↑k) ∧ dx * (2 * (j : ℝ) - ↑k) ≤ b
      then Nat.choose k j * 2 ^ (N - k) else 0) := by
  set S := Finset.univ.filter (fun f : Fin N → Bool =>
    a ≤ dx * (2 * ↑(countTruesBelow N f k) - ↑k) ∧
    dx * (2 * ↑(countTruesBelow N f k) - ↑k) ≤ b) with hS_def
  set g := fun f : Fin N → Bool => countTruesBelow N f k with hg_def
  have hg_range : (S : Set _).MapsTo g ↑(Finset.range (k + 1)) := by
    intro f _; simp only [Finset.coe_range, Set.mem_Iio, g]
    exact Nat.lt_succ_of_le (countTruesBelow_le_k N k f hk)
  rw [Finset.card_eq_sum_card_fiberwise hg_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases hcond : a ≤ dx * (2 * (j : ℝ) - ↑k) ∧ dx * (2 * (j : ℝ) - ↑k) ≤ b
  · rw [if_pos hcond]
    have hfiber_eq : (S.filter (fun f => g f = j)) =
        Finset.univ.filter (fun f => countTruesBelow N f k = j) := by
      ext f; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS_def, g]
      constructor
      · exact fun ⟨_, h⟩ => h
      · intro h; exact ⟨by rw [h]; exact hcond, h⟩
    rw [hfiber_eq]
    exact card_prefix_suffix_product N k j hk hjk
  · rw [if_neg hcond]
    have hempty : S.filter (fun f => g f = j) = ∅ := by
      by_contra h
      obtain ⟨f, hf⟩ := Finset.nonempty_iff_ne_empty.mpr h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS_def, g] at hf
      obtain ⟨hc, hctb⟩ := hf
      rw [hctb] at hc; exact hcond hc
    simp [hempty]

/-- The count of flip sequences satisfying a condition on S_k equals
    walkIntervalProb(k, a, b, 1/√N) × 2^N.

    Specifically:
    #{f : Fin N → Bool | a ≤ S_k(f)/√N ≤ b} / 2^N = walkIntervalProb(k, a, b, 1/√N)

    where S_k(f) = partialSumFin N f k depends only on the first k flips. -/
theorem scaledProb_eq_walkIntervalProb (N : ℕ) (k : ℕ) (hk : k ≤ N) (a b : ℝ)
    (_hN : 0 < N) :
    ((Finset.univ : Finset (Fin N → Bool)).filter
      (fun flips =>
        let walk := (partialSumFin N flips k : ℝ) / Real.sqrt N
        a ≤ walk ∧ walk ≤ b)).card / (2^N : ℝ) =
    walkIntervalProb k a b (1 / Real.sqrt N) := by
  set dx : ℝ := 1 / Real.sqrt N with hdx_def
  -- Step 1: Walk value equals dx * (2*ctb - k)
  have hwalk : ∀ f : Fin N → Bool,
      (partialSumFin N f k : ℝ) / Real.sqrt N =
      dx * (2 * ↑(countTruesBelow N f k) - ↑k) := by
    intro f
    have h := partialSumFin_eq_countTrues N f k hk
    have hcast : (partialSumFin N f k : ℝ) = 2 * (countTruesBelow N f k : ℝ) - (k : ℝ) := by
      exact_mod_cast h
    rw [hcast]; ring
  -- Step 2: Rewrite filter using ctb
  have hfilter_eq :
      (Finset.univ.filter (fun f =>
        let walk := (partialSumFin N f k : ℝ) / Real.sqrt N
        a ≤ walk ∧ walk ≤ b)).card =
      (Finset.univ.filter (fun f =>
        a ≤ dx * (2 * ↑(countTruesBelow N f k) - ↑k) ∧
        dx * (2 * ↑(countTruesBelow N f k) - ↑k) ≤ b)).card := by
    congr 1; apply Finset.filter_congr; intro f _; simp only [hwalk f]
  rw [show ((Finset.univ.filter _).card : ℝ) =
      ((Finset.univ.filter (fun f =>
        a ≤ dx * (2 * ↑(countTruesBelow N f k) - ↑k) ∧
        dx * (2 * ↑(countTruesBelow N f k) - ↑k) ≤ b)).card : ℝ) from by
    exact_mod_cast hfilter_eq]
  -- Step 3: Apply fiber decomposition (ℕ identity)
  have hcard := card_walk_filter_eq_sum N k hk a b dx
  rw [show ((Finset.univ.filter _).card : ℝ) =
      ((Finset.range (k + 1)).sum (fun j =>
        if a ≤ dx * (2 * (j : ℝ) - ↑k) ∧ dx * (2 * (j : ℝ) - ↑k) ≤ b
        then Nat.choose k j * 2 ^ (N - k) else 0) : ℝ) from by
    exact_mod_cast hcard]
  -- Step 4: Push ℕ→ℝ cast, divide by 2^N, match with walkIntervalProb
  rw [Finset.sum_div]
  unfold walkIntervalProb
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases hcond : a ≤ dx * (2 * (j : ℝ) - ↑k) ∧ dx * (2 * (j : ℝ) - ↑k) ≤ b
  · rw [if_pos hcond]
    -- Show walkValInInterval equals binomial probability
    have hrhs : walkValInInterval k j a b dx = (Nat.choose k j : ℝ) / 2 ^ k := by
      unfold walkValInInterval binomialWalkProb
      rw [if_pos hcond, if_pos hjk]
    rw [hrhs]
    -- Now: ↑(k.choose j) * 2^(N-k) / 2^N = ↑(k.choose j) / 2^k
    have h2N : (2 : ℝ) ^ N = 2 ^ k * 2 ^ (N - k) := by
      rw [← pow_add]; congr 1; omega
    rw [h2N]; field_simp
  · rw [if_neg hcond]
    have hrhs : walkValInInterval k j a b dx = 0 := by
      unfold walkValInInterval; rw [if_neg hcond]
    rw [hrhs]; simp

/-! ## Ratio Convergence

The key analytical step: each binomial probability is close to
the Gaussian density × mesh width.

C(k, j) / 2^k ≈ gaussianDensitySigma(√t, (2j-k)/√N) × (2/√N)
-/

-- Helper lemmas for the final combining step in binomProb_ratio_near_one.
-- Extracted to keep nlinarith context small.
private lemma ratio_lower_bound {θ P Q ε δ : ℝ}
    (hθ_lower : 1 - ε ≤ θ) (hθ_pos : 0 < θ)
    (hP_ge : 1 ≤ P) (hP_pos : 0 < P)
    (hQ_ge : 1 - 2 * ε ≤ Q) (hQ_pos : 0 < Q)
    (hε_pos : 0 < ε) (hε_def : ε = δ / 30) :
    -δ < θ * P * Q - 1 := by
  have hθPQ_pos : 0 < θ * P * Q := mul_pos (mul_pos hθ_pos hP_pos) hQ_pos
  by_cases hδ : δ ≤ 1
  · -- δ ≤ 1: ε ≤ 1/30, product bounds work
    have hε_small : ε ≤ 1 / 30 := by linarith
    have hPQ : 1 - 2 * ε ≤ P * Q := by
      nlinarith [mul_le_mul hP_ge hQ_ge (by linarith) (le_of_lt hP_pos)]
    have hPQ_nn : 0 ≤ P * Q := le_of_lt (mul_pos hP_pos hQ_pos)
    have h : (1 - ε) * (1 - 2 * ε) ≤ θ * (P * Q) :=
      le_trans (mul_le_mul_of_nonneg_left hPQ (by linarith))
        (mul_le_mul_of_nonneg_right hθ_lower hPQ_nn)
    nlinarith [sq_nonneg ε, mul_assoc θ P Q]
  · -- δ > 1: 1 - δ < 0 < θPQ
    push_neg at hδ; linarith

private lemma ratio_upper_bound {θ P Q ε δ : ℝ}
    (hθ_upper : θ ≤ 1 + ε) (hθ_pos : 0 < θ)
    (hP_le : P ≤ 1 + 2 * ε) (hP_pos : 0 < P)
    (hQ_le : Q ≤ 1) (_hQ_pos : 0 < Q)
    (hε_pos : 0 < ε) (hε_def : ε = δ / 30) (hδ_le : δ ≤ 1) :
    θ * P * Q - 1 < δ := by
  have hθP_pos : 0 < θ * P := mul_pos hθ_pos hP_pos
  have h1 : θ * P * Q ≤ θ * P := by
    nlinarith [mul_le_mul_of_nonneg_left hQ_le (le_of_lt hθP_pos)]
  have h2 : θ * P ≤ (1 + ε) * (1 + 2 * ε) :=
    le_trans (mul_le_mul_of_nonneg_right hθ_upper (le_of_lt hP_pos))
      (mul_le_mul_of_nonneg_left hP_le (by linarith))
  have h3 : (1 + ε) * (1 + 2 * ε) = 1 + 3 * ε + 2 * ε ^ 2 := by ring
  -- With δ ≤ 1: ε = δ/30 ≤ 1/30, so ε² ≤ ε/30
  have hε_small : ε ≤ 1 / 30 := by linarith
  have h_eps_sq : ε ^ 2 ≤ ε / 30 := by
    rw [sq]
    have : ε * ε ≤ ε * (1 / 30) :=
      mul_le_mul_of_nonneg_left hε_small (le_of_lt hε_pos)
    linarith
  -- θPQ - 1 ≤ 3ε + 2ε² ≤ 3ε + 2ε/30 = 3ε + ε/15 = 46ε/15
  -- δ = 30ε, and 46ε/15 < 30ε since 46/15 < 30
  linarith

set_option maxHeartbeats 3200000 in
private theorem binomProb_ratio_near_one_small (a b : ℝ) (t : ℝ) (_ha : a < b) (ht : 0 < t)
    (δ : ℝ) (hδ : 0 < δ) (hδ_le : δ ≤ 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let k := Nat.floor (t * N)
      ∀ j : ℕ, j ≤ k →
        let x := (2 * (j : ℝ) - k) / Real.sqrt N
        a ≤ x → x ≤ b →
        let binomP := (Nat.choose k j : ℝ) / 2^k
        let gaussP := gaussianDensitySigma (Real.sqrt t) x * (2 / Real.sqrt N)
        0 < gaussP → |binomP / gaussP - 1| < δ := by
  /-
  Proof sketch:
  The ratio binomP/gaussP decomposes as θ × A × B where:
  - θ = stirlingSeq(k)√π/(stirlingSeq(j)×stirlingSeq(k-j)) → 1 (Stirling)
  - A = √(tN/(k(1-v²))) → 1 (since k ≈ tN and v → 0)
  - B = exp(-(k/2)h(v) + k²v²/(2tN)) → 1 (exponent → 0)
  where v = (2j-k)/k. Each factor converges uniformly for x ∈ [a,b].

  Quantitative bounds (for N large, x ∈ [a,b]):
  - v² ≤ B²/(t²N) where B = max(|a|,|b|)+1, so v → 0
  - |θ-1| < ε by stirlingSeq_triple_ratio_near_one
  - |A-1| ≤ C/N for some constant C
  - |B-1| ≤ C'/N for some constant C'
  Then |θ×A×B - 1| < 10ε < δ by mul_three_near_one.
  -/
  -- Set error tolerance: ε = δ/30
  set ε := δ / 30 with hε_def
  have hε_pos : 0 < ε := by positivity
  -- Bound on |x|
  set Bnd := max (|a|) (|b|) + 1 with hBnd_def
  have hBnd_pos : 0 < Bnd := by positivity
  -- Step 1: Get stirling triple ratio → 1
  obtain ⟨M_stir, hM_stir⟩ := Arithmetic.stirlingSeq_triple_ratio_near_one ε hε_pos
  -- Step 2: Choose N₀ large enough for all bounds
  -- Key requirements on N:
  --   (a) t*N ≥ 2*M_stir + 4  (so k ≥ M_stir+2, hence j ≥ M_stir and k-j ≥ M_stir)
  --   (b) t*N ≥ 16*Bnd²/t     (so v² ≤ 1/4 for x ∈ [-Bnd,Bnd])
  --   (c) N ≥ C/ε             (so analytical error terms < ε)
  -- We combine into a single N₀.
  -- Compute the required threshold
  -- Key requirements:
  -- (a) tN ≥ 4M_stir + 4  (so j, k-j ≥ M_stir for central x)
  -- (b) N ≥ 16Bnd²/t²    (so Bnd√N ≤ tN/4, hence v² ≤ 1/4)
  -- (c) N ≥ some_C/ε     (so analytical error terms < ε)
  set C_thresh := max ((4 * ↑M_stir + 4) / t)
    (max (16 * Bnd ^ 2 / t ^ 2)
         (max (4 * Bnd ^ 2 / (t ^ 2 * ε))
              (max (8 / (t * ε))
                   (max (Bnd ^ 4 / (t ^ 3 * ε)) (2 / t))))) with hC_def
  refine ⟨Nat.ceil C_thresh + 1, ?_⟩
  intro N hN k j hj_le x hax hxb binomP gaussP hgaussP_pos
  -- Extract the threshold consequences
  have hN_ge : C_thresh < N := by
    have h1 : Nat.ceil C_thresh + 1 ≤ N := hN
    have h2 : C_thresh ≤ Nat.ceil C_thresh := Nat.le_ceil C_thresh
    exact lt_of_le_of_lt h2 (by exact_mod_cast (by omega : Nat.ceil C_thresh < N))
  -- Derive threshold consequences
  have hC_le : C_thresh ≤ (N : ℝ) := le_of_lt hN_ge
  have htN_ge_a : (4 : ℝ) * ↑M_stir + 4 ≤ t * ↑N := by
    have h1 : (4 * ↑M_stir + 4) / t ≤ C_thresh := le_max_left _ _
    have h2 : (4 * ↑M_stir + 4) / t ≤ (N : ℝ) := le_trans h1 hC_le
    rw [div_le_iff₀ ht] at h2; linarith
  have htN_ge_b : 16 * Bnd ^ 2 / t ^ 2 ≤ (N : ℝ) := by
    exact le_trans ((le_max_left _ _).trans (le_max_right _ _)) hC_le
  have htN_ge_2 : 2 ≤ t * ↑N := by
    have h1 : 2 / t ≤ C_thresh :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
        ((le_max_right _ _).trans (le_max_right _ _))))
    have h2 : 2 / t ≤ (N : ℝ) := le_trans h1 hC_le
    rw [div_le_iff₀ ht] at h2; linarith
  -- New threshold consequences for P and Q bounds
  have hN_ge_teps : 8 / (t * ε) ≤ (N : ℝ) := by
    exact le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))) hC_le
  have hN_ge_bnd4 : Bnd ^ 4 / (t ^ 3 * ε) ≤ (N : ℝ) := by
    exact le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))) hC_le
    -- path: Bnd⁴/(t³ε) ≤ max(Bnd⁴/(t³ε), 2/t) ≤ max(8/(tε), ...) ≤ ... ≤ C_thresh
  -- N > 0 and √N > 0
  have hN_pos : (0 : ℝ) < N := by nlinarith
  have hN_pos' : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
  have hN_ne : Real.sqrt N ≠ 0 := ne_of_gt hN_pos'
  -- Basic k properties
  have hk_pos : 0 < k := Nat.floor_pos.mpr (by linarith : 1 ≤ t * ↑N)
  have hk_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk_pos
  have hk_le : (↑k : ℝ) ≤ t * ↑N := Nat.floor_le (by linarith)
  have hk_gt : t * ↑N - 1 < ↑k := by
    have := Nat.lt_floor_add_one (t * ↑N); push_cast at this; linarith
  -- x = (2j-k)/√N bounds
  have hx_bound : |x| < Bnd := by
    rw [abs_lt]; constructor
    · calc -(Bnd) < -(|a|) := by linarith [le_max_left (|a|) (|b|)]
        _ ≤ a := neg_abs_le a
        _ ≤ x := hax
    · calc x ≤ b := hxb
        _ ≤ |b| := le_abs_self b
        _ < Bnd := by linarith [le_max_right (|a|) (|b|)]
  -- Key bound: |2j - k| < Bnd × √N
  have h2jk : (2 * (j : ℝ) - ↑k) = x * Real.sqrt N := by
    show (2 * (j : ℝ) - ↑k) = (2 * ↑j - ↑k) / Real.sqrt ↑N * Real.sqrt ↑N
    rw [div_mul_cancel₀ _ hN_ne]
  have h2jk_bound : |2 * (j : ℝ) - ↑k| < Bnd * Real.sqrt N := by
    rw [h2jk, abs_mul, abs_of_pos hN_pos']
    exact mul_lt_mul_of_pos_right hx_bound hN_pos'
  -- Bound: Bnd × √N ≤ tN/4 (from N ≥ 16Bnd²/t²)
  -- √N ≥ 4Bnd/t follows from N ≥ 16Bnd²/t²
  have hBnd_sqrtN : Bnd * Real.sqrt N ≤ t * ↑N / 4 := by
    have hN_sq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (le_of_lt hN_pos)
    -- From htN_ge_b: 16Bnd²/t² ≤ N, so 16Bnd² ≤ t²N
    have h16 : 16 * Bnd ^ 2 ≤ t ^ 2 * (N : ℝ) := by
      have := htN_ge_b; rw [div_le_iff₀ (by positivity : (0:ℝ) < t ^ 2)] at this; linarith
    -- (4Bnd)² ≤ (t√N)²
    have h_sq : (4 * Bnd) ^ 2 ≤ (t * Real.sqrt N) ^ 2 := by
      have : (t * Real.sqrt N) ^ 2 = t ^ 2 * N := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hN_pos)]
      linarith
    -- 4Bnd ≤ t√N (both nonneg)
    have h_tsqrtN : 4 * Bnd ≤ t * Real.sqrt N := by
      have h1 : 0 ≤ 4 * Bnd := by positivity
      have h2 : 0 ≤ t * Real.sqrt N := by positivity
      nlinarith [sq_nonneg (t * Real.sqrt N - 4 * Bnd)]
    -- Bnd × √N ≤ (t√N/4) × √N = tN/4
    calc Bnd * Real.sqrt N ≤ (t * Real.sqrt N / 4) * Real.sqrt N := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            linarith
      _ = t * (Real.sqrt N * Real.sqrt N) / 4 := by ring
      _ = t * ↑N / 4 := by rw [hN_sq]
  -- j bounds: j ≥ (k - Bnd√N)/2 and k-j ≥ (k - Bnd√N)/2
  -- Key chain: k - Bnd√N ≥ 3tN/4 - 1 ≥ 3(4M+4)/4 - 1 = 3M + 2
  -- So (k - Bnd√N)/2 ≥ (3M + 2)/2 ≥ max(M, 1) for M ≥ 0
  have hk_bnd_lower : 3 * ↑M_stir + 2 ≤ ↑k - Bnd * Real.sqrt N := by
    have h1 : 3 * (t * ↑N) / 4 - 1 ≤ ↑k - Bnd * Real.sqrt N := by linarith
    have h2 : 3 * (4 * (↑M_stir : ℝ) + 4) / 4 - 1 ≤ 3 * (t * ↑N) / 4 - 1 := by linarith
    have h3 : 3 * (4 * (↑M_stir : ℝ) + 4) / 4 - 1 = 3 * ↑M_stir + 2 := by ring
    linarith
  have hj_lower : (↑k - Bnd * Real.sqrt N) / 2 ≤ (j : ℝ) := by
    have h1 : ↑k - Bnd * Real.sqrt N < 2 * (j : ℝ) := by
      linarith [(abs_lt.mp h2jk_bound).1]
    linarith
  have hkj_lower : (↑k - Bnd * Real.sqrt N) / 2 ≤ (↑k - (j : ℝ)) := by
    have h1 : 2 * (j : ℝ) - ↑k < Bnd * Real.sqrt N := by
      linarith [(abs_lt.mp h2jk_bound).2]
    linarith
  have hj_pos : 1 ≤ j := by
    have : (1 : ℝ) ≤ j := by linarith
    exact_mod_cast this
  have hkj_pos : 1 ≤ k - j := by
    have h1 : (1 : ℝ) ≤ ↑k - (j : ℝ) := by linarith
    have h2 : (1 : ℝ) ≤ ↑(k - j) := by rw [Nat.cast_sub hj_le]; exact h1
    exact_mod_cast h2
  have hj_lt_k : j < k := by omega
  -- Stirling triple ratio bounds
  have hj_ge_M : M_stir ≤ j := by
    have : (M_stir : ℝ) ≤ j := by linarith
    exact_mod_cast this
  have hkj_ge_M : M_stir ≤ k - j := by
    have h1 : (M_stir : ℝ) ≤ ↑k - (j : ℝ) := by linarith
    have h2 : (M_stir : ℝ) ≤ ↑(k - j) := by rw [Nat.cast_sub hj_le]; exact h1
    exact_mod_cast h2
  -- |θ - 1| < ε
  have hθ_bound : |Stirling.stirlingSeq k * Real.sqrt Real.pi /
      (Stirling.stirlingSeq j * Stirling.stirlingSeq (k - j)) - 1| < ε :=
    hM_stir k j (by omega : M_stir ≤ k) hj_ge_M hkj_ge_M
  -- === Main proof: show |binomP / gaussP - 1| < δ ===
  -- Strategy: binomP/gaussP = θ × P × Q where θ is Stirling ratio,
  -- P = √(tN/(k(1-v²))), Q = pp * exp(x²/(2t)). Each factor ≈ 1.
  set kj := k - j
  -- Positivity setup
  have hst_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hj_r' : (0 : ℝ) < ↑j := Nat.cast_pos.mpr (by omega)
  have hkj_r : (0 : ℝ) < ↑kj := Nat.cast_pos.mpr (show 0 < k - j by omega)
  have h2j_pos : (0 : ℝ) < 2 * ↑j := by linarith
  have h2kj_pos : (0 : ℝ) < 2 * ↑kj := by linarith
  -- Stirling decomposition: binomP = θ * (sqrtPart * pp)
  set θ := Stirling.stirlingSeq k * Real.sqrt Real.pi /
      (Stirling.stirlingSeq j * Stirling.stirlingSeq kj)
  -- Force ℝ interpretation for pp using explicit cast
  set pp := ((↑k : ℝ) / (2 * ↑j)) ^ j * ((↑k : ℝ) / (2 * ↑kj)) ^ kj with hpp_def
  set sqrtPart := Real.sqrt ((↑k : ℝ) / (2 * Real.pi * ↑j * ↑kj)) with hsqrt_def
  have h_stirling := BinomGaussRatioHelpers.binomProb_stirling_decomp k j hj_pos hj_lt_k
  have hpp_pos : 0 < pp :=
    mul_pos (pow_pos (div_pos hk_r h2j_pos) j) (pow_pos (div_pos hk_r h2kj_pos) kj)
  -- Unfold gaussP
  have hgauss_val : gaussianDensitySigma (Real.sqrt t) x =
      (1 / (Real.sqrt t * Real.sqrt (2 * Real.pi))) *
      Real.exp (-(x ^ 2) / (2 * t)) := by
    unfold gaussianDensitySigma; rw [if_pos hst_pos, Real.sq_sqrt (le_of_lt ht)]
  -- v bounds: |v| ≤ 1/2 where v = (2j-k)/k
  set v := (2 * (j : ℝ) - ↑k) / ↑k with hv_def
  have hv_abs : |v| ≤ 1 / 2 := by
    rw [abs_le]; constructor
    · -- -(1/2) ≤ v
      show -(1 / 2) ≤ (2 * (j : ℝ) - ↑k) / ↑k
      rw [le_div_iff₀ hk_r]
      have h_lower : -(t * ↑N / 4) < 2 * (↑j : ℝ) - ↑k := by
        linarith [(abs_lt.mp h2jk_bound).1, hBnd_sqrtN]
      linarith [htN_ge_2, hk_gt]
    · -- v ≤ 1/2
      show (2 * (j : ℝ) - ↑k) / ↑k ≤ 1 / 2
      rw [div_le_iff₀ hk_r]
      have h_upper : 2 * (↑j : ℝ) - ↑k < t * ↑N / 4 := by
        linarith [(abs_lt.mp h2jk_bound).2, hBnd_sqrtN]
      have h1k : (1:ℝ) ≤ ↑k := by exact_mod_cast hk_pos
      linarith [hk_gt]
  have hv_sq_bound : v ^ 2 ≤ 1 / 4 := by
    calc v ^ 2 = |v| ^ 2 := (sq_abs v).symm
      _ ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg v) hv_abs 2
      _ = 1 / 4 := by norm_num
  have h1mv2_pos : 0 < 1 - v ^ 2 := by linarith [hv_sq_bound]
  have hv_abs_lt1 : |v| < 1 := by linarith [hv_abs]
  -- Q ≤ 1 where Q = pp * exp(x²/(2t))
  have hx2_le_s2 : x ^ 2 / (2 * t) ≤ (2 * (j : ℝ) - ↑k) ^ 2 / (2 * ↑k) := by
    have hx_eq' : x = (2 * ↑j - ↑k) / Real.sqrt ↑N := rfl
    rw [hx_eq', div_pow, Real.sq_sqrt (show 0 ≤ (↑N : ℝ) from by positivity)]
    rw [div_div]
    -- Goal: (2j-k)² / (↑N * (2*t)) ≤ (2j-k)² / (2*↑k)
    -- Since 2k ≤ N*(2t) = 2tN (from k ≤ tN), larger denom → smaller fraction
    have h2k_le : 2 * ↑k ≤ ↑N * (2 * t) := by nlinarith [hk_le]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (show (0:ℝ) < 2 * ↑k by positivity) h2k_le
  have hQ_le_one : pp * Real.exp (x ^ 2 / (2 * t)) ≤ 1 := by
    calc pp * Real.exp (x ^ 2 / (2 * t))
        ≤ pp * Real.exp ((2 * (j : ℝ) - ↑k) ^ 2 / (2 * ↑k)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le hx2_le_s2) (le_of_lt hpp_pos)
      _ ≤ 1 := LocalCLTHelpers.exp_factor_le_one k j hj_pos hj_lt_k
  -- P bounds where P² = tN/(k(1-v²))
  set P_sq := t * ↑N / (↑k * (1 - v ^ 2)) with hP_sq_def
  have hk1v2_pos : (0 : ℝ) < ↑k * (1 - v ^ 2) := by positivity
  have hP_sq_ge_one : 1 ≤ P_sq := by
    rw [le_div_iff₀ hk1v2_pos]
    nlinarith [hk_le, hv_sq_bound]
  have hP_bound : P_sq - 1 < 2 * ε := by
    rw [hP_sq_def, div_sub_one (ne_of_gt hk1v2_pos)]
    rw [div_lt_iff₀ hk1v2_pos]
    -- Numerator: tN - k(1-v²) = tN - k + kv²
    -- kv² = (2j-k)²/k < Bnd²N/k ≤ 2Bnd²/t
    have hkv2 : ↑k * v ^ 2 = (2 * ↑j - ↑k) ^ 2 / ↑k := by
      rw [hv_def, div_pow, mul_div_assoc']; field_simp
    have h2jk_sq_bound : (2 * (j : ℝ) - ↑k) ^ 2 < Bnd ^ 2 * ↑N := by
      calc (2 * (j : ℝ) - ↑k) ^ 2
          < (Bnd * Real.sqrt ↑N) ^ 2 :=
            sq_lt_sq' ((abs_lt.mp h2jk_bound).1) ((abs_lt.mp h2jk_bound).2)
        _ = Bnd ^ 2 * ↑N := by
            rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (↑N : ℝ))]
    have hkv2_bound : ↑k * v ^ 2 < Bnd ^ 2 * ↑N / ↑k := by
      rw [hkv2]; exact div_lt_div_of_pos_right h2jk_sq_bound hk_r
    have h_tN_le_2k : t * ↑N ≤ 2 * ↑k := by linarith [hk_gt, htN_ge_2]
    have h_bnd2 : Bnd ^ 2 * ↑N / ↑k ≤ 2 * Bnd ^ 2 / t := by
      rw [div_le_div_iff₀ hk_r (by positivity : (0:ℝ) < t)]
      -- Goal: Bnd^2 * N * t ≤ 2 * Bnd^2 * k
      calc Bnd ^ 2 * ↑N * t
          = Bnd ^ 2 * (↑N * t) := by ring
        _ ≤ Bnd ^ 2 * (2 * ↑k) :=
            mul_le_mul_of_nonneg_left (by linarith [h_tN_le_2k]) (sq_nonneg Bnd)
        _ = 2 * Bnd ^ 2 * ↑k := by ring
    have hkv2_upper : ↑k * v ^ 2 < 2 * Bnd ^ 2 / t := lt_of_lt_of_le hkv2_bound h_bnd2
    -- From thresholds
    have htN_val : 8 ≤ ε * (t * ↑N) := by
      have h := hN_ge_teps  -- 8 / (t * ε) ≤ N
      rw [div_le_iff₀ (by positivity : 0 < t * ε)] at h
      linarith
    have h_from_c : 4 * Bnd ^ 2 ≤ t ^ 2 * ε * ↑N := by
      have : 4 * Bnd ^ 2 / (t ^ 2 * ε) ≤ ↑N :=
        le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans
          (le_max_right _ _))) hC_le
      rw [div_le_iff₀ (by positivity : 0 < t ^ 2 * ε)] at this
      linarith
    -- LHS: tN - k(1-v²) = (tN - k) + kv² < 1 + 2Bnd²/t
    have h_lhs : t * ↑N - ↑k * (1 - v ^ 2) < 1 + 2 * Bnd ^ 2 / t := by
      have : t * ↑N - ↑k * (1 - v ^ 2) = (t * ↑N - ↑k) + ↑k * v ^ 2 := by ring
      linarith [hk_gt, hkv2_upper]
    -- RHS: 2ε × k(1-v²) ≥ 2ε × (tN-1) × (3/4) = (3/2)ε(tN-1)
    have h_rhs : 3 / 2 * ε * (t * ↑N - 1) ≤ 2 * ε * (↑k * (1 - v ^ 2)) := by
      have hk_ge : t * ↑N - 1 ≤ ↑k := by linarith [hk_gt]
      have h1mv2_ge : (3:ℝ) / 4 ≤ 1 - v ^ 2 := by linarith [hv_sq_bound]
      have htN1_nn : (0:ℝ) ≤ t * ↑N - 1 := by linarith [htN_ge_2]
      calc 3 / 2 * ε * (t * ↑N - 1)
          = 2 * ε * (3 / 4 * (t * ↑N - 1)) := by ring
        _ ≤ 2 * ε * ((1 - v ^ 2) * ↑k) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul h1mv2_ge hk_ge htN1_nn (by linarith)
        _ = 2 * ε * (↑k * (1 - v ^ 2)) := by ring
    have h_one_bound : 1 ≤ ε * (t * ↑N) / 8 := by linarith [htN_val]
    have h_bnd_bound : 2 * Bnd ^ 2 / t ≤ ε * (t * ↑N) / 2 := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < t) (by positivity : (0:ℝ) < 2)]
      calc 2 * Bnd ^ 2 * 2 = 4 * Bnd ^ 2 := by ring
        _ ≤ t ^ 2 * ε * ↑N := h_from_c
        _ = ε * (t * ↑N) * t := by ring
    -- 1 + 2Bnd²/t ≤ εtN/8 + εtN/2 = 5εtN/8
    -- 5εtN/8 ≤ 3εtN/2 - 3ε/2 = 3/2*ε*(tN-1) since tN ≥ 2 > 12/7
    have h_etN_bound : ε * 2 ≤ ε * (t * ↑N) :=
      mul_le_mul_of_nonneg_left htN_ge_2 (le_of_lt hε_pos)
    linarith
  -- Q lower bound: 1 - Q < 2ε
  have hQ_lower : 1 - pp * Real.exp (x ^ 2 / (2 * t)) < 2 * ε := by
    -- pp = exp(-(k/2)hv) via power_product_eq_exp
    -- Q = exp(E) where E = -(k/2)hv + x²/(2t) ≤ 0
    -- 1-Q ≤ -E = (k/2)(hv-v²) + (kv²/2)(1-k/(tN))
    -- ≤ kv⁴/(12(1-v²)) + kv²/(2tN) < ε + ε = 2ε
    have h_pp_eq := BinomGaussRatioHelpers.power_product_eq_exp k j hj_pos hj_lt_k
    have hx2_eq : x ^ 2 = ↑k ^ 2 * v ^ 2 / ↑N := by
      have : x = (2 * ↑j - ↑k) / Real.sqrt ↑N := rfl
      rw [this, div_pow, Real.sq_sqrt (by positivity : 0 ≤ (↑N : ℝ))]
      rw [hv_def, div_pow]; field_simp
    set hv := (1 + v) * Real.log (1 + v) + (1 - v) * Real.log (1 - v) with hv_hv
    -- Unfold pp to expose k-j (h_pp_eq uses k-j, not kj)
    have hpp_unfold : pp = ((↑k : ℝ) / (2 * ↑j)) ^ j *
        ((↑k : ℝ) / (2 * ↑(k - j))) ^ (k - j) := by
      simp only [hpp_def, show kj = k - j from rfl]
    rw [hpp_unfold, h_pp_eq, ← Real.exp_add]
    set E := -(↑k / 2) * hv + x ^ 2 / (2 * t) with hE_def
    -- E ≤ 0
    have hE_le : E ≤ 0 := by
      have : Real.exp E ≤ 1 := by
        rw [hE_def, Real.exp_add, ← h_pp_eq, ← hpp_unfold]; exact hQ_le_one
      linarith [Real.exp_pos E, Real.add_one_le_exp E]
    -- 1 - exp(E) ≤ -E
    have h_1mexpE : 1 - Real.exp E ≤ -E := by linarith [Real.add_one_le_exp E]
    -- Bound -E
    have hE_neg : -E = ↑k / 2 * (hv - v ^ 2) + ↑k * v ^ 2 / 2 -
        ↑k ^ 2 * v ^ 2 / (2 * (t * ↑N)) := by
      rw [hE_def, hx2_eq]; ring
    -- -E = (k/2)(hv-v²) + (kv²/2)(1-k/(tN))
    have h_rearrange : -E = ↑k / 2 * (hv - v ^ 2) +
        ↑k * v ^ 2 * (t * ↑N - ↑k) / (2 * (t * ↑N)) := by
      rw [hE_neg]; field_simp; ring
    -- Term 1: (k/2)(hv-v²) ≤ kv⁴/(12(1-v²)) < ε
    have h_excess := LocalCLTHelpers.pinsker_excess_crude_abs hv_abs_lt1
    have h_term1 : ↑k / 2 * (hv - v ^ 2) ≤ ↑k * v ^ 4 / (12 * (1 - v ^ 2)) := by
      have h_eq : ↑k / 2 * (v ^ 4 / (6 * (1 - v ^ 2))) =
          ↑k * v ^ 4 / (12 * (1 - v ^ 2)) := by field_simp; ring
      linarith [mul_le_mul_of_nonneg_left h_excess (show (0:ℝ) ≤ ↑k / 2 by positivity)]
    -- kv⁴ ≤ 8Bnd⁴/(t³N)
    have hkv2' : ↑k * v ^ 2 = (2 * ↑j - ↑k) ^ 2 / ↑k := by
      rw [hv_def, div_pow, mul_div_assoc']; field_simp
    have h2jk_sq' : (2 * (j : ℝ) - ↑k) ^ 2 < Bnd ^ 2 * ↑N := by
      calc (2 * (j : ℝ) - ↑k) ^ 2
          < (Bnd * Real.sqrt ↑N) ^ 2 :=
            sq_lt_sq' ((abs_lt.mp h2jk_bound).1) ((abs_lt.mp h2jk_bound).2)
        _ = Bnd ^ 2 * ↑N := by
            rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (↑N : ℝ))]
    have h_tN_le_2k' : t * ↑N ≤ 2 * ↑k := by linarith [hk_gt, htN_ge_2]
    have hkv2_bound' : ↑k * v ^ 2 ≤ 2 * Bnd ^ 2 / t := by
      have hkv2_lt : ↑k * v ^ 2 < Bnd ^ 2 * ↑N / ↑k := by
        rw [hkv2']; exact div_lt_div_of_pos_right h2jk_sq' hk_r
      have : Bnd ^ 2 * ↑N / ↑k ≤ 2 * Bnd ^ 2 / t := by
        rw [div_le_div_iff₀ hk_r (by positivity : (0:ℝ) < t)]
        calc Bnd ^ 2 * ↑N * t
            = Bnd ^ 2 * (↑N * t) := by ring
          _ = Bnd ^ 2 * (t * ↑N) := by ring
          _ ≤ Bnd ^ 2 * (2 * ↑k) :=
              mul_le_mul_of_nonneg_left h_tN_le_2k' (sq_nonneg Bnd)
          _ = 2 * Bnd ^ 2 * ↑k := by ring
      linarith
    have hv2_upper : v ^ 2 ≤ 4 * Bnd ^ 2 / (t ^ 2 * ↑N) := by
      have : v ^ 2 = (↑k * v ^ 2) / ↑k := by field_simp
      rw [this, div_le_div_iff₀ hk_r (by positivity : 0 < t ^ 2 * ↑N)]
      -- Goal: kv² × t²N ≤ 4Bnd² × k
      calc ↑k * v ^ 2 * (t ^ 2 * ↑N)
          ≤ (2 * Bnd ^ 2 / t) * (t ^ 2 * ↑N) :=
            mul_le_mul_of_nonneg_right hkv2_bound' (by positivity)
        _ = 2 * Bnd ^ 2 * (t * ↑N) := by field_simp
        _ ≤ 2 * Bnd ^ 2 * (2 * ↑k) :=
            mul_le_mul_of_nonneg_left h_tN_le_2k' (by positivity)
        _ = 4 * Bnd ^ 2 * ↑k := by ring
    have hkv4_bound : ↑k * v ^ 4 ≤ 8 * Bnd ^ 4 / (t ^ 3 * ↑N) :=
      calc ↑k * v ^ 4 = (↑k * v ^ 2) * v ^ 2 := by ring
        _ ≤ (2 * Bnd ^ 2 / t) * (4 * Bnd ^ 2 / (t ^ 2 * ↑N)) :=
            mul_le_mul hkv2_bound' hv2_upper (sq_nonneg _) (by positivity)
        _ = 8 * Bnd ^ 4 / (t ^ 3 * ↑N) := by ring
    have h_from_bnd4 : Bnd ^ 4 ≤ t ^ 3 * ε * ↑N := by
      rw [div_le_iff₀ (by positivity : 0 < t ^ 3 * ε)] at hN_ge_bnd4
      linarith [mul_comm (↑N : ℝ) (t ^ 3 * ε)]
    have h_t1 : ↑k * v ^ 4 / (12 * (1 - v ^ 2)) < ε := by
      rw [div_lt_iff₀ (by positivity : 0 < 12 * (1 - v ^ 2))]
      -- Goal: kv⁴ < ε × 12(1-v²)
      have h_bnd4_eps : 8 * Bnd ^ 4 / (t ^ 3 * ↑N) ≤ 8 * ε := by
        rw [div_le_iff₀ (by positivity : 0 < t ^ 3 * ↑N)]
        linarith [h_from_bnd4]
      have h_rhs_ge : 9 * ε ≤ ε * (12 * (1 - v ^ 2)) := by
        have h9 : 9 ≤ 12 * (1 - v ^ 2) := by linarith [hv_sq_bound]
        have := mul_le_mul_of_nonneg_left h9 (le_of_lt hε_pos)
        linarith
      linarith [hkv4_bound]
    -- Term 2: (kv²/2)(1-k/(tN)) ≤ kv²/(2tN) < ε
    have h_from_c : 4 * Bnd ^ 2 ≤ t ^ 2 * ε * ↑N := by
      have : 4 * Bnd ^ 2 / (t ^ 2 * ε) ≤ ↑N :=
        le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans
          (le_max_right _ _))) hC_le
      rw [div_le_iff₀ (by positivity : 0 < t ^ 2 * ε)] at this
      linarith [mul_comm (↑N : ℝ) (t ^ 2 * ε)]
    have h_t2 : ↑k * v ^ 2 / (2 * (t * ↑N)) < ε := by
      rw [div_lt_iff₀ (by positivity : 0 < 2 * (t * ↑N))]
      -- Goal: kv² < ε × 2tN
      have h_bnd2_eps : 2 * Bnd ^ 2 / t ≤ t * ε * ↑N / 2 := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < t) (by positivity : (0:ℝ) < 2)]
        calc 2 * Bnd ^ 2 * 2 = 4 * Bnd ^ 2 := by ring
          _ ≤ t ^ 2 * ε * ↑N := h_from_c
          _ = t * ε * ↑N * t := by ring
      have h_eq : ε * (2 * (t * ↑N)) = 4 * (t * ε * ↑N / 2) := by ring
      rw [h_eq]
      have : 0 < t * ε * ↑N / 2 := by positivity
      linarith [hkv2_bound']
    -- Combine: 1-exp(E) ≤ -E = term1 + term2 < ε + ε = 2ε
    have h_t2_ineq : ↑k * v ^ 2 * (t * ↑N - ↑k) / (2 * (t * ↑N)) ≤
        ↑k * v ^ 2 / (2 * (t * ↑N)) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt (show 0 < 2 * (t * ↑N) from by positivity))
      have h_tNk_le_1 : t * ↑N - ↑k ≤ 1 := by linarith [hk_gt]
      have h_kv2_nn : 0 ≤ ↑k * v ^ 2 := by positivity
      calc ↑k * v ^ 2 * (t * ↑N - ↑k) ≤ ↑k * v ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left h_tNk_le_1 h_kv2_nn
        _ = ↑k * v ^ 2 := by ring
    -- Chain: 1-exp(E) ≤ -E (h_1mexpE)
    --   -E = (k/2)(hv-v²) + kv²(tN-k)/(2tN) (h_rearrange)
    --   ≤ kv⁴/(12(1-v²)) + kv²/(2tN) (h_term1, h_t2_ineq)
    --   < ε + ε (h_t1, h_t2)
    linarith [h_1mexpE, h_rearrange, h_term1, h_t1, h_t2_ineq, h_t2]
  -- Combine: binomP/gaussP = θ × P × Q, show |ratio - 1| < δ
  set P_val := Real.sqrt (t * ↑N / (↑k * (1 - v ^ 2)))
  set Q_val := pp * Real.exp (x ^ 2 / (2 * t))
  have hP_val_pos : 0 < P_val := Real.sqrt_pos.mpr (by positivity : 0 < P_sq)
  have hP_val_ge_one : 1 ≤ P_val := by
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ P_val := Real.sqrt_le_sqrt hP_sq_ge_one
  have hP_val_le : P_val ≤ 1 + 2 * ε := by
    calc P_val = Real.sqrt (P_val ^ 2) := (Real.sqrt_sq (le_of_lt hP_val_pos)).symm
      _ = Real.sqrt P_sq := by rw [show P_val ^ 2 = P_sq from
          Real.sq_sqrt (le_of_lt (by positivity : 0 < P_sq))]
      _ ≤ Real.sqrt ((1 + 2 * ε) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [hP_bound, sq_nonneg ε])
      _ = 1 + 2 * ε := Real.sqrt_sq (by linarith)
  -- Key algebraic identity: decomp/gaussP = P_val * Q_val
  have hP := BinomGaussRatioHelpers.sqrt_prefactor_simplify k j N t hj_pos hj_lt_k ht
    (show 0 < N by exact_mod_cast (show 0 < ↑N from by linarith [hN_pos]))
  -- hP : sqrtPart * (√(2πt) * √N) / 2 = P_val
  have hdecomp_eq : (sqrtPart * pp) / gaussP = P_val * Q_val := by
    rw [show gaussP = gaussianDensitySigma (Real.sqrt t) x * (2 / Real.sqrt ↑N) from rfl]
    rw [hgauss_val]
    rw [show P_val * Q_val = (sqrtPart * (Real.sqrt (2 * Real.pi * t) *
        Real.sqrt ↑N) / 2) * (pp * Real.exp (x ^ 2 / (2 * t))) from by rw [hP]]
    have h_gaussP_ne : (1 / (Real.sqrt t * Real.sqrt (2 * Real.pi))) *
        Real.exp (-(x ^ 2) / (2 * t)) * (2 / Real.sqrt ↑N) ≠ 0 := by
      apply ne_of_gt
      exact mul_pos (mul_pos (div_pos one_pos (mul_pos hst_pos
        (Real.sqrt_pos.mpr (by linarith [Real.pi_pos])))) (Real.exp_pos _))
        (div_pos two_pos (Real.sqrt_pos.mpr (by linarith [hN_pos])))
    field_simp
    -- Cancel exp terms and simplify sqrt
    -- Cancel exp(-a)*exp(a) = 1 and simplify √(2πt) = √t * √(2π)
    have hexp_cancel : Real.exp (-(x ^ 2 / (2 * t))) * Real.exp (x ^ 2 / (2 * t)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hsqrt_eq : Real.sqrt (2 * Real.pi * t) = Real.sqrt t * Real.sqrt (2 * Real.pi) := by
      rw [show 2 * Real.pi * t = t * (2 * Real.pi) from by ring]
      exact Real.sqrt_mul (le_of_lt ht) _
    rw [hsqrt_eq]
    have hrearr : sqrtPart * Real.exp (-(x ^ 2 / (2 * t))) *
        (Real.sqrt t * Real.sqrt (2 * Real.pi)) * Real.exp (x ^ 2 / (2 * t)) =
        sqrtPart * Real.sqrt t * Real.sqrt (2 * Real.pi) *
        (Real.exp (-(x ^ 2 / (2 * t))) * Real.exp (x ^ 2 / (2 * t))) := by ring
    rw [hrearr, hexp_cancel, mul_one]
  -- binomP/gaussP = θ * P_val * Q_val
  have hratio : binomP / gaussP = θ * P_val * Q_val := by
    rw [show binomP = θ * (sqrtPart * pp) from h_stirling, mul_div_assoc,
        hdecomp_eq, mul_assoc]
  -- Final bounds
  have hθ_lower : 1 - ε ≤ θ := by linarith [(abs_le.mp (le_of_lt hθ_bound)).1]
  have hθ_upper : θ ≤ 1 + ε := by linarith [(abs_le.mp (le_of_lt hθ_bound)).2]
  have hε_small : ε ≤ 1 / 30 := by linarith [hε_def, hδ_le]
  have hθ_pos : 0 < θ := by linarith
  have h_1m2e_pos : (0 : ℝ) < 1 - 2 * ε := by linarith
  have hQ_ge : 1 - 2 * ε ≤ Q_val := by linarith [hQ_lower]
  have hQ_pos : 0 < Q_val := lt_of_lt_of_le h_1m2e_pos hQ_ge
  rw [hratio, abs_lt]; constructor
  · -- Lower: θPQ ≥ (1-ε)(1-2ε) = 1-3ε+2ε² > 1-δ
    have hPQ_ge : 1 - 2 * ε ≤ P_val * Q_val := by
      have := mul_le_mul hP_val_ge_one hQ_ge (le_of_lt h_1m2e_pos) (le_of_lt hP_val_pos)
      linarith
    have hPQ_nn : (0 : ℝ) ≤ P_val * Q_val := by linarith
    have hθPQ_ge : (1 - ε) * (1 - 2 * ε) ≤ θ * P_val * Q_val := by
      calc (1 - ε) * (1 - 2 * ε)
          ≤ θ * (1 - 2 * ε) := mul_le_mul_of_nonneg_right hθ_lower (le_of_lt h_1m2e_pos)
        _ ≤ θ * (P_val * Q_val) := mul_le_mul_of_nonneg_left hPQ_ge (le_of_lt hθ_pos)
        _ = θ * P_val * Q_val := (mul_assoc _ _ _).symm
    have h_expand : (1 - ε) * (1 - 2 * ε) = 1 - 3 * ε + 2 * ε ^ 2 := by ring
    -- -δ < θPQ - 1: since θPQ ≥ 1-3ε+2ε² and δ = 30ε,
    -- need 3ε-2ε² < 30ε, i.e., 0 < 27ε+2ε²
    nlinarith [sq_nonneg ε, hε_def, hε_pos]
  · -- Upper: θPQ ≤ (1+ε)(1+2ε) = 1+3ε+2ε² < 1+δ
    have hθP_pos : 0 < θ * P_val := mul_pos hθ_pos hP_val_pos
    have h1 : θ * P_val * Q_val ≤ θ * P_val := by
      have := mul_le_mul_of_nonneg_left hQ_le_one (le_of_lt hθP_pos)
      linarith [mul_one (θ * P_val)]
    have h2 : θ * P_val ≤ (1 + ε) * (1 + 2 * ε) :=
      le_trans (mul_le_mul_of_nonneg_right hθ_upper (le_of_lt hP_val_pos))
        (mul_le_mul_of_nonneg_left hP_val_le (by linarith))
    have h3 : (1 + ε) * (1 + 2 * ε) = 1 + 3 * ε + 2 * ε ^ 2 := by ring
    have h_eps_sq : ε ^ 2 ≤ ε / 30 := by
      rw [sq]
      have : ε * ε ≤ ε * (1 / 30) :=
        mul_le_mul_of_nonneg_left hε_small (le_of_lt hε_pos)
      linarith
    -- θPQ - 1 ≤ 3ε + 2ε² ≤ 3ε + 2ε/30 = 46ε/15 < 30ε = δ
    linarith [hε_def]

/-- For any δ > 0 and t > 0, for N large enough and k = ⌊tN⌋:
    The ratio C(k,j)/2^k / [gaussianDensitySigma(√t, x_j) × Δx] is in (1-δ, 1+δ)
    for all lattice points x_j = (2j-k)/√N in [a, b].

    This is the quantitative form of the local CLT ratio convergence. -/
theorem binomProb_ratio_near_one (a b : ℝ) (t : ℝ) (ha : a < b) (ht : 0 < t) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let k := Nat.floor (t * N)
      ∀ j : ℕ, j ≤ k →
        let x := (2 * (j : ℝ) - k) / Real.sqrt N
        a ≤ x → x ≤ b →
        let binomP := (Nat.choose k j : ℝ) / 2^k
        let gaussP := gaussianDensitySigma (Real.sqrt t) x * (2 / Real.sqrt N)
        0 < gaussP → |binomP / gaussP - 1| < δ := by
  by_cases hδ_le : δ ≤ 1
  · exact binomProb_ratio_near_one_small a b t ha ht δ hδ hδ_le
  · -- For δ > 1, use the δ₀ = 1 case: |ratio - 1| < 1 < δ
    push_neg at hδ_le
    obtain ⟨N₀, hN₀⟩ := binomProb_ratio_near_one_small a b t ha ht 1 one_pos le_rfl
    refine ⟨N₀, fun N hN => ?_⟩
    intro k j hj x hax hxb binomP gaussP hgP
    exact lt_trans (hN₀ N hN j hj hax hxb hgP) hδ_le

/-! ## Riemann Sum Convergence

The sum of Gaussian density values × mesh converges to the integral.
-/

/-- A Riemann sum with lattice spacing 2/√N over [a, b] converges to the integral.
    This uses the continuity of gaussianDensitySigma and standard Riemann sum theory. -/
theorem gaussDensity_Riemann_sum_converges (a b : ℝ) (t : ℝ) (ha : a ≤ b) (ht : 0 < t) :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let k := Nat.floor (t * N)
      |∑ j ∈ Finset.range (k + 1),
        (if a ≤ (2 * (j : ℝ) - k) / Real.sqrt N ∧ (2 * (j : ℝ) - k) / Real.sqrt N ≤ b
         then gaussianDensitySigma (Real.sqrt t) ((2 * (j : ℝ) - k) / Real.sqrt N) * (2 / Real.sqrt N)
         else 0) -
       ∫ x in Set.Icc a b, gaussianDensitySigma (Real.sqrt t) x| < δ := by
  -- The sum is a Riemann sum of a continuous function with mesh 2/√N → 0.
  -- By the standard Riemann sum convergence theorem, it converges to the integral.
  sorry

/-! ## Tail Bounds for Binomial Sums

The sum of binomial probabilities outside [-C√k, C√k] is small.

### Proof Strategy

We use the Chernoff method directly on the binomial sum:
1. Exponential Markov: Σ_{j : 2j-k > t} C(k,j)/2^k ≤ exp(-λt) × MGF(λ)
2. MGF computation: Σ C(k,j)/2^k × exp(λ(2j-k)) = cosh(λ)^k
3. Chernoff bound: cosh(λ) ≤ exp(λ²/2)
4. Optimize λ = C/√k with t = C√k → exp(-C²/2)
-/

/-- Exponential Markov inequality for non-negative weighted sums.
    For any λ > 0 and threshold t:
    Σ_{j : f(j) > t} w_j ≤ exp(-λt) × Σ_j w_j × exp(λ f(j)). -/
theorem weighted_exp_markov {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (l t : ℝ) (hl : 0 < l) :
    ∑ i ∈ s.filter (fun i => t < f i), w i ≤
    Real.exp (-l * t) * ∑ i ∈ s, w i * Real.exp (l * f i) := by
  calc ∑ i ∈ s.filter (fun i => t < f i), w i
      = ∑ i ∈ s.filter (fun i => t < f i), w i * 1 := by simp
    _ ≤ ∑ i ∈ s.filter (fun i => t < f i),
        w i * Real.exp (l * (f i - t)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hfi : t < f i := by
          simp only [Finset.mem_filter] at hi; exact hi.2
        apply mul_le_mul_of_nonneg_left _ (hw i (Finset.mem_of_mem_filter i hi))
        linarith [Real.add_one_le_exp (l * (f i - t)),
                  mul_nonneg (le_of_lt hl) (le_of_lt (sub_pos.mpr hfi))]
    _ = ∑ i ∈ s.filter (fun i => t < f i),
        w i * (Real.exp (-l * t) * Real.exp (l * f i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.exp_add]
        congr 1; ring_nf
    _ = ∑ i ∈ s.filter (fun i => t < f i),
        Real.exp (-l * t) * (w i * Real.exp (l * f i)) := by
        apply Finset.sum_congr rfl
        intro i _; ring
    _ = Real.exp (-l * t) * ∑ i ∈ s.filter (fun i => t < f i),
        w i * Real.exp (l * f i) := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (-l * t) * ∑ i ∈ s, w i * Real.exp (l * f i) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact mul_nonneg (hw i (by assumption)) (le_of_lt (Real.exp_pos _))

/-- The binomial MGF: Σ_{j=0}^k C(k,j)/2^k × exp(λ(2j-k)) = cosh(λ)^k.
    Proof uses the binomial theorem: (x+y)^k = Σ C(k,j) x^j y^{k-j}
    with x = exp(λ)/2, y = exp(-λ)/2. -/
theorem binomial_mgf (k : ℕ) (l : ℝ) :
    ∑ j ∈ Finset.range (k + 1),
        (Nat.choose k j : ℝ) / 2^k * Real.exp (l * (2 * (j : ℝ) - ↑k)) =
    (Real.cosh l) ^ k := by
  -- cosh(l) = (exp l + exp(-l))/2 = exp(l)/2 + exp(-l)/2
  have hcosh : Real.cosh l = Real.exp l / 2 + Real.exp (-l) / 2 := by
    rw [Real.cosh_eq]; ring
  rw [hcosh, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- Goal: (exp l / 2)^j * (exp(-l) / 2)^{k-j} * C(k,j) = C(k,j)/2^k * exp(l*(2j-k))
  -- Step 1: Split (a/b)^n into a^n/b^n
  rw [div_pow, div_pow]
  -- Step 2: Convert (exp x)^n to exp(n*x) using exp_nat_mul
  rw [← Real.exp_nat_mul l, ← Real.exp_nat_mul (-l)]
  -- Step 3: Combine the two fractions
  rw [div_mul_div_comm]
  -- Step 4: Combine exponents
  rw [← Real.exp_add]
  -- Step 5: Simplify 2^j * 2^{k-j} = 2^k
  rw [show (2 : ℝ) ^ j * 2 ^ (k - j) = 2 ^ k from by rw [← pow_add]; congr 1; omega]
  -- Step 6: Simplify exponent: j*l + (k-j)*(-l) = l*(2j-k)
  rw [show ↑j * l + ↑(k - j) * (-l) = l * (2 * ↑j - ↑k) from by
    push_cast [Nat.cast_sub hj_le]; ring]
  -- Step 7: Commutativity
  ring

/-- One-sided Chernoff bound for positive tail of binomial:
    Σ_{j : 2j-k > t} C(k,j)/2^k ≤ exp(-t²/(2k)) for t > 0. -/
theorem binomial_chernoff_upper (k : ℕ) (t : ℝ) (hk : 0 < k) (ht : 0 < t) :
    ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => t < 2 * (j : ℝ) - ↑k),
      (Nat.choose k j : ℝ) / 2^k ≤ Real.exp (-t^2 / (2 * k)) := by
  -- Use exponential Markov with λ = t/k and f(j) = 2j - k
  set l := t / (k : ℝ) with hl_def
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hl_pos : 0 < l := div_pos ht hk_pos
  -- Apply weighted exponential Markov
  have hmarkov := weighted_exp_markov (Finset.range (k + 1))
    (fun j => (Nat.choose k j : ℝ) / 2^k)
    (fun j => 2 * (j : ℝ) - ↑k)
    (fun j _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k))
    l t hl_pos
  -- The MGF equals cosh(l)^k
  have hmgf : ∑ j ∈ Finset.range (k + 1),
      (Nat.choose k j : ℝ) / 2^k * Real.exp (l * (2 * ↑j - ↑k)) =
      (Real.cosh l) ^ k := binomial_mgf k l
  -- cosh(l)^k ≤ exp(kl²/2) = exp(t²/(2k))
  have hcosh : (Real.cosh l) ^ k ≤ Real.exp (↑k * l ^ 2 / 2) := by
    calc (Real.cosh l) ^ k ≤ (Real.exp (l ^ 2 / 2)) ^ k :=
          pow_le_pow_left₀ (by positivity) (Real.cosh_le_exp_half_sq l) k
      _ = Real.exp (↑k * l ^ 2 / 2) := by
          rw [← Real.exp_nat_mul (l ^ 2 / 2) k]; congr 1; ring
  -- Combine: bound ≤ exp(-lt) × exp(kl²/2) = exp(kl²/2 - lt) = exp(-t²/(2k))
  calc ∑ j ∈ (Finset.range (k + 1)).filter _, (Nat.choose k j : ℝ) / 2^k
      ≤ Real.exp (-l * t) * ∑ j ∈ Finset.range (k + 1),
          (Nat.choose k j : ℝ) / 2^k * Real.exp (l * (2 * ↑j - ↑k)) := hmarkov
    _ = Real.exp (-l * t) * (Real.cosh l) ^ k := by rw [hmgf]
    _ ≤ Real.exp (-l * t) * Real.exp (↑k * l ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left hcosh (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-l * t + ↑k * l ^ 2 / 2) := by rw [← Real.exp_add]
    _ = Real.exp (-t ^ 2 / (2 * ↑k)) := by
        congr 1
        rw [hl_def]
        field_simp
        ring

/-- One-sided Chernoff bound for negative tail (by symmetry). -/
theorem binomial_chernoff_lower (k : ℕ) (t : ℝ) (hk : 0 < k) (ht : 0 < t) :
    ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t),
      (Nat.choose k j : ℝ) / 2^k ≤ Real.exp (-t^2 / (2 * k)) := by
  -- By symmetry j ↦ k - j, the negative tail sum equals the positive tail sum
  have hupper := binomial_chernoff_upper k t hk ht
  -- Show the two sums are equal via the bijection j ↦ k - j
  suffices heq : ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t),
      (Nat.choose k j : ℝ) / 2^k =
    ∑ j ∈ (Finset.range (k + 1)).filter
        (fun j : ℕ => t < 2 * (j : ℝ) - ↑k),
      (Nat.choose k j : ℝ) / 2^k by
    rw [heq]; exact hupper
  -- Use sum_nbij' with inverse j ↦ k - j
  apply Finset.sum_nbij' (fun j => k - j) (fun j => k - j)
  · -- hi: maps negative filter to positive filter
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨by omega, ?_⟩
    push_cast [Nat.cast_sub (by omega : j ≤ k)]
    linarith [hj.2]
  · -- hj: maps positive filter to negative filter
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    refine ⟨by omega, ?_⟩
    push_cast [Nat.cast_sub (by omega : j ≤ k)]
    linarith [hj.2]
  · -- left_inv: k - (k - j) = j
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    omega
  · -- right_inv: k - (k - j) = j
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    omega
  · -- Values match: C(k, k-j)/2^k = C(k, j)/2^k
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    congr 1; exact_mod_cast (Nat.choose_symm (by omega : j ≤ k)).symm

/-- Tail bound: For the random walk of length k, the probability of being
    outside [-t, t] is at most 2exp(-t²/(2k)) (from Hoeffding). -/
theorem binomial_tail_small (k : ℕ) (C : ℝ) (hk : 0 < k) (hC : 0 < C) :
    ∑ j ∈ (Finset.range (k + 1)).filter
      (fun j : ℕ => C * Real.sqrt k < |(2 * (j : ℝ) - k)|),
      (Nat.choose k j : ℝ) / 2^k ≤ 2 * Real.exp (-C^2 / 2) := by
  -- Split |2j-k| > C√k into two tails: 2j-k > C√k and 2j-k < -C√k
  set t := C * Real.sqrt k with ht_def
  have ht : 0 < t := mul_pos hC (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk))
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  -- The |·| filter is subset of the union of one-sided filters
  have hwnonneg : ∀ j ∈ Finset.range (k + 1),
      0 ≤ (Nat.choose k j : ℝ) / 2^k :=
    fun _ _ => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
  -- The two one-sided filters are disjoint (can't have both 2j-k > t and 2j-k < -t)
  have hdisjoint : Disjoint
      ((Finset.range (k + 1)).filter (fun j : ℕ => t < 2 * (j : ℝ) - ↑k))
      ((Finset.range (k + 1)).filter (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t)) := by
    simp only [Finset.disjoint_filter]
    intro j _ h1 h2; linarith
  calc ∑ j ∈ (Finset.range (k + 1)).filter
          (fun j : ℕ => t < |(2 * (j : ℝ) - ↑k)|),
        (Nat.choose k j : ℝ) / 2^k
      ≤ ∑ j ∈ ((Finset.range (k + 1)).filter (fun j : ℕ => t < 2 * (j : ℝ) - ↑k)) ∪
           ((Finset.range (k + 1)).filter (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t)),
        (Nat.choose k j : ℝ) / 2^k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at hj ⊢
          have habs := hj.2
          rw [lt_abs] at habs
          rcases habs with h | h
          · exact Or.inl ⟨hj.1, h⟩
          · exact Or.inr ⟨hj.1, by linarith⟩
        · intro j hj _
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hj
          exact hwnonneg j (Finset.mem_range.mpr (by rcases hj with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h))
    _ = (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => t < 2 * (j : ℝ) - ↑k),
          (Nat.choose k j : ℝ) / 2^k) +
        (∑ j ∈ (Finset.range (k + 1)).filter (fun j : ℕ => (2 * (j : ℝ) - ↑k) < -t),
          (Nat.choose k j : ℝ) / 2^k) :=
        Finset.sum_union hdisjoint
    _ ≤ Real.exp (-t^2 / (2 * k)) + Real.exp (-t^2 / (2 * k)) :=
        add_le_add (binomial_chernoff_upper k t hk ht) (binomial_chernoff_lower k t hk ht)
    _ = 2 * Real.exp (-t^2 / (2 * k)) := by ring
    _ = 2 * Real.exp (-C^2 / 2) := by
        congr 1; congr 1
        rw [ht_def, mul_pow, Real.sq_sqrt (le_of_lt hk_pos)]
        field_simp

end SPDE.Nonstandard
