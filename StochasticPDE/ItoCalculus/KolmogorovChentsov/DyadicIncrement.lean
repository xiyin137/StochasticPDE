/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Instances.ENNReal.Lemmas
import StochasticPDE.ItoCalculus.KolmogorovChentsov.DyadicPartition
import StochasticPDE.ItoCalculus.KolmogorovChentsov.MomentToTail

/-!
# Dyadic Increment Bounds + Borel-Cantelli

Under the Kolmogorov moment condition `E[|X_t - X_s|^p] ≤ M * |t-s|^q`,
for any threshold sequence `(δ_n)` with summable tail bounds,
a.e. eventually all dyadic increments at level n are ≤ δ_n.

## Main Results

* `dyadicSingleBad_measure_le` — Markov bound for a single dyadic interval
* `dyadicLevelBad_measure_le` — Union bound at level n
* `ae_eventually_dyadic_controlled` — Borel-Cantelli conclusion

## References

* Karatzas, Shreve, "Brownian Motion and Stochastic Calculus", Theorem 2.2.8
-/

namespace KolmogorovChentsov

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Dyadic bad events -/

/-- The bad event for a single dyadic interval (n, k): the increment exceeds threshold δ -/
def dyadicSingleBad (X : ℝ → Ω → ℝ) (T : ℝ) (n k : ℕ) (δ : ℝ) : Set Ω :=
  {ω | δ < |X (dyadicPoint T n (k + 1)) ω - X (dyadicPoint T n k) ω|}

/-- The bad event at level n: some dyadic increment exceeds threshold δ -/
def dyadicLevelBad (X : ℝ → Ω → ℝ) (T : ℝ) (n : ℕ) (δ : ℝ) : Set Ω :=
  ⋃ (k : Fin (2 ^ n)), dyadicSingleBad X T n k δ

/-! ## Step 1: Individual interval bound -/

/-- Markov bound for a single dyadic interval increment -/
theorem dyadicSingleBad_measure_le [IsFiniteMeasure μ]
    {p : ℕ} (hp : 0 < p) {q : ℕ}
    {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T) {M : ℝ}
    {n : ℕ} {k : ℕ} (_hk : k < 2 ^ n) {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun ω => |X (dyadicPoint T n (k + 1)) ω -
      X (dyadicPoint T n k) ω| ^ p) μ)
    (hbound : (∫ ω, |X (dyadicPoint T n (k + 1)) ω -
      X (dyadicPoint T n k) ω| ^ p ∂μ) ≤
      M * |dyadicPoint T n (k + 1) - dyadicPoint T n k| ^ q) :
    μ (dyadicSingleBad X T n k δ) ≤
      ENNReal.ofReal (M * (T / 2 ^ n) ^ q / δ ^ p) := by
  unfold dyadicSingleBad
  apply moment_tail_bound_strict hp hδ hint
  calc (∫ ω, |X (dyadicPoint T n (k + 1)) ω -
        X (dyadicPoint T n k) ω| ^ p ∂μ)
      ≤ M * |dyadicPoint T n (k + 1) - dyadicPoint T n k| ^ q := hbound
    _ = M * (T / 2 ^ n) ^ q := by rw [dyadicPoint_spacing_abs hT.le n k]

/-! ## Step 2: Union bound at level n -/

/-- Union bound: the level-n bad event probability is bounded by
    ENNReal.ofReal of (2^n * single_bound) -/
theorem dyadicLevelBad_measure_le [IsFiniteMeasure μ]
    {p : ℕ} (hp : 0 < p) {q : ℕ}
    {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T) {M : ℝ}
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hint : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      Integrable (fun ω => |X t ω - X s ω| ^ p) μ)
    (hbound : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      (∫ ω, |X t ω - X s ω| ^ p ∂μ) ≤ M * |t - s| ^ q) :
    μ (dyadicLevelBad X T n δ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / δ ^ p)) := by
  unfold dyadicLevelBad
  -- Each single bad event is bounded
  have hbound_each : ∀ k : Fin (2 ^ n),
      μ (dyadicSingleBad X T n ↑k δ) ≤
        ENNReal.ofReal (M * (T / 2 ^ n) ^ q / δ ^ p) := by
    intro ⟨k, hk⟩
    have hk_le : k ≤ 2 ^ n := Nat.le_of_lt hk
    have hk1_le : k + 1 ≤ 2 ^ n := hk
    exact dyadicSingleBad_measure_le hp hT hk hδ
      (hint _ _ (dyadicPoint_mem_Icc hT.le hk_le) (dyadicPoint_mem_Icc hT.le hk1_le))
      (hbound _ _ (dyadicPoint_mem_Icc hT.le hk_le) (dyadicPoint_mem_Icc hT.le hk1_le))
  -- Union ≤ sum ≤ 2^n * individual bound
  set c := ENNReal.ofReal (M * (T / 2 ^ n) ^ q / δ ^ p) with hc_def
  calc μ (⋃ k : Fin (2 ^ n), dyadicSingleBad X T n ↑k δ)
      ≤ ∑' k : Fin (2 ^ n), μ (dyadicSingleBad X T n ↑k δ) :=
        measure_iUnion_le _
    _ ≤ ∑' _ : Fin (2 ^ n), c := ENNReal.tsum_le_tsum hbound_each
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / δ ^ p)) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        -- Goal: (2^n) • c ≤ ENNReal.ofReal (2^n * ...)
        rw [hc_def]
        simp only [nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast (2 ^ n),
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ↑(2 ^ n : ℕ))]
        exact ENNReal.ofReal_le_ofReal (le_of_eq (by push_cast; rfl))

/-! ## Step 3: Borel-Cantelli conclusion -/

/-- **Borel-Cantelli for dyadic increments**: Under the Kolmogorov condition, for any
    threshold sequence `δ` with summable tail bounds, a.e. eventually all dyadic increments
    at level n are controlled by `δ n`. -/
theorem ae_eventually_dyadic_controlled [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 < T) {p q : ℕ} (hp : 0 < p)
    {M : ℝ}
    (hint : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      Integrable (fun ω => |X t ω - X s ω| ^ p) μ)
    (hbound : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      (∫ ω, |X t ω - X s ω| ^ p ∂μ) ≤ M * |t - s| ^ q)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n)
    (hterms_nn : ∀ n, 0 ≤ (2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p))
    (hsum : Summable (fun n => (2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p))) :
    ∀ᵐ ω ∂μ, ∃ N, ∀ n ≥ N, ∀ k, k < 2 ^ n →
      |X (dyadicPoint T n (k + 1)) ω - X (dyadicPoint T n k) ω| ≤ δ n := by
  -- Step 1: Show ∑ μ(E_n) < ∞
  have h_tsum_ne_top : (∑' n, μ (dyadicLevelBad X T n (δ n))) ≠ ⊤ := by
    have h_each : ∀ n, μ (dyadicLevelBad X T n (δ n)) ≤
        ENNReal.ofReal ((2 : ℝ) ^ n * (M * (T / 2 ^ n) ^ q / (δ n) ^ p)) :=
      fun n => dyadicLevelBad_measure_le hp hT n (hδ n) hint hbound
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h_each)
    rw [← ENNReal.ofReal_tsum_of_nonneg hterms_nn hsum]
    exact ENNReal.ofReal_ne_top
  -- Step 2: Apply Borel-Cantelli
  have h_bc := ae_eventually_notMem h_tsum_ne_top
  -- Step 3: Convert to explicit form
  refine h_bc.mono (fun ω hω => ?_)
  rw [Filter.eventually_atTop] at hω
  obtain ⟨N, hN⟩ := hω
  exact ⟨N, fun n hn k hk => by
    have h_not_bad := hN n hn
    simp only [dyadicLevelBad, Set.mem_iUnion, not_exists] at h_not_bad
    have := h_not_bad ⟨k, hk⟩
    simp only [dyadicSingleBad, Set.mem_setOf_eq, not_lt] at this
    exact this⟩

end KolmogorovChentsov
