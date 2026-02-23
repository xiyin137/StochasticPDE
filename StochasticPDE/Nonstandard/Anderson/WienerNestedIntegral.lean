/-
# wienerNestedIntegral: Definition and Properties

Defines the nested integral computing Wiener cylinder probabilities via independent
increments, and proves key analytic properties:
* `wienerNestedIntegral_nonneg`: 0 ≤ W_n(x) for all x
* `wienerNestedIntegral_le_one`: W_n(x) ≤ 1 for all x
* `wienerNestedIntegral_continuous`: W_n is continuous in the prevPos argument

Extracted to a standalone file to break circular imports between
`AndersonTheorem.lean` and the properties file.
-/

import StochasticPDE.Nonstandard.LoebMeasure.WienerMeasure

namespace SPDE.Nonstandard

open MeasureTheory Real Finset Filter

/-! ## Definition -/

/-- Nested integral for computing Wiener cylinder probabilities via independent increments.
    Recursively computes:
    ∫_{I₁} ... ∫_{Iₙ} φ(x₁-x₀; t₁-t₀) · ... · φ(xₙ-xₙ₋₁; tₙ-tₙ₋₁) dxₙ...dx₁
    where (t₀, x₀) = (prevTime, prevPos) is the previous state. -/
noncomputable def wienerNestedIntegral : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) →
    (Fin n → ℝ) → ℝ → ℝ → ℝ
  | 0, _, _, _, _, _ => 1
  | k + 1, times, lowers, uppers, prevTime, prevPos =>
      let dt := times 0 - prevTime
      ∫ x in (lowers 0)..(uppers 0),
        gaussianDensity dt (x - prevPos) *
        wienerNestedIntegral k (times ∘ Fin.succ) (lowers ∘ Fin.succ)
          (uppers ∘ Fin.succ) (times 0) x

/-! ## Gaussian density infrastructure -/

/-- gaussianDensity is continuous as a function of x (for fixed variance). -/
theorem gaussianDensity_continuous (dt : ℝ) : Continuous (gaussianDensity dt) := by
  unfold gaussianDensity
  by_cases h : dt ≤ 0
  · simp only [if_pos h]
    exact continuous_const
  · simp only [if_neg h]
    apply Continuous.mul continuous_const
    show Continuous (fun x => Real.exp (-x ^ 2 / (2 * dt)))
    fun_prop

/-- gaussianDensity is integrable over ℝ when variance > 0. -/
theorem gaussianDensity_integrable {variance : ℝ} (hv : 0 < variance) :
    Integrable (gaussianDensity variance) := by
  unfold gaussianDensity
  simp only [if_neg (not_le.mpr hv)]
  have h_rewrite : ∀ x : ℝ, -x ^ 2 / (2 * variance) = -(1/(2 * variance)) * x ^ 2 := by
    intro x; field_simp
  simp_rw [h_rewrite]
  apply Integrable.const_mul
  exact integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / (2 * variance))

/-- gaussianDensity is IntervalIntegrable on any interval. -/
theorem gaussianDensity_intervalIntegrable (variance : ℝ) (p a b : ℝ) :
    IntervalIntegrable (fun x => gaussianDensity variance (x - p)) MeasureTheory.volume a b :=
  ((gaussianDensity_continuous variance).comp (continuous_id.sub continuous_const)).intervalIntegrable a b

/-- Shifted Gaussian integral: ∫ gaussianDensity(v, x - p) dx = 1 when v > 0. -/
theorem gaussianDensity_shifted_integral {variance : ℝ} (hv : 0 < variance) (p : ℝ) :
    ∫ x, gaussianDensity variance (x - p) = 1 := by
  rw [MeasureTheory.integral_sub_right_eq_self (gaussianDensity variance) p]
  exact gaussianDensity_integral_eq_one hv

/-! ## wienerNestedIntegral properties -/

/-- wienerNestedIntegral is nonneg: it's a nested integral of nonneg functions. -/
theorem wienerNestedIntegral_nonneg :
    ∀ (n : ℕ) (times : Fin n → ℝ) (lowers uppers : Fin n → ℝ)
      (prevTime prevPos : ℝ),
    (∀ i, lowers i < uppers i) →
    0 ≤ wienerNestedIntegral n times lowers uppers prevTime prevPos := by
  intro n
  induction n with
  | zero => intros; simp [wienerNestedIntegral]
  | succ k ih =>
    intro times lowers uppers prevTime prevPos hbounds
    simp only [wienerNestedIntegral]
    apply intervalIntegral.integral_nonneg (le_of_lt (hbounds 0))
    intro x _
    apply mul_nonneg
    · exact gaussianDensity_nonneg _ _
    · exact ih _ _ _ _ _ (fun i => hbounds i.succ)

/-- Combined properties of wienerNestedIntegral:
    bounded by 1 and continuous in the prevPos argument.
    Proved by combined induction since continuity is needed for integrability
    in the le_one proof. -/
theorem wienerNestedIntegral_le_one_and_continuous :
    ∀ (n : ℕ) (times : Fin n → ℝ) (lowers uppers : Fin n → ℝ)
      (prevTime : ℝ),
    (∀ i, prevTime < times i) →
    (∀ i j, i < j → times i < times j) →
    (∀ i, lowers i < uppers i) →
    (∀ prevPos, wienerNestedIntegral n times lowers uppers prevTime prevPos ≤ 1) ∧
    Continuous (fun prevPos => wienerNestedIntegral n times lowers uppers prevTime prevPos) := by
  intro n
  induction n with
  | zero =>
    intro times lowers uppers prevTime _ _ _
    refine ⟨fun _ => by simp [wienerNestedIntegral], ?_⟩
    simp only [wienerNestedIntegral]
    exact continuous_const
  | succ k ih =>
    intro times lowers uppers prevTime htimes htimes_incr hbounds
    -- Collect IH hypotheses for the recursive call
    have h_ih_time : ∀ i, times 0 < (times ∘ Fin.succ) i := by
      intro i; simp [Function.comp]
      exact htimes_incr ⟨0, by omega⟩ i.succ (by exact Fin.succ_pos i)
    have h_ih_incr : ∀ (i j : Fin k), i < j → (times ∘ Fin.succ) i < (times ∘ Fin.succ) j := by
      intro i j hij; simp [Function.comp]
      exact htimes_incr i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
    have h_ih_bounds : ∀ (i : Fin k), (lowers ∘ Fin.succ) i < (uppers ∘ Fin.succ) i := by
      intro i; simp [Function.comp]; exact hbounds i.succ
    -- Apply IH
    obtain ⟨ih_le_one, ih_cont⟩ := ih _ _ _ _ h_ih_time h_ih_incr h_ih_bounds
    -- Now prove both properties for k+1
    set dt := times 0 - prevTime with hdt_def
    have hdt_pos : 0 < dt := by simp [hdt_def]; linarith [htimes 0]
    -- Abbreviate the inner function
    set W_k := fun x => wienerNestedIntegral k (times ∘ Fin.succ) (lowers ∘ Fin.succ)
        (uppers ∘ Fin.succ) (times 0) x
    have hW_nn : ∀ x, 0 ≤ W_k x :=
      fun x => wienerNestedIntegral_nonneg k _ _ _ _ _ h_ih_bounds
    have hW_le : ∀ x, W_k x ≤ 1 := ih_le_one
    have hW_cont : Continuous W_k := ih_cont
    constructor
    · -- le_one: W_{k+1}(p) ≤ 1
      intro prevPos
      simp only [wienerNestedIntegral]
      set gauss_p := fun x => gaussianDensity dt (x - prevPos)
      set integrand := fun x => gauss_p x * W_k x
      have h_gauss_cont : Continuous gauss_p :=
        (gaussianDensity_continuous dt).comp (continuous_id.sub continuous_const)
      have h_int_intble : IntervalIntegrable integrand volume (lowers 0) (uppers 0) :=
        (h_gauss_cont.mul hW_cont).intervalIntegrable _ _
      have h_gauss_intble : IntervalIntegrable gauss_p volume (lowers 0) (uppers 0) :=
        h_gauss_cont.intervalIntegrable _ _
      calc ∫ x in (lowers 0)..(uppers 0), integrand x
          ≤ ∫ x in (lowers 0)..(uppers 0), gauss_p x := by
            apply intervalIntegral.integral_mono_on (le_of_lt (hbounds 0))
              h_int_intble h_gauss_intble
            intro x _
            calc gauss_p x * W_k x
                ≤ gauss_p x * 1 :=
                  mul_le_mul_of_nonneg_left (hW_le x) (gaussianDensity_nonneg _ _)
              _ = gauss_p x := mul_one _
        _ ≤ ∫ x, gauss_p x := by
            rw [intervalIntegral.integral_of_le (le_of_lt (hbounds 0))]
            exact setIntegral_le_integral
              ((gaussianDensity_integrable hdt_pos).comp_sub_right prevPos)
              (Eventually.of_forall (fun x => gaussianDensity_nonneg _ _))
        _ = 1 := gaussianDensity_shifted_integral hdt_pos prevPos
    · -- continuity: W_{k+1} is continuous in prevPos
      simp only [wienerNestedIntegral]
      have h_jointly_cont : Continuous (fun (px : ℝ × ℝ) =>
          gaussianDensity dt (px.2 - px.1) * W_k px.2) := by
        apply Continuous.mul
        · exact (gaussianDensity_continuous dt).comp (continuous_snd.sub continuous_fst)
        · exact hW_cont.comp continuous_snd
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun p x => gaussianDensity dt (x - p) * W_k x)
        h_jointly_cont continuous_const

/-- wienerNestedIntegral is bounded by 1. -/
theorem wienerNestedIntegral_le_one
    (n : ℕ) (times : Fin n → ℝ) (lowers uppers : Fin n → ℝ)
    (prevTime prevPos : ℝ)
    (htimes : ∀ i, prevTime < times i)
    (htimes_incr : ∀ i j, i < j → times i < times j)
    (hbounds : ∀ i, lowers i < uppers i) :
    wienerNestedIntegral n times lowers uppers prevTime prevPos ≤ 1 :=
  (wienerNestedIntegral_le_one_and_continuous n times lowers uppers prevTime
    htimes htimes_incr hbounds).1 prevPos

/-- wienerNestedIntegral is continuous in the prevPos argument. -/
theorem wienerNestedIntegral_continuous
    (n : ℕ) (times : Fin n → ℝ) (lowers uppers : Fin n → ℝ)
    (prevTime : ℝ)
    (htimes : ∀ i, prevTime < times i)
    (htimes_incr : ∀ i j, i < j → times i < times j)
    (hbounds : ∀ i, lowers i < uppers i) :
    Continuous (fun prevPos => wienerNestedIntegral n times lowers uppers prevTime prevPos) :=
  (wienerNestedIntegral_le_one_and_continuous n times lowers uppers prevTime
    htimes htimes_incr hbounds).2

end SPDE.Nonstandard
