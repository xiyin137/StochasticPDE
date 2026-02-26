/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.ItoCalculus.ItoProcessCore
import StochasticPDE.ItoCalculus.ItoRemainderDef
import StochasticPDE.ItoCalculus.ItoFormulaProof

/-!
# Ito Formula Core Bridge

Compatibility theorems that apply the existing Itô formula proof to the
split `ItoProcessCore` assumption bundles via the reconstruction adapter.
-/

namespace SPDE

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Compatibility theorem: martingale property of the Itô remainder for
    split `core` assumptions, via the reconstruction adapter. -/
theorem ito_formula_martingale_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (hf_t_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
      ∫ ω in A, itoRemainderCore X f t ω ∂μ = ∫ ω in A, itoRemainderCore X f s ω ∂μ := by
  let R : ItoProcessRegularity X := ItoProcessRegularity.ofSplit C DR D FC
  let Xp : ItoProcess F μ := X.toItoProcess R
  have hdiff_bdd_core : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M := hdiff_bdd
  have hdrift_bdd_core : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M := hdrift_bdd
  have hf_x_bdd_core : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M := hf_x_bdd
  have hf_xx_bdd_core : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M := hf_xx_bdd
  have hf_t_bdd_core : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M := hf_t_bdd
  let Mσ : ℝ := hdiff_bdd_core.choose
  have hσ : ∀ t ω, |X.diffusion t ω| ≤ Mσ := hdiff_bdd_core.choose_spec
  let Md : ℝ := hdrift_bdd_core.choose
  have hd : ∀ t ω, |X.drift t ω| ≤ Md := hdrift_bdd_core.choose_spec
  let Mx : ℝ := hf_x_bdd_core.choose
  have hMx : ∀ t x, |deriv (fun x => f t x) x| ≤ Mx := hf_x_bdd_core.choose_spec
  let Mxx : ℝ := hf_xx_bdd_core.choose
  have hMxx : ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ Mxx := hf_xx_bdd_core.choose_spec
  let Mt : ℝ := hf_t_bdd_core.choose
  have hMt : ∀ t x, |deriv (fun s => f s x) t| ≤ Mt := hf_t_bdd_core.choose_spec
  have hdiff_bdd' : ∃ M : ℝ, ∀ t ω, |Xp.diffusion t ω| ≤ M := by
    simpa [Xp] using hdiff_bdd_core
  have hdrift_bdd' : ∃ M : ℝ, ∀ t ω, |Xp.drift t ω| ≤ M := by
    simpa [Xp] using hdrift_bdd_core
  have hX0 : Integrable (X.process 0) μ :=
    integrable_of_sq_integrable
      (((X.process_adapted 0).mono (F.le_ambient 0) le_rfl).aestronglyMeasurable)
      hX0_sq
  have hrem_int : ∀ t', 0 ≤ t' → Integrable (itoRemainderCore X f t') μ := by
    intro t' ht'
    exact itoRemainder_integrable_core (X := X) (C := C) (FC := FC)
      DR.drift_jointly_measurable D.diffusion_jointly_measurable
      f hf_t hf_x hMx hMt hMxx hd hσ
      hf_t_cont hf'_cont hf''_cont hX0 t' ht'
  have hrem_sq_int : ∀ t', 0 ≤ t' → Integrable (fun ω => (itoRemainderCore X f t' ω)^2) μ := by
    intro t' ht'
    exact itoRemainder_sq_integrable_core (X := X) (C := C) (FC := FC)
      DR.drift_jointly_measurable D.diffusion_jointly_measurable
      f hf_t hf_x hMx hMt hMxx hd hσ
      hf_t_cont hf'_cont hf''_cont hX0_sq t' ht'
  have hrem_int' : ∀ t', 0 ≤ t' →
      Integrable (itoRemainder Xp f t') μ := by
    intro t' ht'
    simpa [Xp, itoRemainder_eq_core] using hrem_int t' ht'
  have hrem_sq_int' : ∀ t', 0 ≤ t' →
      Integrable (fun ω => (itoRemainder Xp f t' ω)^2) μ := by
    intro t' ht'
    simpa [Xp, itoRemainder_eq_core] using hrem_sq_int t' ht'
  intro s t hs hst A hA
  by_cases hst_eq : s = t
  · subst hst_eq
    rfl
  have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
  have ht_pos : 0 < t := lt_of_le_of_lt hs hst_lt
  have hmain :
      ∫ ω in A, itoRemainder Xp f t ω ∂μ = ∫ ω in A, itoRemainder Xp f s ω ∂μ := by
    exact martingale_setIntegral_eq_of_L2_limit
      (hrem_int' s hs)
      (hrem_int' t ht_pos.le)
      (fun n => si_increment_integrable Xp f hf_x hf_x_bdd_core t ht_pos.le n s hs)
      (fun n => si_increment_integrable Xp f hf_x hf_x_bdd_core t ht_pos.le n t ht_pos.le)
      (fun n => si_increment_diff_sq_integrable Xp f hf_x hf_x_bdd_core t ht_pos.le n s hs
        (hrem_int' s hs) (hrem_sq_int' s hs))
      (fun n => si_increment_diff_sq_integrable Xp f hf_x hf_x_bdd_core t ht_pos.le n t ht_pos.le
        (hrem_int' t ht_pos.le) (hrem_sq_int' t ht_pos.le))
      (si_increment_L2_convergence Xp f hf_t hf_x hdiff_bdd' hdrift_bdd' hf_x_bdd_core hf_xx_bdd_core
        hf_t_bdd_core hf_t_cont hf'_cont hf''_cont t ht_pos s hs hst
        (hrem_int' s hs) (hrem_sq_int' s hs))
      (si_increment_L2_convergence Xp f hf_t hf_x hdiff_bdd' hdrift_bdd' hf_x_bdd_core hf_xx_bdd_core
        hf_t_bdd_core hf_t_cont hf'_cont hf''_cont t ht_pos t ht_pos.le le_rfl
        (hrem_int' t ht_pos.le) (hrem_sq_int' t ht_pos.le))
      (F.le_ambient s _ hA)
      (fun n => si_increment_martingale_property Xp f hf_x hf_x_bdd_core t ht_pos n
        s t hs hst le_rfl A hA)
  simpa [Xp, itoRemainder_eq_core] using hmain

/-- Compatibility theorem: existing Itô formula proof works for
    split `core` assumptions
    via the reconstruction adapter. -/
theorem ito_formula_core {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (C : ItoProcessConstruction X)
    (DR : ItoProcessDriftRegularity X)
    (D : ItoProcessDiffusionRegularity X)
    (FC : ItoProcessFiltrationCompatibility X)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (hf_t_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ) :
    ∃ (stoch_int : ℝ → Ω → ℝ),
      (∀ᵐ ω ∂μ, stoch_int 0 ω = 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t →
        ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
        ∫ ω in A, stoch_int t ω ∂μ = ∫ ω in A, stoch_int s ω ∂μ) ∧
      (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
        f t (X.process t ω) = f 0 (X.process 0 ω) +
          (∫ (s : ℝ) in Set.Icc 0 t,
            (deriv (fun u => f u (X.process s ω)) s +
             deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
             (1 / 2) * deriv (deriv (fun x => f s x)) (X.process s ω) *
             (X.diffusion s ω) ^ 2) ∂volume) +
          stoch_int t ω) := by
  have R : ItoProcessRegularity X :=
    ItoProcessRegularity.ofSplit C DR D FC
  refine ⟨itoRemainderCore X f, ?_, ?_, ?_⟩
  · filter_upwards with ω
    unfold itoRemainderCore
    have hmeas_zero : (volume.restrict (Set.Icc (0 : ℝ) 0)) = 0 := by
      rw [Measure.restrict_eq_zero, Set.Icc_self]
      simp
    rw [hmeas_zero, integral_zero_measure]
    ring
  · exact ito_formula_martingale_core X
      R.toConstruction R.toDriftRegularity
      R.toDiffusionRegularity R.toFiltrationCompatibility
      f hf_t hf_x hdiff_bdd hdrift_bdd
      hf_x_bdd hf_xx_bdd hf_t_bdd hf_t_cont hf'_cont hf''_cont hX0_sq
  · intro t ht
    filter_upwards with ω
    unfold itoRemainderCore
    ring

/-- Regularity-first entry point for the martingale part of Itô formula on
    `ItoProcessCore`. -/
theorem ito_formula_martingale_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (hf_t_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ) :
    ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
      ∫ ω in A, itoRemainderCore X f t ω ∂μ = ∫ ω in A, itoRemainderCore X f s ω ∂μ := by
  simpa using
    (ito_formula_martingale_core (X := X)
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      f hf_t hf_x hdiff_bdd hdrift_bdd hf_x_bdd hf_xx_bdd hf_t_bdd
      hf_t_cont hf'_cont hf''_cont hX0_sq)

/-- Regularity-first entry point for Itô formula on `ItoProcessCore`. -/
theorem ito_formula_core_ofRegularity {F : Filtration Ω ℝ}
    [IsProbabilityMeasure μ]
    (X : ItoProcessCore F μ)
    (R : ItoProcessRegularity X)
    (f : ℝ → ℝ → ℝ)
    (hf_t : ∀ x, Differentiable ℝ (fun t => f t x))
    (hf_x : ∀ t, ContDiff ℝ 2 (fun x => f t x))
    (hdiff_bdd : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M)
    (hdrift_bdd : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M)
    (hf_x_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M)
    (hf_xx_bdd : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M)
    (hf_t_bdd : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M)
    (hf_t_cont : Continuous (fun p : ℝ × ℝ => deriv (fun t => f t p.2) p.1))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => f p.1 x) p.2))
    (hf''_cont : Continuous (fun p : ℝ × ℝ => deriv (deriv (fun x => f p.1 x)) p.2))
    (hX0_sq : Integrable (fun ω => (X.process 0 ω) ^ 2) μ) :
    ∃ (stoch_int : ℝ → Ω → ℝ),
      (∀ᵐ ω ∂μ, stoch_int 0 ω = 0) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t →
        ∀ A : Set Ω, @MeasurableSet Ω (F.σ_algebra s) A →
        ∫ ω in A, stoch_int t ω ∂μ = ∫ ω in A, stoch_int s ω ∂μ) ∧
      (∀ t : ℝ, t ≥ 0 → ∀ᵐ ω ∂μ,
        f t (X.process t ω) = f 0 (X.process 0 ω) +
          (∫ (s : ℝ) in Set.Icc 0 t,
            (deriv (fun u => f u (X.process s ω)) s +
             deriv (fun x => f s x) (X.process s ω) * X.drift s ω +
             (1 / 2) * deriv (deriv (fun x => f s x)) (X.process s ω) *
             (X.diffusion s ω) ^ 2) ∂volume) +
          stoch_int t ω) := by
  simpa using
    (ito_formula_core (X := X)
      (C := R.toConstruction) (DR := R.toDriftRegularity)
      (D := R.toDiffusionRegularity) (FC := R.toFiltrationCompatibility)
      f hf_t hf_x hdiff_bdd hdrift_bdd hf_x_bdd hf_xx_bdd hf_t_bdd
      hf_t_cont hf'_cont hf''_cont hX0_sq)

end SPDE
