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
  let JM : ItoProcessCoefficientJointMeasurability X :=
    ItoProcessCoefficientJointMeasurability.ofDriftDiffusion DR D
  obtain ⟨Mσ, hσ⟩ := hdiff_bdd
  obtain ⟨Md, hd⟩ := hdrift_bdd
  obtain ⟨Mx, hMx⟩ := hf_x_bdd
  obtain ⟨Mxx, hMxx⟩ := hf_xx_bdd
  obtain ⟨Mt, hMt⟩ := hf_t_bdd
  have hdiff_bdd' : ∃ M : ℝ, ∀ t ω, |X.diffusion t ω| ≤ M := ⟨Mσ, hσ⟩
  have hdrift_bdd' : ∃ M : ℝ, ∀ t ω, |X.drift t ω| ≤ M := ⟨Md, hd⟩
  have hf_x_bdd' : ∃ M : ℝ, ∀ t x, |deriv (fun x => f t x) x| ≤ M := ⟨Mx, hMx⟩
  have hf_xx_bdd' : ∃ M : ℝ, ∀ t x, |deriv (deriv (fun x => f t x)) x| ≤ M := ⟨Mxx, hMxx⟩
  have hf_t_bdd' : ∃ M : ℝ, ∀ t x, |deriv (fun s => f s x) t| ≤ M := ⟨Mt, hMt⟩
  have hX0 : Integrable (X.process 0) μ :=
    integrable_of_sq_integrable
      (((X.process_adapted 0).mono (F.le_ambient 0) le_rfl).aestronglyMeasurable)
      hX0_sq
  have hrem_int : ∀ t', 0 ≤ t' → Integrable (itoRemainderCore X f t') μ := by
    intro t' ht'
    exact itoRemainder_integrable_core X C FC JM f hf_t hf_x hMx hMt hMxx hd hσ
      hf_t_cont hf'_cont hf''_cont hX0 t' ht'
  have hrem_sq_int : ∀ t', 0 ≤ t' → Integrable (fun ω => (itoRemainderCore X f t' ω)^2) μ := by
    intro t' ht'
    exact itoRemainder_sq_integrable_core X C FC JM f hf_t hf_x hMx hMt hMxx hd hσ
      hf_t_cont hf'_cont hf''_cont hX0_sq t' ht'
  have hrem_int' : ∀ t', 0 ≤ t' →
      Integrable (itoRemainder (X.toItoProcessOfSplit C DR D FC) f t') μ := by
    intro t' ht'
    simpa [itoRemainder_eq_core] using hrem_int t' ht'
  have hrem_sq_int' : ∀ t', 0 ≤ t' →
      Integrable (fun ω => (itoRemainder (X.toItoProcessOfSplit C DR D FC) f t' ω)^2) μ := by
    intro t' ht'
    simpa [itoRemainder_eq_core] using hrem_sq_int t' ht'
  simpa [itoRemainder_eq_core] using
    (ito_formula_martingale (X := X.toItoProcessOfSplit C DR D FC) f hf_t hf_x hdiff_bdd'
      hdrift_bdd' hf_x_bdd' hf_xx_bdd' hf_t_bdd' hf_t_cont hf'_cont hf''_cont
      hrem_int' hrem_sq_int')

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
  simpa using
    (ito_formula (X := X.toItoProcessOfSplit C DR D FC) f hf_t hf_x hdiff_bdd hdrift_bdd
      hf_x_bdd hf_xx_bdd hf_t_bdd hf_t_cont hf'_cont hf''_cont hX0_sq)

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
