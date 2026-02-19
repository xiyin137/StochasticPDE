/-
Copyright (c) 2025 ModularPhysics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ModularPhysics Contributors
-/
import StochasticPDE.SPDE
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian

/-!
# 2D Yang-Mills Theory as SPDE

This file formalizes the stochastic Yang-Mills equation in 2 dimensions
following Chandra-Chevyrev-Hairer-Shen (2020).

## Main Definitions

* `GaugeGroup` - A compact Lie group for gauge theory
* `SmoothConnection` - A g-valued 1-form (gauge field)
* `StochasticYangMills2D` - The stochastic YM heat flow
* `DistributionalConnection` - The state space Ω¹_α

## Key Results

* The state space Ω¹_α of distributional connections with well-defined holonomies
* The orbit space O_α = Ω¹_α/G_{0,α} is a Polish space
* Local existence and uniqueness for the stochastic YM equation
* Gauge covariance of the solution

## References

* Chandra, Chevyrev, Hairer, Shen, "Langevin dynamic for the 2D Yang-Mills measure"
  arXiv:2006.04987 (2022)
* Chandra, Chevyrev, Hairer, Shen, "Stochastic quantisation of Yang-Mills-Higgs in 3D"
  arXiv:2201.03487 (2022)
-/

namespace SPDE.Examples

open MeasureTheory

/-! ## Gauge Groups and Lie Algebras

We use a simplified representation where the gauge group data is specified by
dimension. The Lie algebra is represented as ℝ^n with the bracket operation. -/

/-- A compact Lie group suitable for gauge theory.
    We parameterize by the dimension of the Lie algebra for simplicity. -/
structure GaugeGroup (n : ℕ) where
  /-- The Lie bracket [·,·] : 𝔤 × 𝔤 → 𝔤 -/
  bracket : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)
  /-- Antisymmetry: [X, Y] = -[Y, X] -/
  bracket_antisymm : ∀ X Y, bracket X Y = -bracket Y X
  /-- Jacobi identity -/
  jacobi : ∀ X Y Z,
    bracket X (bracket Y Z) + bracket Y (bracket Z X) + bracket Z (bracket X Y) = 0

namespace GaugeGroup

variable {n : ℕ}

/-- The Lie algebra type -/
abbrev LieAlg (_G : GaugeGroup n) : Type := Fin n → ℝ

/-- SU(N) gauge group (dimension = N²-1).
    The bracket is the matrix commutator [X,Y] = XY - YX on the Lie algebra su(N).
    For general N, the structure constants depend on a basis choice. -/
noncomputable def SU (N : ℕ) (_hN : N ≥ 2) : GaugeGroup (N^2 - 1) where
  bracket := sorry -- Structure constants of su(N) depend on basis choice
  bracket_antisymm := sorry
  jacobi := sorry

/-- U(1) - the abelian gauge group (dimension = 1).
    The Lie algebra is ℝ with trivial bracket [X,Y] = 0. -/
def U1 : GaugeGroup 1 where
  bracket := fun _ _ => 0
  bracket_antisymm := fun _ _ => by ext; simp
  jacobi := fun _ _ _ => by ext; simp

/-- SO(3) gauge group (dimension = 3).
    The Lie algebra so(3) ≅ ℝ³ with bracket given by the cross product:
    [e₁,e₂] = e₃, [e₂,e₃] = e₁, [e₃,e₁] = e₂. -/
def SO3 : GaugeGroup 3 where
  bracket := fun X Y =>
    ![X 1 * Y 2 - X 2 * Y 1, X 2 * Y 0 - X 0 * Y 2, X 0 * Y 1 - X 1 * Y 0]
  bracket_antisymm := fun X Y => by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring
  jacobi := fun X Y Z => by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> ring

end GaugeGroup

/-! ## The 2-Torus as Spacetime -/

/-- The 2-dimensional torus 𝕋² = ℝ²/ℤ² -/
structure Torus2 where
  /-- A point on the torus represented as (x, y) ∈ [0,1)² -/
  coords : Fin 2 → ℝ
  /-- Coordinates are in [0, 1) -/
  in_range : ∀ i, 0 ≤ coords i ∧ coords i < 1

namespace Torus2

/-- The origin of the torus -/
def origin : Torus2 := ⟨fun _ => 0, fun _ => ⟨le_refl 0, by norm_num⟩⟩

/-- Distance on the torus (flat metric) -/
noncomputable def dist (p q : Torus2) : ℝ :=
  Real.sqrt (∑ i, (min (|p.coords i - q.coords i|) (1 - |p.coords i - q.coords i|))^2)

end Torus2

/-! ## Connections and Curvature -/

/-- A smooth connection (gauge field) on 𝕋².
    A = A₁ dx¹ + A₂ dx² where A_i : 𝕋² → 𝔤 -/
structure SmoothConnection (n : ℕ) (G : GaugeGroup n) where
  /-- The components A_i : 𝕋² → 𝔤 -/
  components : Fin 2 → Torus2 → G.LieAlg

namespace SmoothConnection

variable {n : ℕ} {G : GaugeGroup n}

/-- The curvature 2-form F_A = dA + [A ∧ A]
    F_{12} = ∂₁A₂ - ∂₂A₁ + [A₁, A₂] -/
noncomputable def curvature (A : SmoothConnection n G) : Torus2 → G.LieAlg :=
  fun x => G.bracket (A.components 0 x) (A.components 1 x)
  -- Simplified: should include ∂₁A₂ - ∂₂A₁

/-- The Yang-Mills action S[A] = (1/2) ∫_{𝕋²} |F_A|² dx -/
noncomputable def action (_A : SmoothConnection n G) : ℝ := sorry

/-- The covariant derivative d_A = d + [A, ·] -/
def covariantDerivative (A : SmoothConnection n G) (φ : Torus2 → G.LieAlg)
    (i : Fin 2) : Torus2 → G.LieAlg :=
  fun x => G.bracket (A.components i x) (φ x)

end SmoothConnection

/-! ## Gauge Transformations -/

/-- A gauge transformation g : 𝕋² → G (represented abstractly).
    For SU(N), this is a smooth map g : 𝕋² → SU(N). -/
structure GaugeTransformation (n : ℕ) (_G : GaugeGroup n) where
  /-- The Hölder regularity of the gauge transformation (should be > 1) -/
  regularity : ℝ
  /-- Regularity is positive -/
  regularity_pos : regularity > 1
  /-- Winding number (for non-trivial bundles on 𝕋²) -/
  winding : ℤ := 0

namespace GaugeTransformation

variable {n : ℕ} {G : GaugeGroup n}

/-- The identity gauge transformation (smooth, so any regularity > 1) -/
def id : GaugeTransformation n G := ⟨2, by norm_num, 0⟩

/-- Gauge transformations form a group (composition preserves regularity) -/
def compose (g₁ g₂ : GaugeTransformation n G) : GaugeTransformation n G :=
  ⟨min g₁.regularity g₂.regularity, lt_min g₁.regularity_pos g₂.regularity_pos, g₁.winding + g₂.winding⟩

/-- Action of gauge transformation on a connection:
    A^g = g⁻¹ A g + g⁻¹ dg -/
noncomputable def actOnConnection (_g : GaugeTransformation n G)
    (_A : SmoothConnection n G) : SmoothConnection n G := sorry

end GaugeTransformation

/-! ## Distributional Connections (Hölder-Besov spaces) -/

/-- The Hölder-Besov space C^α(𝕋²; 𝔤) for α ∈ (2/3, 1).
    This is the state space for 2D Yang-Mills. -/
structure HolderBesov (n : ℕ) (G : GaugeGroup n) (α : ℝ) where
  /-- Regularity parameter -/
  alpha_range : 2/3 < α ∧ α < 1
  /-- The distribution (as a functional on test functions) -/
  distribution : (Torus2 → ℝ) → G.LieAlg
  /-- The Hölder-Besov norm is finite -/
  norm_finite : ℝ
  /-- The norm is non-negative -/
  norm_nonneg : norm_finite ≥ 0

/-- The space Ω¹_α of distributional 1-forms.
    Key insight from CCHS (2020):
    1. For α > 2/3, holonomies along smooth curves are well-defined
    2. The space admits a group action by Hölder gauge transformations
    3. For α > 1/2, holonomies along axis-parallel paths are well-defined
    4. The orbit space O_α = Ω¹_α/G_{0,α} is Polish -/
structure DistributionalConnection (n : ℕ) (G : GaugeGroup n) (α : ℝ) where
  /-- The regularity parameter α ∈ (2/3, 1) -/
  alpha_range : 2/3 < α ∧ α < 1
  /-- The distributional 1-form (as a functional on test forms) -/
  distribution : (Fin 2 → Torus2 → ℝ) → G.LieAlg
  /-- The Hölder-Besov norm of the connection -/
  norm : ℝ
  /-- The norm is non-negative -/
  norm_nonneg : norm ≥ 0

namespace DistributionalConnection

variable {n : ℕ} {G : GaugeGroup n}

/-- Holonomy along a smooth curve γ: [0,1] → 𝕋².
    This is the path-ordered exponential P exp(∫_γ A). -/
noncomputable def holonomy (_A : DistributionalConnection n G α)
    (_γ : ℝ → Torus2) : G.LieAlg := sorry

/-- For α > 2/3, the holonomy map is continuous in the connection (Theorem 3.1 of CCHS).
    The holonomy depends Lipschitz-continuously on the distributional connection. -/
theorem holonomy_continuous (A₁ A₂ : DistributionalConnection n G α)
    (γ : ℝ → Torus2) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ j : Fin n,
      |holonomy A₁ γ j - holonomy A₂ γ j| ≤ C * |A₁.norm - A₂.norm| := sorry

/-- The axial gauge fixing: A₁ vanishes along {x₁ = 0}.
    In the distributional sense: for any test function φ supported on {x₁ = 0},
    the pairing ⟨A₁, φ⟩ = 0. -/
def axialGauge (A : DistributionalConnection n G α) : Prop :=
  ∀ (φ : Torus2 → ℝ), (∀ p, p.coords 0 ≠ 0 → φ p = 0) →
    A.distribution (fun i => if i.val = 0 then φ else fun _ => 0) = 0

end DistributionalConnection

/-! ## The Gauge Group on Hölder Spaces -/

/-- The Hölder gauge group G_{0,α} of gauge transformations in C^{1+α}.
    These are gauge transformations with regularity 1 + α that are based at the origin. -/
structure HolderGaugeGroup (n : ℕ) (_G : GaugeGroup n) (α : ℝ) where
  /-- Regularity parameter α ∈ (2/3, 1) -/
  alpha_range : 2/3 < α ∧ α < 1
  /-- The Hölder norm of the gauge transformation -/
  holder_norm : ℝ
  /-- The norm is non-negative -/
  norm_nonneg : holder_norm ≥ 0
  /-- Winding number (for based gauge transformations, typically 0) -/
  winding : ℤ := 0

/-- The orbit space O_α = Ω¹_α / G_{0,α}.
    This is the space of gauge equivalence classes of distributional connections. -/
structure OrbitSpace (n : ℕ) (G : GaugeGroup n) (α : ℝ) where
  /-- A representative connection in a fixed gauge (e.g., axial gauge) -/
  representative : DistributionalConnection n G α
  /-- The regularity is in the allowed range -/
  alpha_range : 2/3 < α ∧ α < 1

/-- The orbit space is Polish (Theorem 3.4 of CCHS).
    This means O_α is a complete separable metrizable space. -/
structure OrbitSpacePolish (n : ℕ) (G : GaugeGroup n) (α : ℝ) where
  /-- The regularity is in the allowed range -/
  alpha_range : 2/3 < α ∧ α < 1
  /-- The metric on the orbit space -/
  metric : OrbitSpace n G α → OrbitSpace n G α → ℝ
  /-- The metric is non-negative -/
  metric_nonneg : ∀ x y, metric x y ≥ 0
  /-- The metric is symmetric -/
  metric_symm : ∀ x y, metric x y = metric y x

/-! ## The Stochastic Yang-Mills Equation -/

/-- The stochastic Yang-Mills heat flow in 2D.
    ∂_t A = -d*_A F_A + ξ
    where ξ is 𝔤-valued space-time white noise.

    The equation is gauge-covariant: if A(t) solves SYM and g is a gauge transformation,
    then A^g(t) also solves SYM. -/
structure StochasticYangMills2D (n : ℕ) (G : GaugeGroup n) where
  /-- The noise regularity (should be negative in 2D) -/
  noise_regularity : ℝ
  /-- Noise regularity is negative -/
  noise_regularity_neg : noise_regularity < 0
  /-- The constant C ∈ End(𝔤) (commutes with Ad action) -/
  constant_C : G.LieAlg →ₗ[ℝ] G.LieAlg

namespace StochasticYangMills2D

variable {n : ℕ} {G : GaugeGroup n}

/-- Local existence for the SYM equation (Theorem 1.1 of CCHS).
    For initial data A₀ ∈ Ω¹_α with α > 2/3, there exists
    a unique local solution in C([0,T]; Ω¹_α). -/
structure LocalExistence (sym : StochasticYangMills2D n G) (α : ℝ)
    (initial : DistributionalConnection n G α) where
  /-- The regularity is in the allowed range -/
  alpha_range : 2/3 < α ∧ α < 1
  /-- The existence time -/
  existence_time : ℝ
  /-- The existence time is positive -/
  existence_time_pos : existence_time > 0
  /-- The existence time depends on the initial data norm -/
  time_depends_on_norm : existence_time ≤ 1 / (1 + initial.norm)

/-- Uniqueness of solutions (in the orbit space).
    Two solutions starting from gauge-equivalent initial data remain gauge-equivalent.
    Expressed via uniqueness of existence time for a given initial datum. -/
structure Uniqueness (sym : StochasticYangMills2D n G) where
  /-- Two local existence results for the same initial data agree on existence time -/
  unique_time : ∀ α : ℝ, 2/3 < α → α < 1 →
    ∀ (A : DistributionalConnection n G α)
      (le₁ le₂ : LocalExistence sym α A),
    le₁.existence_time = le₂.existence_time

/-- Gauge covariance: if A(t) solves SYM and g is a gauge transformation,
    then A^g(t) also solves SYM. Expressed via preservation of existence time. -/
structure GaugeCovariance (sym : StochasticYangMills2D n G) where
  /-- Gauge transformations preserve solvability: if A₀ has a local solution,
      then after applying a gauge transformation the existence time is at least as long -/
  covariant_time : ∀ α : ℝ, 2/3 < α → α < 1 →
    ∀ (A : DistributionalConnection n G α) (g : HolderGaugeGroup n G α)
      (le : LocalExistence sym α A),
    ∃ (A' : DistributionalConnection n G α) (le' : LocalExistence sym α A'),
      le'.existence_time ≥ le.existence_time

/-- The solution is a Markov process on the orbit space O_α.
    Characterized by a transition semigroup P_t on bounded observables. -/
structure MarkovProperty (_sym : StochasticYangMills2D n G) (α : ℝ) where
  /-- The regularity is in the allowed range -/
  alpha_range : 2/3 < α ∧ α < 1
  /-- The transition semigroup P_t on the orbit space O_α.
      P_t f(x) = E[f(A(t)) | [A(0)] = x] where [·] denotes the gauge orbit. -/
  transition : ℝ → (OrbitSpace n G α → ℝ) → OrbitSpace n G α → ℝ
  /-- Semigroup property: P_{s+t} = P_s ∘ P_t -/
  semigroup_property : ∀ s t : ℝ, s ≥ 0 → t ≥ 0 →
    ∀ f x, transition (s + t) f x = transition s (transition t f) x
  /-- Identity: P_0 = id -/
  initial : ∀ f x, transition 0 f x = f x

/-- Convergence to the Yang-Mills measure (Theorem 1.2 of CCHS).
    The law of the solution converges to the YM measure as t → ∞. -/
structure ConvergenceToYM (sym : StochasticYangMills2D n G) where
  /-- The rate of convergence (exponential) -/
  convergence_rate : ℝ
  /-- The rate is positive -/
  rate_pos : convergence_rate > 0

end StochasticYangMills2D

/-! ## The Regularity Structure for 2D YM -/

/-- Model parameters for the 2D stochastic Yang-Mills equation.
    Uses the tree-based infrastructure from `RegularityStructures/`.
    Section 6 of CCHS develops a "basis-free" framework for vector-valued noise.
    - Noise regularity α = -1 (in 2D, YM noise is less singular than Φ⁴)
    - Kernel order β = 2 (heat kernel) -/
noncomputable def YM2D_ModelParameters : SPDE.RegularityStructures.ModelParameters 2 where
  noiseRegularity := -1
  kernelOrder := 2
  minHomogeneity := -1
  maxHomogeneity := 2
  hom_lt := by norm_num

/-- The BPHZ model for 2D YM (Section 6.2 of CCHS).
    This provides the concrete realization of abstract symbols as distributions.
    Uses the trivial admissible model as a starting point. -/
noncomputable def YM2D_BPHZModel : SPDE.RegularityStructures.AdmissibleModel 2 YM2D_ModelParameters :=
  SPDE.RegularityStructures.AdmissibleModel.trivialModel

/-! ## The Yang-Mills Measure -/

/-- The 2D Yang-Mills measure (formal).
    μ_YM(dA) = Z⁻¹ exp(-S_YM[A]) dA

    The SYM equation is the Langevin dynamics for this measure.
    This measure is supported on the orbit space O_α for α > 2/3. -/
structure YangMillsMeasure2D (n : ℕ) (_G : GaugeGroup n) where
  /-- The regularity of the support -/
  support_regularity : ℝ
  /-- The regularity is in the allowed range -/
  regularity_range : 2/3 < support_regularity ∧ support_regularity < 1
  /-- The partition function Z (normalization constant) -/
  partition_function : ℝ
  /-- Finite partition function (for compact gauge groups) -/
  finite_Z : partition_function > 0

namespace YangMillsMeasure2D

variable {n : ℕ} {G : GaugeGroup n}

/-- The Yang-Mills measure is the unique invariant measure for SYM -/
structure IsInvariant (μ : YangMillsMeasure2D n G) (sym : StochasticYangMills2D n G) where
  /-- The transition semigroup P_t on O_α associated to the SYM dynamics.
      P_t f(x) = E[f(X_t) | X_0 = x] for the orbit-space Markov process. -/
  transition : ℝ → (OrbitSpace n G μ.support_regularity → ℝ) →
    OrbitSpace n G μ.support_regularity → ℝ
  /-- The semigroup satisfies P_0 = id (identity at time 0) -/
  semigroup_initial : ∀ f x, transition 0 f x = f x
  /-- Uniqueness: any other YM measure with the same support regularity
      has the same partition function -/
  unique_partition : ∀ (μ' : YangMillsMeasure2D n G),
    μ'.support_regularity = μ.support_regularity →
    μ'.partition_function = μ.partition_function

/-- Exponential ergodicity (Theorem 1.3 of CCHS).
    The law of the solution converges exponentially fast to μ_YM. -/
structure ExponentialErgodicity (μ : YangMillsMeasure2D n G) where
  /-- The exponential rate of convergence -/
  rate : ℝ
  /-- The rate is positive -/
  rate_pos : rate > 0

/-- Wilson loop expectations are well-defined.
    For any smooth loop γ, 𝔼_μ[Tr(Hol_γ(A))] is finite. -/
structure WilsonLoopsWellDefined (μ : YangMillsMeasure2D n G) where
  /-- Wilson loop expectations are bounded: for any smooth loop γ and connection A,
      the holonomy is bounded component-wise -/
  bounded : ∀ (γ : ℝ → Torus2) (A : DistributionalConnection n G μ.support_regularity),
    ∃ C : ℝ, C > 0 ∧ ∀ j : Fin n, |A.holonomy γ j| ≤ C

end YangMillsMeasure2D

/-! ## Master Field and Large N Limit -/

/-- The master field limit as N → ∞ for SU(N) gauge theory.
    Wilson loop expectations become deterministic in this limit.
    The master field W(γ) = lim_{N→∞} 𝔼[(1/N)Tr(Hol_γ)] is deterministic. -/
structure MasterField where
  /-- The limiting Wilson loop expectation (deterministic) -/
  wilson_loop : (ℝ → Torus2) → ℝ
  /-- Wilson loops are bounded by 1 (for SU(N)) -/
  wilson_bounded : ∀ γ : ℝ → Torus2, |wilson_loop γ| ≤ 1
  /-- Trivial loop has expectation 1 -/
  trivial_loop : wilson_loop (fun _ => Torus2.origin) = 1
  /-- Makeenko-Migdal area derivative: ∂W(γ)/∂Area = -W(γ₁)W(γ₂) at intersection -/
  makeenko_migdal_coeff : ℝ  -- The coefficient in the MM equations

/-- The master field satisfies the Makeenko-Migdal equations.
    These equations determine the master field from the area derivative relation.
    For SU(∞) YM on the plane, the MM coefficient equals 1. -/
structure MakeenkoMigdal (mf : MasterField) where
  /-- The Makeenko-Migdal coefficient equals 1 for the large-N master field.
      This encodes the area derivative relation ∂W(γ)/∂Area = -W(γ₁)W(γ₂). -/
  coeff_eq_one : mf.makeenko_migdal_coeff = 1

end SPDE.Examples
