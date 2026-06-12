import IsingModel.ContinuousSpin.TwoComponent
import IsingModel.Hamiltonian
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Two-component (planar rotator) multi-site Gibbs system (GJ §4.7)

The multi-site continuous vector-spin framework underlying GJ Theorem 4.7.1
(p. 70): two-component spins `ξ : ι → ℝ × ℝ` on a finite graph, with the
`SO(2)`-invariant single-spin potential `P(ξᵢ) = A·(ξᵢ·ξᵢ)² + σ·(ξᵢ·ξᵢ)`, the
ferromagnetic Hamiltonian `H = −∑ J·ξᵢ·ξⱼ − ∑ h·ξᵢ`, and the Gibbs weight
`exp(−β·H − ∑ᵢ P(ξᵢ))` integrated against the flat Lebesgue measure on
`(ℝ × ℝ)^ι`. The `t/q` correlations are `⟨∏_{i∈A} tᵢ · ∏_{j∈B} qⱼ⟩`.

This file establishes the definitions and their basic positivity /
measurability. The single-spin integrability, the multi-site weight
integrability, and the three inequalities of Theorem 4.7.1 follow in
subsequent PRs (Issue #3918).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §4.7, Theorem 4.7.1, p. 70
-/

namespace IsingModel.ContinuousSpin

open Real MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A two-component spin configuration: a vector spin `ξ i = (tᵢ, qᵢ) ∈ ℝ²` at
each site. -/
abbrev VectorConfig (ι : Type*) : Type _ := ι → ℝ × ℝ

/-- The first (`t`) component of the spin at site `i`. -/
def vSpinT (ξ : VectorConfig ι) (i : ι) : ℝ := (ξ i).1

/-- The second (`q`) component of the spin at site `i`. -/
def vSpinQ (ξ : VectorConfig ι) (i : ι) : ℝ := (ξ i).2

/-- The inner product `ξᵢ · ξⱼ = tᵢtⱼ + qᵢqⱼ` of two vector spins. -/
def vDot (ξ : VectorConfig ι) (i j : ι) : ℝ :=
  vSpinT ξ i * vSpinT ξ j + vSpinQ ξ i * vSpinQ ξ j

/-- The per-edge inner product as a symmetric quantity on `Sym2 ι`. -/
noncomputable def vEdgeDot (ξ : VectorConfig ι) : Sym2 ι → ℝ :=
  Sym2.lift ⟨fun i j => vDot ξ i j, fun i j => by simp only [vDot]; ring⟩

/-- The total single-spin potential `∑ᵢ P(ξᵢ)` with `P(ξ) = A(t²+q²)² + σ(t²+q²)`. -/
noncomputable def vectorPotentialSum (A σ : ℝ) (ξ : VectorConfig ι) : ℝ :=
  ∑ i : ι, twoCompPotential A σ (vSpinT ξ i) (vSpinQ ξ i)

/-- The two-component Hamiltonian `H = −J·∑_e ξᵢ·ξⱼ − h¹·∑ tᵢ − h²·∑ qᵢ`. -/
noncomputable def vectorHamiltonian (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h1 h2 : ℝ) (ξ : VectorConfig ι) : ℝ :=
  -J * ∑ e ∈ G.edgeFinset, vEdgeDot ξ e
    - h1 * ∑ i : ι, vSpinT ξ i - h2 * ∑ i : ι, vSpinQ ξ i

/-- The two-component Gibbs weight `exp(−β·H − ∑ᵢ P(ξᵢ))`. -/
noncomputable def vectorWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A σ J h1 h2 β : ℝ) (ξ : VectorConfig ι) : ℝ :=
  Real.exp (-β * vectorHamiltonian G J h1 h2 ξ - vectorPotentialSum A σ ξ)

omit [DecidableEq ι] in
/-- **The two-component Gibbs weight is positive.** -/
theorem vectorWeight_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A σ J h1 h2 β : ℝ) (ξ : VectorConfig ι) :
    0 < vectorWeight G A σ J h1 h2 β ξ :=
  Real.exp_pos _

/-- The two-component partition function `∫ exp(−βH − ∑P) dξ` over `(ℝ²)^ι`. -/
noncomputable def vectorPartition (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A σ J h1 h2 β : ℝ) : ℝ :=
  ∫ ξ : VectorConfig ι, vectorWeight G A σ J h1 h2 β ξ

/-- The two-component Gibbs expectation `⟨F⟩ = Z⁻¹ ∫ F·weight`. -/
noncomputable def vectorExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A σ J h1 h2 β : ℝ) (F : VectorConfig ι → ℝ) : ℝ :=
  (vectorPartition G A σ J h1 h2 β)⁻¹ *
    ∫ ξ : VectorConfig ι, F ξ * vectorWeight G A σ J h1 h2 β ξ

/-- The `t/q` monomial `∏_{i∈A} tᵢ · ∏_{j∈B} qⱼ`. -/
noncomputable def vectorMonomial (A B : Finset ι) (ξ : VectorConfig ι) : ℝ :=
  (∏ i ∈ A, vSpinT ξ i) * ∏ j ∈ B, vSpinQ ξ j

/-- The two-component correlation `⟨t^A q^B⟩`. -/
noncomputable def vectorCorrelation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (Apar σpar J h1 h2 β : ℝ) (A B : Finset ι) : ℝ :=
  vectorExpectation G Apar σpar J h1 h2 β (vectorMonomial A B)

/-! ## Continuity and measurability -/

omit [Fintype ι] [DecidableEq ι] in
/-- The spin components are continuous in the configuration. -/
theorem continuous_vSpinT (i : ι) : Continuous fun ξ : VectorConfig ι => vSpinT ξ i :=
  (continuous_apply i).fst

omit [Fintype ι] [DecidableEq ι] in
/-- The second spin component is continuous in the configuration. -/
theorem continuous_vSpinQ (i : ι) : Continuous fun ξ : VectorConfig ι => vSpinQ ξ i :=
  (continuous_apply i).snd

omit [Fintype ι] [DecidableEq ι] in
/-- The per-edge inner product is continuous. -/
theorem continuous_vEdgeDot (e : Sym2 ι) :
    Continuous fun ξ : VectorConfig ι => vEdgeDot ξ e := by
  induction e using Sym2.ind with
  | _ i j =>
    simp only [vEdgeDot, Sym2.lift_mk, vDot]
    exact ((continuous_vSpinT i).mul (continuous_vSpinT j)).add
      ((continuous_vSpinQ i).mul (continuous_vSpinQ j))

omit [DecidableEq ι] in
/-- The single-spin potential sum is continuous. -/
theorem continuous_vectorPotentialSum (A σ : ℝ) :
    Continuous fun ξ : VectorConfig ι => vectorPotentialSum A σ ξ := by
  refine continuous_finset_sum _ fun i _ => ?_
  simp only [twoCompPotential]
  have hsq : Continuous fun ξ : VectorConfig ι => vSpinT ξ i ^ 2 + vSpinQ ξ i ^ 2 :=
    ((continuous_vSpinT i).pow 2).add ((continuous_vSpinQ i).pow 2)
  exact (continuous_const.mul (hsq.pow 2)).add (continuous_const.mul hsq)

omit [DecidableEq ι] in
/-- The two-component Hamiltonian is continuous. -/
theorem continuous_vectorHamiltonian (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J h1 h2 : ℝ) :
    Continuous fun ξ : VectorConfig ι => vectorHamiltonian G J h1 h2 ξ := by
  unfold vectorHamiltonian
  refine ((continuous_const.mul (continuous_finset_sum _ fun e _ =>
    continuous_vEdgeDot e)).sub (continuous_const.mul
      (continuous_finset_sum _ fun i _ => continuous_vSpinT i))).sub
    (continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_vSpinQ i))

omit [DecidableEq ι] in
/-- The Gibbs weight is continuous, hence measurable. -/
theorem continuous_vectorWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A σ J h1 h2 β : ℝ) :
    Continuous fun ξ : VectorConfig ι => vectorWeight G A σ J h1 h2 β ξ := by
  unfold vectorWeight
  exact Real.continuous_exp.comp
    ((continuous_const.mul (continuous_vectorHamiltonian G J h1 h2)).sub
      (continuous_vectorPotentialSum A σ))

omit [Fintype ι] [DecidableEq ι] in
/-- The `t/q` monomial is continuous. -/
theorem continuous_vectorMonomial (A B : Finset ι) :
    Continuous fun ξ : VectorConfig ι => vectorMonomial A B ξ := by
  unfold vectorMonomial
  exact (continuous_finset_prod _ fun i _ => continuous_vSpinT i).mul
    (continuous_finset_prod _ fun j _ => continuous_vSpinQ j)

end IsingModel.ContinuousSpin
