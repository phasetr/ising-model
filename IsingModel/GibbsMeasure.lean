import IsingModel.Hamiltonian
import Mathlib.Analysis.Complex.Exponential

/-!
# Gibbs measure, partition function, and expectations

Definitions for the Ising model Gibbs measure on a finite lattice.
These are specialized to `ℝ` since they require the exponential function.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Boltzmann weight and partition function -/

/-- The Boltzmann weight for a configuration: `exp(-β * H(σ))`. -/
noncomputable def boltzmannWeight (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) : ℝ :=
  Real.exp (-p.β * hamiltonian G p σ)

/-- The partition function: `Z = ∑_σ exp(-β * H(σ))`. -/
noncomputable def partitionFunction (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) : ℝ :=
  ∑ σ : Config ι, boltzmannWeight G p σ

omit [DecidableEq ι] in
/-- Each Boltzmann weight is positive. -/
theorem boltzmannWeight_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (σ : Config ι) :
    0 < boltzmannWeight G p σ :=
  Real.exp_pos _

/-- The partition function is positive. -/
theorem partitionFunction_pos (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    0 < partitionFunction G p := by
  unfold partitionFunction
  apply Finset.sum_pos
  · intro σ _
    exact boltzmannWeight_pos G p σ
  · exact Finset.univ_nonempty

/-- The partition function is nonzero. -/
theorem partitionFunction_ne_zero (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) :
    partitionFunction G p ≠ 0 :=
  ne_of_gt (partitionFunction_pos G p)

/-! ## Gibbs expectation -/

/-- The Gibbs expectation of an observable `F`: `⟨F⟩ = Z⁻¹ ∑_σ F(σ) exp(-β H(σ))`. -/
noncomputable def gibbsExpectation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) : ℝ :=
  (partitionFunction G p)⁻¹ * ∑ σ : Config ι, F σ * boltzmannWeight G p σ

/-! ## Correlation function -/

/-- The spin product `σ^A = ∏_{i ∈ A} toSign(σ_i)`, as a real number. -/
noncomputable def spinProduct (A : Finset ι) (σ : Config ι) : ℝ :=
  ∏ i ∈ A, (↑(σ i).toSign : ℝ)

/-- The correlation function `⟨σ^A⟩ = ⟨∏_{i ∈ A} s(σ_i)⟩`. -/
noncomputable def correlation (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) : ℝ :=
  gibbsExpectation G p (spinProduct A)

/-! ## Spin product algebra -/

omit [Fintype ι] [DecidableEq ι] in
/-- The spin product over the empty set is `1`. -/
@[simp]
theorem spinProduct_empty (σ : Config ι) : spinProduct ∅ σ = 1 := by
  simp [spinProduct]

omit [Fintype ι] [DecidableEq ι] in
/-- The spin product over a singleton is the spin sign at that site. -/
@[simp]
theorem spinProduct_singleton (i : ι) (σ : Config ι) :
    spinProduct {i} σ = ↑(σ i).toSign := by
  simp [spinProduct]

omit [Fintype ι] in
/-- The spin product over a disjoint union factors: `σ^{A ∪ B} = σ^A · σ^B`. -/
theorem spinProduct_union {A B : Finset ι} (h : Disjoint A B) (σ : Config ι) :
    spinProduct (A ∪ B) σ = spinProduct A σ * spinProduct B σ := by
  simp [spinProduct, Finset.prod_union h]

omit [Fintype ι] [DecidableEq ι] in
/-- The square of any spin product is `1`, since each factor is `±1`. -/
theorem spinProduct_sq (A : Finset ι) (σ : Config ι) :
    spinProduct A σ ^ 2 = 1 := by
  simp only [sq, spinProduct, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => by
    simp [← sq, ← Int.cast_pow, Spin.toSign_sq]

end IsingModel
