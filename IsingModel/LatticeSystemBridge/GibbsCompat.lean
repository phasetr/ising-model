import IsingModel.LatticeSystemBridge.Abstraction
import IsingModel.GibbsMeasure

/-!
# Lattice-system bridge: Gibbs expectation compatibility

Demonstrate that the abstract `ClassicalSpinSystem` data structure
(`LatticeSystemBridge.Abstraction`) preserves the existing `IsingModel.gibbsExpectation`
semantics on its canonical Ising instance: the `IsingModel.gibbsExpectation G p` is
computable from the abstract `isingAsClassicalSpinSystem G p` together with the existing
`IsingModel.partitionFunction G p`.

This file provides:

* `gibbsExpectationOfAbstract` — a generic Gibbs expectation defined on the abstract
  `ClassicalSpinSystem` data, given a partition function value `Z`.
* `gibbsExpectationOfAbstract_isingAsClassicalSpinSystem` — bridge identity: the
  generic Gibbs expectation, applied to the canonical Ising abstract instance with
  `Z = IsingModel.partitionFunction G p`, equals the concrete `IsingModel.gibbsExpectation`.

The abstraction is intentionally **thin**: it captures the algebraic shape
`⟨F⟩ = (∑_σ F(σ) · exp(-β · H(σ))) / Z` without referencing graph- or spin-specific
structure, so it ports directly to other classical spin systems (continuous spins, Potts,
clock models, …) when those are integrated.
-/

namespace IsingModel
namespace LatticeSystemBridge

open Finset

variable {Λ S K : Type*}

/-- **Generic Gibbs expectation** on the abstract `ClassicalSpinSystem` data.

Given a classical spin system, an observable `F : (Λ → S) → K`, and a partition function
value `Z : K`, returns the standard Gibbs expectation:

    ⟨F⟩ = (∑_σ F(σ) · exp(-β · H(σ))) / Z

The Boltzmann weight `exp(-β · H(σ))` requires `K` to support the exponential function
(`Real`, `Complex`, etc.); we expose it as a parameter `weight : K → K` (typically
`Real.exp ∘ Neg.neg`) so the bridge stays purely algebraic and `K`-agnostic.

The classical Ising instance recovers `IsingModel.gibbsExpectation` exactly when
`weight = fun e => Real.exp (-e)` and `Z = IsingModel.partitionFunction G p`. -/
noncomputable def gibbsExpectationOfAbstract [Fintype (Λ → S)] [Field K]
    (system : ClassicalSpinSystem Λ S K) (weight : K → K) (Z : K)
    (F : (Λ → S) → K) : K :=
  (∑ σ : Λ → S, F σ * weight (system.inverseTemperature * system.hamiltonian σ)) / Z

/-- **Bridge identity**: the generic abstract Gibbs expectation, applied to the canonical
Ising `ClassicalSpinSystem` instance with `weight = Real.exp ∘ Neg.neg` and
`Z = IsingModel.partitionFunction G p`, equals the concrete `IsingModel.gibbsExpectation`.

Confirms the abstract layer is **semantically compatible** with the existing Ising
implementation: nothing changes in behavior, only the data structure is reorganized.

Both sides equal `(∑_σ F(σ) · exp(-β · H(σ))) / Z`. -/
theorem gibbsExpectationOfAbstract_isingAsClassicalSpinSystem_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (F : Config ι → ℝ) :
    gibbsExpectationOfAbstract (isingAsClassicalSpinSystem G p)
        (fun e => Real.exp (-e)) (IsingModel.partitionFunction G p) F
      = IsingModel.gibbsExpectation G p F := by
  unfold gibbsExpectationOfAbstract IsingModel.gibbsExpectation
  simp only [isingAsClassicalSpinSystem_hamiltonian, isingAsClassicalSpinSystem_inverseTemperature]
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  unfold IsingModel.boltzmannWeight
  ring_nf

end LatticeSystemBridge
end IsingModel
