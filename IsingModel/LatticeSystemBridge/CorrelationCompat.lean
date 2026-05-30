import IsingModel.LatticeSystemBridge.GibbsCompat

/-!
# Lattice-system bridge: correlation function compatibility

Extends `LatticeSystemBridge.GibbsCompat` with a generic correlation function on the
abstract `ClassicalSpinSystem` structure. The classical Ising correlation
`⟨σ^A⟩ = ⟨∏_{i ∈ A} spinSign(σ_i)⟩` becomes a specific instance via the
`spinProduct`-style observable.

Provides:

* `correlationOfAbstract` — generic correlation: takes an observable extractor
  `observable : Finset Λ → (Λ → S) → K` (typically a per-site product) and reduces to
  `gibbsExpectationOfAbstract` applied to that observable. The observable extractor is the
  spin-type-specific piece (Ising: `spinProduct = ∏ sign(σ_i)`; Potts: indicator product;
  etc.).
* `correlationOfAbstract_isingAsClassicalSpinSystem_eq` — bridge identity: the generic
  correlation specialized to the Ising instance with `observable = spinProduct` matches
  `IsingModel.correlation`.

This completes the basic abstraction triple (`ClassicalSpinSystem`,
`gibbsExpectationOfAbstract`, `correlationOfAbstract`) on which lattice-system's future
classical-spin-system layer can directly build.
-/

namespace IsingModel
namespace LatticeSystemBridge

open Finset

variable {Λ S K : Type*}

/-- **Generic correlation** on the abstract `ClassicalSpinSystem` data structure.

Given a classical spin system, an observable extractor
`observable : Finset Λ → (Λ → S) → K` (mapping a site subset and a configuration to a
field element — typically the spin-product `∏_{i ∈ A} spinSign(σ_i)` for Ising or a
similar product for Potts/clock models), a partition function value `Z`, a weight function
`weight : K → K`, and a subset `A : Finset Λ`, returns

    ⟨σ^A⟩ = (∑_σ observable A σ · weight(β · H(σ))) / Z

i.e. the Gibbs expectation of the observable at `A`. -/
noncomputable def correlationOfAbstract [Fintype (Λ → S)] [Field K]
    (system : ClassicalSpinSystem Λ S K) (weight : K → K) (Z : K)
    (observable : Finset Λ → (Λ → S) → K) (A : Finset Λ) : K :=
  gibbsExpectationOfAbstract system weight Z (observable A)

/-- **Bridge identity**: the generic correlation on the canonical Ising
`ClassicalSpinSystem` instance, with `observable = spinProduct`,
`weight = fun e => Real.exp (-e)`, and `Z = IsingModel.partitionFunction G p`, equals
the concrete `IsingModel.correlation G p A`. -/
theorem correlationOfAbstract_isingAsClassicalSpinSystem_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (p : IsingParams ℝ) (A : Finset ι) :
    correlationOfAbstract (isingAsClassicalSpinSystem G p)
        (fun e => Real.exp (-e)) (IsingModel.partitionFunction G p)
        IsingModel.spinProduct A
      = IsingModel.correlation G p A := by
  unfold correlationOfAbstract IsingModel.correlation
  exact gibbsExpectationOfAbstract_isingAsClassicalSpinSystem_eq G p (IsingModel.spinProduct A)

end LatticeSystemBridge
end IsingModel
