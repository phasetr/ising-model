import IsingModel.Hamiltonian

/-!
# Lattice-system bridge: classical spin-system abstraction

A thin **abstract structure** for classical lattice spin systems, designed to be the
generic counterpart of `lattice-system`'s quantum framework. The structure is purely
record-shaped and additive — no existing `IsingModel.*` definition is touched, and no
property is required at the abstraction level (concrete spin models supply their own).

The abstraction captures three pieces of data common to all classical lattice spin systems:

* a vertex type `Λ` (a graph in the lattice-system convention),
* a per-site spin type `S` (Ising: `Spin` with sign `±1`; vector spins: `EuclideanSpace`; etc.),
* a coefficient field `K` (real for thermodynamic quantities; complex in analytic-continuation
  contexts).

A `ClassicalSpinSystem Λ S K` consists of:

* `hamiltonian : (Λ → S) → K` — the energy functional on configurations,
* `inverseTemperature : K` — the β parameter.

The Ising-specific data (`IsingParams`, `interactionEnergy + externalFieldEnergy`) is a
specific instance of this structure (see `Bridges/IsingAsClassicalSpinSystem`, below).
General constructions — Boltzmann weight, partition function, Gibbs expectation,
correlation — can be defined at this abstract level and specialized to Ising on demand.

This file does **not** define those generic constructions; that work belongs in subsequent
PRs (or in the lattice-system repository post-merger). It provides only the record type and
the canonical Ising instance, sufficient to verify that the abstraction layer is compatible
with the existing concrete Ising machinery.

References:

* `LatticeSystem.Lattice.couplingOf` and `LatticeSystem.Lattice.LatticeWithSpacing`
  (lattice-system, `Lattice/`).
* `IsingModel.IsingParams`, `IsingModel.hamiltonian` (this repo, `Basic.lean`,
  `Hamiltonian.lean`).
-/

namespace IsingModel
namespace LatticeSystemBridge

/-- **Generic classical spin-system data**: vertex type `Λ`, per-site spin type `S`,
coefficient field `K`, with an energy functional and an inverse-temperature parameter.

This is the lattice-system-compatible abstraction over which generic constructions
(Boltzmann weight, partition function, Gibbs expectation, correlation) can be defined
once the configuration space is finite (`[Fintype (Λ → S)]`, typically via `[Fintype Λ]`
and `[Fintype S]`).

The Ising model is a specific instance: `Λ = ι`, `S = Spin`, `K = ℝ`, with
`hamiltonian = IsingModel.hamiltonian G p` and `inverseTemperature = p.β`. -/
structure ClassicalSpinSystem (Λ S K : Type*) where
  /-- Energy functional on spin configurations. -/
  hamiltonian : (Λ → S) → K
  /-- Inverse temperature (the `β` parameter of the Gibbs measure). -/
  inverseTemperature : K

/-- **The Ising model as a `ClassicalSpinSystem`**: bridge constructor from the concrete
`IsingModel.IsingParams` and `IsingModel.hamiltonian G p` to the abstract data. -/
def isingAsClassicalSpinSystem {ι K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams K) :
    ClassicalSpinSystem ι Spin K where
  hamiltonian := IsingModel.hamiltonian G p
  inverseTemperature := p.β

@[simp]
theorem isingAsClassicalSpinSystem_hamiltonian {ι K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams K) (σ : Config ι) :
    (isingAsClassicalSpinSystem G p).hamiltonian σ = IsingModel.hamiltonian G p σ := rfl

@[simp]
theorem isingAsClassicalSpinSystem_inverseTemperature {ι K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (p : IsingParams K) :
    (isingAsClassicalSpinSystem G p).inverseTemperature = p.β := rfl

end LatticeSystemBridge
end IsingModel
