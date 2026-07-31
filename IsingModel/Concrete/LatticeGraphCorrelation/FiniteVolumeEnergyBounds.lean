import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume Boltzmann factorization and partition non-vanishing

Narrow child module for the two direct concrete `latticeGraph` finite-volume
wrappers `boltzmannWeight_subgraph_factor_latticeGraph` and
`partitionFunctionΛ_latticeGraph_ne_zero`, so that callers can avoid importing
the monolithic concrete module.

Boltzmann positivity and the `|H|` bound at the same induced graph are stated
once, in `EnergyClosedForms.lean`, as `boltzmannWeight_pos_latticeGraph` and
`hamiltonian_abs_le_latticeGraph`; the identically-stated copies that used to
sit here have been removed.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d Boltzmann subgraph factorization and partition non-vanishing -/

/-- **ℤ^d boltzmannWeight_subgraph_factor direct** (Λ-induced):
`w_{G₂} = (∏_e exp(...)) · w_{G₁}` for `G₁ ≤ G₂` on `↑Λ`. -/
theorem boltzmannWeight_subgraph_factor_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {G₁ G₂ : SimpleGraph (↑Λ : Type _)}
    [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    (h₁₂ : G₁ ≤ G₂) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.boltzmannWeight G₂ p σ
      = (∏ e ∈ G₂.edgeFinset \ G₁.edgeFinset,
          Real.exp (p.β * p.J * IsingModel.edgeSpin (K := ℝ) σ e))
        * IsingModel.boltzmannWeight G₁ p σ :=
  IsingModel.boltzmannWeight_subgraph_factor h₁₂ p σ

/-- **ℤ^d partitionFunctionΛ ≠ 0** at Λ-induced subgraph. -/
theorem partitionFunctionΛ_latticeGraph_ne_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p ≠ 0 :=
  IsingModel.partitionFunction_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-! ## Moved: freeEnergyΛ / partitionFunctionΛ upper / lower wrappers

The three wrappers
`freeEnergyΛ_latticeGraph_upper_bound`,
`partitionFunctionΛ_latticeGraph_upper`,
`partitionFunctionΛ_latticeGraph_lower` now live in
`FiniteVolumeEnergyBoundsPartition.lean`. -/


end Ambient
end IsingModel
