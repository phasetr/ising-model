import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume energy and partition bounds

Narrow child module for direct concrete `latticeGraph` finite-volume
Boltzmann-weight, Hamiltonian, partition-function, and free-energy bound
wrappers. The theorem names are the same as the former declarations, but
callers can now avoid importing the monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume energy and partition bounds -/

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

/-- **ℤ^d boltzmannWeight positivity** at Λ-induced subgraph:
`0 < exp(-β H_Λ(σ))`. -/
theorem boltzmannWeightΛ_latticeGraph_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.boltzmannWeight_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d partitionFunctionΛ ≠ 0** at Λ-induced subgraph. -/
theorem partitionFunctionΛ_latticeGraph_ne_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ p ≠ 0 :=
  IsingModel.partitionFunction_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `hamiltonian` absolute value bound** at Λ-induced subgraph:
`|H_Λ(σ)| ≤ |J|·|E| + |h|·|Λ|`. -/
theorem hamiltonianΛ_latticeGraph_abs_le
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ|
      ≤ |p.J|
          * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        + |p.h| * Fintype.card (↑Λ : Type _) :=
  IsingModel.hamiltonian_abs_le
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-! ## Moved: freeEnergyΛ / partitionFunctionΛ upper / lower wrappers

The three wrappers
`freeEnergyΛ_latticeGraph_upper_bound`,
`partitionFunctionΛ_latticeGraph_upper`,
`partitionFunctionΛ_latticeGraph_lower` now live in
`FiniteVolumeEnergyBoundsPartition.lean`. -/


end Ambient
end IsingModel
