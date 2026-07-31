import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume Boltzmann positivity and Hamiltonian bound

Narrow child module for the two direct `latticeGraph` finite-volume wrappers
`boltzmannWeight_pos_latticeGraph` and `hamiltonian_abs_le_latticeGraph`. Each
is a thin pass-through to the corresponding general `IsingModel.*` statement at
`Ambient.inducedGraph (latticeGraph d) Λ`, so that callers can avoid importing
the monolithic concrete module.

The ℤ^d Hamiltonian closed forms at `J = 0`, at zero parameters, and against the
edgeless graph are stated once, in `EnergyClosedFormsHamiltonian.lean`, as
`hamiltonian_{J_zero,zero_params,eq_bot_at_J_zero}_latticeGraph`; the
identically-stated copies that used to sit here have been removed.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d Boltzmann positivity and finite-volume energy bound -/

/-- **ℤ^d boltzmannWeight_pos direct** (Λ-induced): `0 < w(σ)` pointwise.
Thin pass-through of `IsingModel.boltzmannWeight_pos`. -/
theorem boltzmannWeight_pos_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    0 < IsingModel.boltzmannWeight
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.boltzmannWeight_pos
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-- **ℤ^d hamiltonian_abs_le direct** (Λ-induced):
`|H(σ)| ≤ |J| · |E(latticeGraph d)|_Λ + |h| · |Λ|`. Thin pass-through of
`IsingModel.hamiltonian_abs_le`. Finite-volume energy bound (GJ §10.3). -/
theorem hamiltonian_abs_le_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ|
      ≤ |p.J| *
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        + |p.h| * Fintype.card (↑Λ : Type _) :=
  IsingModel.hamiltonian_abs_le
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ

/-! ## Moved: partition / freeEnergy bound wrappers

The three wrappers
`partitionFunction_upper_latticeGraph`,
`partitionFunction_lower_latticeGraph`,
`freeEnergy_upper_bound_latticeGraph` now live in
`EnergyClosedFormsPartitionBounds.lean`. -/


/-! ## Moved: `hamiltonian_*_latticeGraph` direct wrappers

The five wrappers `hamiltonian_{J_zero,flip_eq,neg_h,zero_params,eq_bot_at_J_zero}_latticeGraph`
now live in `EnergyClosedFormsHamiltonian.lean`. -/


/-! ## Moved: spinProduct and `J = 0` bot wrappers

The four wrappers `correlation_eq_bot_at_J_zero_latticeGraph`,
`spinProduct_singleton_latticeGraph`, `spinProduct_union_latticeGraph`,
`spinProduct_sq_latticeGraph` now live in
`EnergyClosedFormsSpinProductAndBot.lean`. -/



end Ambient
end IsingModel
