import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete finite-volume energy closed forms and direct graph wrappers

Narrow child module for concrete `latticeGraph` finite-volume Hamiltonian
closed-form wrappers, direct finite-volume energy / partition / free-energy
bounds, and base spin-product helper wrappers. The theorem names are the same
as the former declarations, but callers can now avoid importing the
monolithic concrete module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d finite-volume Hamiltonian closed forms -/

/-- **ℤ^d hamiltonianΛ at `J = 0`** (Λ-induced subgraph): the Hamiltonian
reduces to `-h · Σ sign σ`. -/
theorem hamiltonianΛ_latticeGraph_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = -h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-- **ℤ^d hamiltonianΛ at zero parameters** (Λ-induced subgraph):
`H_Λ ⟨0, 0, β⟩ σ = 0`. -/
theorem hamiltonianΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) σ = 0 :=
  IsingModel.hamiltonian_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β σ

/-- **ℤ^d hamiltonianΛ equals `⊥`-hamiltonian at `J = 0`** (Λ-induced subgraph):
at `J = 0` the Hamiltonian is graph-independent. -/
theorem hamiltonianΛ_latticeGraph_eq_bot_at_J_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) σ :=
  IsingModel.hamiltonian_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-! ### Hamiltonian / Z bound / `J = 0` closed-form wrappers -/

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

The five wrappers `partitionFunction_eq_bot_at_J_zero_latticeGraph`,
`correlation_eq_bot_at_J_zero_latticeGraph`,
`spinProduct_singleton_latticeGraph`, `spinProduct_union_latticeGraph`,
`spinProduct_sq_latticeGraph` now live in
`EnergyClosedFormsSpinProductAndBot.lean`. -/



end Ambient
end IsingModel
