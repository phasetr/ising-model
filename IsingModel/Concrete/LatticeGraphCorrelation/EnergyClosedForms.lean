import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d finite-volume Hamiltonian closed forms and energy bounds (§10.3)

Concrete `latticeGraph d` statements on the subgraph induced by a fixed finite volume, at a
configuration on that volume. At vanishing coupling the Hamiltonian reduces to minus the
external field times the sum of the spin signs, and coincides with the Hamiltonian of the
edgeless graph over the same vertex type; when the field vanishes as well it is zero. The
Boltzmann weight is strictly positive at every configuration and every parameter record, and
the absolute value of the Hamiltonian is bounded by the absolute coupling times the induced
edge-set cardinality plus the absolute field times the number of sites. No statement here
carries a hypothesis, and no instance argument is taken.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
