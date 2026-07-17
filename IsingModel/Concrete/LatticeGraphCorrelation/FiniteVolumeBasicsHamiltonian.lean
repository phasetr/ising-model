import IsingModel.AmbientLattice.Monotonicity
import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete Hamiltonian flip / symmetry wrappers

Narrow child module for five ℤ^d Hamiltonian flip / negative-field /
bottom-graph wrappers at the Λ layer (`edgeSpin_flip`,
`interactionEnergy_flip`, `hamiltonianΛ_flip_eq`,
`hamiltonianΛ_neg_h`, and `hamiltonian_bot`). Each wrapper is a thin
pass-through to the corresponding `IsingModel.*` lemma at the induced
graph.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d edgeSpin_flip at Λ-induced**:
`edgeSpin(σ.flip, e) = edgeSpin(σ, e)`. -/
theorem edgeSpin_flip_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (σ : IsingModel.Config (↑Λ : Type _)) (e : Sym2 (↑Λ : Type _)) :
    IsingModel.edgeSpin (K := ℝ) σ.flip e = IsingModel.edgeSpin σ e :=
  IsingModel.edgeSpin_flip σ e

/-- **ℤ^d interactionEnergy_flip at Λ-induced**:
`interactionEnergy_Λ(J, σ.flip) = interactionEnergy_Λ(J, σ)`. -/
theorem interactionEnergy_flip_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.interactionEnergy
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ.flip
      = IsingModel.interactionEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ :=
  IsingModel.interactionEnergy_flip
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J σ

/-- **ℤ^d hamiltonian_flip_eq at Λ-induced**: at `h = 0` the Hamiltonian
is invariant under spin flip. -/
theorem hamiltonianΛ_flip_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hp : p.h = 0)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ.flip
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.hamiltonian_flip_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hp σ

/-- **ℤ^d hamiltonian_neg_h at Λ-induced**:
`H_Λ(σ; -h) = H_Λ(σ.flip; h)`. -/
theorem hamiltonianΛ_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) σ.flip :=
  IsingModel.hamiltonian_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β σ

/-- **ℤ^d hamiltonian_bot at Λ**: `H_⊥(σ) = -h · Σ sign σ`. -/
theorem hamiltonian_bot_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian (⊥ : SimpleGraph (↑Λ : Type _)) p σ
      = -p.h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_bot p σ

end Ambient
end IsingModel
