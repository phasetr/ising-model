import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete `hamiltonian_*_latticeGraph` direct wrappers

Narrow child module for five ℤ^d `hamiltonian_*_latticeGraph` direct
wrappers (`hamiltonian_J_zero`, `hamiltonian_flip_eq`,
`hamiltonian_neg_h`, `hamiltonian_zero_params`,
`hamiltonian_eq_bot_at_J_zero`). Each wrapper is a thin pass-through to
the corresponding `IsingModel.hamiltonian_*` lemma at the induced
graph.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d hamiltonian_J_zero direct** (Λ-induced): at `J = 0`,
`H = -h · ∑ sign(σ_i)`. Thin pass-through of
`IsingModel.hamiltonian_J_zero`. -/
theorem hamiltonian_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = -h * ∑ i : (↑Λ : Type _), IsingModel.Spin.sign ℝ (σ i) :=
  IsingModel.hamiltonian_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

/-! ### Hamiltonian spin-flip, `J = 0` graph-independence, and spinProduct helpers -/

/-- **ℤ^d hamiltonian_flip_eq direct** (Λ-induced, `h = 0`): at `h = 0`
the Hamiltonian is invariant under global spin flip. Thin pass-through
of `IsingModel.hamiltonian_flip_eq`. -/
theorem hamiltonian_flip_eq_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) (hp : p.h = 0)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ.flip
      = IsingModel.hamiltonian
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p σ :=
  IsingModel.hamiltonian_flip_eq
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p hp σ

/-- **ℤ^d hamiltonian_neg_h direct** (Λ-induced): the `h → -h` reflection
corresponds to the global spin flip:
`H(σ; J, -h, β) = H(σ.flip; J, h, β)`. Thin pass-through of
`IsingModel.hamiltonian_neg_h`. -/
theorem hamiltonian_neg_h_latticeGraph
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

/-- **ℤ^d hamiltonian_zero_params direct** (Λ-induced): at `J = h = 0`,
`H = 0`. Thin pass-through of `IsingModel.hamiltonian_zero_params`. -/
theorem hamiltonian_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) σ = 0 :=
  IsingModel.hamiltonian_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β σ

/-- **ℤ^d hamiltonian_eq_bot_at_J_zero direct** (Λ-induced):
at `J = 0` the Hamiltonian coincides with the one on the edgeless graph
`⊥`. Thin pass-through of `IsingModel.hamiltonian_eq_bot_at_J_zero`. -/
theorem hamiltonian_eq_bot_at_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (σ : IsingModel.Config (↑Λ : Type _)) :
    IsingModel.hamiltonian
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) σ
      = IsingModel.hamiltonian
          (⊥ : SimpleGraph (↑Λ : Type _))
          (⟨0, h, β⟩ : IsingParams ℝ) σ :=
  IsingModel.hamiltonian_eq_bot_at_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β σ

end Ambient
end IsingModel
