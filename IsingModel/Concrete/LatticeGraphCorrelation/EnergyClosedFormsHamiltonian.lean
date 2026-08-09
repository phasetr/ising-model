import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d Hamiltonian identities on the induced subgraph

Concrete `latticeGraph d` identities for the Hamiltonian on the subgraph induced by a fixed
finite volume, at a configuration on that volume. At vanishing coupling the Hamiltonian is
minus the external field times the sum of the spin signs, and agrees with the Hamiltonian of
the edgeless graph over the same vertex type; at vanishing coupling and field it is zero.
Reversing the sign of the field has the same effect as flipping every spin, and, when the
field of the parameter record vanishes, flipping every spin leaves the Hamiltonian unchanged.
That vanishing-field equation is the only hypothesis appearing in this module, and
no instance argument is taken.
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
