import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# ℤ^d Mayer identity on polymer-free and edgeless volumes

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the agreement of
`polymerFreeEnergy` with the Mayer partial sum at every truncation order in the degenerate
cases: when the induced subgraph has no polymer, when it has no edge, and, at the activity
`tanh (β * J)`, under the disjunction that `β * J = 0` or that subgraph has no polymer. The
polymer-free and edgeless cases are each given at a bare activity and at the activity
`tanh (β * J)`, and no statement here imposes a sign condition on the activity or on the
parameters.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d Λ: Mayer identity for empty-polymer induced graphs**. -/
theorem mayer_identity_of_no_polymers_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t :=
  Ambient.mayer_identity_of_no_polymers_Λ
    (IsingModel.latticeGraph d) Λ h_no t N

/-- **ℤ^d Λ: Mayer identity for empty-polymer induced graphs (tanh
form)**. -/
theorem mayer_identity_of_no_polymers_tanh_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_no_polymers_tanh_Λ
    (IsingModel.latticeGraph d) Λ h_no β J N

/-- **ℤ^d Λ: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_trivial_Λ
    (IsingModel.latticeGraph d) Λ h N

/-- **ℤ^d Λ: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N t :=
  Ambient.mayer_identity_of_edgeFinset_empty_Λ
    (IsingModel.latticeGraph d) Λ h_empty t N

/-- **ℤ^d Λ: Mayer identity for edgeless induced graphs (tanh form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_Λ_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h_empty : (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) Λ) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_edgeFinset_empty_tanh_Λ
    (IsingModel.latticeGraph d) Λ h_empty β J N

end Ambient
end IsingModel
