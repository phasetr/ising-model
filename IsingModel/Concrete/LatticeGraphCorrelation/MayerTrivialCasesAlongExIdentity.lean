import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerTrivialCasesIdentity

/-!
# Concrete AlongExhaustion Mayer identity trivial-case wrappers

Narrow child module for five ℤ^d
`mayer_identity_*_AlongExhaustion_latticeGraph_*` Mayer trivial case
wrappers (`no_polymers`, `no_polymers_tanh`, `trivial`,
`edgeFinset_empty`, `edgeFinset_empty_tanh`). Each wrapper is a thin
pass-through to the corresponding ambient
`mayer_identity_*_AlongExhaustion` lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d along-ex: Mayer identity for empty-polymer induced graphs**. -/
theorem mayer_identity_of_no_polymers_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t :=
  Ambient.mayer_identity_of_no_polymers_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_no t N

/-- **ℤ^d along-ex: Mayer identity for empty-polymer induced graphs
(tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_no_polymers_tanh_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_no β J N

/-- **ℤ^d along-ex: Mayer identity under disjunctive trivial
conditions**. -/
theorem mayer_identity_of_trivial_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) = ∅)
    (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_trivial_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h N

/-- **ℤ^d along-ex: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N t :=
  Ambient.mayer_identity_of_edgeFinset_empty_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_empty t N

/-- **ℤ^d along-ex: Mayer identity for edgeless induced graphs (tanh
form)**. -/
theorem
mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ)
    (h_empty : (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  Ambient.mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion
    (IsingModel.latticeGraph d) Λ n h_empty β J N


end Ambient
end IsingModel
