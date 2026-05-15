import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer identity edge-case wrappers along an exhaustion

Narrow child module for the five §18.5 along-exhaustion Mayer
identity wrappers for no-polymer, trivial, and edgeless cases. Each
wrapper is a thin pass-through to the corresponding
`mayer_identity_of_*_Λ` ambient lemma. Theorem names are unchanged
from the former `MayerTrivialCases` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 mayer_identity_of edge-case along-ex wraps -/

/-- **Along-ex: Mayer identity for empty-polymer induced graphs**. -/
theorem mayer_identity_of_no_polymers_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N t :=
  mayer_identity_of_no_polymers_Λ G (Λ.volume n) h_no t N

/-- **Along-ex: Mayer identity for empty-polymer induced graphs
(tanh form)**. -/
theorem mayer_identity_of_no_polymers_tanh_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_no_polymers_tanh_Λ G (Λ.volume n) h_no β J N

/-- **Along-ex: Mayer identity under disjunctive trivial conditions**. -/
theorem mayer_identity_of_trivial_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) {β J : ℝ}
    (h : β * J = 0 ∨
      IsingModel.allPolymers
        (inducedGraph G (Λ.volume n)) = ∅) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_trivial_Λ G (Λ.volume n) h N

/-- **Along-ex: Mayer identity for edgeless induced graphs**. -/
theorem mayer_identity_of_edgeFinset_empty_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N t :=
  mayer_identity_of_edgeFinset_empty_Λ G (Λ.volume n) h_empty t N

/-- **Along-ex: Mayer identity for edgeless induced graphs (tanh
form)**. -/
theorem mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (β J : ℝ) (N : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) =
      IsingModel.mayerPartialSum
        (inducedGraph G (Λ.volume n)) N
        (Real.tanh (β * J)) :=
  mayer_identity_of_edgeFinset_empty_tanh_Λ
    G (Λ.volume n) h_empty β J N

end Ambient
end IsingModel
