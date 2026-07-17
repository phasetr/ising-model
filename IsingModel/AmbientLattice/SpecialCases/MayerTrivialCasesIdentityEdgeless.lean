import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerIdentity

/-!
# Mayer identity edgeless wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion Mayer
identity wrappers for edgeless induced graphs extracted from
`MayerTrivialCasesIdentity.lean`:

* `mayer_identity_of_edgeFinset_empty_AlongExhaustion`
* `mayer_identity_of_edgeFinset_empty_tanh_AlongExhaustion`

Each wrapper is a thin pass-through to the corresponding
`mayer_identity_of_edgeFinset_empty_*_Λ` ambient lemma. Theorem
names are unchanged from the former `MayerTrivialCases`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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
