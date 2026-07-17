import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaCapstones

/-!
# Mayer filter-connected base-case wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion
`mayerExpansionTermAlongExhaustion_filter_connected_{zero,one}`
base-case wrappers extracted from `MayerFilterConnected.lean`:

* `mayerExpansionTermAlongExhaustion_filter_connected_zero`
* `mayerExpansionTermAlongExhaustion_filter_connected_one`

Each wrapper is a thin pass-through to the corresponding ambient
`mayerExpansionTerm_Λ_filter_connected_{zero,one}` lemma stating
that the filter-connected piFinset is empty at `k = 0` and the
entire piFinset at `k = 1`. Theorem names are unchanged from the
former `MayerFilterConnected` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: mayerExpansionTerm filter-connected at k=0 = ∅**. -/
theorem mayerExpansionTermAlongExhaustion_filter_connected_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 0 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) = ∅ :=
  mayerExpansionTerm_Λ_filter_connected_zero G (Λ.volume n) t

/-- **Along-ex: mayerExpansionTerm filter-connected at k=1 = full
piFinset**. -/
theorem mayerExpansionTermAlongExhaustion_filter_connected_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n)))).filter
        (fun ω =>
          (IsingModel.polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset
        (fun _ : Fin 1 =>
          IsingModel.allPolymers
            (inducedGraph G (Λ.volume n))) :=
  mayerExpansionTerm_Λ_filter_connected_one G (Λ.volume n)

end Ambient
end IsingModel
