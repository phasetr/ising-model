import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# Polymer free-energy edge-case vanishing wrappers along an exhaustion

Narrow child module for the two §18.5 ambient alongExhaustion
`polymerFreeEnergyAlongExhaustion_eq_zero_of_*` boundary-case
vanishing wrappers extracted from `PolymerFreeEnergyBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_eq_zero_of_no_polymers`
* `polymerFreeEnergyAlongExhaustion_eq_zero_of_edgeFinset_empty`

Each wrapper is a thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_eq_zero_of_*` lemma. Theorem names are
unchanged from the former `PolymerFreeEnergyBounds` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy = 0` for empty-polymer induced
graphs** (§18.5 along-ex wrap of Step 621). -/
theorem polymerFreeEnergyAlongExhaustion_eq_zero_of_no_polymers
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_no : IsingModel.allPolymers
      (inducedGraph G (Λ.volume n)) = ∅) (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t = 0 :=
  polymerFreeEnergy_Λ_eq_zero_of_no_polymers G (Λ.volume n) h_no t

/-- **Along-ex: `polymerFreeEnergy = 0` for edgeless induced
graphs** (§18.5 along-ex wrap of Step 623). -/
theorem
polymerFreeEnergyAlongExhaustion_eq_zero_of_edgeFinset_empty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ)
    (h_empty : (inducedGraph G (Λ.volume n)).edgeFinset = ∅)
    (t : ℝ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t = 0 :=
  polymerFreeEnergy_Λ_eq_zero_of_edgeFinset_empty
    G (Λ.volume n) h_empty t

end Ambient
end IsingModel
