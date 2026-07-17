import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Polymer free-energy `HasDerivAt` wrapper along an exhaustion

Narrow child module for the along-exhaustion
`polymerFreeEnergyAlongExhaustion_hasDerivAt` wrapper extracted
from `PolymerFreeEnergyTanhBounds.lean`. The wrapper is a thin
pass-through to `polymerFreeEnergy_Λ_hasDerivAt`. The theorem name
is unchanged from the former `PolymerFreeEnergyTanhBounds`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  polymerFreeEnergy_Λ_hasDerivAt G (Λ.volume n) ht

end Ambient
end IsingModel
