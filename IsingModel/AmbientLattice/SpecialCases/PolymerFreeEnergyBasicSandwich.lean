import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerPfeEdgeBounds

/-!
# Polymer free-energy sandwich-of-nonneg wrapper along an exhaustion

Narrow child module for the along-exhaustion
`polymerFreeEnergyAlongExhaustion_sandwich_of_nonneg` wrapper
extracted from `PolymerFreeEnergyBasic.lean`. The wrapper is a
thin pass-through to `polymerFreeEnergy_Λ_sandwich_of_nonneg`. The
theorem name is unchanged from the former `PolymerFreeEnergyBasic`
declaration.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy sandwich for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_sandwich_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + t) :=
  polymerFreeEnergy_Λ_sandwich_of_nonneg G (Λ.volume n) ht

end Ambient
end IsingModel
