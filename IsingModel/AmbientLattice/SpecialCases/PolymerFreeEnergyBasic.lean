import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Basic polymer free-energy wrappers along an exhaustion

Narrow child module for along-exhaustion `polymerFreeEnergy` at-zero, at-one,
and nonnegative sandwich wrappers. This keeps callers that only need these
forwarders out of the monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy at-zero/at-one + sandwich along-ex -/

/-- **Along-ex: polymerFreeEnergy at `t = 0`** = 0. -/
theorem polymerFreeEnergyAlongExhaustion_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) 0 = 0 :=
  polymerFreeEnergy_Λ_at_zero G (Λ.volume n)

/-- **Along-ex: polymerFreeEnergy at `t = 1`** =
`log |vdCompatiblePolymerFamilies|`. -/
theorem polymerFreeEnergyAlongExhaustion_at_one
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) 1 =
      Real.log (IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G (Λ.volume n))).card :=
  polymerFreeEnergy_Λ_at_one G (Λ.volume n)

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
