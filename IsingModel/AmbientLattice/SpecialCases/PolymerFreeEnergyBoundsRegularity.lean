import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularityOn

/-!
# Ambient polymerFreeEnergyAlongExhaustion regularity wrappers

Provides pointwise regularity of the along-exhaustion polymer free energy (GJ §18.5), the
input for differentiating the cluster expansion in the activity parameter. Each result
passes through the corresponding Λ-level `polymerFreeEnergy_Λ_*` lemma.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-exhaustion: `polymerFreeEnergy` is `ContinuousAt` for
`t ≥ 0`** (§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_continuousAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ContinuousAt (fun s : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) s) t :=
  polymerFreeEnergy_Λ_continuousAt G (Λ.volume n) ht

/-- **Along-exhaustion: `polymerFreeEnergy` is `DifferentiableAt`
for `t ≥ 0`** (§18.5 along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_differentiableAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    DifferentiableAt ℝ (fun s : ℝ =>
        IsingModel.polymerFreeEnergy
          (inducedGraph G (Λ.volume n)) s) t :=
  polymerFreeEnergy_Λ_differentiableAt G (Λ.volume n) ht

end Ambient
end IsingModel
