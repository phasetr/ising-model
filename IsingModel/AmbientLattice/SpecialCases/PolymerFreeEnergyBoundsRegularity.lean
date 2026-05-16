import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularityOn

/-!
# Ambient polymerFreeEnergyAlongExhaustion regularity wrappers

Narrow child module for 4 ambient `polymerFreeEnergyAlongExhaustion_*`
regularity wrappers (`ContinuousAt`, `DifferentiableAt`,
`ContinuousOn`, `DifferentiableOn`) extracted from
`PolymerFreeEnergyBounds.lean`:

* `polymerFreeEnergyAlongExhaustion_continuousAt`,
* `polymerFreeEnergyAlongExhaustion_differentiableAt`,
* `polymerFreeEnergyAlongExhaustion_continuousOn_Ici_zero`,
* `polymerFreeEnergyAlongExhaustion_differentiableOn_Ici_zero`.

Each result is a thin pass-through of the corresponding Λ-level
`polymerFreeEnergy_Λ_{continuousAt,differentiableAt,
continuousOn_Ici_zero,differentiableOn_Ici_zero}` lemma. The theorem
names are unchanged from the former `PolymerFreeEnergyBounds`
declarations.
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

/-! ## Moved: 2 `_On_Ici_zero` regularity wrappers

The two `_On_Ici_zero` regularity wrappers
(`polymerFreeEnergyAlongExhaustion_continuousOn_Ici_zero`,
`polymerFreeEnergyAlongExhaustion_differentiableOn_Ici_zero`) now
live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularityOn`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from the umbrella.
-/

end Ambient
end IsingModel
