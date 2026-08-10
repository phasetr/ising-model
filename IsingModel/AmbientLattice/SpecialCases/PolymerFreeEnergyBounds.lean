import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsRegularity
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsNonneg
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsTanh
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsEdgeCases
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsMonotoneOn

/-!
# Order preservation of the polymer free energy in the activity, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

The polymer free energy of the stage subgraph is order-preserving in the activity on the
nonnegative ray: from `0 ≤ t` and `t ≤ s` the value at `t` is at most the value at `s`. The
same conclusion is recorded a second time with `0 ≤ s` added to the hypothesis list.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy` preserves order on `[0, ∞)`**
(§18.5 along-ex wrap of Step 649). -/
theorem polymerFreeEnergyAlongExhaustion_le_of_le_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s :=
  polymerFreeEnergy_Λ_le_of_le_of_nonneg
    G (Λ.volume n) ht hs hts

/-- **Along-ex: `polymerFreeEnergy` strict-form order preservation**
(§18.5 along-ex wrap of Step 650). -/
theorem polymerFreeEnergyAlongExhaustion_le_of_le_strict_form
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ)
    {t s : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ≤
      IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s :=
  polymerFreeEnergy_Λ_le_of_le_strict_form
    G (Λ.volume n) ht hts

end Ambient
end IsingModel
