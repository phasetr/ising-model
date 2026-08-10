import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticityTanh

/-!
# Real-analyticity of the polymer free energy in the activity, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

The polymer free energy of the stage subgraph, viewed as a function of the activity, is
real-analytic at each point of the nonnegative ray. The pointwise statement has `0 ≤ t` as its
only Prop-valued hypothesis; the `AnalyticOnNhd ℝ · (Set.Ici 0)` statement carries no
Prop-valued hypothesis.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_analyticAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G (Λ.volume n)) s) t :=
  polymerFreeEnergy_Λ_analyticAt G (Λ.volume n) ht

/-- **Along-ex: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem polymerFreeEnergyAlongExhaustion_analyticOnNhd_Ici_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph G (Λ.volume n)) s) (Set.Ici 0) :=
  polymerFreeEnergy_Λ_analyticOnNhd_Ici_zero G (Λ.volume n)

end Ambient
end IsingModel
