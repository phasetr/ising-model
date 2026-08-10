import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaPolymerBounds

/-!
# Nonnegativity of the polymer free energy at a nonnegative activity

Stage-`n` statement for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. It takes `DecidableEq V` and
the stagewise `Fintype` instance on that subgraph's edge set, and has `0 ≤ t` as its only
Prop-valued hypothesis.

Under that hypothesis the polymer free energy of the stage subgraph at activity `t` is
nonnegative.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: `polymerFreeEnergy ≥ 0` under `t ≥ 0`** (§18.5
along-ex wrap). -/
theorem polymerFreeEnergyAlongExhaustion_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t :=
  polymerFreeEnergy_Λ_nonneg_of_nonneg G (Λ.volume n) ht

end Ambient
end IsingModel
