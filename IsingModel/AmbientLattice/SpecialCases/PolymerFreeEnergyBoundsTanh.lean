import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBoundsTanhLogTwo

/-!
# Ambient polymerFreeEnergyAlongExhaustion tanh-form bound wrappers

Bounds the along-exhaustion polymer free energy in the `tanh` parametrization (GJ §18.5),
which is the form in which the high-temperature convergence criterion is checked. Each
result passes through the corresponding Λ-level `polymerFreeEnergy_Λ_*` lemma.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: `polymerFreeEnergy` tanh-form sandwich** (§18.5
along-ex wrap of Step 632). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log (1 + Real.tanh (β * J)) :=
  polymerFreeEnergy_Λ_tanh_sandwich G (Λ.volume n) hβJ

/-- **Along-ex: `polymerFreeEnergy_tanh` double bound** (§18.5
along-ex wrap of Step 645). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_double_bound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.log 2 :=
  polymerFreeEnergy_Λ_tanh_double_bound G (Λ.volume n) hβJ

end Ambient
end IsingModel
