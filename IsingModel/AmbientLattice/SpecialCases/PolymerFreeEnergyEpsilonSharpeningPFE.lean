import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFELtPow

/-!
# Vanishing and positivity of the polymer free energy, read off the reduced sum

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and has
`0 ≤ t` as its only Prop-valued hypothesis.

Write `ε(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint compatible polymer
families `Γ` of the stage subgraph with the empty family erased from the index set.

For an activity `t` in the admissible range `0 ≤ t`, the polymer free energy of the stage
subgraph is `0` if and only if `ε(t)` is `0`; it is positive if and only if `ε(t)` is
positive; and it is strictly below `ε(t)` if and only if `ε(t)` is positive.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero G (Λ.volume n) ht

/-- **Along-ex: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_pos_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_lt_eps_iff_eps_pos G (Λ.volume n) ht

end Ambient
end IsingModel
