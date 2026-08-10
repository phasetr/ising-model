import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFE

/-!
# Sign and zero-activity value of the reduced polymer-family sum

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Write `ε(t)` for the sum of `∏ P ∈ Γ, t ^ P.card` over the vertex-disjoint compatible polymer
families `Γ` of the stage subgraph with the empty family erased from the index set.

Under `0 ≤ t` as the only Prop-valued hypothesis, `ε(t)` is nonnegative. At the activity `0`
the power `ε(0) ^ k` is `0` for every exponent `k` admitted by the only Prop-valued hypothesis
`1 ≤ k`; the restriction is sharp, since `ε(0) ^ 0` is `1`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: ε(0)^k = 0** for `k ≥ 1`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pow_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ k = 0 :=
  vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero G (Λ.volume n) hk

end Ambient
end IsingModel
