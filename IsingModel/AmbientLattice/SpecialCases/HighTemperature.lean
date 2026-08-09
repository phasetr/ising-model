import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFE
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureTanh

/-!
# The cluster-expansion convergence regime `(1 + t) ^ |E| < 2`, along an exhaustion

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set.

Each statement assumes an activity `t` with `0 ≤ t` and the convergence condition
`(1 + t) ^ |E| < 2`, where `|E|` is the edge count of the stage subgraph. Write `ε(t)` for
the sum of `∏ P ∈ Γ, t ^ P.card` over that subgraph's vertex-disjoint compatible polymer
families other than the empty family, and `F(t)` for `IsingModel.polymerFreeEnergy` of that
subgraph at `t`.

In that regime `0 ≤ F(t) ≤ ε(t) ≤ (1 + t) ^ |E| - 1 < 1`, together with `F(t) < Real.log 2`;
and the alternating series `(-1) ^ k * ε(t) ^ (k + 1) / (k + 1)` sums to `F(t)`.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion: high-temperature sandwich for
`polymerFreeEnergy`** (§18.5 along-ex wrap of #1526). -/
theorem polymerFreeEnergyAlongExhaustion_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_pow : (1 + t) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 ∧
    (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t < Real.log 2 :=
  polymerFreeEnergy_Λ_high_temp_sandwich G (Λ.volume n) ht h_pow

/-- **Along-exhaustion: log Taylor expansion for `polymerFreeEnergy`**
(§18.5 along-ex wrap of #1517). -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_pow : (1 + t) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log_of_pow_lt_two
    G (Λ.volume n) ht h_pow

end Ambient
end IsingModel
