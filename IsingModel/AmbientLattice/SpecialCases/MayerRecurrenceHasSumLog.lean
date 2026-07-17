import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# Polymer free-energy log-series `HasSum` wrappers along an exhaustion

Narrow child module for the two §18.5 along-exhaustion
`polymerFreeEnergy_hasSum_via_log_*` log-series `HasSum` wrappers
extracted from `MayerRecurrenceHasSum.lean`:

* `polymerFreeEnergyAlongExhaustion_hasSum_via_log`
* `polymerFreeEnergyAlongExhaustion_hasSum_via_log_eventually`

Each wrapper is a thin pass-through to the corresponding ambient
`polymerFreeEnergy_Λ_hasSum_via_log*` lemma expressing `pFE` as the
sum of the standard `log(1 + ε(t))` Taylor series in `ε(t)`.
Theorem names are unchanged from the former `MayerRecurrence`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: polymerFreeEnergy hasSum via log under `|ε(t)| < 1`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) {t : ℝ}
    (h_abs : |∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                        (inducedGraph G (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card| < 1) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                    (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log G (Λ.volume n) h_abs

/-- **Along-ex: polymerFreeEnergy hasSum eventually as `t → 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasSum_via_log_eventually
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0,
      HasSum (fun k : ℕ =>
          (-1 : ℝ) ^ k *
            (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                      (inducedGraph G (Λ.volume n))).erase ∅,
                ∏ P ∈ Γ, t ^ P.card) ^ (k + 1) /
            (k + 1))
        (IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t) :=
  polymerFreeEnergy_Λ_hasSum_via_log_eventually G (Λ.volume n)

end Ambient
end IsingModel
