import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerro

/-!
# Polymer free-energy tanh-bound wrappers along an exhaustion

Narrow child module for along-exhaustion `polymerFreeEnergy` general
tanh bound, the `log(1 + eps)` decomposition, and the `HasDerivAt`
wrapper. This keeps callers that only need these forwarders out of the
monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy tanh-bound + ferro + hasDerivAt +
eq_log_one_add along-ex wraps -/

/-- **Along-ex: polymerFreeEnergy tanh ≤ |E| · tanh** under
`0 ≤ β·J`. -/
theorem polymerFreeEnergyAlongExhaustion_tanh_le_card_mul
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) ≤
      (inducedGraph G (Λ.volume n)).edgeFinset.card *
        Real.tanh (β * J) :=
  polymerFreeEnergy_Λ_tanh_le_card_mul G (Λ.volume n) hβJ

/-! ## Moved: 3 ferromagnetic tanh bound wrappers

The three §18.5 ferromagnetic bound wrappers
(`polymerFreeEnergyAlongExhaustion_tanh_le_card_mul_ferro`,
`polymerFreeEnergyAlongExhaustion_tanh_sandwich_ferro`,
`polymerFreeEnergyAlongExhaustion_tanh_le_card_log_two_ferro`) now
live in
`IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBoundsFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex: polymerFreeEnergy = log(1 + ε(t))** decomposition. -/
theorem polymerFreeEnergyAlongExhaustion_eq_log_one_add_eps
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (t : ℝ) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t =
      Real.log (1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, t ^ P.card) :=
  polymerFreeEnergy_Λ_eq_log_one_add_eps G (Λ.volume n) t

/-- **Along-ex: polymerFreeEnergy hasDerivAt at `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_hasDerivAt
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    HasDerivAt (fun s : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph G (Λ.volume n)) s)
      ((∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∑ Q ∈ Γ, (∏ P ∈ Γ.erase Q, t ^ P.card) *
            ((Q.card : ℝ) * t ^ (Q.card - 1))) /
        (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, t ^ P.card)) t :=
  polymerFreeEnergy_Λ_hasDerivAt G (Λ.volume n) ht

end Ambient
end IsingModel
