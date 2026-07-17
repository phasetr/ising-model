import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.AnalyticityLambdaTanhFerroIff

/-!
# Mayer ferromagnetic tanh iff wrappers for `pFE` (allPolymers form)

Narrow child module for the two §18.5 along-exhaustion ferromagnetic
tanh `polymerFreeEnergy_*_ferro` iff wrappers in the `allPolymers`
form extracted from `MayerTanhFerromagneticIffPFEIff.lean`:

* `polymerFreeEnergyAlongExhaustion_tanh_pos_iff_ferro`
* `polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_ferro`

Each wrapper is a thin pass-through to the corresponding
`polymerFreeEnergy_Λ_tanh_*_iff_ferro` ambient lemma stating that
the ferromagnetic positivity / vanishing of `pFE(tanh)` is
characterized by the joint behaviour of `tanh(βJ)` and
`allPolymers`. Theorem names are unchanged from the former
`MayerTanhFerromagneticIffPFE` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: 0 < pFE(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  polymerFreeEnergy_Λ_tanh_pos_iff_ferro G (Λ.volume n) hβ hJ

/-- **Along-ex: pFE(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro G (Λ.volume n) hβ hJ

end Ambient
end IsingModel
