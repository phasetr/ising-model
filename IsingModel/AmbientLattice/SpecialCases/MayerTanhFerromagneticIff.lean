import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIffPFE

/-!
# Mayer tanh ferromagnetic iff wrappers along an exhaustion

Narrow child module for along-exhaustion ferromagnetic tanh iff wrappers for
`polymerFreeEnergy` and `vdPolymerFamilies_sum`. This keeps callers that only
need these forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
along-ex wraps -/

/-! ## Moved: polymerFreeEnergy tanh-ferro iff wrappers

The seven `polymerFreeEnergyAlongExhaustion_tanh_*_ferro` wrappers
now live in
`IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIffPFE`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-- **Along-ex: 1 < vdSum(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**
(ferro). -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_gt_one_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph G (Λ.volume n))).Nonempty :=
  vdPolymerFamilies_sum_Λ_tanh_gt_one_iff_ferro G (Λ.volume n) hβ hJ

/-- **Along-ex: vdSum(tanh) = 1 ↔ tanh = 0 ∨ allPolymers = ∅**
(ferro). -/
theorem vdPolymerFamilies_sumAlongExhaustion_tanh_eq_one_iff_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n)),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G (Λ.volume n)) = ∅ :=
  vdPolymerFamilies_sum_Λ_tanh_eq_one_iff_ferro G (Λ.volume n) hβ hJ

end Ambient
end IsingModel
