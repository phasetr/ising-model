import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFreeEnergy

/-!
# §18.5 cluster-expansion convergence sandwich wrappers along an exhaustion

Narrow child module for the four §18.5 ambient alongExhaustion
`vdPolymerFamilies_sumAlongExhaustion_sandwich*` cluster-expansion
convergence sandwich wrappers (general, sharp, ferromagnetic, sharp
ferromagnetic). Each wrapper is a thin pass-through to the
corresponding `vdPolymerFamilies_sum_Λ_sandwich*` ambient lemma.
Theorem names are unchanged from the former `HighTemperature`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion: VD polymer-family sum sandwich** (§18.5
along-ex wrap of `vdPolymerFamilies_sum_sandwich`). -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich G (Λ.volume n) hβJ

/-- **Along-exhaustion: VD polymer-family sum sharp sandwich** (§18.5
along-ex wrap of `vdPolymerFamilies_sum_sandwich_sharp`). -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich_sharp
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_sharp G (Λ.volume n) hβJ

/-- **Along-exhaustion: VD polymer-family sum sandwich
(ferromagnetic)** (§18.5 ferromagnetic along-ex wrap). -/
theorem vdPolymerFamilies_sumAlongExhaustion_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_ferromagnetic G (Λ.volume n) hJ hβ

/-- **Along-exhaustion: VD polymer-family sum sharp sandwich
(ferromagnetic)** (§18.5 ferromagnetic along-ex wrap). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_sandwich_sharp_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card :=
  vdPolymerFamilies_sum_Λ_sandwich_sharp_ferromagnetic
    G (Λ.volume n) hJ hβ

/-! ## Moved: 2 strict `freeEnergyAlongExhaustion` cluster-expansion bounds

The two strict free-energy upper bound wrappers
(`freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction`,
`freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction_ferromagnetic`)
now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureVdSandwichFreeEnergy`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

end Ambient
end IsingModel
