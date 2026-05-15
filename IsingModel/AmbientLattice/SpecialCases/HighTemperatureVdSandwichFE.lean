import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# §18.5 cluster-expansion convergence sandwich wrappers along an exhaustion

Narrow child module for the six §18.5 ambient alongExhaustion
cluster-expansion convergence sandwich wrappers: four
`vdPolymerFamilies_sumAlongExhaustion_sandwich*` variants (general,
sharp, ferromagnetic, sharp ferromagnetic) and the two strict
`freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction*`
bounds (general and ferromagnetic). Each wrapper is a thin
pass-through to the corresponding `vdPolymerFamilies_sum_Λ_sandwich*`
or `freeEnergyΛ_lt_log_two_plus_high_temp_correction*` ambient
lemma. Theorem names are unchanged from the former
`HighTemperature` declarations.
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

/-- **Along-exhaustion: strict `freeEnergyAlongExhaustion` upper
bound in cluster-expansion convergence regime** (§18.5 along-ex
wrap of #1527). -/
theorem
freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) (hne : 0 < (Λ.volume n).card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n <
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / (Λ.volume n).card := by
  unfold freeEnergyAlongExhaustion
  exact freeEnergyΛ_lt_log_two_plus_high_temp_correction
    G (Λ.volume n) J β hβJ hne h_pow

/-- **Along-exhaustion: strict `freeEnergyAlongExhaustion` upper
bound in cluster-expansion convergence regime (ferromagnetic)**
(§18.5 along-ex wrap, ferro). -/
theorem
freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (hne : 0 < (Λ.volume n).card)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card < 2) :
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n <
      Real.log 2 +
        ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) /
          (Λ.volume n).card *
          Real.log (Real.cosh (β * J)) +
        Real.log 2 / (Λ.volume n).card :=
  freeEnergyAlongExhaustion_lt_log_two_plus_high_temp_correction
    G Λ J β (mul_nonneg hβ.le hJ) n hne h_pow

end Ambient
end IsingModel
