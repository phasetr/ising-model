import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaSandwich

/-!
# Concrete ferromagnetic cluster-expansion wrappers

Narrow child module for eight ℤ^d ferromagnetic cluster-expansion
wrappers: ferromagnetic `polymerFreeEnergy_{Λ,AlongExhaustion}_tanh_*`
sandwich and `hasSum` via log Taylor, plus ferromagnetic
`vdPolymerFamilies_sum_{Λ,sumAlongExhaustion}_*_sandwich(_sharp)`. Each
wrapper is a thin pass-through to the corresponding ambient
ferromagnetic lemma at `IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: high-temperature sandwich for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic ℤ^d Λ wrap). -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_high_temp_sandwich_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  Ambient.polymerFreeEnergy_Λ_tanh_high_temp_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ h_pow

/-- **ℤ^d Λ: log Taylor expansion for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic ℤ^d Λ wrap). -/
theorem
polymerFreeEnergy_Λ_latticeGraph_tanh_hasSum_via_log_of_pow_lt_two_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J))) :=
  Ambient.polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ h_pow

/-! ## Moved: along-ex polymerFreeEnergy ferromagnetic wrappers

The two along-ex `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*_ferro`
wrappers (`_high_temp_sandwich`, `_hasSum_via_log_of_pow_lt_two`) now
live in `HighTemperatureFerromagneticAlongEx.lean`. -/


/-- **ℤ^d Λ: VD polymer-family sum sandwich (ferromagnetic)**
(§18.5 ferromagnetic ℤ^d Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_sandwich_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-- **ℤ^d Λ: VD polymer-family sum sharp sandwich (ferromagnetic)**
(§18.5 ferromagnetic ℤ^d Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_sandwich_sharp_ferro
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_sandwich_sharp_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ

/-! ## Moved: along-ex vdPolymerFamilies sum ferromagnetic wrappers

The two along-ex `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich_*_ferro`
wrappers (`_sandwich`, `_sandwich_sharp`) now live in
`HighTemperatureFerromagneticAlongEx.lean`. -/


end Ambient
end IsingModel
