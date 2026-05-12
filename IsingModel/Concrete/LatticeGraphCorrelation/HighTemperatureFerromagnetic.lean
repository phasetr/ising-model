import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.HighTemperature

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

/-- **ℤ^d along-exhaustion: high-temperature sandwich for
`polymerFreeEnergy` (ferromagnetic tanh form)** (§18.5 ferromagnetic
ℤ^d along-ex wrap). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_high_temp_sandwich_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J)) < Real.log 2 :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_high_temp_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ n h_pow

/-- **ℤ^d along-exhaustion: log Taylor expansion for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic ℤ^d along-ex wrap). -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_hasSum_via_log_of_pow_lt_two_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card < 2) :
    HasSum (fun k : ℕ =>
        (-1 : ℝ) ^ k *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (k + 1) /
          (k + 1))
      (IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J))) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ n h_pow

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

/-- **ℤ^d along-exhaustion: VD polymer-family sum sandwich
(ferromagnetic)** (§18.5 ferromagnetic ℤ^d along-ex wrap). -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph (IsingModel.latticeGraph d)
        (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_sandwich_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d along-exhaustion: VD polymer-family sum sharp sandwich
(ferromagnetic)** (§18.5 ferromagnetic ℤ^d along-ex wrap). -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_sandwich_sharp_ferro
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_sandwich_sharp_ferromagnetic
    (IsingModel.latticeGraph d) Λ hJ hβ n

end Ambient
end IsingModel
