import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.HighTempGeneralRegularity.PolymerBounds

/-!
# AmbientLattice/Analyticity polymerFreeEnergy_Λ sandwich + hasSum wrappers

Narrow child module for 10 §18.4 / §18.5 polymerFreeEnergy_Λ
high_temp_sandwich, tanh sandwich, hasSum_via_log, and
vdPolymerFamilies_sum_Λ sandwich wrappers (with ferromagnetic
variants). The theorem names are unchanged from the former
`Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`** (§18.4 Λ wrap of PR #1526). -/
theorem polymerFreeEnergy_Λ_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + t) ^ (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ) t < Real.log 2 :=
  IsingModel.polymerFreeEnergy_high_temp_sandwich (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: explicit log Taylor expansion for `polymerFreeEnergy`**
(§18.4 Λ wrap of PR #1517). -/
theorem polymerFreeEnergy_Λ_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_pow : (1 + t) ^ (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ) t) :=
  IsingModel.polymerFreeEnergy_hasSum_via_log_of_pow_lt_two
    (inducedGraph G Λ) ht h_pow

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`
(tanh form)** (§18.5 Λ wrap of the abstract tanh-form
`polymerFreeEnergy_tanh_high_temp_sandwich`). -/
theorem polymerFreeEnergy_Λ_tanh_high_temp_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_high_temp_sandwich
    (inducedGraph G Λ) hβJ h_pow

/-- **Λ-layer: explicit log Taylor expansion for `polymerFreeEnergy`
(tanh form)** (§18.5 Λ wrap of the abstract tanh-form
`polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two`). -/
theorem polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J))) :=
  IsingModel.polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two
    (inducedGraph G Λ) hβJ h_pow

/-- **Λ-layer: VD polymer-family sum sandwich** (§18.5 Λ wrap of
`vdPolymerFamilies_sum_sandwich`). -/
theorem vdPolymerFamilies_sum_Λ_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich (inducedGraph G Λ) hβJ

/-- **Λ-layer: VD polymer-family sum sharp sandwich** (§18.5 Λ wrap
of `vdPolymerFamilies_sum_sandwich_sharp`). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_sharp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_sharp
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: high-temperature sandwich for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic Λ wrap). -/
theorem polymerFreeEnergy_Λ_tanh_high_temp_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    0 ≤ IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) ≤
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ∧
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ)).erase ∅,
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ≤
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 ∧
    (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card - 1 < 1 ∧
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) < Real.log 2 :=
  IsingModel.polymerFreeEnergy_tanh_high_temp_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ h_pow

/-- **Λ-layer: log Taylor expansion for `polymerFreeEnergy`
(ferromagnetic tanh form)** (§18.5 ferromagnetic Λ wrap). -/
theorem
polymerFreeEnergy_Λ_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β)
    (h_pow : (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card < 2) :
    HasSum (fun n : ℕ =>
        (-1 : ℝ) ^ n *
          (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ^ (n + 1) /
          (n + 1))
      (IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J))) :=
  IsingModel.polymerFreeEnergy_tanh_hasSum_via_log_of_pow_lt_two_ferromagnetic
    (inducedGraph G Λ) hJ hβ h_pow

/-- **Λ-layer: VD polymer-family sum sandwich (ferromagnetic)**
(§18.5 ferromagnetic Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_ferromagnetic
    (inducedGraph G Λ) hJ hβ

/-- **Λ-layer: VD polymer-family sum sharp sandwich
(ferromagnetic)** (§18.5 ferromagnetic Λ wrap). -/
theorem vdPolymerFamilies_sum_Λ_sandwich_sharp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^
        (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_sandwich_sharp_ferromagnetic
    (inducedGraph G Λ) hJ hβ


end Ambient

end IsingModel
