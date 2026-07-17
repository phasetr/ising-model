import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.MayerPartialFerro

/-!
# AmbientLattice/Analyticity polymerFreeEnergy/vdSum tanh ferromagnetic iff wrappers

Narrow child module for 9 §18.5 Λ-layer wrappers covering the
`polymerFreeEnergy_Λ_tanh_*_ferro` and
`vdPolymerFamilies_sum_Λ_tanh_*_ferro` ferromagnetic iff family
under `0 ≤ β`, `0 ≤ J` (`_lt_eps_iff_eps_pos`,
`_eq_zero_iff_eps_eq_zero`, `_pos_iff_eps_pos`, `_pos_iff`,
`_eq_zero_iff`, `_gt_one_iff`, `_eq_one_iff`,
`_lt_pow_sub_one_of_eps_pos`, `_lt_eps_of_eps_pos`). The theorem
names are unchanged from the former `Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
Λ-layer wraps (under `0 ≤ β, 0 ≤ J`) -/

/-- **Λ-layer: pFE(tanh) < ε(tanh) ↔ ε(tanh) > 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ ε(tanh) = 0** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_eps_eq_zero_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < ε(tanh)** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 0 < pFE(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_pos_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G Λ)
          (Real.tanh (β * J)) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.polymerFreeEnergy_tanh_pos_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) = 0 ↔ tanh = 0 ∨ allPolymers = ∅** (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_eq_zero_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) = 0 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.polymerFreeEnergy_tanh_eq_zero_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: 1 < vdSum(tanh) ↔ 0 < tanh ∧ allPolymers ≠ ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ),
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: vdSum(tanh) = 1 ↔ tanh = 0 ∨ allPolymers = ∅**
(ferro). -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff_ferromagnetic
    (inducedGraph G Λ) hβ hJ

/-- **Λ-layer: pFE(tanh) < (1 + tanh)^|E| - 1** under ε(tanh) > 0
(ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card - 1 :=
  IsingModel.polymerFreeEnergy_tanh_lt_pow_sub_one_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos

/-- **Λ-layer: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (ferro). -/
theorem polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G Λ)
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  IsingModel.polymerFreeEnergy_tanh_lt_eps_of_eps_pos_ferromagnetic
    (inducedGraph G Λ) hβ hJ h_eps_pos


end Ambient

end IsingModel
