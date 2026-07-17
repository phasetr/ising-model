import IsingModel.AmbientLattice.Defs.Core
import IsingModel.ClusterExpansion.StrictPositivity.IffCharacterisations

/-!
# AmbientLattice/Analyticity basic identities + bounds + iff wrappers

Narrow child module for 17 §18.5 Λ-layer wrappers covering basic
`at_zero` / `at_one` identities for `vdPolymerFamilies_sum`,
`mayerPartialSum`, and `mayerExpansionTerm`; tanh iff characterizations
for `vdPolymerFamilies_sum_Λ` (`tanh_gt_one_iff`, `tanh_eq_one_iff`);
the bound family
(`le_two_pow`, `le_one_plus_tanh_pow`, `one_le_vdPolymerFamilies_sum_Λ`);
and generic-`t` bounds + `_eq_one_add` decomposition
(`ge_one_of_nonneg`, `le_one_plus_pow_of_nonneg`, `pos_of_nonneg`,
`eq_one_add`). The theorem names are unchanged from the former
`Analyticity` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 basic identities at_zero / at_one Λ wraps -/

/-- **Λ-layer: vdPolymerFamilies_sum at t = 0 = 1**. -/
theorem vdPolymerFamilies_sum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 1 :=
  IsingModel.vdPolymerFamilies_sum_at_zero (inducedGraph G Λ)

/-- **Λ-layer: vdPolymerFamilies_sum at t = 1 = #vdCompatPoly families**. -/
theorem vdPolymerFamilies_sum_Λ_at_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, (1 : ℝ) ^ P.card) =
      (IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ)).card :=
  IsingModel.vdPolymerFamilies_sum_at_one (inducedGraph G Λ)

/-- **Λ-layer: mayerPartialSum at N = 0 = 0**. -/
theorem mayerPartialSum_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerPartialSum_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at N = 1 = ∑_P t^|P|**. -/
theorem mayerPartialSum_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerPartialSum_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerPartialSum at t = 0 = 0**. -/
theorem mayerPartialSum_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    IsingModel.mayerPartialSum (inducedGraph G Λ) N 0 = 0 :=
  IsingModel.mayerPartialSum_at_zero (inducedGraph G Λ) N

/-- **Λ-layer: mayerExpansionTerm at n = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 0 t = 0 :=
  IsingModel.mayerExpansionTerm_zero (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at n = 1 = ∑_P t^|P|**. -/
theorem mayerExpansionTerm_Λ_one
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) 1 t =
      ∑ P ∈ IsingModel.allPolymers (inducedGraph G Λ), t ^ P.card :=
  IsingModel.mayerExpansionTerm_one (inducedGraph G Λ) t

/-- **Λ-layer: mayerExpansionTerm at t = 0 = 0**. -/
theorem mayerExpansionTerm_Λ_at_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : ℕ) :
    IsingModel.mayerExpansionTerm (inducedGraph G Λ) n 0 = 0 :=
  IsingModel.mayerExpansionTerm_at_zero (inducedGraph G Λ) n

/-! ### §18.5 vdPolymerFamilies_sum tanh iff characterizations Λ wraps -/

/-- **Λ-layer: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_gt_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph G Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers (inducedGraph G Λ)).Nonempty :=
  IsingModel.vdPolymerFamilies_sum_tanh_gt_one_iff
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_tanh_eq_one_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
        (inducedGraph G Λ),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers (inducedGraph G Λ) = ∅ :=
  IsingModel.vdPolymerFamilies_sum_tanh_eq_one_iff
    (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum bound family Λ-layer wraps -/

/-- **Λ-layer: vdSum_tanh ≤ 2^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_two_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (2 : ℝ) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_two_pow (inducedGraph G Λ) hβJ

/-- **Λ-layer: vdSum_tanh ≤ (1+tanh)^|E|** under `0 ≤ β·J`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_tanh_pow
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card)
      ≤ (1 + Real.tanh (β * J)) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_tanh_pow
    (inducedGraph G Λ) hβJ

/-- **Λ-layer: 1 ≤ vdSum_tanh** under `0 ≤ β·J`. -/
theorem one_le_vdPolymerFamilies_sum_Λ
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
        ∏ P ∈ Γ, Real.tanh (β * J) ^ P.card :=
  IsingModel.one_le_vdPolymerFamilies_sum (inducedGraph G Λ) hβJ

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds Λ-layer -/

/-- **Λ-layer: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_ge_one_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_ge_one_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^ (inducedGraph G Λ).edgeFinset.card :=
  IsingModel.vdPolymerFamilies_sum_le_one_plus_pow_of_nonneg
    (inducedGraph G Λ) ht

/-- **Λ-layer: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_pos_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_pos_of_nonneg (inducedGraph G Λ) ht

/-- **Λ-layer: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sum_Λ_eq_one_add
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies (inducedGraph G Λ),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  IsingModel.vdPolymerFamilies_sum_eq_one_add (inducedGraph G Λ) t


end Ambient

end IsingModel
