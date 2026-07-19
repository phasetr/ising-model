import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer tanh ferromagnetic iff wrappers along an exhaustion

Narrow child module for along-exhaustion ferromagnetic tanh iff wrappers for
`polymerFreeEnergy` and `vdPolymerFamilies_sum`. This keeps callers that only
need these forwarders out of the monolithic original special-cases module.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 polymerFreeEnergy/vdSum tanh ferromagnetic iff family
along-ex wraps -/

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

/-- **Along-ex: pFE(tanh) < (1+tanh)^|E| - 1** under ε(tanh) > 0
(ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_lt_pow_sub_one_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      (1 + Real.tanh (β * J)) ^
        (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_tanh_lt_pow_sub_one_of_eps_pos_ferro
    G (Λ.volume n) hβ hJ h_eps_pos

/-- **Along-ex: pFE(tanh) < ε(tanh)** under ε(tanh) > 0 (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_of_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_of_eps_pos_ferro
    G (Λ.volume n) hβ hJ h_eps_pos

/-- **Along-ex: pFE(tanh) < ε(tanh) ↔ ε(tanh) > 0** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_lt_eps_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
              ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_lt_eps_iff_eps_pos_ferro
    G (Λ.volume n) hβ hJ

/-- **Along-ex: pFE(tanh) = 0 ↔ ε(tanh) = 0** (ferro). -/
theorem
polymerFreeEnergyAlongExhaustion_tanh_eq_zero_iff_eps_eq_zero_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
        (Real.tanh (β * J)) = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_tanh_eq_zero_iff_eps_eq_zero_ferro
    G (Λ.volume n) hβ hJ

/-- **Along-ex: 0 < pFE(tanh) ↔ 0 < ε(tanh)** (ferro). -/
theorem polymerFreeEnergyAlongExhaustion_tanh_pos_iff_eps_pos_ferro
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n))
          (Real.tanh (β * J)) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
                (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card :=
  polymerFreeEnergy_Λ_tanh_pos_iff_eps_pos_ferro G (Λ.volume n) hβ hJ

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
