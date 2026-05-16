import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Mayer ferromagnetic tanh iff wrappers for `polymerFreeEnergy` (iff family)

Narrow child module for the five §18.5 along-exhaustion
ferromagnetic tanh iff wrappers for `polymerFreeEnergy`. Each
wrapper is a thin pass-through to the corresponding
`polymerFreeEnergy_Λ_tanh_*_iff_*_ferro` ambient lemma. Theorem
names are unchanged from the former `MayerTanhFerromagneticIffPFE`
declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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
