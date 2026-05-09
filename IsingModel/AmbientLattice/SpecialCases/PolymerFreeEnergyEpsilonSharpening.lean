import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion

/-!
# Polymer free-energy epsilon sharpening wrappers along an exhaustion

Narrow child module for along-exhaustion `epsilon(t)` nonnegativity and
non-tanh polymer free-energy sharpening wrappers. This keeps callers that only
need these forwarders out of the monolithic legacy special-cases module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### §18.5 epsilon(t) nonneg + non-tanh polymerFreeEnergy sharpening
along-ex wraps -/

/-- **Along-ex: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_nonneg_of_nonneg
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg G (Λ.volume n) ht

/-- **Along-ex: ε(0)^k = 0** for `k ≥ 1`. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_pow_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ k = 0 :=
  vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero G (Λ.volume n) hk

/-- **Along-ex: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero G (Λ.volume n) ht

/-- **Along-ex: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_pos_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  polymerFreeEnergy_Λ_lt_eps_iff_eps_pos G (Λ.volume n) ht

/-- **Along-ex: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t` and ε(t) > 0. -/
theorem polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy (inducedGraph G (Λ.volume n)) t <
      (1 + t) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card - 1 :=
  polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    G (Λ.volume n) ht h_eps_pos

end Ambient
end IsingModel
