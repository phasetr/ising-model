import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpening

/-!
# Concrete polymer free-energy epsilon sharpening wrappers

Narrow child module for concrete `Z^d` wrappers around the ambient
`epsilon(t)` nonnegativity and non-tanh polymer free-energy sharpening API.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-! ### §18.5 epsilon(t) nonneg + non-tanh polymerFreeEnergy sharpening
Z^d wraps -/

/-- **Z^d Λ: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **Z^d Λ: ε(0)^n = 0** for `n ≥ 1`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_pow_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ n = 0 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_pow_at_zero
    (IsingModel.latticeGraph d) Λ hn

/-- **Z^d Λ: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_eq_zero_iff_eps_eq_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  Ambient.polymerFreeEnergy_Λ_eq_zero_iff_eps_eq_zero
    (IsingModel.latticeGraph d) Λ ht

/-- **Z^d Λ: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_pos_iff_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d) Λ) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_pos_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht

/-- **Z^d Λ: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergy_Λ_latticeGraph_lt_eps_iff_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.polymerFreeEnergy_Λ_lt_eps_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht

/-- **Z^d Λ: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t`, ε(t) > 0. -/
theorem polymerFreeEnergy_Λ_latticeGraph_lt_pow_sub_one_of_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ) t <
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.polymerFreeEnergy_Λ_lt_pow_sub_one_of_eps_pos
    (IsingModel.latticeGraph d) Λ ht h_eps_pos

/-- **Z^d along-ex: 0 ≤ ε(t)** for `0 ≤ t`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_nonneg_of_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_nonneg_of_nonneg
    (IsingModel.latticeGraph d) Λ ht n

/-- **Z^d along-ex: ε(0)^k = 0** for `k ≥ 1`. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_minus_one_pow_at_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, (0 : ℝ) ^ P.card) ^ k = 0 :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_minus_one_pow_at_zero
    (IsingModel.latticeGraph d) Λ hk n

/-- **Z^d along-ex: pFE(t) = 0 ↔ ε(t) = 0** under `0 ≤ t`. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_eq_zero_iff_eps_eq_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t = 0 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) = 0 :=
  Ambient.polymerFreeEnergyAlongExhaustion_eq_zero_iff_eps_eq_zero
    (IsingModel.latticeGraph d) Λ ht n

/-- **Z^d along-ex: 0 < pFE(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_pos_iff_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 < IsingModel.polymerFreeEnergy
          (inducedGraph (IsingModel.latticeGraph d)
            (Λ.volume n)) t ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_pos_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht n

/-- **Z^d along-ex: pFE(t) < ε(t) ↔ 0 < ε(t)** under `0 ≤ t`. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_lt_eps_iff_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t <
        ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.polymerFreeEnergyAlongExhaustion_lt_eps_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht n

/-- **Z^d along-ex: pFE(t) < (1+t)^|E| - 1** under `0 ≤ t`,
ε(t) > 0. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_lt_pow_sub_one_of_eps_pos
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ)
    (h_eps_pos : 0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d)
                (Λ.volume n))).erase ∅,
            ∏ P ∈ Γ, t ^ P.card) :
    IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) t <
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card - 1 :=
  Ambient.polymerFreeEnergyAlongExhaustion_lt_pow_sub_one_of_eps_pos
    (IsingModel.latticeGraph d) Λ ht n h_eps_pos

end Ambient
end IsingModel
