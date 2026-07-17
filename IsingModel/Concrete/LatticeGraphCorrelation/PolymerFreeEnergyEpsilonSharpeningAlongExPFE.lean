import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpeningPFE

/-!
# Concrete along-ex polymerFreeEnergyAlongExhaustion ε(t) sharpening wrappers

Narrow child module for 4 ℤ^d along-exhaustion
`polymerFreeEnergyAlongExhaustion_latticeGraph_*` ε(t)-sharpening
wrappers extracted from `PolymerFreeEnergyEpsilonSharpeningAlongEx.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_eq_zero_iff_eps_eq_zero`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_pos_iff_eps_pos`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_lt_eps_iff_eps_pos`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_lt_pow_sub_one_of_eps_pos`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.polymerFreeEnergyAlongExhaustion_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyEpsilonSharpeningAlongEx` declarations.
-/

namespace IsingModel
namespace Ambient


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
