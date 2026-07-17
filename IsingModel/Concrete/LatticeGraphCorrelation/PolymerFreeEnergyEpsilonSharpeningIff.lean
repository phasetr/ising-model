import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# ℤ^d Λ-layer polymerFreeEnergy ε iff wrappers

Narrow child module for three Λ-layer
`polymerFreeEnergy_Λ_latticeGraph_*_eps_*` iff wrappers extracted
from `PolymerFreeEnergyEpsilonSharpening.lean`:

* `polymerFreeEnergy_Λ_latticeGraph_eq_zero_iff_eps_eq_zero`,
* `polymerFreeEnergy_Λ_latticeGraph_pos_iff_eps_pos`,
* `polymerFreeEnergy_Λ_latticeGraph_lt_eps_iff_eps_pos`.

Each result is a thin pass-through of the ambient
`Ambient.polymerFreeEnergy_Λ_*_iff_eps_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyEpsilonSharpening` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

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

end Ambient
end IsingModel
