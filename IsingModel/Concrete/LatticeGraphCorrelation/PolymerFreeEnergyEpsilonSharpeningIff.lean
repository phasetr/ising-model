import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# ℤ^d Λ polymerFreeEnergy against the remainder ε(t) (§18.5)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d`, for `0 ≤ t`, the
equivalences that pin the polymer free energy to the cluster-expansion remainder `ε(t)`, the
activity sum over the nonempty members of `vdCompatiblePolymerFamilies`: the free energy
vanishes exactly when the remainder does, is positive exactly when the remainder is, and
falls strictly below the remainder exactly then too. These sharpen the GJ §18.5 polymer
free-energy bounds on ℤ^d.
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
