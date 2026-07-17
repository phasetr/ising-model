import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# ℤ^d Λ vdPolymerFamilies_sum generic-t bound wrappers

Narrow child module for four ℤ^d Λ
`vdPolymerFamilies_sum_Λ_latticeGraph_*` generic-`t` bound wrappers
extracted from `MayerVdBounds.lean`:

* `vdPolymerFamilies_sum_Λ_latticeGraph_ge_one_of_nonneg`,
* `vdPolymerFamilies_sum_Λ_latticeGraph_le_one_plus_pow_of_nonneg`,
* `vdPolymerFamilies_sum_Λ_latticeGraph_pos_of_nonneg`,
* `vdPolymerFamilies_sum_Λ_latticeGraph_eq_one_add`.
-/

namespace IsingModel
namespace Ambient

/-! ### §18.5 vdPolymerFamilies_sum generic-t bounds ℤ^d wraps -/

/-- **ℤ^d Λ: 1 ≤ vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_ge_one_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_ge_one_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum ≤ (1+t)^|E|** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_le_one_plus_pow_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card)
      ≤ (1 + t) ^
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_le_one_plus_pow_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: 0 < vdSum** under `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_pos_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    0 < ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_pos_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum = 1 + ε(t)** decomposition. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_eq_one_add
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) =
      1 + ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
              ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_eq_one_add
    (IsingModel.latticeGraph d) Λ t

end Ambient
end IsingModel
