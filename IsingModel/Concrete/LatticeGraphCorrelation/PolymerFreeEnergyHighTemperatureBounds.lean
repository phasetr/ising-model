import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPfeSharpening

/-!
# ℤ^d Λ `vdPolymerFamilies_sum` high-temperature bounds (§18.5)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d` the high-temperature control
of the vertex-disjoint compatible polymer-family sum: its sandwich between `1` and
`(1 + t) ^ |E|` for `0 ≤ t`, its monotonicity on `Set.Ici 0`, and the matching ceiling
`(1 + t) ^ |E| − 1` on the remainder `ε(t)` left after dropping the empty family. This is the
convergence input for the ℤ^d GJ §18.5 cluster expansion.
-/

namespace IsingModel
namespace Ambient

/-! ## §18.5 vdPolymerFamilies_sum high-temperature bounds ℤ^d wraps -/

/-- **ℤ^d Λ: vdSum sandwich for `t ≥ 0`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_sandwich_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) ∧
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card :=
  Ambient.vdPolymerFamilies_sum_Λ_sandwich_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum is `MonotoneOn (Set.Ici 0)`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_monotoneOn_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    MonotoneOn
      (fun t : ℝ => ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) (Set.Ici 0) :=
  Ambient.vdPolymerFamilies_sum_Λ_monotoneOn_Ici_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: ε(t) ≤ (1+t)^|E| - 1** for `0 ≤ t`. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_le_of_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) ≤
      (1 + t) ^
        (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card -
        1 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_le_of_nonneg
    (IsingModel.latticeGraph d) Λ ht

end Ambient
end IsingModel
