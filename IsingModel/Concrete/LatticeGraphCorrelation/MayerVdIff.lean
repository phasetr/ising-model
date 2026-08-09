import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaPolymer
import IsingModel.AmbientLattice.AnalyticityLambdaBasicIdentities

/-!
# ℤ^d threshold characterisations of the polymer activity sum at `1`

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the
characterisations of when the activity sum over the vertex-disjoint compatible polymer
families of the induced subgraph sits at `1` and of when it exceeds `1`: it equals `1` exactly
when the sum over the families other than the empty one vanishes, it exceeds `1` exactly when
that sum is strictly positive, and at the activity `tanh (β * J)` these unfold to the activity
being `0`, respectively strictly positive, together with the induced subgraph having no
polymer, respectively at least one. The comparison against the nonempty-family sum at equality
holds at an arbitrary activity; its strict counterpart assumes `0 ≤ t`, and the `tanh`
statements assume `0 ≤ β * J`.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d Λ: vdSum = 1 ↔ ε = 0**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_eq_one_iff_eps_eq_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (t : ℝ) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, t ^ P.card) = 1 ↔
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sum_Λ_eq_one_iff_eps_zero
    (IsingModel.latticeGraph d) Λ t

/-- **ℤ^d Λ: vdSum > 1 ↔ ε > 0**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_gt_one_iff_eps_pos
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, t ^ P.card) ↔
      0 < ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
            ∏ P ∈ Γ, t ^ P.card :=
  Ambient.vdPolymerFamilies_sum_Λ_gt_one_iff_eps_pos
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: vdSum_tanh > 1 ↔ 0 < tanh ∧ allPolymers ≠ ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_gt_one_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    1 < (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) ↔
      0 < Real.tanh (β * J) ∧
        (IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ)).Nonempty :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_gt_one_iff
    (IsingModel.latticeGraph d) Λ hβJ

/-- **ℤ^d Λ: vdSum_tanh = 1 ↔ tanh = 0 ∨ allPolymers = ∅**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_eq_one_iff
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
        ∏ P ∈ Γ, (Real.tanh (β * J)) ^ P.card) = 1 ↔
      Real.tanh (β * J) = 0 ∨
        IsingModel.allPolymers
          (inducedGraph (IsingModel.latticeGraph d) Λ) = ∅ :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_eq_one_iff
    (IsingModel.latticeGraph d) Λ hβJ

end Ambient
end IsingModel
