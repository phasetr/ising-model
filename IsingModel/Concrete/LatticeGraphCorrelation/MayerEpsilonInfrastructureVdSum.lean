import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# ℤ^d nonempty-family activity sum near zero activity, on a fixed volume

Instantiates at `IsingModel.latticeGraph d`, on a fixed finite volume `Λ`, the behaviour near
activity `0` of the activity sum `∑_Γ ∏_{P ∈ Γ} t ^ |P|` taken over the vertex-disjoint
compatible polymer families of the induced subgraph other than the empty one: it vanishes at
activity `0`, it is `Continuous` in the activity, and it is eventually strictly below `1` as
the activity tends to `0`. No condition on the activity is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: ε(0) = 0**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_at_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_at_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_continuous
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_continuous
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d Λ: ε(t) < 1 eventually as t → 0**. -/
theorem
vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_lt_one_eventually
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    ∀ᶠ t : ℝ in nhds 0,
      (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph (IsingModel.latticeGraph d) Λ)).erase ∅,
          ∏ P ∈ Γ, t ^ P.card) < 1 :=
  Ambient.vdPolymerFamilies_sum_Λ_minus_one_lt_one_eventually
    (IsingModel.latticeGraph d) Λ

end Ambient
end IsingModel
