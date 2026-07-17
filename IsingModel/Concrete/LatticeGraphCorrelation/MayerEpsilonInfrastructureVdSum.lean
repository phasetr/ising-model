import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMayerRecurrenceEpsilon

/-!
# Concrete Λ-direct vdPolymerFamilies_sum_Λ ε(t) wrappers

Narrow child module for 3 ℤ^d Λ-direct
`vdPolymerFamilies_sum_Λ_*_minus_one_*` ε(t) wrappers extracted from
`MayerEpsilonInfrastructure.lean`:

* `vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_at_zero`,
* `vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_continuous`,
* `vdPolymerFamilies_sum_Λ_latticeGraph_minus_one_lt_one_eventually`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.vdPolymerFamilies_sum_Λ_minus_one_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerEpsilonInfrastructure` declarations.
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
