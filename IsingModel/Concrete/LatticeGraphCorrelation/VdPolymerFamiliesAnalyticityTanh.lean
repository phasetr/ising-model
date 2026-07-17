import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticityTanh

/-!
# ℤ^d `vdPolymerFamilies_sum` tanh-composed analyticity wrappers

Narrow child module for four ℤ^d
`vdPolymerFamilies_sum_*_latticeGraph_tanh_analyticAt_*` wrappers
extracted from `VdPolymerFamiliesAnalyticity.lean`:

* `vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_beta`,
* `vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_J`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_beta`,
* `vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_J`.

Each result is a thin pass-through of the corresponding ambient
`Ambient.vdPolymerFamilies_sum*_tanh_analyticAt_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `VdPolymerFamiliesAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β

/-- **ℤ^d Λ: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sum_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) Λ),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  Ambient.vdPolymerFamilies_sum_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem
vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β' * J) ^ P.card) β :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β n

/-- **ℤ^d along-ex: vdPolymerFamilies_sum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ =>
        ∑ Γ ∈ IsingModel.vdCompatiblePolymerFamilies
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)),
          ∏ P ∈ Γ, Real.tanh (β * J') ^ P.card) J :=
  Ambient.vdPolymerFamilies_sumAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J n

end Ambient
end IsingModel
