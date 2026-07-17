import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity

/-!
# ℤ^d Λ-layer polymerFreeEnergy tanh analyticity wrappers (§18.6)

Narrow child module for four ℤ^d Λ-layer
`polymerFreeEnergy_Λ_latticeGraph_tanh_*` analyticity wrappers
extracted from `PolymerFreeEnergyAnalyticity.lean`:

* `polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_beta`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_J`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_beta_Ici_zero`,
* `polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_J_Ici_zero`.

Each result is a thin pass-through of the ambient
`Ambient.polymerFreeEnergy_Λ_tanh_*` analytic lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `PolymerFreeEnergyAnalyticity` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β' * J))) β :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β hβJ

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J'))) J :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J hβJ

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticOnNhd
on (Set.Ici 0) in β under `0 ≤ J`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_beta_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β' * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticOnNhd_beta_Ici_zero
    (IsingModel.latticeGraph d) Λ hJ

/-- **ℤ^d Λ: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticOnNhd
on (Set.Ici 0) in J under `0 ≤ β`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_J_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) Λ)
        (Real.tanh (β * J'))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_tanh_analyticOnNhd_J_Ici_zero
    (IsingModel.latticeGraph d) Λ hβ

end Ambient
end IsingModel
