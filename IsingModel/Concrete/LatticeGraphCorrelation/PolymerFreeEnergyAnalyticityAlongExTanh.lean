import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticityTanh

/-!
# ℤ^d AlongExhaustion polymerFreeEnergy tanh analyticity wrappers

Narrow child module for four ℤ^d
`polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*` analyticity wrappers
extracted from `PolymerFreeEnergyAnalyticity.lean`:

* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticAt_beta`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticAt_J`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta_Ici_zero`,
* `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J_Ici_zero`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β' * J))) β :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (β J : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J'))) J :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ β J hβJ n

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (·*J) AnalyticOnNhd
on (Set.Ici 0) in β under `0 ≤ J`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β' * J))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_beta_Ici_zero
    (IsingModel.latticeGraph d) Λ hJ n

/-- **ℤ^d along-ex: polymerFreeEnergy ∘ tanh ∘ (β*·) AnalyticOnNhd
on (Set.Ici 0) in J under `0 ≤ β`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.polymerFreeEnergy
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n))
        (Real.tanh (β * J'))) (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_tanh_analyticOnNhd_J_Ici_zero
    (IsingModel.latticeGraph d) Λ hβ n

end Ambient
end IsingModel
