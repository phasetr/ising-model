import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaRegularity

/-!
# ℤ^d Λ polymerFreeEnergy tanh-composition analyticity (§18.6)

Instantiates at fixed volume `Λ` on `IsingModel.latticeGraph d` the analyticity of the
polymer free energy at activity `tanh (β * J)` as a function of `β` and as a function of `J`:
analytic at a single parameter value under `0 ≤ β * J`, and analytic on a neighbourhood of
`Set.Ici 0` in one parameter whenever the other is nonnegative. This is the ℤ^d form of the
GJ §18.6 analyticity of the cluster expansion in the physical parameters.
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
