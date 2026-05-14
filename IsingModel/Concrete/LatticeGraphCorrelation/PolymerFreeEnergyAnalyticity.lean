import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity

/-!
# Concrete polymer free-energy analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `polymerFreeEnergy` analytic wrappers. The theorem
names are the same as the former legacy declarations, but callers can now
import this child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: Λ-layer polymerFreeEnergy tanh analyticity wrappers

The four wrappers
`polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_beta`,
`polymerFreeEnergy_Λ_latticeGraph_tanh_analyticAt_J`,
`polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_beta_Ici_zero`,
`polymerFreeEnergy_Λ_latticeGraph_tanh_analyticOnNhd_J_Ici_zero` now
live in `PolymerFreeEnergyAnalyticityLambdaTanh.lean`. -/


/-! ## Moved: AlongExhaustion polymerFreeEnergy tanh analyticity wrappers

The four `polymerFreeEnergyAlongExhaustion_latticeGraph_tanh_*` analyticity
wrappers (`analyticAt_beta`, `analyticAt_J`,
`analyticOnNhd_beta_Ici_zero`, `analyticOnNhd_J_Ici_zero`) now live in
`PolymerFreeEnergyAnalyticityAlongExTanh.lean`. -/



/-- **ℤ^d Λ: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_analyticAt
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    {t : ℝ} (ht : 0 ≤ t) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) Λ) s) t :=
  Ambient.polymerFreeEnergy_Λ_analyticAt
    (IsingModel.latticeGraph d) Λ ht

/-- **ℤ^d Λ: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem polymerFreeEnergy_Λ_latticeGraph_analyticOnNhd_Ici_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet] :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) Λ) s) (Set.Ici 0) :=
  Ambient.polymerFreeEnergy_Λ_analyticOnNhd_Ici_zero
    (IsingModel.latticeGraph d) Λ

/-- **ℤ^d along-ex: polymerFreeEnergy is `AnalyticAt ℝ` for `t ≥ 0`**. -/
theorem polymerFreeEnergyAlongExhaustion_latticeGraph_analyticAt
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    AnalyticAt ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s) t :=
  Ambient.polymerFreeEnergyAlongExhaustion_analyticAt
    (IsingModel.latticeGraph d) Λ ht n

/-- **ℤ^d along-ex: polymerFreeEnergy AnalyticOnNhd over `[0, ∞)`**. -/
theorem
polymerFreeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_Ici_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (n : ℕ) :
    AnalyticOnNhd ℝ (fun s : ℝ => IsingModel.polymerFreeEnergy
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) s)
      (Set.Ici 0) :=
  Ambient.polymerFreeEnergyAlongExhaustion_analyticOnNhd_Ici_zero
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
