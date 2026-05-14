import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity

/-!
# ℤ^d freeEnergyAlongEx AnalyticOnNhd general-h wrappers

Narrow child module for three ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_*` general-h
wrappers extracted from `FreeEnergyAnalyticityAlongEx.lean`:

* `freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_beta_general_h`,
* `freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_J_general_h`,
* `freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_h`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `β`
at general `h`**. -/
theorem
freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_beta_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h, β'⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_beta_general_h
    (IsingModel.latticeGraph d) Λ J h n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `J`
at general `h`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_J_general_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (β h : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J', h, β⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_J_general_h
    (IsingModel.latticeGraph d) Λ β h n

/-- **ℤ^d along-ex: freeEnergy `AnalyticOnNhd ℝ _ Set.univ` in `h`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet] (J β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun h' : ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        Λ ⟨J, h', β⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_h
    (IsingModel.latticeGraph d) Λ J β n

end Ambient
end IsingModel
