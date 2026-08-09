import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity

/-!
# ℤ^d along-exhaustion free-energy analyticity at a general external field

Concrete `latticeGraph d` statements that, at a fixed stage of an arbitrary
`Ambient.Exhaustion` of `Fin d → ℤ`, the free energy of that stage is analytic on a
neighbourhood of all of `Set.univ` as a function of one real parameter with the others held
fixed. The inverse temperature and the coupling are each treated at an unrestricted external
field, and the external field itself is treated as well. Each statement requires a
`Fintype` instance on the edge set induced at every stage, and that instance is its entire
requirement: no `Prop`-typed hypothesis is carried anywhere in this module.
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
