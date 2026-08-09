import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeNonempty

/-!
# ℤ^d along-exhaustion free-energy deviation on a nonempty stage volume

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ` and at the parameter record `⟨J, 0, β⟩`, the bound
`f_n - log 2 ≤ β * J * |E_n| / |Λ_n|` and the strict statement `log 2 < f_n`, each with the
stage volume assumed nonempty in the `Finset.Nonempty` spelling. The bound assumes
`0 ≤ β * J`; the strict statement assumes `0 < β * J` and, in addition, that the stage-`n`
induced subgraph carries at least one edge.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex f deviation bound under nonempty**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_bound_exp_of_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_bound_exp_of_nonempty
    (IsingModel.latticeGraph d) Λ J β hβJ n hne

/-- **ℤ^d along-ex f strict deviation under nonempty**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_pos_of_nonempty
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 < β * J) (n : ℕ) (hne : (Λ.volume n).Nonempty)
    (hEpos : 0 <
      (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :
    0 < freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n - Real.log 2 :=
  freeEnergyAlongExhaustion_high_temp_h_zero_deviation_pos_of_nonempty
    (IsingModel.latticeGraph d) Λ J β hβJ n hne hEpos

end Ambient
end IsingModel
