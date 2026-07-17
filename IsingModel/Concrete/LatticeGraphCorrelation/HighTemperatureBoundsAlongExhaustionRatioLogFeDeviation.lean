import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeNonempty

/-!
# ℤ^d AlongExhaustion freeEnergy deviation bound wrappers

Narrow child module for two ℤ^d
`freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_*`
wrappers extracted from `HighTemperatureBoundsAlongExhaustionRatioLogFe.lean`:

* `freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_bound_exp_of_nonempty`,
* `freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_deviation_pos_of_nonempty`.
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
