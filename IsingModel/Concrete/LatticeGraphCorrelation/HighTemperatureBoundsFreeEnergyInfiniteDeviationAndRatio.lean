import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d ∞-vol freeEnergy deviation sandwich wrapper

Narrow child module for the ℤ^d
`freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_*`
wrapper extracted from `HighTemperatureBoundsFreeEnergyInfinite.lean`:

* `_deviation_sandwich_exp`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d ∞-vol f deviation sandwich on `cubicExhaustion d`**: under
ferromagnetic `0 ≤ J, 0 < β`,
`0 ≤ freeEnergyInfinite ⟨J, 0, β⟩ - log 2 ≤ β·J·d`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_deviation_sandwich_exp
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (d : ℝ) := by
  refine freeEnergyInfinite_high_temp_h_zero_deviation_sandwich_exp
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β hJ hβ
    (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

end Ambient
end IsingModel
