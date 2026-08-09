import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d infinite-volume free energy near the trivial slices on the cubic exhaustion

Instantiates at `IsingModel.latticeGraph d` and on `Ambient.cubicExhaustion d`, at the
parameter record `⟨J, 0, β⟩`, the quantitative continuity bound `β * J * d` on the absolute
difference between `freeEnergyInfinite` and its value at `⟨0, 0, β⟩`, the same bound against
its value at `⟨J, 0, 0⟩`, and the statement pairing them. Every statement here assumes
`0 ≤ J` together with `0 < β`, and the separate bounds obtain the edge-density constant `d`
from `inducedLatticeGraph_card_edgeFinset_le`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d ∞-vol f quantitative continuity at `J = 0` on `cubicExhaustion d`**:
under ferromagnetic `0 ≤ J, 0 < β`,
`|freeEnergyInfinite ⟨J, 0, β⟩ - freeEnergyInfinite ⟨0, 0, β⟩| ≤ β·J·d`.
ℤ^d concrete wrapper of Step 423 with `c = d`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_at_J_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    |freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * (d : ℝ) := by
  refine freeEnergyInfinite_high_temp_h_zero_continuity_at_J_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β hJ hβ
    (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d ∞-vol f continuity at `β = 0` on `cubicExhaustion d`**:
under ferromagnetic `0 ≤ J, 0 < β`,
`|freeEnergyInfinite ⟨J, 0, β⟩ - freeEnergyInfinite ⟨J, 0, 0⟩| ≤ β·J·d`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_at_beta_zero
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    |freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * (d : ℝ) := by
  refine freeEnergyInfinite_high_temp_h_zero_continuity_at_beta_zero
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) J β hJ hβ
    (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d ∞-vol f continuity bundle at trivial slices**: under
ferromagnetic `0 ≤ J, 0 < β`, both `J = 0` and `β = 0` continuity at
the ∞-volume on `cubicExhaustion d`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_bundle
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    |freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨0, 0, β⟩ : IsingParams ℝ)| ≤ β * J * (d : ℝ) ∧
    |freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, β⟩ : IsingParams ℝ)
      - freeEnergyInfinite (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d)
        (⟨J, 0, 0⟩ : IsingParams ℝ)| ≤ β * J * (d : ℝ) :=
  ⟨freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_at_J_zero
      d J β hJ hβ,
   freeEnergyInfinite_latticeGraph_cubicExhaustion_high_temp_h_zero_continuity_at_beta_zero
      d J β hJ hβ⟩

end Ambient
end IsingModel
