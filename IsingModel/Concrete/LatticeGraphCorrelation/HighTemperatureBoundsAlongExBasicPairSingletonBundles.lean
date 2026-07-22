import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonBundle

/-!
# Concrete §18.3-§18.4 along-ex pair+singleton complete-summary wrapper

Narrow child module for the ℤ^d along-exhaustion
`correlationAlongExhaustion_*_pair_singleton_complete_summary`
bundle wrapper extracted from
`HighTemperatureBoundsAlongExhaustionBasic.lean`. The result is a
thin pass-through of the corresponding ambient
`correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary`
lemma at `G := IsingModel.latticeGraph d`. The theorem name is
unchanged from the former `HighTemperatureBoundsAlongExhaustionBasic`
declaration.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d along-ex pair + singleton complete-summary bundle at h = 0**:
under `0 ≤ β·J`, at every stage `n` packages pair upper bound, pair
sandwich lower, singleton vanishing, and pair vanishing at `J = 0` /
`β = 0` trivial slices. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary`. -/
theorem
    correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_singleton_complete_summary
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ≤ 1 ∧
      0 ≤ correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 ∧
      correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_singleton_complete_summary
    (IsingModel.latticeGraph d) Λ J β hβJ i j n

end Ambient

end IsingModel
