import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingleton

/-!
# Concrete HT AlongExhaustion correlation singleton / odd-vanishing wrappers

Instantiates the ambient zero-field correlation degeneracies along an exhaustion at
`IsingModel.latticeGraph d`: the single-site value and the Z₂ vanishing on odd subsets.
Each is a pass-through of the matching `correlationAlongExhaustion_high_temp_h_zero_*`
ambient lemma.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-exhaustion magnetization vanishes at h = 0**: at every
stage `n`,
`correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ {i} n = 0`
for any ambient site `i : Fin d → ℤ`. ℤ^d wrapper. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton
    (IsingModel.latticeGraph d) Λ J β i n

/-- **ℤ^d along-exhaustion Z₂ symmetry of correlation at h = 0**:
for ambient `A : Finset (Fin d → ℤ)` of odd cardinality,
`correlationAlongExhaustion (latticeGraph d) Λ ⟨J, 0, β⟩ A n = 0` at
every stage `n`. ℤ^d wrapper of
`correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero`. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_odd_card_eq_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (A : Finset (Fin d → ℤ)) (hA_odd : Odd A.card) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) A n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_odd_card_eq_zero
    (IsingModel.latticeGraph d) Λ J β A hA_odd n

end Ambient

end IsingModel
