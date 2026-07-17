import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingleton

/-!
# Concrete HT AlongExhaustion correlation trivial-slice / symmetry wrappers

Narrow child module for the 6 ℤ^d along-exhaustion correlation
trivial-slice / symmetry wrappers
(`correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_J_zero`,
`_at_pair_beta_zero`, `_at_singleton_J_zero`, `_at_singleton_beta_zero`,
`_at_singleton`, `_odd_card_eq_zero`) extracted from
`HighTemperatureBoundsAlongExhaustionBasic.lean` in PR #2076. Each is
a thin pass-through to the corresponding ambient
`correlationAlongExhaustion_high_temp_h_zero_*` lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `HighTemperatureBoundsAlongExhaustionBasic` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## Moved: trivial-slice wrappers (J = 0, β = 0)

The four `correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_*_{J,beta}_zero`
trivial-slice wrappers (singleton/pair at J = 0 and β = 0) now live in
`HighTemperatureBoundsAlongExBasicTrivialSlices.lean`. -/


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
