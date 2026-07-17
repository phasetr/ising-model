import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonTrivial
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairTrivial

/-!
# Concrete HT AlongExhaustion correlation trivial-slice wrappers (J = 0, β = 0)

Narrow child module for 4 ℤ^d along-exhaustion correlation trivial-slice
wrappers extracted from `HighTemperatureBoundsAlongExBasicTrivial.lean`:

* `correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_J_zero`,
* `correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_beta_zero`,
* `correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_J_zero`,
* `correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_beta_zero`.

Each result is a thin pass-through of the corresponding ambient
`correlationAlongExhaustion_high_temp_h_zero_at_*_{J,beta}_zero` lemma
at `G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureBoundsAlongExBasicTrivial` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex pair at J=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_J_zero
    (IsingModel.latticeGraph d) Λ β i j n

/-- **ℤ^d along-ex pair at β=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_pair_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ)
    (i j : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i, j} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_pair_beta_zero
    (IsingModel.latticeGraph d) Λ J i j n

/-- **ℤ^d along-ex singleton at J=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_J_zero
    (IsingModel.latticeGraph d) Λ β i n

/-- **ℤ^d along-ex singleton at β=0,h=0**: = 0. -/
theorem correlationAlongExhaustion_latticeGraph_high_temp_h_zero_at_singleton_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J : ℝ)
    (i : Fin d → ℤ) (n : ℕ) :
    correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, 0⟩ : IsingParams ℝ) ({i} : Finset (Fin d → ℤ)) n = 0 :=
  correlationAlongExhaustion_high_temp_h_zero_at_singleton_beta_zero
    (IsingModel.latticeGraph d) Λ J i n

end Ambient

end IsingModel
