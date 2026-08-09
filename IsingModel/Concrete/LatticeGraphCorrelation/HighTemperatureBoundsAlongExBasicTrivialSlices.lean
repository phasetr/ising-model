import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicSingletonTrivial
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsCorrelationBasicPairTrivial

/-!
# ℤ^d along-exhaustion correlations vanish on the trivial slices `J = 0` and `β = 0`

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the vanishing of `correlationAlongExhaustion` on a pair `{i, j}` and on a
singleton `{i}` at the parameter records `⟨0, 0, β⟩` and `⟨J, 0, 0⟩`. The vanishing coupling
or vanishing inverse temperature is fixed inside the parameter record rather than assumed, so
no hypothesis is carried by any statement here.
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
