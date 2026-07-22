import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Concrete HT Λ-layer deviation_bound wrappers

Narrow child module for the 2 ℤ^d Λ-layer freeEnergy deviation_bound
wrappers
(`freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_bound_exp`,
`_ferromagnetic`) extracted from
`HighTemperatureBoundsDeviation.lean` in PR #2079. Each is a thin
pass-through to the corresponding ambient `freeEnergyΛ_*` lemma at
`IsingModel.latticeGraph d`. The theorem names are unchanged from
the former `HighTemperatureBoundsDeviation` declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d Λ sharper f deviation bound**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_bound_exp
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_bound_exp
    (IsingModel.latticeGraph d) Λ J β hβJ hne

/-- **ℤ^d Λ ferromagnetic f deviation bound**. -/
theorem freeEnergyΛ_latticeGraph_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J *
          (inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card /
            Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ hne

end Ambient

end IsingModel
