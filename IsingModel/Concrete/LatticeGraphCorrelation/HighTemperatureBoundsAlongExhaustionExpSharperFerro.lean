import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharperFerro

/-!
# ℤ^d alongExhaustion sharper-exp ferromagnetic upper-bound wrappers

Narrow child module for three ℤ^d alongExhaustion sharper-exp HT
upper-bound ferromagnetic wrappers extracted from
`HighTemperatureBoundsAlongExhaustionExpSharper.lean`:

* `partitionFunctionAlongExhaustion_latticeGraph_h_zero_upper_bound_exp_ferromagnetic`,
* `log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_upper_bound_exp_ferromagnetic`,
* `freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_upper_bound_exp_ferromagnetic`.

Each result is a thin pass-through of the corresponding ambient
`*_ferromagnetic` along-exhaustion HT bound at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `HighTemperatureBoundsAlongExhaustionExpSharper`
declarations.
-/

namespace IsingModel
namespace Ambient

open scoped symmDiff

/-- **ℤ^d along-ex ferromagnetic Z/logZ/f sharper upper bounds at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ (2 : ℝ) ^ (Λ.volume n).card *
          Real.exp (β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card) :=
  partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic log Z sharper upper bound at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
      ≤ ((Λ.volume n).card : ℝ) * Real.log 2
        + β * J *
          (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

/-- **ℤ^d along-ex ferromagnetic f sharper upper bound at stage `n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n
      ≤ Real.log 2 +
          β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card /
              (Λ.volume n).card :=
  freeEnergyAlongExhaustion_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n hne

end Ambient
end IsingModel
