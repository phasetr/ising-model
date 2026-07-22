import IsingModel.Lattice
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly

/-!
# ℤ^d alongExhaustion log Z ratio_bound_bundle wrappers at h = 0

Narrow child module for the concrete (`latticeGraph d`)
alongExhaustion `log_partitionFunction` ratio_bound_bundle wrappers at
h = 0 (with ferromagnetic variant) extracted from
`HighTemperatureBoundsAlongExhaustionRatioLogFe.lean`:

* `log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle`,
* `log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_ratio_bound_bundle_ferromagnetic`.

The theorem names are unchanged from the former
`HighTemperatureBoundsAlongExhaustionRatioLogFe` declarations. The two
companion `freeEnergyAlongExhaustion_latticeGraph_*_ratio_bound_bundle`
wrappers were removed as unused conjunction bundles.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]


/-- **ℤ^d along-ex log Z ratio bound bundle at stage `n`**. -/
theorem
log_partitionFunctionAlongExhaustion_latticeGraph_high_temp_expansion_h_zero_ratio_bound_bundle
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hβJ : 0 ≤ β * J) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle
    (IsingModel.latticeGraph d) Λ J β hβJ n

/-- **ℤ^d along-ex ferromagnetic log Z ratio bound bundle at stage `n`**. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_h_zero_ratio_bound_bundle_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card ∧
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n)
        ≤ β * J *
            (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)).edgeFinset.card :=
  log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle_ferromagnetic
    (IsingModel.latticeGraph d) Λ J β hJ hβ n

end Ambient

end IsingModel
