import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeLogBoundOnlySingletons
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFeFreeEnergyBoundOnly

/-!
# Ambient alongExhaustion ferromagnetic triple-ratio bound_bundle wrapper at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
ferromagnetic `triple_ratio_bound_bundle_ferromagnetic` wrapper
extracted from `HighTemperatureBoundsTripleRatioBoundBundle.lean`:

* `partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic`

To avoid an import cycle (the parent retains the non-ferromagnetic
J=0 triple bundle that the ferromagnetic proof previously
forwarded to), the child's PROOF BODY constructs the conjunction
directly from the three Z / log Z / freeEnergy ratio-bound
slice-singleton wrappers under `mul_nonneg hβ.le hJ`. The theorem
name is unchanged from the former `HighTemperatureBoundsTripleRatio`
declaration.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex ferromagnetic triple ratio bound bundle at J=0, stage `n`**. -/
theorem
partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (n : ℕ) (hne : 0 < (Λ.volume n).card) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J *
            (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) n)
        - Real.log (partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n)
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card ∧
    freeEnergyAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n
        - freeEnergyAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card /
            (Λ.volume n).card :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
     G Λ J β (mul_nonneg hβ.le hJ) n,
   log_partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
     G Λ J β (mul_nonneg hβ.le hJ) n,
   freeEnergyAlongExhaustion_high_temp_h_zero_ratio_bound
     G Λ J β (mul_nonneg hβ.le hJ) n hne⟩

end Ambient

end IsingModel
