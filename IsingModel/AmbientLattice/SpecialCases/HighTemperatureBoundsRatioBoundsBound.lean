import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundOnly
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBoundFerro

/-!
# Ambient alongExhaustion Z `ratio_bound` bundle at h = 0

Bundles the GJ §18.3–§18.4 zero-field partition-function ratio estimate along an exhaustion
into a single statement, so a caller gets the ratio bound without re-deriving it from the
underlying `_ratio_sandwich*` lemma.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-ex Z ratio upper bound bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) ∧
    partitionFunctionAlongExhaustion G Λ (⟨J, 0, β⟩ : IsingParams ℝ) n /
        partitionFunctionAlongExhaustion G Λ (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card) :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_bound_beta_zero
      G Λ J β hβJ n⟩

end Ambient

end IsingModel
