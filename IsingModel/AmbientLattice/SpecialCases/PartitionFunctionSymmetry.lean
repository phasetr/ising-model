import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetryMonotone

/-!
# Partition-function h-symmetry wrappers along an exhaustion

Narrow child module for the two finite-stage partition-function
`h`-symmetry wrappers along an exhaustion (h-evenness,
|h|-rewrite). The ferromagnetic `|h|`-monotonicity wrapper now
lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetryMonotone`
and is re-imported through this parent module. Theorem names are
unchanged from the former monolithic special-cases declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## h-symmetry / `|h|`-monotonicity along exhaustion -/

/-- **Along-exhaustion partition-function h-evenness**:
`partitionFunctionAlongExhaustion G Λ ⟨J, -h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n`. Per-stage lift of
`IsingModel.partitionFunction_neg_h` via the flip involution. -/
theorem partitionFunctionAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_neg_h G (Λ.volume n) J h β

/-- **Along-exhaustion partition-function `|h|`-rewrite**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_eq_abs_h G (Λ.volume n) J h β

/-! ## Moved: 1 ferromagnetic `|h|`-monotonicity wrapper

The `partitionFunctionAlongExhaustion_monotone_abs_h` wrapper now
lives in
`IsingModel.AmbientLattice.SpecialCases.PartitionFunctionSymmetryMonotone`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
