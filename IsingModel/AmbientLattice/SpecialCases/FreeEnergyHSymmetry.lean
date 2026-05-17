import IsingModel.AmbientLattice.SpontaneousMono
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyHSymmetryMonotone

/-!
# Free-energy `h`-symmetry along an exhaustion

Narrow child module for the two along-exhaustion
`freeEnergyAlongExhaustion` `h`-symmetry wrappers extracted from
`FreeEnergy.lean`:

* `freeEnergyAlongExhaustion_neg_h` (h-evenness)
* `freeEnergyAlongExhaustion_eq_abs_h` (|h|-rewrite)

The ferromagnetic `|h|`-monotonicity wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyHSymmetryMonotone`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding `IsingModel.freeEnergy_*`
ambient lemma via `change` + `exact`. Theorem names are unchanged
from the former `FreeEnergy` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Along-exhaustion h-evenness**:
`freeEnergyAlongExhaustion G Λ ⟨J, -h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, -h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, h, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_neg_h _ J h β

/-- **Along-exhaustion `|h|`-rewrite**:
`freeEnergyAlongExhaustion G Λ ⟨J, h, β⟩ n = freeEnergyAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. -/
theorem freeEnergyAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = freeEnergyAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n := by
  change IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
      (⟨J, h, β⟩ : IsingParams ℝ)
    = IsingModel.freeEnergy (inducedGraph G (Λ.volume n))
        (⟨J, |h|, β⟩ : IsingParams ℝ)
  exact IsingModel.freeEnergy_eq_abs_h _ J h β

/-! ## Moved: 1 ferromagnetic `|h|`-monotonicity wrapper

The ferromagnetic `freeEnergyAlongExhaustion_monotone_abs_h`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.FreeEnergyHSymmetryMonotone`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
