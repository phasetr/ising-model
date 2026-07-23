import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpansion
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsExpSharper
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsDeviation
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsSingletons
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsFerro

/-!
# Ambient alongExhaustion Z/f/log Z ratio sandwich / ratio bound wrappers at h = 0

Narrow child module for the §18.3-§18.4 ambient alongExhaustion
`partitionFunctionAlongExhaustion` `ratio_sandwich` / `ratio_bound`
wrappers (with `J = 0` / `β = 0` / bundle variants plus ferromagnetic
counterparts). The log / freeEnergy ratio wrappers now live in
`HighTemperatureBoundsRatioLogFe.lean` (split off in PR #1995); the 2
`triple_ratio_sandwich_bundle` wrappers now live in
`HighTemperatureBoundsTripleRatio.lean` (split off in PR #1994; the
bound-bundle and ferromagnetic variants were dropped in PR #4676). The
theorem names are unchanged from the former `HighTemperatureBounds`
declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]


/-! ## Moved: 2 Z ratio sandwich singleton wrappers

The two slice-singleton wrappers
(`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich`
[J = 0 trivial slice],
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero`
[β = 0 trivial slice]) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsSingletons`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-- **Along-ex Z ratio sandwich bundle at stage `n`**. -/
theorem partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (n : ℕ) :
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨0, 0, β⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨0, 0, β⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card)) ∧
    (Real.cosh (β * J) ^ (inducedGraph G (Λ.volume n)).edgeFinset.card
        ≤ partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, β⟩ : IsingParams ℝ) n /
            partitionFunctionAlongExhaustion G Λ
              (⟨J, 0, 0⟩ : IsingParams ℝ) n ∧
      partitionFunctionAlongExhaustion G Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) n /
          partitionFunctionAlongExhaustion G Λ
            (⟨J, 0, 0⟩ : IsingParams ℝ) n
        ≤ Real.exp (β * J * (inducedGraph G (Λ.volume n)).edgeFinset.card)) :=
  ⟨partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich
      G Λ J β hβJ n,
   partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
      G Λ J β hβJ n⟩

/-! ## Moved: 1 ferromagnetic Z ratio_sandwich_bundle wrapper

The ferromagnetic
`partitionFunctionAlongExhaustion_high_temp_expansion_h_zero_ratio_sandwich_bundle_ferromagnetic`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsFerro`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

/-! ## Moved: Z `ratio_bound` (non-bundle and bundle) wrappers

The six ambient alongExhaustion `partitionFunctionAlongExhaustion`
`ratio_bound` wrappers (four non-bundle slice variants — `J = 0` /
`β = 0` and ferromagnetic counterparts — and the two
`ratio_bound_bundle` wrappers, general and ferromagnetic) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioBoundsBound`.
The earlier import path is preserved by re-exporting the new child
from the umbrella `HighTemperatureBounds.lean`.
-/

/-! ## Moved: log Z + freeEnergy ratio wrappers

The 17 ambient alongExhaustion `log_partitionFunction` and
`freeEnergy` ratio_sandwich / ratio_bound (+ deviation_pos /
pow_two_lt) wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsRatioLogFe`.
The umbrella `HighTemperatureBounds.lean` re-imports
the new child so the import paths and theorem names remain
unchanged.

The 2 ambient alongExhaustion `triple_ratio_sandwich_bundle` wrappers
(J = 0 / β = 0 trivial slices) now live in
`IsingModel.AmbientLattice.SpecialCases.HighTemperatureBoundsTripleRatio`
(narrowed in PR #1994). The earlier import path is preserved by
re-exporting the child from the umbrella module that aggregates it.
-/

end Ambient

end IsingModel
