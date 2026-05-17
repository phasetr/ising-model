import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureVdSumEventually

/-!
# Mayer ε(t) `at_zero` / `continuous` wrappers along an exhaustion

Narrow child module for the two §18.5 ambient alongExhaustion
ε(t) = `vdPolymerFamilies_sum_minus_one` infrastructure
pointwise wrappers extracted from `MayerEpsilonInfrastructure.lean`:

* `vdPolymerFamilies_sumAlongExhaustion_minus_one_at_zero`
* `vdPolymerFamilies_sumAlongExhaustion_minus_one_continuous`

The corresponding `_lt_one_eventually` wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureVdSumEventually`
and is re-imported through this parent module. Each wrapper is a
thin pass-through to the corresponding ambient
`vdPolymerFamilies_sum_Λ_minus_one_*` lemma. Theorem names are
unchanged from the former `MayerEpsilonInfrastructure` declarations.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: ε(0) = 0**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_at_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    (∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, (0 : ℝ) ^ P.card) = 0 :=
  vdPolymerFamilies_sum_Λ_minus_one_at_zero G (Λ.volume n)

/-- **Along-ex: ε(t) is `Continuous`**. -/
theorem vdPolymerFamilies_sumAlongExhaustion_minus_one_continuous
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] (n : ℕ) :
    Continuous (fun t : ℝ =>
      ∑ Γ ∈ (IsingModel.vdCompatiblePolymerFamilies
              (inducedGraph G (Λ.volume n))).erase ∅,
        ∏ P ∈ Γ, t ^ P.card) :=
  vdPolymerFamilies_sum_Λ_minus_one_continuous G (Λ.volume n)

/-! ## Moved: 1 lt_one_eventually wrapper

The `vdPolymerFamilies_sumAlongExhaustion_minus_one_lt_one_eventually`
wrapper now lives in
`IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructureVdSumEventually`.
The earlier import path is preserved by re-exporting the new child
from this parent module and from the umbrella `SpecialCases.lean`.
-/

end Ambient
end IsingModel
