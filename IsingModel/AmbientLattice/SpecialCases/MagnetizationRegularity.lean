import IsingModel.AmbientLattice.Defs
import IsingModel.AmbientLattice.Exhaustion
import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityDifferentiable

/-!
# Magnetization regularity wrappers along an exhaustion

Narrow child module for finite-stage magnetization `Continuous` and
`Differentiable` wrappers along an exhaustion. The theorem names are the same
as the former legacy declarations, but callers can now avoid importing the
monolithic special-cases legacy module.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### magnetization regularity along-ex wraps -/

/-- **Along-ex: magnetization Continuous in `h` for `i ∈
Λ.volume n`**. The site coercion is the obvious lift. -/
theorem magnetizationAlongExhaustion_continuous_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun h' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_continuous_field G (Λ.volume n) J β _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization Continuous in `J`**. -/
theorem magnetizationAlongExhaustion_continuous_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (i : V) (n : ℕ) :
    Continuous (fun J' =>
      magnetizationAlongExhaustion G Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_continuous_J G (Λ.volume n) h β _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-- **Along-ex: magnetization Continuous in `β`** (general h). -/
theorem magnetizationAlongExhaustion_continuous_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (i : V) (n : ℕ) :
    Continuous (fun β' =>
      magnetizationAlongExhaustion G Λ
        (⟨J, h, β'⟩ : IsingParams ℝ) i n) := by
  unfold magnetizationAlongExhaustion correlationAlongExhaustion
  by_cases hi : ({i} : Finset V) ⊆ Λ.volume n
  · simp only [hi, dif_pos]
    exact magnetizationΛ_continuous_beta G (Λ.volume n) J h _
  · simp only [hi, dif_neg, not_false_iff]
    exact continuous_const

/-! ### Moved: Differentiable along-ex wrappers

The three `magnetizationAlongExhaustion_differentiable_*` wrappers
(`_field`, `_J`, `_beta`) now live in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityDifferentiable`.
The legacy import path is preserved by re-exporting the new child
from this parent module and from `Legacy.lean`.
-/

/-! ### Moved: ContinuousAt / DifferentiableAt along-ex wrappers

The six `magnetizationAlongExhaustion_{continuousAt,differentiableAt}_{beta,field,J}`
pointwise wrappers now live in
`IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularityAt`.
The legacy import path is preserved by re-exporting the new child
from `Legacy.lean`.
-/

end Ambient
end IsingModel
