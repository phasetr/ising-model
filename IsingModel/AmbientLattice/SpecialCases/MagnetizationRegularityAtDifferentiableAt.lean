import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularity

/-!
# Magnetization `DifferentiableAt` along-ex wrappers

Narrow child module for the three pointwise `DifferentiableAt`
wrappers along an exhaustion extracted from
`MagnetizationRegularityAt.lean`:

* `magnetizationAlongExhaustion_differentiableAt_beta`
* `magnetizationAlongExhaustion_differentiableAt_field`
* `magnetizationAlongExhaustion_differentiableAt_J`

Each wrapper is a thin pass-through to the corresponding
`magnetizationAlongExhaustion_differentiable_*` parent lemma via the
`.differentiableAt` projection. Theorem names are unchanged from
the former `MagnetizationRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-- **Along-ex: magnetization DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_differentiable_beta G Λ J h i n).differentiableAt

/-- **Along-ex: magnetization DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_differentiable_field G Λ J β i n).differentiableAt

/-- **Along-ex: magnetization DifferentiableAt J**. -/
theorem magnetizationAlongExhaustion_differentiableAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_differentiable_J G Λ h β i n).differentiableAt

end Ambient
end IsingModel
