import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularity

/-!
# Magnetization `ContinuousAt` / `DifferentiableAt` along-ex wrappers

Narrow child module for the six pointwise `ContinuousAt` /
`DifferentiableAt` wrappers along an exhaustion, obtained from the
corresponding `Continuous` / `Differentiable` wrappers in the parent
`MagnetizationRegularity` module via the `.continuousAt` /
`.differentiableAt` projections. Theorem names are unchanged from
the former `MagnetizationRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

open Finset Real

variable {V : Type*} [DecidableEq V]

/-! ### ContinuousAt / DifferentiableAt along-ex wrappers -/

/-- **Along-ex: magnetization ContinuousAt β** (general h). -/
theorem magnetizationAlongExhaustion_continuousAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_continuous_beta G Λ J h i n).continuousAt

/-- **Along-ex: magnetization DifferentiableAt β** (general h). -/
theorem magnetizationAlongExhaustion_differentiableAt_beta
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun β' => magnetizationAlongExhaustion G Λ
          (⟨J, h, β'⟩ : IsingParams ℝ) i n) β :=
  (magnetizationAlongExhaustion_differentiable_beta G Λ J h i n).differentiableAt

/-- **Along-ex: magnetization ContinuousAt h**. -/
theorem magnetizationAlongExhaustion_continuousAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_continuous_field G Λ J β i n).continuousAt

/-- **Along-ex: magnetization DifferentiableAt h**. -/
theorem magnetizationAlongExhaustion_differentiableAt_field
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    DifferentiableAt ℝ
      (fun h' => magnetizationAlongExhaustion G Λ
          (⟨J, h', β⟩ : IsingParams ℝ) i n) h :=
  (magnetizationAlongExhaustion_differentiable_field G Λ J β i n).differentiableAt

/-- **Along-ex: magnetization ContinuousAt J**. -/
theorem magnetizationAlongExhaustion_continuousAt_J
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (i : V) (n : ℕ) :
    ContinuousAt
      (fun J' => magnetizationAlongExhaustion G Λ
          (⟨J', h, β⟩ : IsingParams ℝ) i n) J :=
  (magnetizationAlongExhaustion_continuous_J G Λ h β i n).continuousAt

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
