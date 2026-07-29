import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# Concrete pointwise joint regularity wrappers

Narrow child module for two ℤ^d Λ-layer pointwise
`correlationΛ_latticeGraph_*_joint`
wrappers (with `continuousAt` and `differentiableAt`). Each wrapper is a
thin pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`. The two AlongExhaustion variants now live in
`JointRegularityPointwiseAlongEx.lean`.
-/

namespace IsingModel
namespace Ambient


/-! ### ℤ^d joint pointwise wrappers -/

/-- **ℤ^d Λ: correlationΛ jointly ContinuousAt**. -/
theorem correlationΛ_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  Ambient.correlationΛ_continuousAt_joint (IsingModel.latticeGraph d) Λ A p

/-- **ℤ^d Λ: correlationΛ jointly DifferentiableAt**. -/
theorem correlationΛ_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (A : Finset (↑Λ : Type _)) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.correlationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ A) p :=
  Ambient.correlationΛ_differentiableAt_joint (IsingModel.latticeGraph d) Λ A p

/-! ## Moved: AlongExhaustion joint pointwise wrappers

The two AlongExhaustion joint pointwise wrappers
(`correlationAlongExhaustion_latticeGraph_*_joint`
with `continuousAt` and `differentiableAt`) now live in
`JointRegularityPointwiseAlongEx.lean`. -/



end Ambient
end IsingModel
