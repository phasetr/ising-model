import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointRegularity

/-!
# Concrete pointwise joint regularity wrappers

Narrow child module for six ℤ^d Λ-layer pointwise
`{correlation,magnetization,susceptibility}Λ_latticeGraph_*_joint`
wrappers (with `continuousAt` and `differentiableAt`). Each wrapper is a
thin pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`. The six AlongExhaustion variants now live in
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

/-- **ℤ^d Λ: magnetizationΛ jointly ContinuousAt**. -/
theorem magnetizationΛ_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.magnetizationΛ_continuousAt_joint (IsingModel.latticeGraph d) Λ i p

/-- **ℤ^d Λ: magnetizationΛ jointly DifferentiableAt**. -/
theorem magnetizationΛ_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.magnetizationΛ_differentiableAt_joint (IsingModel.latticeGraph d) Λ i p

/-- **ℤ^d Λ: susceptibilityΛ jointly ContinuousAt**. -/
theorem susceptibilityΛ_latticeGraph_continuousAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.susceptibilityΛ_continuousAt_joint (IsingModel.latticeGraph d) Λ i p

/-- **ℤ^d Λ: susceptibilityΛ jointly DifferentiableAt**. -/
theorem susceptibilityΛ_latticeGraph_differentiableAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (p : ℝ × ℝ × ℝ) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨q.2.1, q.2.2, q.1⟩ i) p :=
  Ambient.susceptibilityΛ_differentiableAt_joint (IsingModel.latticeGraph d) Λ i p

/-! ## Moved: AlongExhaustion joint pointwise wrappers

The six AlongExhaustion joint pointwise wrappers
(`{correlation,magnetization,susceptibility}AlongExhaustion_latticeGraph_*_joint`
with `continuousAt` and `differentiableAt`) now live in
`JointRegularityPointwiseAlongEx.lean`. -/



end Ambient
end IsingModel
