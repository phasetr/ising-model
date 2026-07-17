import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# ℤ^d Λ-layer joint pointwise mag + susc wrappers

Narrow child module for four ℤ^d Λ-layer joint pointwise wrappers
extracted from `JointRegularityPointwise.lean`:

* `magnetizationΛ_latticeGraph_continuousAt_joint`,
* `magnetizationΛ_latticeGraph_differentiableAt_joint`,
* `susceptibilityΛ_latticeGraph_continuousAt_joint`,
* `susceptibilityΛ_latticeGraph_differentiableAt_joint`.

Each result is a thin pass-through of the ambient
`Ambient.{magnetizationΛ,susceptibilityΛ}_*_joint` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `JointRegularityPointwise` declarations.
-/

namespace IsingModel
namespace Ambient

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

end Ambient
end IsingModel
