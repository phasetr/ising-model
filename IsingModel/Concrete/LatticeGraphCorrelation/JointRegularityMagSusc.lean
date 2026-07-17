import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# ℤ^d Λ-layer joint mag + susc Continuous/Differentiable wrappers

Narrow child module for four ℤ^d Λ-layer joint Continuous/Differentiable
wrappers extracted from `JointRegularity.lean`:

* `magnetizationΛ_latticeGraph_continuous_joint`,
* `magnetizationΛ_latticeGraph_differentiable_joint`,
* `susceptibilityΛ_latticeGraph_continuous_joint`,
* `susceptibilityΛ_latticeGraph_differentiable_joint`.

Each result is a thin pass-through of the corresponding ambient
`{magnetization,susceptibility}Λ_{continuous,differentiable}_joint`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `JointRegularity` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: magnetizationΛ jointly Continuous in `(β, J, h)`**. -/
theorem magnetizationΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.magnetizationΛ_continuous_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: magnetizationΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem magnetizationΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.magnetizationΛ_differentiable_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly Continuous in `(β, J, h)`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.susceptibilityΛ_continuous_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly Differentiable ℝ in `(β, J, h)`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    Differentiable ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i) :=
  Ambient.susceptibilityΛ_differentiable_joint (IsingModel.latticeGraph d) Λ i

end Ambient
end IsingModel
