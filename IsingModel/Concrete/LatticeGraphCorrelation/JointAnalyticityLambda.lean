import IsingModel.Lattice
import IsingModel.AmbientLattice.AnalyticityLambdaMagSuscep

/-!
# ℤ^d Λ-direct joint analyticity wrappers

Narrow child module for four ℤ^d Λ-direct joint analyticity wrappers
extracted from `JointAnalyticity.lean`:

* `magnetizationΛ_latticeGraph_analyticAt_joint`,
* `magnetizationΛ_latticeGraph_analyticOnNhd_joint`,
* `susceptibilityΛ_latticeGraph_analyticAt_joint`,
* `susceptibilityΛ_latticeGraph_analyticOnNhd_joint`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: magnetizationΛ jointly AnalyticAt**. -/
theorem magnetizationΛ_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) :=
  Ambient.magnetizationΛ_analyticAt_joint (IsingModel.latticeGraph d) Λ i β J h

/-- **ℤ^d Λ: magnetizationΛ jointly AnalyticOnNhd**. -/
theorem magnetizationΛ_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  Ambient.magnetizationΛ_analyticOnNhd_joint (IsingModel.latticeGraph d) Λ i

/-- **ℤ^d Λ: susceptibilityΛ jointly AnalyticAt**. -/
theorem susceptibilityΛ_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      (β, J, h) :=
  Ambient.susceptibilityΛ_analyticAt_joint (IsingModel.latticeGraph d) Λ i β J h

/-- **ℤ^d Λ: susceptibilityΛ jointly AnalyticOnNhd**. -/
theorem susceptibilityΛ_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (i : ↑Λ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ ⟨p.2.1, p.2.2, p.1⟩ i)
      Set.univ :=
  Ambient.susceptibilityΛ_analyticOnNhd_joint (IsingModel.latticeGraph d) Λ i

end Ambient
end IsingModel
