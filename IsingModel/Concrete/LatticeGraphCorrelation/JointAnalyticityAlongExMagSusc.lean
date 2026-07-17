import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityMagnetization
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticitySusceptibility

/-!
# ℤ^d AlongExhaustion joint mag + susc analyticity wrappers

Narrow child module for four ℤ^d AlongExhaustion joint
`Analytic{At,OnNhd}` wrappers extracted from
`JointAnalyticityAlongExCorr.lean`:

* `magnetizationAlongExhaustion_latticeGraph_analyticAt_joint`,
* `magnetizationAlongExhaustion_latticeGraph_analyticOnNhd_joint`,
* `susceptibilityAlongExhaustion_latticeGraph_analyticAt_joint`,
* `susceptibilityAlongExhaustion_latticeGraph_analyticOnNhd_joint`.

Each result is a thin pass-through of the corresponding ambient
`{magnetization,susceptibility}AlongExhaustion_analytic*_joint*`
lemma at `G := IsingModel.latticeGraph d`. The theorem names are
unchanged from the former `JointAnalyticityAlongExCorr` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly AnalyticAt**. -/
theorem magnetizationAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) :=
  Ambient.magnetizationAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ i n β J h

/-- **ℤ^d along-ex: magnetizationAlongExhaustion jointly AnalyticOnNhd**. -/
theorem magnetizationAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.magnetizationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  Ambient.magnetizationAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ i n

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly AnalyticAt**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) (β, J, h) :=
  Ambient.susceptibilityAlongExhaustion_analyticAt_joint_gen
    (IsingModel.latticeGraph d) Λ i n β J h

/-- **ℤ^d along-ex: susceptibilityAlongExhaustion jointly AnalyticOnNhd**. -/
theorem susceptibilityAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (i : Fin d → ℤ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.susceptibilityAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ i n) Set.univ :=
  Ambient.susceptibilityAlongExhaustion_analyticOnNhd_joint_gen
    (IsingModel.latticeGraph d) Λ i n

end Ambient
end IsingModel
