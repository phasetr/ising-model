import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticity

/-!
# Concrete AlongExhaustion correlation/mag/susc joint analyticity

Narrow child module for six ℤ^d
`{correlation,magnetization,susceptibility}AlongExhaustion_latticeGraph_analytic{At,OnNhd}_joint`
wrappers. Each wrapper is a thin pass-through to the corresponding
ambient `*AlongExhaustion_analytic*_joint` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly AnalyticAt**. -/
theorem correlationAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) (β, J, h) :=
  Ambient.correlationAlongExhaustion_analyticAt_joint_gen
    (IsingModel.latticeGraph d) Λ A n β J h

/-- **ℤ^d along-ex: correlationAlongExhaustion jointly AnalyticOnNhd**. -/
theorem correlationAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (A : Finset (Fin d → ℤ)) (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.correlationAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ A n) Set.univ :=
  Ambient.correlationAlongExhaustion_analyticOnNhd_joint_gen
    (IsingModel.latticeGraph d) Λ A n

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
