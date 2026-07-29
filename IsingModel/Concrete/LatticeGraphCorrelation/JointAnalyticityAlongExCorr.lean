import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticity

/-!
# Concrete AlongExhaustion correlation joint analyticity

Narrow child module for two ℤ^d
`correlationAlongExhaustion_latticeGraph_analytic{At,OnNhd}_joint`
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

end Ambient
end IsingModel
