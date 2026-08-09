import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticity

/-!
# ℤ^d joint analyticity of the along-exhaustion correlation

Concrete `latticeGraph d` statements that, for a fixed finite subset of `Fin d → ℤ` and at a
fixed stage of an arbitrary `Ambient.Exhaustion`, the correlation of that subset is analytic
in the inverse temperature, the coupling and the external field jointly, read as a function
of the triple `(β, J, h)` — at a prescribed base triple, and on a neighbourhood of all of
`Set.univ`. Each requires a `Fintype` instance on the edge set induced at every stage, and
that instance is its entire requirement: no `Prop`-typed hypothesis is carried here.
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
