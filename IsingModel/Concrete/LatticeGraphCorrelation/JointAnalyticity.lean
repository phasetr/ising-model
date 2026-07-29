import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityPartitionFreeEnergy

/-!
# Concrete joint analyticity wrappers for the lattice graph

Narrow child module for ℤ^d `AnalyticAt` / `AnalyticOnNhd` forwarders in the
joint `(β, J, h)` parameters. The theorem names are the same as the former
former declarations, but callers can now import this child module directly.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d joint AnalyticAt + AnalyticOnNhd wrappers
(partitionFunction / freeEnergy) along-ex -/

/-! ## Moved: AlongEx correlation joint analyticity

The two wrappers
`correlationAlongExhaustion_latticeGraph_analytic{At,OnNhd}_joint`
now live in `JointAnalyticityAlongExCorr.lean`. -/

/-- **ℤ^d along-ex: partitionFunctionAlongExhaustion jointly AnalyticAt**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  Ambient.partitionFunctionAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ n β J h

/-- **ℤ^d along-ex: partitionFunctionAlongExhaustion jointly AnalyticOnNhd**. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  Ambient.partitionFunctionAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: freeEnergyAlongExhaustion jointly AnalyticAt**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticAt_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  Ambient.freeEnergyAlongExhaustion_analyticAt_joint
    (IsingModel.latticeGraph d) Λ n β J h

/-- **ℤ^d along-ex: freeEnergyAlongExhaustion jointly AnalyticOnNhd**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_analyticOnNhd_joint
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      Ambient.freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  Ambient.freeEnergyAlongExhaustion_analyticOnNhd_joint
    (IsingModel.latticeGraph d) Λ n

end Ambient
end IsingModel
