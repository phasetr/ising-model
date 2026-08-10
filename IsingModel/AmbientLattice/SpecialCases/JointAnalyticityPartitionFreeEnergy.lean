import IsingModel.AmbientLattice.Analyticity
import IsingModel.AmbientLattice.MagnetizationAlongExhaustion
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticityFreeEnergy

/-!
# Joint real-analyticity of the stage partition function in `(β, J, h)`

Stage-`n` statements for an ambient graph `G : SimpleGraph V` and an exhaustion `Λ` of `V`,
read on the induced subgraph of the finite volume `Λ.volume n`. Every statement takes
`DecidableEq V` and the stagewise `Fintype` instance on that subgraph's edge set, and carries
no Prop-valued hypothesis.

Reading the parameter triple as the point `(β, J, h) : ℝ × ℝ × ℝ`, the stage partition
function is real-analytic at every such point, and the same fact is packaged as
`AnalyticOnNhd ℝ · Set.univ`. Each statement is the finite-volume statement for the induced
subgraph of `Λ.volume n`, applied at that volume.
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]


/-- **Along-ex: partitionFunction jointly AnalyticAt**. -/
theorem partitionFunctionAlongExhaustion_analyticAt_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) (β J h : ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) (β, J, h) :=
  partitionFunctionΛ_analyticAt_joint G (Λ.volume n) β J h

/-- **Along-ex: partitionFunction jointly AnalyticOnNhd over Set.univ**. -/
theorem partitionFunctionAlongExhaustion_analyticOnNhd_joint
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (n : ℕ) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ × ℝ =>
      partitionFunctionAlongExhaustion G Λ ⟨p.2.1, p.2.2, p.1⟩ n) Set.univ :=
  partitionFunctionΛ_analyticOnNhd_joint G (Λ.volume n)

end Ambient
end IsingModel
