import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity

/-!
# ℤ^d analyticity of the Mayer partial sum at the `tanh` activity

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the analyticity of `mayerPartialSum` of the stage-`n` induced subgraph evaluated
at the activity `tanh (β * J)`, separately in the inverse temperature with the coupling fixed
and in the coupling with the inverse temperature fixed: `AnalyticAt ℝ` at an arbitrary point
of the varying parameter, and `AnalyticOnNhd ℝ` on `Set.univ`. No sign condition on either
parameter is imposed.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticAt in β**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J β : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) β :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticAt_beta
    (IsingModel.latticeGraph d) Λ N J β n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticAt in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β J : ℝ) (n : ℕ) :
    AnalyticAt ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) J :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticAt_J
    (IsingModel.latticeGraph d) Λ N β J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) AnalyticOnNhd
Set.univ in β**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_beta
    (IsingModel.latticeGraph d) Λ N J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) AnalyticOnNhd
Set.univ in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) Set.univ :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_analyticOnNhd_J
    (IsingModel.latticeGraph d) Λ N β n

end Ambient
end IsingModel
