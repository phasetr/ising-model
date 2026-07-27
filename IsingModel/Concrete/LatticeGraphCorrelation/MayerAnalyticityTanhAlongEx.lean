import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity

/-!
# ℤ^d AlongExhaustion mayerPartialSum tanh analyticity wrappers

Narrow child module for four ℤ^d
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_analytic*` wrappers:

* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_beta`,
* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticAt_J`,
* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_beta`,
* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_analyticOnNhd_J`.

Each result is a thin pass-through of the ambient
`Ambient.mayerPartialSumAlongExhaustion_tanh_*` lemma at
`G := IsingModel.latticeGraph d`.
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
