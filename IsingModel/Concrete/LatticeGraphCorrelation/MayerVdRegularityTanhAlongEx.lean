import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanh

/-!
# ℤ^d regularity of the Mayer partial sum at the `tanh` activity

Instantiates at `IsingModel.latticeGraph d`, at a stage `n` of an `Ambient.Exhaustion` of
`Fin d → ℤ`, the regularity of the Mayer partial sum of the stage-`n` induced subgraph
evaluated at the activity `tanh (β * J)`, separately in the inverse temperature with the
coupling fixed and in the coupling with the inverse temperature fixed: `Continuous` and
`Differentiable ℝ` in each direction. No sign condition on either parameter is imposed.
-/

namespace IsingModel
namespace Ambient

open Finset Real

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ N J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ N β n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem
mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β' * J))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ N J n

/-- **ℤ^d along-ex: mayerPartialSum ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (N : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerPartialSum
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) N
        (Real.tanh (β * J'))) :=
  Ambient.mayerPartialSumAlongExhaustion_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ N β n

end Ambient

end IsingModel
