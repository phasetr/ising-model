import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanh

/-!
# ℤ^d AlongExhaustion Mayer tanh regularity wrappers

Narrow child module for four ℤ^d
`mayerPartialSumAlongExhaustion_latticeGraph_tanh_*` regularity
wrappers extracted from `MayerVdRegularityTanh.lean`:

* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_beta`,
* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_continuous_J`,
* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_beta`,
* `mayerPartialSumAlongExhaustion_latticeGraph_tanh_differentiable_J`.

Each result is a thin pass-through of the ambient
`Ambient.mayerPartialSumAlongExhaustion_tanh_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `MayerVdRegularityTanh` declarations.
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
