import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityTanhExpansionTerm

/-!
# Concrete `mayerExpansionTermAlongExhaustion` tanh regularity wrappers

Narrow child module for four ℤ^d
`mayerExpansionTermAlongExhaustion_latticeGraph_tanh_*` regularity
wrappers (`continuous_beta`, `continuous_J`, `differentiable_beta`,
`differentiable_J`). Each wrapper is a thin pass-through to the
corresponding
ambient `mayerExpansionTermAlongExhaustion_tanh_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Continuous (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ k J n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Continuous (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ k β n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem
mayerExpansionTermAlongExhaustion_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (J : ℝ) (n : ℕ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ k J n

/-- **ℤ^d along-ex: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (β : ℝ) (n : ℕ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTermAlongExhaustion_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ k β n

end Ambient
end IsingModel
