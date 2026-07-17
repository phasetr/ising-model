import IsingModel.AmbientLattice.AnalyticityLambdaMayer
import IsingModel.Lattice

/-!
# Concrete `mayerExpansionTerm_Λ` tanh regularity wrappers

Narrow child module for four ℤ^d
`mayerExpansionTerm_Λ_latticeGraph_tanh_*` regularity wrappers
(`continuous_beta`, `continuous_J`, `differentiable_beta`,
`differentiable_J`). Each wrapper is a thin pass-through to the
corresponding ambient `mayerExpansionTerm_Λ_tanh_*` lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (·*J) continuous in β**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_continuous_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (J : ℝ) :
    Continuous (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_continuous_beta
    (IsingModel.latticeGraph d) Λ n J

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (β*·) continuous in J**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (β : ℝ) :
    Continuous (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_continuous_J
    (IsingModel.latticeGraph d) Λ n β

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (·*J) differentiable in β**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_differentiable_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (J : ℝ) :
    Differentiable ℝ (fun β' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β' * J))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_differentiable_beta
    (IsingModel.latticeGraph d) Λ n J

/-- **ℤ^d Λ: mayerExpansionTerm ∘ tanh ∘ (β*·) differentiable in J**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_tanh_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) (β : ℝ) :
    Differentiable ℝ (fun J' : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n
        (Real.tanh (β * J'))) :=
  Ambient.mayerExpansionTerm_Λ_tanh_differentiable_J
    (IsingModel.latticeGraph d) Λ n β

end Ambient
end IsingModel
