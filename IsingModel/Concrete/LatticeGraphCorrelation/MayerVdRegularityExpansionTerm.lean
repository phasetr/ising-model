import IsingModel.Lattice
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityDifferentiableExpansionTerm
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularityExpansionTerm

/-!
# ℤ^d §18.6 mayerExpansionTerm regularity wrappers

Narrow child module for four ℤ^d
`mayerExpansionTerm_{Λ,AlongExhaustion}_latticeGraph_{continuous,differentiable}`
wrappers extracted from `MayerVdRegularity.lean`. Each wrapper is a thin
pass-through to the corresponding ambient lemma at
`IsingModel.latticeGraph d`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d Λ: mayerExpansionTerm Continuous**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_continuous
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n t) :=
  Ambient.mayerExpansionTerm_Λ_continuous
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d Λ: mayerExpansionTerm Differentiable ℝ**. -/
theorem mayerExpansionTerm_Λ_latticeGraph_differentiable
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) Λ) n t) :=
  Ambient.mayerExpansionTerm_Λ_differentiable
    (IsingModel.latticeGraph d) Λ n

/-- **ℤ^d along-ex: mayerExpansionTerm Continuous**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_continuous
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Continuous (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k t) :=
  Ambient.mayerExpansionTermAlongExhaustion_continuous
    (IsingModel.latticeGraph d) Λ k n

/-- **ℤ^d along-ex: mayerExpansionTerm Differentiable ℝ**. -/
theorem mayerExpansionTermAlongExhaustion_latticeGraph_differentiable
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (inducedGraph (IsingModel.latticeGraph d)
      (Λ.volume n)).edgeSet]
    (k : ℕ) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ => IsingModel.mayerExpansionTerm
        (inducedGraph (IsingModel.latticeGraph d) (Λ.volume n)) k t) :=
  Ambient.mayerExpansionTermAlongExhaustion_differentiable
    (IsingModel.latticeGraph d) Λ k n

end Ambient
end IsingModel
