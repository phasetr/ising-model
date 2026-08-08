import IsingModel.FreeEnergy
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# Parameter monotonicity of the finite-volume partition function in ℤ^d

Records that the partition function of the subgraph induced by the nearest-neighbor lattice
graph on a finite `Λ ⊆ ℤ^d` increases when the coupling, the external field or the inverse
temperature is increased with the other two held fixed. Each statement assumes
nonnegativity of the two parameters held fixed, strengthened to strict positivity when the
inverse temperature is one of them, together with nonnegativity of the smaller of the two
compared values, again strict for the inverse-temperature comparison.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d partitionFunction_monotone_h direct** at Λ-induced (ferromagnetic). -/
theorem partitionFunction_monotone_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (h₁ h₂ : ℝ) (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β hJ hβ h₁ h₂ hh₁ hh

/-- **ℤ^d partitionFunction_monotone_J direct** at Λ-induced (ferromagnetic). -/
theorem partitionFunction_monotone_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β)
    (J₁ J₂ : ℝ) (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J₁, h, β⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J₂, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β hh hβ J₁ J₂ hJ₁ hJ

/-- **ℤ^d partitionFunction_monotone_beta direct** at Λ-induced (ferromagnetic). -/
theorem partitionFunction_monotone_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h)
    (β₁ β₂ : ℝ) (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, β₁⟩ : IsingParams ℝ)
      ≤ IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β₂⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_monotone_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h hJ hh β₁ β₂ hβ₁ hβ

end Ambient
end IsingModel
