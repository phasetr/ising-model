import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.FreeEnergy

/-!
# Concrete finite-volume partition-function wrappers

Narrow child module for direct concrete `latticeGraph` finite-volume
`partitionFunction` monotonicity, trivial-slice, and h-symmetry wrappers. The
theorem names are the same as the former legacy declarations, but callers can
now avoid importing the monolithic concrete legacy module.
-/

namespace IsingModel
namespace Ambient

/-! ### ℤ^d direct finite-volume partition-function wrappers -/

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

/-- **ℤ^d partitionFunction_J_zero direct** at Λ-induced:
`Z_Λ at ⟨0, h, β⟩ = (2·cosh(β·h))^|Λ|`. -/
theorem partitionFunction_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ)
      = (2 * Real.cosh (β * h)) ^ Fintype.card (↑Λ : Type _) :=
  IsingModel.partitionFunction_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-- **ℤ^d partitionFunction_beta_zero direct** at Λ-induced:
`Z_Λ at ⟨J, h, 0⟩ = |Config Λ| = 2^|Λ|`. -/
theorem partitionFunction_beta_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ)
      = (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) :=
  IsingModel.partitionFunction_beta_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h

/-- **ℤ^d partitionFunction_zero_params direct** at Λ-induced:
`Z_Λ at ⟨0, 0, β⟩ = |Config Λ|`. -/
theorem partitionFunction_zero_params_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ)
      = (Fintype.card (IsingModel.Config (↑Λ : Type _)) : ℝ) :=
  IsingModel.partitionFunction_zero_params
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β

/-- **ℤ^d partitionFunction_neg_h direct** at Λ-induced:
`Z_Λ at ⟨J, -h, β⟩ = Z_Λ at ⟨J, h, β⟩`. -/
theorem partitionFunction_neg_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β : ℝ) :
    IsingModel.partitionFunction
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, -h, β⟩ : IsingParams ℝ)
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.partitionFunction_neg_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β

end Ambient
end IsingModel
