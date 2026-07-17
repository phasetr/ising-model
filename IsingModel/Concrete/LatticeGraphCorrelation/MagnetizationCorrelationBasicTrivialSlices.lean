import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d correlation trivial-slice wrappers on `latticeGraph d`

Narrow child module for the four ℤ^d `correlation_*_latticeGraph`
trivial-slice wrappers extracted from `MagnetizationCorrelationBasic`:

* `correlation_beta_zero_vanish_of_nonempty_A_latticeGraph`,
* `correlation_zero_params_vanish_of_nonempty_A_latticeGraph`,
* `correlation_J_zero_latticeGraph`,
* `correlation_empty_latticeGraph`.

Each result is a thin pass-through of the abstract
`IsingModel.correlation_*` lemma on
`Ambient.inducedGraph (IsingModel.latticeGraph d) Λ`. The theorem
names are unchanged from the former `MagnetizationCorrelationBasic`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlation_beta_zero_vanish_of_nonempty_A direct** (Λ-induced):
`⟨σ^A⟩ at ⟨J, h, 0⟩ = 0` for nonempty `A`. -/
theorem correlation_beta_zero_vanish_of_nonempty_A_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_beta_zero_vanish_of_nonempty_A
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h A hA

/-- **ℤ^d correlation_zero_params_vanish_of_nonempty_A direct** (Λ-induced):
`⟨σ^A⟩ at ⟨0, 0, β⟩ = 0` for nonempty `A`. -/
theorem correlation_zero_params_vanish_of_nonempty_A_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ)
    (A : Finset (↑Λ : Type _)) (hA : A.Nonempty) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  IsingModel.correlation_zero_params_vanish_of_nonempty_A
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β A hA

/-- **ℤ^d correlation_J_zero direct at Λ-induced**:
`⟨σ^A⟩ at ⟨0, h, β⟩ = tanh(βh)^|A|`. -/
theorem correlation_J_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ)
    (A : Finset (↑Λ : Type _)) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  IsingModel.correlation_J_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β A

/-- **ℤ^d correlation_empty at Λ-induced**: `⟨σ^∅⟩_Λ = 1`. -/
theorem correlation_empty_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.correlation
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p ∅ = 1 :=
  IsingModel.correlation_empty
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

end Ambient

end IsingModel
