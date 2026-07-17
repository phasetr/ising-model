import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetizationΛ Λ-direct trivial-slice wrappers

Narrow child module for three ℤ^d
`magnetizationΛ_latticeGraph_*` Λ-direct trivial-slice wrappers
extracted from `UniformMagMagnetizationTrivial.lean`:

* `magnetizationΛ_latticeGraph_h_zero`,
* `magnetizationΛ_latticeGraph_beta_zero`,
* `magnetizationΛ_latticeGraph_zero_params`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationΛ at h = 0 vanishes (Z₂)**. -/
theorem magnetizationΛ_latticeGraph_h_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_h_zero (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d magnetizationΛ vanishes at β=0**. -/
theorem magnetizationΛ_latticeGraph_beta_zero
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d magnetizationΛ vanishes at J=h=0**. -/
theorem magnetizationΛ_latticeGraph_zero_params
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β : ℝ) (i : ↑Λ) :
    magnetizationΛ (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) i = 0 :=
  magnetizationΛ_zero_params (IsingModel.latticeGraph d) Λ β i

end Ambient
end IsingModel
