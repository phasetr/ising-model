import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d magnetizationInfinite trivial-slice wrappers

Narrow child module for three ℤ^d
`magnetizationInfinite_latticeGraph_*` trivial-slice wrappers
extracted from `UniformMagCorrelationTrivial.lean`:

* `magnetizationInfinite_latticeGraph_zero_at_h_zero`,
* `magnetizationInfinite_latticeGraph_beta_zero`,
* `magnetizationInfinite_latticeGraph_J_zero`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d magnetizationInfinite at h = 0 site-wise**:
`magnetizationInfinite (latticeGraph d) Λ ⟨J, 0, β⟩ i = 0`. -/
theorem magnetizationInfinite_latticeGraph_zero_at_h_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, 0, β⟩ i = 0 :=
  magnetizationInfinite_zero_at_h_zero (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d magnetizationInfinite at β = 0 site-wise**. -/
theorem magnetizationInfinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨J, h, 0⟩ i = 0 :=
  magnetizationInfinite_beta_zero (IsingModel.latticeGraph d) Λ J h i

/-- **ℤ^d magnetizationInfinite at J = 0 site-wise** (ferromagnetic). -/
theorem magnetizationInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    magnetizationInfinite (IsingModel.latticeGraph d) Λ ⟨0, h, β⟩ i
      = Real.tanh (β * h) :=
  magnetizationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf i

end Ambient
end IsingModel
