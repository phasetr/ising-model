import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `correlationInfinite_latticeGraph_*` trivial-slice wrappers

Narrow child module for three ℤ^d
`correlationInfinite_latticeGraph_*` trivial-slice wrappers extracted
from `UniformMagBoundsMonotonicity.lean`:

* `correlationInfinite_latticeGraph_J_zero`,
* `correlationInfinite_latticeGraph_beta_zero_vanish`,
* `correlationInfinite_latticeGraph_zero_params_vanish`.

Each result is a thin pass-through of the ambient
`Ambient.correlationInfinite_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `UniformMagBoundsMonotonicity` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d correlationInfinite at J = 0 general-A closed form** (ferromagnetic):
`correlationInfinite (latticeGraph d) Λ ⟨0, h, β⟩ A = tanh(β·h)^|A|`. -/
theorem correlationInfinite_latticeGraph_J_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (A : Finset (Fin d → ℤ)) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) A
      = Real.tanh (β * h) ^ A.card :=
  correlationInfinite_J_zero (IsingModel.latticeGraph d) Λ h β hf A

/-- **ℤ^d correlationInfinite at β = 0 vanishes** for nonempty A. -/
theorem correlationInfinite_latticeGraph_beta_zero_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) A = 0 :=
  correlationInfinite_beta_zero_vanish (IsingModel.latticeGraph d) Λ J h A hA

/-- **ℤ^d correlationInfinite at J=h=0 vanishes** for nonempty A. -/
theorem correlationInfinite_latticeGraph_zero_params_vanish
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (β : ℝ)
    (A : Finset (Fin d → ℤ)) (hA : A.Nonempty) :
    correlationInfinite (IsingModel.latticeGraph d) Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) A = 0 :=
  correlationInfinite_zero_params_vanish (IsingModel.latticeGraph d) Λ β A hA

end Ambient

end IsingModel
