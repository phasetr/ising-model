import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d `truncated4Infinite_latticeGraph_J_zero_*` coincidence wrappers

Narrow child module for three ℤ^d
`truncated4Infinite_latticeGraph_J_zero_*` higher coincidence
wrappers extracted from `TwoPointTruncatedHigherTruncated4.lean`:

* `truncated4Infinite_latticeGraph_J_zero_of_two_pair_coincidence` (#746),
* `truncated4Infinite_latticeGraph_J_zero_of_triple_coincidence` (#747),
* `truncated4Infinite_latticeGraph_J_zero_all_coincident` (#748).

Each result is a thin pass-through of the ambient
`Ambient.truncated4Infinite_J_zero_*` lemma at
`G := IsingModel.latticeGraph d`. The theorem names are unchanged
from the former `TwoPointTruncatedHigherTruncated4` declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d truncated4Infinite J=0 two-pair coincidence** (#746). -/
theorem truncated4Infinite_latticeGraph_J_zero_of_two_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i k k
      = -2 * Real.tanh (β * h) ^ 4 :=
  truncated4Infinite_J_zero_of_two_pair_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hik

/-- **ℤ^d truncated4Infinite J=0 triple coincidence** (#747):
`t² − 3·t³`. -/
theorem truncated4Infinite_latticeGraph_J_zero_of_triple_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    {i l : Fin d → ℤ} (hil : i ≠ l) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i l
      = Real.tanh (β * h) ^ 2 - 3 * Real.tanh (β * h) ^ 3 :=
  truncated4Infinite_J_zero_of_triple_coincidence
    (IsingModel.latticeGraph d) Λ h β hf hil

/-- **ℤ^d truncated4Infinite J=0 all-coincident** (#748): `t − 3·t²`. -/
theorem truncated4Infinite_latticeGraph_J_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (h β : ℝ)
    (hf : Ferromagnetic (⟨(0 : ℝ), h, β⟩ : IsingParams ℝ))
    (i : Fin d → ℤ) :
    truncated4Infinite (IsingModel.latticeGraph d) Λ
        (⟨0, h, β⟩ : IsingParams ℝ) i i i i
      = Real.tanh (β * h) - 3 * Real.tanh (β * h) ^ 2 :=
  truncated4Infinite_J_zero_all_coincident
    (IsingModel.latticeGraph d) Λ h β hf i

end Ambient
end IsingModel
