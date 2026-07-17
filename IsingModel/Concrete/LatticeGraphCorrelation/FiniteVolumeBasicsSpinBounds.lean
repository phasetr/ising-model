import IsingModel.InfiniteVolume.Boundedness

/-!
# ℤ^d spinProduct nonneg / abs wrappers

Narrow child module for three ℤ^d spinProduct sign/bound wrappers
extracted from `FiniteVolumeBasicsSpin.lean`:

* `one_sub_spinProduct_nonneg_latticeGraph`,
* `abs_spinProduct_eq_one_latticeGraph`,
* `abs_spinProduct_le_one_latticeGraph`.

Each result is a thin pass-through of the corresponding abstract
`IsingModel.*_spinProduct_*` lemma. The theorem names are unchanged
from the former `FiniteVolumeBasicsSpin` declarations.
-/

open scoped symmDiff

namespace IsingModel
namespace Ambient

/-- **ℤ^d one_sub_spinProduct_nonneg at Λ-induced**: `0 ≤ 1 - σ^B`. -/
theorem one_sub_spinProduct_nonneg_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (B : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    0 ≤ 1 - IsingModel.spinProduct B σ :=
  IsingModel.one_sub_spinProduct_nonneg B σ

/-- **ℤ^d abs_spinProduct_eq_one at Λ-induced**: `|σ^A| = 1`. -/
theorem abs_spinProduct_eq_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.spinProduct A σ| = 1 :=
  IsingModel.abs_spinProduct_eq_one A σ

/-- **ℤ^d abs_spinProduct_le_one at Λ-induced**: `|σ^A| ≤ 1`. -/
theorem abs_spinProduct_le_one_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (A : Finset (↑Λ : Type _)) (σ : IsingModel.Config (↑Λ : Type _)) :
    |IsingModel.spinProduct A σ| ≤ 1 :=
  IsingModel.abs_spinProduct_le_one A σ

end Ambient
end IsingModel
