import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance

/-!
# ℤ^d truncated4TwoPoint symmetry wrappers

Narrow child module for three ℤ^d `truncated4TwoPoint_symm_{rs,su,ru}`
symmetry wrappers. Each statement is proved by `unfold` +
`Finset` extensionality.
-/

namespace IsingModel
namespace Ambient

/-- **Symmetry of `truncated4TwoPoint` under `(r, s)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p s r u`.

From the Lebowitz 4-point definition: swapping `j ↔ k` in
`truncated4Infinite ... i j k l` permutes the three pair-products,
yielding the same sum. -/
theorem truncated4TwoPoint_symm_rs
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p s r u := by
  unfold truncated4TwoPoint truncated4Infinite
  have h_quad : ({(0 : Fin d → ℤ), r, s, u} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), s, r, u} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h_rs : ({r, s} : Finset (Fin d → ℤ)) = {s, r} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_quad, h_rs]
  ring

/-- **Symmetry of `truncated4TwoPoint` under `(s, u)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p r u s`.

Same Lebowitz-permutation argument applied to swap of `k ↔ l`. -/
theorem truncated4TwoPoint_symm_su
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p r u s := by
  unfold truncated4TwoPoint truncated4Infinite
  have h_quad : ({(0 : Fin d → ℤ), r, s, u} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), r, u, s} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have h_su : ({s, u} : Finset (Fin d → ℤ)) = {u, s} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_quad, h_su]
  ring

/-- **Symmetry of `truncated4TwoPoint` under `(r, u)` swap**:
`truncated4TwoPoint d p r s u = truncated4TwoPoint d p u s r`. Derived by
chaining `_symm_rs`, `_symm_su`, `_symm_rs` to implement the transposition
`(r, u)` via adjacent swaps. -/
theorem truncated4TwoPoint_symm_ru
    (d : ℕ) (p : IsingParams ℝ) (r s u : Fin d → ℤ) :
    truncated4TwoPoint d p r s u = truncated4TwoPoint d p u s r := by
  rw [truncated4TwoPoint_symm_rs d p r s u,
      truncated4TwoPoint_symm_su d p s r u,
      truncated4TwoPoint_symm_rs d p s u r]


end Ambient
end IsingModel
