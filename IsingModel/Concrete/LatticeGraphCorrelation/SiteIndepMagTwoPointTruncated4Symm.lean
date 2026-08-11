import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance

/-!
# Symmetry of the ℤ^d four-point truncated function in its three free sites

`truncated4TwoPoint d p r s u` is `truncated4Infinite` of `IsingModel.latticeGraph d` along the
cubic exhaustion of `Fin d → ℤ`, at an arbitrary parameter record `p : IsingParams ℝ`, with the
first of its four sites pinned to the origin and the remaining three given by `r`, `s` and `u`.
That truncation subtracts from the infinite-volume correlation of `{0, r, s, u}` the three
products of pair correlations formed by the pairings of those four sites.

Since the truncation is symmetric under permuting the four sites, its value is unchanged by
exchanging `r` with `s`, by exchanging `s` with `u`, and by exchanging `r` with `u`. The first
two act on adjacent slots and are proved by unfolding to the underlying correlations and
rewriting the unordered site sets, the pair products being permuted among themselves; the third
is obtained by composing the other two, on the first pair of slots, then the last pair, then the
first pair again.
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
