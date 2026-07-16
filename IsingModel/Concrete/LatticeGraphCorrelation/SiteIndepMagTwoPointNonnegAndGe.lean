import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointTruncated2EqSubMagSq

/-!
# ℤ^d twoPointFunction / truncated2TwoPoint nonneg / ge mag² / symm wrappers

Narrow child module for three ℤ^d wrappers extracted from
`SiteIndepMagTwoPoint.lean`:

* `truncated2TwoPoint_nonneg`,
* `twoPointFunction_ge_magnetization_sq`,
* `truncated3TwoPoint_symm_rs`.
-/

namespace IsingModel
namespace Ambient

/-- **Nonnegativity of `truncated2TwoPoint`** (GKS-II).
`0 ≤ truncated2TwoPoint d p r`. -/
theorem truncated2TwoPoint_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    0 ≤ truncated2TwoPoint d p r :=
  truncated2Infinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf 0 r

/-- **Two-point function bounded below by magnetization squared**:
for ferromagnetic `p` and any `r : Fin d → ℤ`,

`(magnetizationInfinite (latticeGraph d) (cubicExhaustion d) p 0)^2
  ≤ twoPointFunction d p r`.

Proof: from `truncated2TwoPoint_nonneg` (GKS-II) and the identity
`truncated2TwoPoint d p r = twoPointFunction d p r − M²` (PR #261),
we get `0 ≤ twoPointFunction d p r − M²`, hence `M² ≤ twoPointFunction
d p r`. This is a classical physical bound: the 2-point function at
infinite volume is at least as large as the squared magnetization. -/
theorem twoPointFunction_ge_magnetization_sq
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    (magnetizationInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p 0)^2
      ≤ twoPointFunction d p r := by
  have h_nonneg := truncated2TwoPoint_nonneg d p hf r
  have h_identity := truncated2TwoPoint_eq_twoPointFunction_sub_magnetization_sq
    d p hf r
  linarith [h_identity.symm ▸ h_nonneg]

/-- **Symmetry of `truncated3TwoPoint` under `(r, s)` swap**:
`truncated3TwoPoint d p r s = truncated3TwoPoint d p s r`.

Reduces to the pairwise-symmetry of the Ursell 3-point function in
its last two arguments, via unfolding and commutativity of the
relevant Finset literals and products. -/
theorem truncated3TwoPoint_symm_rs
    (d : ℕ) (p : IsingParams ℝ) (r s : Fin d → ℤ) :
    truncated3TwoPoint d p r s = truncated3TwoPoint d p s r := by
  unfold truncated3TwoPoint truncated3Infinite
  -- `{0, r, s} = {0, s, r}` (unordered).
  have h_triple : ({(0 : Fin d → ℤ), r, s} : Finset (Fin d → ℤ))
      = {(0 : Fin d → ℤ), s, r} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h_rs : ({r, s} : Finset (Fin d → ℤ)) = {s, r} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [h_triple, h_rs]
  ring

end Ambient
end IsingModel
