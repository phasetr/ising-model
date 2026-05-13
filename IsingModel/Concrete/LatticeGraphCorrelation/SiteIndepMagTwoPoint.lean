import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPointCorrelationInfinite
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.TranslationInvariance
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag

/-!
# ℤ^d two-point function bounds + symmetry wrappers

Narrow child module for 17 ℤ^d two-point / `truncated2TwoPoint` /
`truncated3TwoPoint` / `truncated4TwoPoint` bounds, trivial slices,
monotonicity, and symmetry wrappers. Theorem names are unchanged
from the former `SiteIndepMag` declarations.
-/

namespace IsingModel
namespace Ambient

/-! ## Basic bounds on the ℤ^d two-point functions -/

/-- **Nonnegativity of `twoPointFunction`** (GKS-I).
`0 ≤ twoPointFunction d p r`. -/
theorem twoPointFunction_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (r : Fin d → ℤ) :
    0 ≤ twoPointFunction d p r :=
  correlationInfinite_nonneg (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf {(0 : Fin d → ℤ), r}

/-- **Upper bound on `twoPointFunction`** (boundedness of correlation).
`twoPointFunction d p r ≤ 1`. -/
theorem twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ≤ 1 :=
  correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`-1 ≤ twoPointFunction`** unconditionally. Direct specialization
of `neg_one_le_correlationInfinite` at `A = {0, r}`. -/
theorem neg_one_le_twoPointFunction
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    -1 ≤ twoPointFunction d p r :=
  neg_one_le_correlationInfinite (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **ℤ^d `twoPointFunction ≥ tanh(β·h)²` for `r ≠ 0`** (ferromagnetic):
specialization of `correlationInfinite_ge_tanh_pow_card` at `A = {0, r}`
where `A.card = 2` (since `r ≠ 0`). -/
theorem twoPointFunction_ge_tanh_sq_of_ne
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    {r : Fin d → ℤ} (hr : r ≠ 0) :
    Real.tanh (β * h) ^ 2 ≤ twoPointFunction d (⟨J, h, β⟩ : IsingParams ℝ) r := by
  have hcard : ({(0 : Fin d → ℤ), r} : Finset (Fin d → ℤ)).card = 2 := by
    rw [Finset.card_pair (Ne.symm hr)]
  have := correlationInfinite_ge_tanh_pow_card (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ ({(0 : Fin d → ℤ), r} : Finset _)
  rw [hcard] at this
  exact this

/-- **`|twoPointFunction| ≤ 1`** unconditionally. Direct specialization
of `abs_correlationInfinite_le_one` at `A = {0, r}`. -/
theorem abs_twoPointFunction_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    |twoPointFunction d p r| ≤ 1 :=
  abs_correlationInfinite_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction² ≤ 1`** unconditionally. Direct specialization
of `correlationInfinite_sq_le_one` at `A = {0, r}`. -/
theorem twoPointFunction_sq_le_one
    (d : ℕ) (p : IsingParams ℝ) (r : Fin d → ℤ) :
    twoPointFunction d p r ^ 2 ≤ 1 :=
  correlationInfinite_sq_le_one (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p {(0 : Fin d → ℤ), r}

/-- **`twoPointFunction` at `h = 0, r = 0` vanishes** (Z₂ via
`twoPointFunction_zero` + `magnetizationInfinite_zero_at_h_zero`):
`twoPointFunction d ⟨J, 0, β⟩ 0 = 0`. -/
theorem twoPointFunction_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    twoPointFunction d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [twoPointFunction_zero,
      magnetizationInfinite_zero_at_h_zero]

/-- **`truncated2TwoPoint` at `h = 0, r = 0` vanishes**: at `r = 0`,
`truncated2TwoPoint = M · (1 − M)`; at `h = 0`, `M = 0` by Z₂, so the
product is `0`. -/
theorem truncated2TwoPoint_h_zero_at_zero (d : ℕ) (J β : ℝ) :
    truncated2TwoPoint d (⟨J, 0, β⟩ : IsingParams ℝ) 0 = 0 := by
  rw [truncated2TwoPoint_zero,
      magnetizationInfinite_zero_at_h_zero]
  ring

/-! ## Moved: twoPointFunction monotone wrappers

The three wrappers `twoPointFunction_monotone_{J,h,beta}` now live in
`SiteIndepMagTwoPointMonotone.lean`. -/

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

/-! ## Moved: truncated4TwoPoint symmetry wrappers

The three wrappers `truncated4TwoPoint_symm_{rs,su,ru}` now live in
`SiteIndepMagTwoPointTruncated4Symm.lean`. -/

end Ambient

end IsingModel
