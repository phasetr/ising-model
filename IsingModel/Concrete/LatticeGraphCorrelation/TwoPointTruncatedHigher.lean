import IsingModel.PhaseTransition
import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED

/-!
# ℤ^d truncated3/4Infinite_latticeGraph trivial-slice wrappers

Narrow child module for 18 ℤ^d `truncated3Infinite_latticeGraph_*`
and `truncated4Infinite_latticeGraph_*` trivial-slice + nonpos +
exhaustion-independence wrappers (β = 0, J = 0 with various
coincidence patterns, h = 0, nonpos, `_indep_exhaustion`).
Theorem names are unchanged from the former `TwoPoint`
declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d truncated3Infinite β=0 site-wise**: `= 0`. -/
theorem truncated3Infinite_latticeGraph_beta_zero
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J h : ℝ)
    (i j k : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) i j k = 0 :=
  truncated3Infinite_beta_zero (IsingModel.latticeGraph d) Λ J h i j k

/-! ## Moved: truncated3Infinite J=0 trivial-slice wrappers

The three wrappers
`truncated3Infinite_latticeGraph_J_zero_of_pairwise_distinct`,
`truncated3Infinite_latticeGraph_J_zero_of_pair_coincidence`,
`truncated3Infinite_latticeGraph_J_zero_all_coincident` now live in
`TwoPointTruncatedHigherJZero.lean`. -/


/-! ## Moved: truncated4Infinite trivial-slice wrappers

The six `truncated4Infinite_latticeGraph_*` trivial-slice wrappers
(β = 0 and J = 0 under various coincidence patterns) now live in
`TwoPointTruncatedHigherTruncated4.lean`. -/

/-- **ℤ^d truncated3Infinite h=0 pair coincidence** (#750):
`truncated3Infinite ⟨J,0,β⟩ i i k = correlationInfinite ⟨J,0,β⟩ {i,k}`
for `i ≠ k` (any Exhaustion). -/
theorem truncated3Infinite_latticeGraph_h_zero_of_pair_coincidence
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    {i k : Fin d → ℤ} (hik : i ≠ k) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i i k
      = correlationInfinite (IsingModel.latticeGraph d) Λ
          (⟨J, 0, β⟩ : IsingParams ℝ) {i, k} :=
  truncated3Infinite_h_zero_of_pair_coincidence
    (IsingModel.latticeGraph d) Λ J β hik

/-- **ℤ^d truncated3Infinite h=0 all-coincident vanishes** (#750). -/
theorem truncated3Infinite_latticeGraph_h_zero_all_coincident
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ)) (J β : ℝ)
    (i : Fin d → ℤ) :
    truncated3Infinite (IsingModel.latticeGraph d) Λ
        (⟨J, 0, β⟩ : IsingParams ℝ) i i i = 0 :=
  truncated3Infinite_h_zero_all_coincident
    (IsingModel.latticeGraph d) Λ J β i

/-! ## Moved: truncated3/4Infinite nonpos + h_zero_of_distinct wrappers

The three wrappers
`truncated3Infinite_latticeGraph_nonpos`,
`truncated4Infinite_latticeGraph_nonpos_h_zero`,
`truncated3Infinite_latticeGraph_h_zero_of_distinct` now live in
`TwoPointTruncatedHigherNonpos.lean`. -/


/-! ## Moved: truncated{2,3,4}Infinite exhaustion-independence wrappers

The three wrappers
`truncated{2,3,4}Infinite_latticeGraph_indep_exhaustion`
now live in `TwoPointTruncatedHigherIndepExhaustion.lean`. -/



end Ambient

end IsingModel
