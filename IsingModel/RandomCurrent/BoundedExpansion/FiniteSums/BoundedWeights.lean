import IsingModel.RandomCurrent.Core

/-!
# Bounded random-current finite sums

Mechanical child split from `RandomCurrent/BoundedExpansion.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

abbrev CurrentBounded (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :=
  (e : (inducedGraph G Λ).edgeSet) → Fin (N + 1)

/-- **Coercion `CurrentBounded → Current`**: forget the bound
on each edge value. -/
def CurrentBounded.toCurrent (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] {N : ℕ}
    (n : CurrentBounded G Λ N) : Current G Λ :=
  fun e => (n e).val

/-- **Finite weight sum over A-source bounded currents**:
`∑ n : CurrentBounded G Λ N, if n.toCurrent.sources = A then n.toCurrent.weight β J else 0`.
Unlike `Current.weightSum` (which uses `tsum`), this is a plain
`Finset.sum` since `CurrentBounded G Λ N` is automatically
`Fintype`. Used as the truncated approximant; the limit
`N → ∞` gives the unbounded `Current.weightSum`. -/
noncomputable def CurrentBounded.weightSum (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) (A : Finset ↑Λ) (β J : ℝ) : ℝ :=
  ∑ n : CurrentBounded G Λ N,
    if (n.toCurrent G Λ).sources G Λ = A
      then (n.toCurrent G Λ).weight G Λ β J
      else 0

omit [DecidableEq V] in
/-- **Bounded weight sum is nonneg under nonneg coupling**: each
summand is either `0` or a nonneg weight; `Finset.sum_nonneg`
finishes. -/
theorem CurrentBounded.weightSum_nonneg (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    0 ≤ CurrentBounded.weightSum G Λ N A β J := by
  unfold CurrentBounded.weightSum
  refine Finset.sum_nonneg (fun n _ => ?_)
  by_cases h : (n.toCurrent G Λ).sources G Λ = A
  · simp [h, Current.weight_nonneg G Λ hβJ (n.toCurrent G Λ)]
  · simp [h]


end Ambient
end IsingModel
