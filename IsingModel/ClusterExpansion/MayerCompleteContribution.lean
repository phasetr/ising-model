import IsingModel.ClusterExpansion.MayerRootComponent

/-!
# Mayer expansion contribution of a fully-incompatible cluster (GJ §18.4)

Builds on the Mayer `K_n` closed form
`alternatingConnectedSubgraphSum K_n = (-1)^(n-1)(n-1)!` and the resulting Ursell
coefficient `ϕ^T(ω) = (-1)^(n-1)/n` for a fully-incompatible polymer sequence
(`ursellCoefficient_complete_eq`). Here we record the absolute value of that
coefficient, its `n = 2` consistency with the pair Ursell value, and the factored
Mayer-term contribution of the complete (all pairwise incompatible) clusters.

These connect the combinatorial `K_n` identity to the actual cluster expansion
`log Ξ = ∑_{n ≥ 1} ∑_ω ϕ^T(ω) z(ω)` of Glimm–Jaffe §18.4.
-/

namespace IsingModel

open Finset

/-- **Absolute Ursell coefficient of a complete cluster**: for `n` pairwise
incompatible polymers, `|ϕ^T(ω)| = 1/n`. Immediate from
`ursellCoefficient_complete_eq` since `|(-1)^(n-1)| = 1` and `n > 0`. -/
theorem ursellCoefficient_complete_abs_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ω : Fin n → Finset (Sym2 ι)}
    (hn : 1 ≤ n) (h : ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)) :
    |ursellCoefficient ω| = 1 / (n : ℝ) := by
  rw [ursellCoefficient_complete_eq hn h, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by exact_mod_cast (show 0 < n by omega))]

/-- **`n = 2` consistency**: a pair of incompatible polymers (`Fin 2`) has
`ϕ^T(ω) = -1/2`, recovering `ursellCoefficient_pair_incompatible` from the
general complete-cluster formula `ursellCoefficient_complete_eq` (`(-1)^1/2`). -/
theorem ursellCoefficient_complete_eq_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ω : Fin 2 → Finset (Sym2 ι)}
    (h : PolymersIncompatible (ω 0) (ω 1)) :
    ursellCoefficient ω = -1 / 2 := by
  have hcomplete : ∀ i j : Fin 2, i ≠ j → PolymersIncompatible (ω i) (ω j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h
    · exact h.symm
    · exact absurd rfl hij
  rw [ursellCoefficient_complete_eq (by omega) hcomplete]
  norm_num

/-- **Mayer-term contribution of the complete clusters**: the part of the Mayer
expansion term over fully-incompatible polymer sequences factors the constant
Ursell coefficient `(-1)^(n-1)/n` out of the activity sum. With
`ursellCoefficient_complete_eq` every term shares the same coefficient, so the
sum collapses to `((-1)^(n-1)/n)·∑ z(ω)` over the complete clusters. -/
theorem mayerExpansionTerm_completeClusterSubsum_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
        ursellCoefficient ω * clusterSeqActivity t ω)
      = ((-1 : ℝ) ^ (n - 1) / (n : ℝ))
        * ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
            (fun ω => ∀ i j, i ≠ j → PolymersIncompatible (ω i) (ω j)),
            clusterSeqActivity t ω := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ω hω => ?_)
  rw [Finset.mem_filter] at hω
  rw [ursellCoefficient_complete_eq hn hω.2]

end IsingModel
