import IsingModel.ClusterExpansion.Penrose
import IsingModel.ClusterExpansion.MayerRootComponent

/-!
# Ursell tree bound from the Penrose inequality (GJ §18.4-18.5, Issue #3954)

Lifts the unconditional Penrose tree-graph inequality (milestone M1,
`Penrose.abs_alternatingConnectedSubgraphSum_le_numSpanningTrees`) to the Ursell
coefficient of a cluster sequence: the cluster weight is bounded by the spanning-tree
count of its incompatibility graph,
`|ϕ^T(ω)| ≤ numSpanningTrees (polymerSeqIncompatibilityGraph ω) / n!`, and uniformly by
the complete-graph spanning-tree count `numSpanningTrees (⊤ : SimpleGraph (Fin n)) / n!`.

This is the sharp replacement of the trivial `2^{|E|}/n!` bound
(`ursellCoefficient_abs_le_pow_div_factorial`) and the entry point of the
Kotecký–Preiss / tree-sum convergence (milestone M2): combined with a summable majorant
for the spanning-tree count (Cayley `n^{n-2}`, or the tree-sum induction), it yields
absolute convergence of the Mayer expansion.

## References
- Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4–18.5, pp. 378–386.
- Penrose tree-graph inequality (Brydges' lectures); Friedli–Velenik §5.7.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Fin n → Finset (Sym2 ι))

/-- **Ursell tree bound** (sharp): the Ursell coefficient of a cluster sequence is
bounded by the spanning-tree count of its incompatibility graph divided by `n!`.
Immediate from the Penrose tree-graph inequality applied to
`polymerSeqIncompatibilityGraph ω` together with
`ursellCoefficient = alternatingConnectedSubgraphSum / n!`. -/
theorem ursellCoefficient_abs_le_numSpanningTrees_div_factorial :
    |ursellCoefficient ω| ≤
      (Penrose.numSpanningTrees (polymerSeqIncompatibilityGraph ω) : ℝ) / n.factorial := by
  rw [ursellCoefficient_eq_alternatingConnectedSubgraphSum_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n.factorial)]
  exact div_le_div_of_nonneg_right
    Penrose.abs_alternatingConnectedSubgraphSum_le_numSpanningTrees (Nat.cast_nonneg _)

/-- **Uniform Ursell tree bound**: bounding the spanning-tree count of the
incompatibility graph by that of the complete graph on `Fin n`
(`Penrose.numSpanningTrees_mono` with `le_top`) gives the sequence-independent bound
`|ϕ^T(ω)| ≤ numSpanningTrees (⊤ : SimpleGraph (Fin n)) / n!`. -/
theorem ursellCoefficient_abs_le_numSpanningTrees_top_div_factorial :
    |ursellCoefficient ω| ≤
      (Penrose.numSpanningTrees (⊤ : SimpleGraph (Fin n)) : ℝ) / n.factorial := by
  refine (ursellCoefficient_abs_le_numSpanningTrees_div_factorial ω).trans ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Penrose.numSpanningTrees_mono le_top

end IsingModel
