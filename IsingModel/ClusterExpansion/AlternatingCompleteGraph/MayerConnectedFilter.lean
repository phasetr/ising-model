import IsingModel.ClusterExpansion.Incompatibility
import IsingModel.ClusterExpansion.MayerCore.Terms
import IsingModel.ClusterExpansion.Families.EvenSubgraphs

/-!
# Cluster expansion complete-graph alternating sums (4/4): Mayer connected-sequence filters

Structural split (4/4) of `IsingModel.ClusterExpansion.AlternatingCompleteGraph`.
This child holds the restriction of `mayerExpansionTerm` and `mayerPartialSum` to cluster
sequences (polymer sequences whose index-side incompatibility graph is connected), together
with the `n = 0` and `n = 1` evaluations of that filter.  It is independent of the other
three children.  See the `IsingModel.ClusterExpansion.AlternatingCompleteGraph` facade
module for the full contents overview.
-/

namespace IsingModel

open Finset

/-- **Mayer expansion term restricts to connected polymer sequences**:
the sum defining `mayerExpansionTerm G n t` can be restricted to
sequences `ω : Fin n → polymers` such that the index-side
incompatibility graph `polymerSeqIncompatibilityGraph ω` is
`Connected`. Proof: for disconnected `ω`, Step 584
(`ursellCoefficient_eq_zero_of_disconnected`) gives `ϕ^T(ω) = 0`,
so the contribution `ϕ^T(ω) · z(t, ω)` vanishes.

This sharpens the Mayer expansion identity: only **cluster
sequences** (connected sequences in the incompatibility graph)
contribute to `log Ξ`, matching the standard formulation
`log Ξ = ∑_{n ≥ 1} ∑_{cluster sequences ω} ϕ^T(ω) · z(t, ω)`. -/
theorem mayerExpansionTerm_filter_connected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (n : ℕ) (t : ℝ) :
    mayerExpansionTerm G n t =
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected),
        ursellCoefficient ω * clusterSeqActivity t ω := by
  classical
  unfold mayerExpansionTerm
  rw [← Finset.sum_filter_add_sum_filter_not
        (Fintype.piFinset (fun _ : Fin n => allPolymers G))
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected)
        (fun ω => ursellCoefficient ω * clusterSeqActivity t ω)]
  have h_disc :
      (∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => ¬ (polymerSeqIncompatibilityGraph ω).Connected),
        ursellCoefficient ω * clusterSeqActivity t ω) = 0 := by
    apply Finset.sum_eq_zero
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [ursellCoefficient_eq_zero_of_disconnected ω hω.2, zero_mul]
  rw [h_disc, add_zero]

/-- **Mayer partial sum restricts to connected polymer sequences**:
the partial sum `mayerPartialSum G N t = ∑_{n=0..N} mayerExpansionTerm G n t`
can be rewritten so each term sums only over cluster sequences (those
`ω : Fin n → polymers` with connected incompatibility graph).
Direct corollary of `mayerExpansionTerm_filter_connected` applied
term-by-term. -/
theorem mayerPartialSum_filter_connected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (N : ℕ) (t : ℝ) :
    mayerPartialSum G N t =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allPolymers G)).filter
          (fun ω => (polymerSeqIncompatibilityGraph ω).Connected),
          ursellCoefficient ω * clusterSeqActivity t ω := by
  unfold mayerPartialSum
  refine Finset.sum_congr rfl (fun n _ => ?_)
  exact mayerExpansionTerm_filter_connected G n t

/-- **Mayer expansion term restricted to connected sequences (n=0)**:
`mayerExpansionTerm G 0 t = 0` since the unique `ω : Fin 0 → polymers`
gives a graph on `Fin 0` which is disconnected (`Connected` requires
`Nonempty`). The filtered sum is empty. -/
theorem mayerExpansionTerm_filter_connected_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] (_t : ℝ) :
    (Fintype.piFinset (fun _ : Fin 0 => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ω hω
  rw [Finset.mem_filter] at hω
  exact hω.2.nonempty.elim Fin.elim0

/-- **Mayer expansion term restricted to connected sequences (n=1)**:
every singleton sequence `ω : Fin 1 → polymers` has trivially-
connected incompatibility graph (single vertex, vacuously
preconnected), so the filter is the entire piFinset. -/
theorem mayerExpansionTerm_filter_connected_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [Fintype G.edgeSet] :
    (Fintype.piFinset (fun _ : Fin 1 => allPolymers G)).filter
        (fun ω => (polymerSeqIncompatibilityGraph ω).Connected) =
      Fintype.piFinset (fun _ : Fin 1 => allPolymers G) := by
  classical
  apply Finset.filter_eq_self.mpr
  intro ω _
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  have huv : u = v := Subsingleton.elim u v
  exact huv ▸ SimpleGraph.Reachable.refl u

end IsingModel
