import IsingModel.AbstractPolymer.Basic
import IsingModel.ClusterExpansion.AlternatingCompleteGraph

/-!
# Abstract cluster / Ursell layer for the polymer model (GJ §18.4)

The cluster (Ursell) layer of the abstract polymer model
(`AbstractPolymer/Basic.lean`, Issue #3954): for a length-`n` polymer sequence
`ω : Fin n → P`, the *incompatibility graph* `seqGraph Incompat ω` on `Fin n`
(`i ~ j` iff `i ≠ j` and `ω i`, `ω j` are incompatible), the *Ursell
coefficient* `ursellCoeff Incompat ω = (∑_{S connected spanning} (-1)^{|S|})/n!`
(reusing the generic `alternatingConnectedSubgraphSum`), and the *cluster
activity* `∏_i z (ω i)`.

The key restriction lemma — `ursellCoeff` vanishes on disconnected sequences,
via the generic `alternatingConnectedSubgraphSum_eq_zero_of_not_connected` — lets
the Mayer/cluster sum range only over genuine clusters.  These feed the abstract
all-order Kotecký–Preiss convergence theorem (the per-polymer cluster-sum bound).

## References

* Glimm–Jaffe, *Quantum Physics*, 2nd ed., §18.4, pp. 378–386.
-/

namespace IsingModel.AbstractPolymer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The connected-spanning alternating sum vanishes on a disconnected graph**
(generic): if `G` is not connected, `alternatingConnectedSubgraphSum G = 0`,
since `connectedSpanningEdgeSubsets G` is empty (any connected spanning subgraph
`fromEdgeSet ↑S ≤ G` would force `G` itself connected via `Reachable.mono`). -/
theorem alternatingConnectedSubgraphSum_eq_zero_of_not_connected
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : ¬ G.Connected) :
    alternatingConnectedSubgraphSum G = 0 := by
  unfold alternatingConnectedSubgraphSum
  have h_empty : connectedSpanningEdgeSubsets G = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    rw [mem_connectedSpanningEdgeSubsets] at hS
    obtain ⟨hS_sub, hS_conn⟩ := hS
    apply h
    refine { preconnected := ?_, nonempty := hS_conn.nonempty }
    intro u v
    have h_le : SimpleGraph.fromEdgeSet (↑S : Set (Sym2 V)) ≤ G := by
      intro a b hab
      rw [SimpleGraph.fromEdgeSet_adj] at hab
      obtain ⟨h_in, _⟩ := hab
      have h_in_finset : s(a, b) ∈ S := h_in
      have h_in_eS : s(a, b) ∈ G.edgeFinset := hS_sub h_in_finset
      rwa [SimpleGraph.mem_edgeFinset] at h_in_eS
    exact (hS_conn.preconnected u v).mono h_le
  rw [h_empty, Finset.sum_empty]

/-- **The connected-spanning alternating sum of any graph on one vertex is `1`**
(generic): on `Fin 1` there are no edges (`Subsingleton`), so the only connected
spanning edge-subset is `∅`, contributing `(-1)^0 = 1`.  The `n = 1` base value of
the cluster expansion. -/
theorem alternatingConnectedSubgraphSum_fin_one
    (G : SimpleGraph (Fin 1)) [DecidableRel G.Adj] :
    alternatingConnectedSubgraphSum G = 1 := by
  classical
  unfold alternatingConnectedSubgraphSum
  have h_emptyG : G.edgeFinset = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := he
      exact (G.ne_of_adj hab) (Subsingleton.elim a b)
  have h_set : connectedSpanningEdgeSubsets G = {∅} := by
    apply Finset.ext
    intro S
    rw [mem_connectedSpanningEdgeSubsets, Finset.mem_singleton]
    constructor
    · rintro ⟨hS_sub, _⟩
      rw [h_emptyG, Finset.subset_empty] at hS_sub
      exact hS_sub
    · intro hS_eq
      refine ⟨?_, ?_⟩
      · rw [hS_eq, h_emptyG]
      · rw [hS_eq]
        refine { preconnected := ?_, nonempty := ⟨0⟩ }
        intro u v
        have huv : u = v := Subsingleton.elim u v
        exact huv ▸ SimpleGraph.Reachable.refl u
  rw [h_set, Finset.sum_singleton, Finset.card_empty, pow_zero]

variable {P : Type*}

/-- **Sequence incompatibility graph**: the graph on `Fin n` with `i ~ j` iff
`i ≠ j` and `ω i` is incompatible with `ω j` (symmetrised). -/
def seqGraph (Incompat : P → P → Prop) [DecidableRel Incompat] {n : ℕ}
    (ω : Fin n → P) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => Incompat (ω i) (ω j))

instance seqGraph_decidableAdj (Incompat : P → P → Prop) [DecidableRel Incompat]
    {n : ℕ} (ω : Fin n → P) : DecidableRel (seqGraph Incompat ω).Adj :=
  fun i j => decidable_of_iff _ (SimpleGraph.fromRel_adj _ i j).symm

/-- **Abstract Ursell coefficient** of a polymer sequence: the connected-spanning
alternating sum of its incompatibility graph, divided by `n!`. -/
noncomputable def ursellCoeff (Incompat : P → P → Prop) [DecidableRel Incompat]
    {n : ℕ} (ω : Fin n → P) : ℝ :=
  alternatingConnectedSubgraphSum (seqGraph Incompat ω) / (n.factorial : ℝ)

/-- **Cluster activity** of a polymer sequence: the product of the activities. -/
def clusterActivity (z : P → ℝ) {n : ℕ} (ω : Fin n → P) : ℝ :=
  ∏ i, z (ω i)

/-- **Cluster activity is non-negative for non-negative activities**. -/
theorem clusterActivity_nonneg {z : P → ℝ} (hz : ∀ p, 0 ≤ z p) {n : ℕ}
    (ω : Fin n → P) : 0 ≤ clusterActivity z ω :=
  Finset.prod_nonneg (fun i _ => hz (ω i))

/-- **Cluster activity of a singleton sequence** equals the single activity:
`clusterActivity z (fun _ : Fin 1 => p) = z p`. -/
theorem clusterActivity_singleton (z : P → ℝ) (p : P) :
    clusterActivity z (fun _ : Fin 1 => p) = z p := by
  rw [clusterActivity, Fin.prod_univ_one]

variable {Incompat : P → P → Prop} [DecidableRel Incompat]

/-- **Ursell coefficient vanishes on disconnected sequences**: if the
incompatibility graph of `ω` is not connected, `ursellCoeff Incompat ω = 0`.  The
cluster sum thus effectively ranges over connected sequences (genuine clusters). -/
theorem ursellCoeff_eq_zero_of_not_connected {n : ℕ} (ω : Fin n → P)
    (h : ¬ (seqGraph Incompat ω).Connected) :
    ursellCoeff Incompat ω = 0 := by
  rw [ursellCoeff, alternatingConnectedSubgraphSum_eq_zero_of_not_connected _ h, zero_div]

/-- **Ursell coefficient of a singleton sequence is `1`**: every single polymer
contributes `ϕ^T = 1` to the cluster expansion (`n = 1` base case), since its
incompatibility graph on `Fin 1` has connected-spanning alternating sum `1` and
`1! = 1`. -/
theorem ursellCoeff_singleton (ω : Fin 1 → P) : ursellCoeff Incompat ω = 1 := by
  rw [ursellCoeff, alternatingConnectedSubgraphSum_fin_one]
  simp

end IsingModel.AbstractPolymer
