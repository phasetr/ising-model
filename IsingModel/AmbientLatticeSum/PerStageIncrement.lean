import IsingModel.BallBoundarySimonLieb.WeakBound
import IsingModel.AmbientLatticeSum.InducedUnion

/-!
# Numeric per-stage correlation increment (Issue #2965, Phase A)

Composes the ball-boundary bond-deletion increment
`correlation_sub_deleteEdges_le_derivBound` (`WeakBound.lean`) with the
component-factorization bridge `correlation_deleteEdges_straddle_eq_inducedGraph`
(`InducedUnion.lean`) to obtain, for a pair `r, s` interior to a region `S`, the
finite-volume coupling increment between the full model and the isolated induced
subgraph on `S`:

`correlation G p {r,s} − correlation (inducedGraph G S) p {⟨r,_⟩,⟨s,_⟩}
  ≤ derivBound G (G.edgeFinset.filter straddle) p r s`.

## Main declaration

* `IsingModel.correlation_pair_sub_inducedGraph_le_derivBound`.
-/

namespace IsingModel

open Finset Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The straddle (cut) predicate for a region `S`: an edge straddles `S` when its
endpoints lie on different sides of `· ∈ S`. Marked `@[reducible]` so it unfolds
during instance synthesis / unification to match the inline straddle set of the
component-factorization lemmas. -/
@[reducible] private def straddlePred (S : Finset V) : Sym2 V → Prop :=
  fun e => ¬ Sym2.lift ⟨fun a b => ((a ∈ S) ↔ (b ∈ S)), fun a b => by simp [iff_comm]⟩ e

noncomputable instance (S : Finset V) : DecidablePred (straddlePred S) :=
  Classical.decPred _

omit [Fintype V] in
/-- The pair `{⟨r,_⟩, ⟨s,_⟩} : Finset ↥S` maps under the subtype inclusion to the
raw pair `{r, s} : Finset V`. -/
private theorem pair_map_val_eq (S : Finset V) {r s : V} (hr : r ∈ S) (hs : s ∈ S) :
    ({⟨r, hr⟩, ⟨s, hs⟩} : Finset (↑S : Type _)).map ⟨Subtype.val, Subtype.val_injective⟩
      = ({r, s} : Finset V) := by
  rw [Finset.map_insert, Finset.map_singleton]
  rfl

set_option linter.unusedFintypeInType false in
/-- **Bond-deleted-graph correlation = isolated induced-subgraph correlation** for
a pair `{r, s}` interior to `S`: composes `deleteEdges_filter_edgeFinset_eq`
(#2987), `correlation_congr_all` (#2986), the observable identity
`triple_map_subtypeUnivEquiv_eq` (#2988) / `pair_map_val_eq`, and the
component-factorization capstone `correlation_deleteEdges_straddle_eq_inducedGraph`
(#2986). Stated separately from the increment to keep elaboration light. -/
private theorem correlation_deleteEdges_filter_pair_eq (G : SimpleGraph V)
    [Fintype G.edgeSet] (S : Finset V) (p : IsingParams ℝ) {r s : V}
    (hr : r ∈ S) (hs : s ∈ S)
    [Fintype (G.deleteEdges ↑(G.edgeFinset.filter (straddlePred S))).edgeSet]
    [Fintype (G.deleteEdges {e : Sym2 V | straddlePred S e}).edgeSet]
    [Fintype (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) S).edgeSet]
    [Fintype (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) Sᶜ).edgeSet]
    [Fintype (((inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) S).sum
        (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) Sᶜ)).map
      (Equiv.Finset.union S Sᶜ disjoint_compl_right).toEmbedding).edgeSet]
    [Fintype (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) (S ∪ Sᶜ)).edgeSet]
    [Fintype ((G.deleteEdges {e : Sym2 V | straddlePred S e}).induce
      (↑(S ∪ Sᶜ) : Set V)).edgeSet]
    [Fintype (inducedGraph G S).edgeSet] :
    correlation (G.deleteEdges ↑(G.edgeFinset.filter (straddlePred S))) p {r, s}
      = correlation (inducedGraph G S) p {⟨r, hr⟩, ⟨s, hs⟩} := by
  have hge : G.deleteEdges (↑(G.edgeFinset.filter (straddlePred S)))
      = G.deleteEdges {e : Sym2 V | straddlePred S e} :=
    SimpleGraph.deleteEdges_filter_edgeFinset_eq G (straddlePred S)
  have hobs : ((({⟨r, hr⟩, ⟨s, hs⟩} : Finset (↑S : Type _)).map
        ⟨Sum.inl, Sum.inl_injective⟩).map
        (Equiv.Finset.union S Sᶜ disjoint_compl_right).toEmbedding).map
        (Equiv.subtypeUnivEquiv (p := fun x => x ∈ (↑(S ∪ Sᶜ) : Set V))
          (fun x => by rw [Finset.union_compl, Finset.coe_univ]; exact Set.mem_univ x)).toEmbedding
      = ({r, s} : Finset V) := by
    rw [triple_map_subtypeUnivEquiv_eq, pair_map_val_eq]
  have h2986 := correlation_deleteEdges_straddle_eq_inducedGraph G S p {⟨r, hr⟩, ⟨s, hs⟩}
  rw [hobs] at h2986
  exact (correlation_congr_all hge p {r, s}).trans h2986

set_option linter.unusedFintypeInType false in
/-- **Numeric per-stage correlation increment**: for a pair `r, s` interior to `S`
(neither on a cut edge), the full-model pair correlation exceeds the isolated
induced-subgraph pair correlation by at most the ball-boundary `derivBound` over
the cut edges. Composes `correlation_sub_deleteEdges_le_derivBound` (#2974) with
`correlation_deleteEdges_filter_pair_eq`. -/
theorem correlation_pair_sub_inducedGraph_le_derivBound (G : SimpleGraph V)
    [Fintype G.edgeSet] (S : Finset V) (p : IsingParams ℝ) (hf : Ferromagnetic p)
    (hh : p.h = 0) (r s : V) (hr : r ∈ S) (hs : s ∈ S) (hrs : r ≠ s)
    (hsep : ∀ e ∈ G.edgeFinset.filter (straddlePred S),
      ¬ Sym2.Mem r e ∧ ¬ Sym2.Mem s e)
    [Fintype (G.deleteEdges ↑(G.edgeFinset.filter (straddlePred S))).edgeSet]
    [Fintype (G.deleteEdges {e : Sym2 V | straddlePred S e}).edgeSet]
    [Fintype (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) S).edgeSet]
    [Fintype (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) Sᶜ).edgeSet]
    [Fintype (((inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) S).sum
        (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) Sᶜ)).map
      (Equiv.Finset.union S Sᶜ disjoint_compl_right).toEmbedding).edgeSet]
    [Fintype (inducedGraph (G.deleteEdges {e : Sym2 V | straddlePred S e}) (S ∪ Sᶜ)).edgeSet]
    [Fintype ((G.deleteEdges {e : Sym2 V | straddlePred S e}).induce
      (↑(S ∪ Sᶜ) : Set V)).edgeSet]
    [Fintype (inducedGraph G S).edgeSet] :
    correlation G p {r, s}
        - correlation (inducedGraph G S) p {⟨r, hr⟩, ⟨s, hs⟩}
      ≤ derivBound G (G.edgeFinset.filter (straddlePred S)) p r s := by
  have hnd : ∀ e ∈ G.edgeFinset.filter (straddlePred S), ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeFinset (Finset.mem_of_mem_filter e he)
  have h1 := correlation_sub_deleteEdges_le_derivBound G
    (G.edgeFinset.filter (straddlePred S)) hnd (Finset.filter_subset _ _) p hf hh r s hrs hsep
  rwa [correlation_deleteEdges_filter_pair_eq G S p hr hs] at h1

end IsingModel
