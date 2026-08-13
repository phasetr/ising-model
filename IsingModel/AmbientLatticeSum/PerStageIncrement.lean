import IsingModel.BallBoundarySimonLieb.WeakBound
import IsingModel.BallBoundarySimonLieb.Tight
import IsingModel.AmbientLatticeSum.InducedUnion

/-!
# Numeric per-stage correlation increment

Composes the ball-boundary bond-deletion increment
`correlation_sub_deleteEdges_le_derivBound` (`WeakBound.lean`) with the
component-factorization bridge `correlation_deleteEdges_straddle_eq_inducedGraph`
(`InducedUnion.lean`) to obtain, for a pair `r, s` interior to a region `S`, the
finite-volume coupling increment between the full model and the isolated induced
subgraph on `S`:

`correlation G p {r,s} − correlation (inducedGraph G S) p {⟨r,_⟩,⟨s,_⟩}
  ≤ derivBound G (G.edgeFinset.filter straddle) p r s`.

It then instantiates this on nested finsets `T₁ ⊆ T₂` (via the double-subtype
relabeling `nestedFinsetEquiv` and the double-induce identification
`correlation_inducedGraph_nested_finset`) to obtain the two-box per-stage
increment, the form used on cubic exhaustion stages `box_k ⊆ box_{k+1}` to bound
`c_{k+1} − c_k`.

## Main declarations

* `IsingModel.correlation_pair_sub_inducedGraph_le_derivBound` (single-box).
* `IsingModel.nestedFinsetEquiv` and
  `IsingModel.correlation_inducedGraph_nested_finset` (double-induce identification).
* `IsingModel.correlation_pair_two_box_le_derivBound` (two-box increment).
-/

namespace IsingModel

open Finset Ambient

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The straddle (cut) predicate for a region `S`: an edge straddles `S` when its
endpoints lie on different sides of `· ∈ S`. Marked `@[reducible]` so it unfolds
during instance synthesis / unification to match the inline straddle set of the
component-factorization lemmas. -/
@[reducible] def straddlePred (S : Finset V) : Sym2 V → Prop :=
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
a pair `{r, s}` interior to `S`: composes `deleteEdges_filter_edgeFinset_eq`,
`correlation_congr_all`, the observable identity `triple_map_subtypeUnivEquiv_eq` /
`pair_map_val_eq`, and the component-factorization capstone
`correlation_deleteEdges_straddle_eq_inducedGraph`. Stated separately from the increment to
keep elaboration light. -/
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
the cut edges. Composes `correlation_sub_deleteEdges_le_derivBound` with
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

/-- The double-subtype relabeling `↥(T₁.subtype (· ∈ T₂)) ≃ ↥T₁` for nested
finsets `T₁ ⊆ T₂`. An element `x : ↥T₂` lies in `T₁.subtype (· ∈ T₂)` exactly when
`x.val ∈ T₁` (`Finset.mem_subtype`), so the inner-subtype's underlying value
recovers a member of `T₁`. This is the concrete-layer companion of
`nestedSubtypeEquiv` used to instantiate the per-stage increment on the cubic
exhaustion stages `box_k ⊆ box_{k+1}`. -/
def nestedFinsetEquiv {T₁ T₂ : Finset V} (hsub : T₁ ⊆ T₂) :
    (↑(T₁.subtype (· ∈ T₂)) : Type _) ≃ (↑T₁ : Type _) where
  toFun x := ⟨x.val.val, Finset.mem_subtype.mp x.property⟩
  invFun y := ⟨⟨y.val, hsub y.property⟩, Finset.mem_subtype.mpr y.property⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

set_option linter.unusedFintypeInType false in
omit [Fintype V] in
/-- **Double induced subgraph correlation = direct induced subgraph correlation**:
for nested finsets `T₁ ⊆ T₂`, the correlation of the isolated induced subgraph on
the `T₁`-slice `T₁.subtype (· ∈ T₂)` inside `inducedGraph G T₂` equals the
correlation of the direct induced subgraph `inducedGraph G T₁`, after relabeling
the observable along `nestedFinsetEquiv`. Proved by the same technique as
`correlation_inducedGraph_induce_preimage`: `correlation_map_equiv` is
applied to the *direct* graph `inducedGraph G T₁`, keeping the heavy double-induce
graph only as the map result, then `correlation_congr_all` absorbs the edge-set
`Fintype` instances. Instantiates the per-stage increment on cubic stages
`box_k ⊆ box_{k+1}`. -/
theorem correlation_inducedGraph_nested_finset (G : SimpleGraph V) {T₁ T₂ : Finset V}
    (hsub : T₁ ⊆ T₂)
    [Fintype (inducedGraph G T₁).edgeSet]
    [Fintype ((inducedGraph G T₁).map (nestedFinsetEquiv hsub).symm.toEmbedding).edgeSet]
    [Fintype (inducedGraph (inducedGraph G T₂) (T₁.subtype (· ∈ T₂))).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑T₁ : Type _)) :
    correlation (inducedGraph (inducedGraph G T₂) (T₁.subtype (· ∈ T₂))) p
        (A.map (nestedFinsetEquiv hsub).symm.toEmbedding)
      = correlation (inducedGraph G T₁) p A := by
  have hmap2 : (inducedGraph G T₁).map (nestedFinsetEquiv hsub).symm.toEmbedding
      = inducedGraph (inducedGraph G T₂) (T₁.subtype (· ∈ T₂)) := by
    ext a b
    simp only [SimpleGraph.map_adj, inducedGraph_apply, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨x, y, hxy, rfl, rfl⟩
      exact hxy
    · intro h
      refine ⟨nestedFinsetEquiv hsub a, nestedFinsetEquiv hsub b, ?_, by simp, by simp⟩
      simpa [nestedFinsetEquiv] using h
  have key := correlation_map_equiv (nestedFinsetEquiv hsub).symm (inducedGraph G T₁) p A
  rw [correlation_congr_all hmap2 p (A.map (nestedFinsetEquiv hsub).symm.toEmbedding)] at key
  exact key

omit [Fintype V] in
/-- The pair `{⟨r,hr₁⟩, ⟨s,hs₁⟩} : Finset ↥T₁` maps under `nestedFinsetEquiv.symm`
to the corresponding pair in the `T₁`-slice `T₁.subtype (· ∈ T₂)` of `↥T₂`. -/
private theorem pair_map_nestedFinsetEquiv_symm {T₁ T₂ : Finset V} (hsub : T₁ ⊆ T₂)
    {r s : V} (hr₁ : r ∈ T₁) (hs₁ : s ∈ T₁) :
    ({⟨r, hr₁⟩, ⟨s, hs₁⟩} : Finset (↑T₁ : Type _)).map
        (nestedFinsetEquiv hsub).symm.toEmbedding
      = {⟨⟨r, hsub hr₁⟩, Finset.mem_subtype.mpr hr₁⟩,
          ⟨⟨s, hsub hs₁⟩, Finset.mem_subtype.mpr hs₁⟩} := by
  rw [Finset.map_insert, Finset.map_singleton]
  rfl

set_option linter.unusedFintypeInType false in
omit [Fintype V] in
/-- **Two-box per-stage correlation increment**: for nested
finsets `T₁ ⊆ T₂` and a pair `r, s` interior to `T₁` (neither endpoint on a cut
edge of the `T₁`-slice), the pair correlation on the larger box exceeds the one on
the smaller box by at most the ball-boundary `derivBound` over the cut edges of the
slice. Composes `correlation_pair_sub_inducedGraph_le_derivBound` (the single-box
increment) on `G' = inducedGraph G T₂` with the double-induce identification
`correlation_inducedGraph_nested_finset`, recovering `inducedGraph G T₁` on the
inner box. This is the form instantiated on cubic exhaustion stages
`box_k ⊆ box_{k+1}` to bound `c_{k+1} − c_k`. -/
theorem correlation_pair_two_box_le_derivBound (G : SimpleGraph V) {T₁ T₂ : Finset V}
    (hsub : T₁ ⊆ T₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    {r s : V} (hr₁ : r ∈ T₁) (hs₁ : s ∈ T₁) (hrs : r ≠ s)
    [Fintype (inducedGraph G T₂).edgeSet]
    (hsep : ∀ e ∈ (inducedGraph G T₂).edgeFinset.filter
        (straddlePred (T₁.subtype (· ∈ T₂))),
      ¬ Sym2.Mem (⟨r, hsub hr₁⟩ : (↑T₂ : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, hsub hs₁⟩ : (↑T₂ : Type _)) e)
    [Fintype ((inducedGraph G T₂).deleteEdges
      ↑((inducedGraph G T₂).edgeFinset.filter
        (straddlePred (T₁.subtype (· ∈ T₂))))).edgeSet]
    [Fintype ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e}).edgeSet]
    [Fintype (inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        (T₁.subtype (· ∈ T₂))).edgeSet]
    [Fintype (inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        (T₁.subtype (· ∈ T₂))ᶜ).edgeSet]
    [Fintype (((inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        (T₁.subtype (· ∈ T₂))).sum
      (inducedGraph ((inducedGraph G T₂).deleteEdges
        {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
          (T₁.subtype (· ∈ T₂))ᶜ)).map
      (Equiv.Finset.union (T₁.subtype (· ∈ T₂)) (T₁.subtype (· ∈ T₂))ᶜ
        disjoint_compl_right).toEmbedding).edgeSet]
    [Fintype (inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        ((T₁.subtype (· ∈ T₂)) ∪ (T₁.subtype (· ∈ T₂))ᶜ)).edgeSet]
    [Fintype (((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e}).induce
      (↑((T₁.subtype (· ∈ T₂)) ∪ (T₁.subtype (· ∈ T₂))ᶜ) : Set (↑T₂ : Type _))).edgeSet]
    [Fintype (inducedGraph (inducedGraph G T₂) (T₁.subtype (· ∈ T₂))).edgeSet]
    [Fintype (inducedGraph G T₁).edgeSet]
    [Fintype ((inducedGraph G T₁).map (nestedFinsetEquiv hsub).symm.toEmbedding).edgeSet] :
    correlation (inducedGraph G T₂) p {⟨r, hsub hr₁⟩, ⟨s, hsub hs₁⟩}
        - correlation (inducedGraph G T₁) p {⟨r, hr₁⟩, ⟨s, hs₁⟩}
      ≤ derivBound (inducedGraph G T₂) ((inducedGraph G T₂).edgeFinset.filter
          (straddlePred (T₁.subtype (· ∈ T₂)))) p ⟨r, hsub hr₁⟩ ⟨s, hsub hs₁⟩ := by
  have hrs' : (⟨r, hsub hr₁⟩ : (↑T₂ : Type _)) ≠ ⟨s, hsub hs₁⟩ := by
    simpa [Subtype.ext_iff] using hrs
  have h1 := correlation_pair_sub_inducedGraph_le_derivBound (inducedGraph G T₂)
    (T₁.subtype (· ∈ T₂)) p hf hh ⟨r, hsub hr₁⟩ ⟨s, hsub hs₁⟩
    (Finset.mem_subtype.mpr hr₁) (Finset.mem_subtype.mpr hs₁) hrs' hsep
  rw [← pair_map_nestedFinsetEquiv_symm hsub hr₁ hs₁,
    correlation_inducedGraph_nested_finset G hsub p {⟨r, hr₁⟩, ⟨s, hs₁⟩}] at h1
  exact h1

set_option linter.unusedFintypeInType false in
/-- **Tight numeric per-stage correlation increment**: tight analogue of
`correlation_pair_sub_inducedGraph_le_derivBound` bounding the same single-box
increment by the *tight* `derivBoundTight` (cross products only, no diagonal
`⟨σ_r σ_s⟩·⟨σ_k σ_l⟩` term). Composes `correlation_sub_deleteEdges_le_derivBoundTight`
with `correlation_deleteEdges_filter_pair_eq`. Dropping the diagonal term is what
makes the per-stage exhaustion increment summable under spatial decay. -/
theorem correlation_pair_sub_inducedGraph_le_derivBoundTight (G : SimpleGraph V)
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
      ≤ derivBoundTight G (G.edgeFinset.filter (straddlePred S)) p r s := by
  have hnd : ∀ e ∈ G.edgeFinset.filter (straddlePred S), ¬ e.IsDiag := fun e he =>
    G.not_isDiag_of_mem_edgeFinset (Finset.mem_of_mem_filter e he)
  have h1 := correlation_sub_deleteEdges_le_derivBoundTight G
    (G.edgeFinset.filter (straddlePred S)) hnd (Finset.filter_subset _ _) p hf hh r s hrs hsep
  rwa [correlation_deleteEdges_filter_pair_eq G S p hr hs] at h1

set_option linter.unusedFintypeInType false in
omit [Fintype V] in
/-- **Tight two-box per-stage correlation increment**:
tight analogue of `correlation_pair_two_box_le_derivBound`, bounding the nested-box
pair correlation increment by the *tight* `derivBoundTight` over the cut edges of
the `T₁`-slice. Composes the tight single-box increment
`correlation_pair_sub_inducedGraph_le_derivBoundTight` with the double-induce
identification `correlation_inducedGraph_nested_finset`. The cross-product-only
`derivBoundTight` is what makes the cubic per-stage increment summable. -/
theorem correlation_pair_two_box_le_derivBoundTight (G : SimpleGraph V) {T₁ T₂ : Finset V}
    (hsub : T₁ ⊆ T₂) (p : IsingParams ℝ) (hf : Ferromagnetic p) (hh : p.h = 0)
    {r s : V} (hr₁ : r ∈ T₁) (hs₁ : s ∈ T₁) (hrs : r ≠ s)
    [Fintype (inducedGraph G T₂).edgeSet]
    (hsep : ∀ e ∈ (inducedGraph G T₂).edgeFinset.filter
        (straddlePred (T₁.subtype (· ∈ T₂))),
      ¬ Sym2.Mem (⟨r, hsub hr₁⟩ : (↑T₂ : Type _)) e ∧
        ¬ Sym2.Mem (⟨s, hsub hs₁⟩ : (↑T₂ : Type _)) e)
    [Fintype ((inducedGraph G T₂).deleteEdges
      ↑((inducedGraph G T₂).edgeFinset.filter
        (straddlePred (T₁.subtype (· ∈ T₂))))).edgeSet]
    [Fintype ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e}).edgeSet]
    [Fintype (inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        (T₁.subtype (· ∈ T₂))).edgeSet]
    [Fintype (inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        (T₁.subtype (· ∈ T₂))ᶜ).edgeSet]
    [Fintype (((inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        (T₁.subtype (· ∈ T₂))).sum
      (inducedGraph ((inducedGraph G T₂).deleteEdges
        {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
          (T₁.subtype (· ∈ T₂))ᶜ)).map
      (Equiv.Finset.union (T₁.subtype (· ∈ T₂)) (T₁.subtype (· ∈ T₂))ᶜ
        disjoint_compl_right).toEmbedding).edgeSet]
    [Fintype (inducedGraph ((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e})
        ((T₁.subtype (· ∈ T₂)) ∪ (T₁.subtype (· ∈ T₂))ᶜ)).edgeSet]
    [Fintype (((inducedGraph G T₂).deleteEdges
      {e : Sym2 (↑T₂ : Type _) | straddlePred (T₁.subtype (· ∈ T₂)) e}).induce
      (↑((T₁.subtype (· ∈ T₂)) ∪ (T₁.subtype (· ∈ T₂))ᶜ) : Set (↑T₂ : Type _))).edgeSet]
    [Fintype (inducedGraph (inducedGraph G T₂) (T₁.subtype (· ∈ T₂))).edgeSet]
    [Fintype (inducedGraph G T₁).edgeSet]
    [Fintype ((inducedGraph G T₁).map (nestedFinsetEquiv hsub).symm.toEmbedding).edgeSet] :
    correlation (inducedGraph G T₂) p {⟨r, hsub hr₁⟩, ⟨s, hsub hs₁⟩}
        - correlation (inducedGraph G T₁) p {⟨r, hr₁⟩, ⟨s, hs₁⟩}
      ≤ derivBoundTight (inducedGraph G T₂) ((inducedGraph G T₂).edgeFinset.filter
          (straddlePred (T₁.subtype (· ∈ T₂)))) p ⟨r, hsub hr₁⟩ ⟨s, hsub hs₁⟩ := by
  have hrs' : (⟨r, hsub hr₁⟩ : (↑T₂ : Type _)) ≠ ⟨s, hsub hs₁⟩ := by
    simpa [Subtype.ext_iff] using hrs
  have h1 := correlation_pair_sub_inducedGraph_le_derivBoundTight (inducedGraph G T₂)
    (T₁.subtype (· ∈ T₂)) p hf hh ⟨r, hsub hr₁⟩ ⟨s, hsub hs₁⟩
    (Finset.mem_subtype.mpr hr₁) (Finset.mem_subtype.mpr hs₁) hrs' hsep
  rw [← pair_map_nestedFinsetEquiv_symm hsub hr₁ hs₁,
    correlation_inducedGraph_nested_finset G hsub p {⟨r, hr₁⟩, ⟨s, hs₁⟩}] at h1
  exact h1

end IsingModel
