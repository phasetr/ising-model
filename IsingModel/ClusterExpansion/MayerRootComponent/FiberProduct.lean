import IsingModel.ClusterExpansion.AlternatingCompleteGraph
import IsingModel.ClusterExpansion.MayerRootComponent.ComponentFiber

/-!
# Mayer K_n root-component recurrence (2/5): the fibre product factorisation

Structural split (2/5) of `IsingModel.ClusterExpansion.MayerRootComponent`.
This child holds the inside/outside edge-subset families `insideConnectedEdgeSubsets` and
`outsideEdgeSubsets` with their membership lemmas, the crossing-free bijection giving the
per-fibre product factorisation `fiber_signed_sum_eq_product`, the real alternating-powerset
dichotomy, and the fibrewise sum `allSignedSubgraphSum_eq_sum_fiber_product`.  See the
`IsingModel.ClusterExpansion.MayerRootComponent` facade module for the full contents
overview.
-/

namespace IsingModel

open Finset

open Classical in
/-- **Inside connected-spanning edge-subsets** of `G` over a vertex set `C`: the
subsets `A ⊆ E(G)` whose edges all lie in `C.sym2` and whose `fromEdgeSet`
restricted to `C` is connected. The ambient analogue (living in `Sym2 V`) of the
connected-spanning edge-subsets of the complete graph on `C`; it is the inside
factor of the root-component fibre split. -/
noncomputable def insideConnectedEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter (fun A => A ⊆ C.sym2
    ∧ ((SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).induce (↑C : Set V)).Connected)

open Classical in
/-- **Outside edge-subsets** of `G` over a vertex set `C`: the subsets `B ⊆ E(G)`
whose edges all lie in `Cᶜ.sym2` (entirely outside `C`). The ambient analogue of
all spanning edge-subsets of the complete graph on `Cᶜ`; the outside factor of the
root-component fibre split. -/
noncomputable def outsideEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C : Finset V) : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter (fun B => B ⊆ Cᶜ.sym2)

/-- **Membership in `insideConnectedEdgeSubsets`**. -/
theorem mem_insideConnectedEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : Finset V} {A : Finset (Sym2 V)} :
    A ∈ insideConnectedEdgeSubsets G C ↔ A ⊆ G.edgeFinset ∧ A ⊆ C.sym2
      ∧ ((SimpleGraph.fromEdgeSet (↑A : Set (Sym2 V))).induce (↑C : Set V)).Connected := by
  classical
  rw [insideConnectedEdgeSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- **Membership in `outsideEdgeSubsets`**. -/
theorem mem_outsideEdgeSubsets {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : Finset V} {B : Finset (Sym2 V)} :
    B ∈ outsideEdgeSubsets G C ↔ B ⊆ G.edgeFinset ∧ B ⊆ Cᶜ.sym2 := by
  classical
  rw [outsideEdgeSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- **Root-component fibre signed sum factorises as a product** (Mayer Phase B
lemma 6): for a fixed vertex set `C` containing the root `r`, the signed sum
`∑ (-1)^|S|` over edge-subsets `S ⊆ E(G)` whose root component equals `C` factors
as the product of the inside connected-spanning signed sum (over `C`) and the
outside signed sum (over `Cᶜ`). Proved by the crossing-free bijection
`S ↦ (S ∩ C.sym2, S ∩ Cᶜ.sym2)` with inverse `(A, B) ↦ A ∪ B`
(`Finset.sum_bij'`): the fibre characterisation `rootComponentFinset_eq_iff`
supplies both membership directions, disjointness `mem_sym2_and_compl_sym2_false`
makes the split a partition, and `rootComponent_edge_card_split` gives
`|S| = |A| + |B|`, so `(-1)^|S| = (-1)^|A|·(-1)^|B|`. The ambient core of the
recurrence `D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}`. -/
theorem fiber_signed_sum_eq_product {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {C : Finset V} {r : V} (hrC : r ∈ C) :
    ∑ S ∈ G.edgeFinset.powerset.filter (fun S => rootComponentFinset S r = C),
        (-1 : ℝ) ^ S.card
      = (∑ A ∈ insideConnectedEdgeSubsets G C, (-1 : ℝ) ^ A.card)
        * (∑ B ∈ outsideEdgeSubsets G C, (-1 : ℝ) ^ B.card) := by
  classical
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun S _ => (S.filter (· ∈ C.sym2), S.filter (· ∈ Cᶜ.sym2)))
    (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · -- i maps the fibre into inside ×ˢ outside
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSroot⟩ := hS
    obtain ⟨_, _, hconn⟩ := rootComponentFinset_eq_iff.mp hSroot
    rw [Finset.mem_product]
    refine ⟨mem_insideConnectedEdgeSubsets.mpr ⟨?_, ?_, hconn⟩,
      mem_outsideEdgeSubsets.mpr ⟨?_, ?_⟩⟩
    · exact (Finset.filter_subset _ _).trans hSsub
    · intro e he; exact (Finset.mem_filter.mp he).2
    · exact (Finset.filter_subset _ _).trans hSsub
    · intro e he; exact (Finset.mem_filter.mp he).2
  · -- j maps inside ×ˢ outside into the fibre
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hA, hB⟩ := hp
    obtain ⟨hAsub, hAC, hAconn⟩ := mem_insideConnectedEdgeSubsets.mp hA
    obtain ⟨hBsub, hBC⟩ := mem_outsideEdgeSubsets.mp hB
    have hfilter : (p.1 ∪ p.2).filter (· ∈ C.sym2) = p.1 := by
      rw [Finset.filter_union, Finset.filter_true_of_mem (fun e he => hAC he),
        Finset.filter_false_of_mem (fun e he h => mem_sym2_and_compl_sym2_false h (hBC he)),
        Finset.union_empty]
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset hAsub hBsub, rootComponentFinset_eq_iff.mpr ⟨hrC, ?_, ?_⟩⟩
    · intro e he
      rcases Finset.mem_union.mp he with h | h
      · exact Or.inl (hAC h)
      · exact Or.inr (hBC h)
    · rw [hfilter]; exact hAconn
  · -- left inverse: (S ∩ C.sym2) ∪ (S ∩ Cᶜ.sym2) = S
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨_, hcross, _⟩ := rootComponentFinset_eq_iff.mp hS.2
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro he
      rcases hcross e he with h | h
      · exact Or.inl ⟨he, h⟩
      · exact Or.inr ⟨he, h⟩
  · -- right inverse: i (A ∪ B) = (A, B)
    intro p hp
    rw [Finset.mem_product] at hp
    obtain ⟨hA, hB⟩ := hp
    obtain ⟨_, hAC, _⟩ := mem_insideConnectedEdgeSubsets.mp hA
    obtain ⟨_, hBC⟩ := mem_outsideEdgeSubsets.mp hB
    have h1 : (p.1 ∪ p.2).filter (· ∈ C.sym2) = p.1 := by
      rw [Finset.filter_union, Finset.filter_true_of_mem (fun e he => hAC he),
        Finset.filter_false_of_mem (fun e he h => mem_sym2_and_compl_sym2_false h (hBC he)),
        Finset.union_empty]
    have h2 : (p.1 ∪ p.2).filter (· ∈ Cᶜ.sym2) = p.2 := by
      rw [Finset.filter_union,
        Finset.filter_false_of_mem (fun e he h => mem_sym2_and_compl_sym2_false (hAC he) h),
        Finset.filter_true_of_mem (fun e he => hBC he), Finset.empty_union]
    exact Prod.ext h1 h2
  · -- value: (-1)^|S| = (-1)^|S∩C.sym2| * (-1)^|S∩Cᶜ.sym2|
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSroot⟩ := hS
    have hnondiag : ∀ e ∈ S, ¬ e.IsDiag := by
      intro e he
      have hes : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp (hSsub he)
      revert hes
      refine Sym2.ind (fun a b hes => ?_) e
      rw [SimpleGraph.mem_edgeSet] at hes
      rw [Sym2.mk_isDiag_iff]
      exact G.ne_of_adj hes
    have hcard := rootComponent_edge_card_split S r hnondiag
    rw [hSroot] at hcard
    rw [← hcard, pow_add]

/-- **Real-valued alternating powerset sum dichotomy**: `∑_{B ⊆ X} (-1)^|B|`
equals `1` if `X = ∅` and `0` otherwise. Real-cast of
`Finset.sum_powerset_neg_one_pow_card`. The signed sum over any full powerset is
determined entirely by whether the base set is empty — used to evaluate the
outside factor `D(K_{Cᶜ})` of the Mayer root-component recurrence. -/
theorem real_signed_sum_powerset {α : Type*} [DecidableEq α] (X : Finset α) :
    ∑ B ∈ X.powerset, (-1 : ℝ) ^ B.card = if X = ∅ then 1 else 0 := by
  have h := @Finset.sum_powerset_neg_one_pow_card α _ X
  have hcast : (∑ B ∈ X.powerset, (-1 : ℝ) ^ B.card)
      = (((∑ B ∈ X.powerset, (-1 : ℤ) ^ B.card) : ℤ) : ℝ) := by
    push_cast; rfl
  rw [hcast, h]
  split <;> simp

/-- **`D(G)` dichotomy**: the signed all-subgraph sum is `1` if `G` is edgeless
and `0` otherwise. Restates `allSignedSubgraphSum` via `real_signed_sum_powerset`;
unifies `allSignedSubgraphSum_eq_one_of_edgeFinset_empty` and
`_eq_zero_of_edgeFinset_nonempty`. The outside factor of the root-component
recurrence is evaluated through this dichotomy. -/
theorem allSignedSubgraphSum_eq_ite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    allSignedSubgraphSum G = if G.edgeFinset = ∅ then 1 else 0 := by
  unfold allSignedSubgraphSum
  exact real_signed_sum_powerset G.edgeFinset

/-- **All-subgraph signed sum as a fibrewise product sum** (Mayer Phase B lemma
7): the signed sum `D(G) = ∑_{S ⊆ E(G)} (-1)^|S|` over *all* spanning edge-subsets
equals the sum over vertex sets `C` containing the root `r` of the per-fibre
product `insideΣ(C) · outsideΣ(C)`. Obtained from `Finset.sum_fiberwise_of_maps_to`
applied to the root-component map `S ↦ rootComponentFinset S r` (which always
contains `r`, `self_mem_rootComponentFinset`), with each fibre evaluated by
`fiber_signed_sum_eq_product`. The ambient form of the root-component recurrence
`D_n = ∑_{C ∋ 0} c_{|C|} D_{n-|C|}` (GJ §18.4); the remaining step is the reindex
`insideΣ(C) = c(K_C)`, `outsideΣ(C) = D(K_{Cᶜ})`. -/
theorem allSignedSubgraphSum_eq_sum_fiber_product {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    allSignedSubgraphSum G
      = ∑ C ∈ Finset.univ.powerset.filter (fun C : Finset V => r ∈ C),
          (∑ A ∈ insideConnectedEdgeSubsets G C, (-1 : ℝ) ^ A.card)
            * (∑ B ∈ outsideEdgeSubsets G C, (-1 : ℝ) ^ B.card) := by
  classical
  have hmaps : ∀ S ∈ G.edgeFinset.powerset,
      rootComponentFinset S r ∈ Finset.univ.powerset.filter (fun C : Finset V => r ∈ C) := by
    intro S _
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ _, self_mem_rootComponentFinset S r⟩
  unfold allSignedSubgraphSum
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun S => (-1 : ℝ) ^ S.card)]
  refine Finset.sum_congr rfl (fun C hC => ?_)
  rw [Finset.mem_filter] at hC
  exact fiber_signed_sum_eq_product G hC.2

end IsingModel
