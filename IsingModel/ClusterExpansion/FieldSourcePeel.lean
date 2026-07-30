import IsingModel.ClusterExpansion.FieldSourceAvoidFactor
import IsingModel.ClusterExpansion.FieldVertexAvoidingRatio

/-!
# Complex field numerator source/avoid peel bijection (GJ §17.6.1, brick F5-pre-2b)

Brick F5-pre-2b of the on-book programme toward Glimm–Jaffe (GJ) Theorem 17.6.1
(the `∂/∂h` infinite-volume differentiability / `h`-analyticity of the two-point
function in the high-temperature window).  It combines the purely combinatorial
weight factorization of F5-pre-1 (`FieldSourceAvoidFactor.lean`,
`fieldSourceWeightℂ_union_avoiding`) with the vertex-set avoiding-graph machinery
of F5-pre-2a (`FieldVertexAvoidingRatio.lean`, `GavoidVertex`,
`subset_edgeFinset_GavoidVertex_iff`) into a **source peel identity**: the complex
field two-point numerator is regrouped by the union `S` of the observable-touching
(`A`-touching) connected components, with the remaining `A`-avoiding gas summed
into the vertex-set avoiding partition function at the `A`-collar
`W = polymerSupport S ∪ A`.

## The bijection

`fieldTwoPointNumℂ G A a b = ∑_{X ⊆ E} fieldSourceWeightℂ A a b X`
(F5-pre-1).  Each subgraph `X` splits, along its polymer decomposition, into
the `A`-touching part `sourcePartOf A X` (the union of all components whose vertex
support meets `A`) and the `A`-avoiding remainder `avoidPartOf A X`.  The map
`X ↦ (sourcePartOf A X, avoidPartOf A X)` is a bijection onto `fieldSourcePairs G A`
(pairs `(S, Y)` with `S` a *source configuration* — every component touches `A` —,
`Y ⊆ E` vertex-disjoint from `S` and avoiding `A`), with inverse `(S, Y) ↦ S ∪ Y`.
The forward-map weight factors by `fieldSourceWeightℂ_union_avoiding`; the inverse
is well defined because `polymerDecomposition` splits across a vertex-disjoint union
(`polymerDecomposition_union_of_vertexDisjoint`, the crux helper H1) and the
`A`-touching / `A`-avoiding classification of the two blocks is forced.

Summing the `A`-avoiding remainders at a fixed source `S` and reducing the index
set `{Y : S ⊥ Y ∧ Y ⊥ A}` to `(GavoidVertex G (polymerSupport S ∪ A)).edgeFinset.powerset`
(`subset_edgeFinset_GavoidVertex_iff`) rewrites the inner sum as the vertex-set
avoiding field partition function, giving the capstone

`fieldTwoPointNumℂ G A a b
  = ∑_{S ∈ fieldSourceConfigs G A}
      fieldSourceWeightℂ A a b S · fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b`.

The `A`-collar `W = polymerSupport S ∪ A` matches F5-pre-2a's vertex-set exactly,
so the F5 volume-uniform geometric bound (F5a) can consume this per-source
factorization directly.  The empty source `S = ∅` is a valid source configuration
(no component, the touching condition is vacuous) and recovers the isolated
observable term `fieldSourceWeightℂ A a b ∅ · fieldPolymerZℂ (GavoidVertex G A) a b`.

## `b = 0` sanity cross-check

At `b = 0` the field weight `Complex.tanh 0 = 0` collapses each factor to its
`h = 0` value, and this identity is the field analogue of the `β`-route
one-component peel `htSubgraphSum_anchored_peel_component` (`AnchoredPeel.lean`):
both regroup an all-subgraph or boundary-subgraph activity sum by an `A`-anchored source block
times an avoiding-gas remainder.  The distinction is that the field peel groups by
the *full union* of `A`-touching components (not a unique anchored component) and
uses the vertex-set collar `GavoidVertex G (polymerSupport S ∪ A)` to exclude the
observable, whereas the `β` peel uses the boundary-set avoiding sum.

Scope of F5-pre-2b: this file is purely combinatorial (no numerical estimate).  The
per-source norm bound, source counting and geometric aggregation into the
volume-uniform correlation bound are F5a (the genuine new analysis, math-before-code).

## References
- Friedli–Velenik §3.7.3, eq. (3.47), is the `h = 0` component template.
  Exercise 5.8, p. 238, with its Appendix C solution, p. 531, gives the exact
  field weight. The field collar peel is a project extension.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Support monotonicity and the vertex-disjoint decomposition split (H1) -/

/-- **Monotonicity of the polymer support**: `C ⊆ D` implies
`polymerSupport C ⊆ polymerSupport D`.  Elementary from `mem_polymerSupport`. -/
private theorem polymerSupport_subset_of_subset {C D : Finset (Sym2 ι)} (h : C ⊆ D) :
    polymerSupport C ⊆ polymerSupport D := by
  intro v hv
  rw [mem_polymerSupport] at hv ⊢
  obtain ⟨e, heC, hve⟩ := hv
  exact ⟨e, h heC, hve⟩

set_option linter.unusedFintypeInType false in
/-- **The polymer decomposition of a sub-family's union recovers the sub-family**: if
`𝒮 ⊆ polymerDecomposition X`, then `polymerDecomposition (𝒮.biUnion id) = 𝒮`.  The members of
`𝒮` are pairwise vertex-disjoint (restriction of `polymerDecomposition_pairwise_vertexDisjoint`),
edge-connected and non-empty, so `polymerDecomposition_biUnion_of_pairwiseVertexDisjoint` applies.
The workhorse for classifying the source / avoid parts. -/
private theorem polymerDecomposition_biUnion_subfamily {X : Finset (Sym2 ι)}
    {𝒮 : Finset (Finset (Sym2 ι))} (h𝒮 : 𝒮 ⊆ polymerDecomposition X) :
    polymerDecomposition (𝒮.biUnion id) = 𝒮 := by
  apply polymerDecomposition_biUnion_of_pairwiseVertexDisjoint
  · exact (polymerDecomposition_pairwise_vertexDisjoint (X := X)).mono
      (Finset.coe_subset.mpr h𝒮)
  · exact fun Q hQ => isEdgeConnected_of_mem_polymerDecomposition (h𝒮 hQ)
  · exact fun Q hQ => nonempty_of_mem_polymerDecomposition (h𝒮 hQ)

/-- **Crux helper H1 — the polymer decomposition splits across a vertex-disjoint union**
(GJ §17.6.1, brick F5-pre-2b).  If `S` and `Y` are vertex-disjoint
(`IsPolymerVertexDisjoint S Y`), then
`polymerDecomposition (S ∪ Y) = polymerDecomposition S ∪ polymerDecomposition Y`.  Proved by
recognizing `polymerDecomposition S ∪ polymerDecomposition Y` as a pairwise vertex-disjoint family
of edge-connected non-empty polymers whose `biUnion` is `S ∪ Y`
(`polymerDecomposition_biUnion_id`), then inverting via
`polymerDecomposition_biUnion_of_pairwiseVertexDisjoint`.  The cross vertex-disjointness of a
component of `S` and a component of `Y` follows from support monotonicity and `hVD`.  This is the
`well-definedness` core of the inverse map `(S, Y) ↦ S ∪ Y` of the source peel. -/
theorem polymerDecomposition_union_of_vertexDisjoint {S Y : Finset (Sym2 ι)}
    (hVD : IsPolymerVertexDisjoint S Y) :
    polymerDecomposition (S ∪ Y) = polymerDecomposition S ∪ polymerDecomposition Y := by
  classical
  set Γ := polymerDecomposition S ∪ polymerDecomposition Y with hΓ
  have hbi : Γ.biUnion id = S ∪ Y := by
    rw [hΓ, Finset.union_biUnion, polymerDecomposition_biUnion_id,
      polymerDecomposition_biUnion_id]
  have hpair : (↑Γ : Set (Finset (Sym2 ι))).Pairwise IsPolymerVertexDisjoint := by
    rw [hΓ, Finset.coe_union,
      Set.pairwise_union_of_symmetric (fun _ _ h => isPolymerVertexDisjoint_symm h)]
    refine ⟨polymerDecomposition_pairwise_vertexDisjoint,
      polymerDecomposition_pairwise_vertexDisjoint, ?_⟩
    intro C hC C' hC' _hne
    have hCS : C ⊆ S := mem_polymerDecomposition_subset (Finset.mem_coe.mp hC)
    have hC'Y : C' ⊆ Y := mem_polymerDecomposition_subset (Finset.mem_coe.mp hC')
    change Disjoint (polymerSupport C) (polymerSupport C')
    exact Finset.disjoint_of_subset_left (polymerSupport_subset_of_subset hCS)
      (Finset.disjoint_of_subset_right (polymerSupport_subset_of_subset hC'Y) hVD)
  have hconn : ∀ Q ∈ Γ, IsEdgeConnected Q := by
    intro Q hQ
    rw [hΓ, Finset.mem_union] at hQ
    rcases hQ with h | h
    · exact isEdgeConnected_of_mem_polymerDecomposition h
    · exact isEdgeConnected_of_mem_polymerDecomposition h
  have hne : ∀ Q ∈ Γ, Q.Nonempty := by
    intro Q hQ
    rw [hΓ, Finset.mem_union] at hQ
    rcases hQ with h | h
    · exact nonempty_of_mem_polymerDecomposition h
    · exact nonempty_of_mem_polymerDecomposition h
  calc polymerDecomposition (S ∪ Y)
      = polymerDecomposition (Γ.biUnion id) := by rw [hbi]
    _ = Γ := polymerDecomposition_biUnion_of_pairwiseVertexDisjoint hpair hconn hne

/-! ## The source / avoid parts of a subgraph -/

/-- **The `A`-touching source part of a subgraph** (GJ §17.6.1, brick F5-pre-2b): the union of all
connected components of `X` whose vertex support meets the observable `A`.  Unlike the `β`-route
anchored component, this is the *full* union of `A`-touching components (there need be no unique
anchor).  With the avoiding part it recovers `X`
(`sourcePartOf_union_avoidPartOf`). -/
noncomputable def sourcePartOf (A : Finset ι) (X : Finset (Sym2 ι)) : Finset (Sym2 ι) := by
  classical
  exact ((polymerDecomposition X).filter
    (fun C => ¬ Disjoint (polymerSupport C) A)).biUnion id

/-- **The `A`-avoiding remainder of a subgraph** (GJ §17.6.1, brick F5-pre-2b): the union of all
connected components of `X` whose vertex support is disjoint from the observable `A`.  This block
avoids `A`, so it lands in the vertex-set avoiding gas of the source peel. -/
noncomputable def avoidPartOf (A : Finset ι) (X : Finset (Sym2 ι)) : Finset (Sym2 ι) := by
  classical
  exact ((polymerDecomposition X).filter
    (fun C => Disjoint (polymerSupport C) A)).biUnion id

/-- **Source / avoid parts reassemble the subgraph** (GJ §17.6.1, brick F5-pre-2b):
`sourcePartOf A X ∪ avoidPartOf A X = X`.  The touching and avoiding component families partition
`polymerDecomposition X` (`Finset.filter` and its complement), and `biUnion` distributes over the
family union (`Finset.union_biUnion`), recovering `X` by `polymerDecomposition_biUnion_id`.  This is
the left inverse of the source-peel bijection. -/
theorem sourcePartOf_union_avoidPartOf (A : Finset ι) (X : Finset (Sym2 ι)) :
    sourcePartOf A X ∪ avoidPartOf A X = X := by
  classical
  have hfam :
      (polymerDecomposition X).filter (fun C => ¬ Disjoint (polymerSupport C) A)
        ∪ (polymerDecomposition X).filter (fun C => Disjoint (polymerSupport C) A)
        = polymerDecomposition X := by
    ext C
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  unfold sourcePartOf avoidPartOf
  rw [← Finset.union_biUnion, hfam, polymerDecomposition_biUnion_id]

/-- **The source part is a sub-subgraph**: `sourcePartOf A X ⊆ X`.  Immediate from
`sourcePartOf_union_avoidPartOf`. -/
theorem sourcePartOf_subset (A : Finset ι) (X : Finset (Sym2 ι)) : sourcePartOf A X ⊆ X := by
  conv_rhs => rw [← sourcePartOf_union_avoidPartOf A X]
  exact Finset.subset_union_left

/-- **The avoiding part is a sub-subgraph**: `avoidPartOf A X ⊆ X`.  Immediate from
`sourcePartOf_union_avoidPartOf`. -/
theorem avoidPartOf_subset (A : Finset ι) (X : Finset (Sym2 ι)) : avoidPartOf A X ⊆ X := by
  conv_rhs => rw [← sourcePartOf_union_avoidPartOf A X]
  exact Finset.subset_union_right

/-- **Polymer decomposition of the source part** (GJ §17.6.1, brick F5-pre-2b): the components of
`sourcePartOf A X` are exactly the `A`-touching components of `X`
(`polymerDecomposition_biUnion_subfamily` applied to the touching filter family).  Used to certify
that `sourcePartOf A X` is a source configuration. -/
theorem polymerDecomposition_sourcePartOf (A : Finset ι) (X : Finset (Sym2 ι)) :
    polymerDecomposition (sourcePartOf A X)
      = (polymerDecomposition X).filter (fun C => ¬ Disjoint (polymerSupport C) A) := by
  classical
  unfold sourcePartOf
  exact polymerDecomposition_biUnion_subfamily (Finset.filter_subset _ _)

/-- **The source and avoiding parts are vertex-disjoint** (GJ §17.6.1, brick F5-pre-2b): distinct
components of `polymerDecomposition X` are vertex-disjoint, and the touching / avoiding families
are disjoint, so their `biUnion`s have disjoint supports.  This is the vertex-disjointness input to
the weight factorization `fieldSourceWeightℂ_union_avoiding`. -/
theorem isPolymerVertexDisjoint_sourcePartOf_avoidPartOf (A : Finset ι) (X : Finset (Sym2 ι)) :
    IsPolymerVertexDisjoint (sourcePartOf A X) (avoidPartOf A X) := by
  classical
  unfold IsPolymerVertexDisjoint sourcePartOf avoidPartOf
  rw [polymerSupport_biUnion, polymerSupport_biUnion, Finset.disjoint_biUnion_left]
  intro C hC
  rw [Finset.disjoint_biUnion_right]
  intro C' hC'
  rw [Finset.mem_filter] at hC hC'
  have hne : C ≠ C' := by
    intro h
    subst h
    exact hC.2 hC'.2
  exact polymerDecomposition_pairwise_vertexDisjoint (Finset.mem_coe.mpr hC.1)
    (Finset.mem_coe.mpr hC'.1) hne

/-- **The avoiding part avoids the observable** (GJ §17.6.1, brick F5-pre-2b):
`Disjoint (polymerSupport (avoidPartOf A X)) A`.  Each component of the avoiding family is disjoint
from `A` by construction, hence so is the support of their `biUnion`.  This is the avoidance input
to `fieldSourceWeightℂ_union_avoiding`. -/
theorem disjoint_polymerSupport_avoidPartOf (A : Finset ι) (X : Finset (Sym2 ι)) :
    Disjoint (polymerSupport (avoidPartOf A X)) A := by
  classical
  unfold avoidPartOf
  rw [polymerSupport_biUnion, Finset.disjoint_biUnion_left]
  intro C hC
  rw [Finset.mem_filter] at hC
  exact hC.2

/-! ## Source configurations and the product-side pair set -/

/-- **Source configurations** (GJ §17.6.1, brick F5-pre-2b): edge subsets `S ⊆ E` every connected
component of which touches the observable `A`.  The empty subgraph is a (vacuous) source
configuration.  The outer index set of the source peel. -/
noncomputable def fieldSourceConfigs (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) : Finset (Finset (Sym2 ι)) := by
  classical
  exact G.edgeFinset.powerset.filter
    (fun S => ∀ C ∈ polymerDecomposition S, ¬ Disjoint (polymerSupport C) A)

/-- **Product-side pair set of the source peel** (GJ §17.6.1, brick F5-pre-2b): a source
configuration `S` together with an arbitrary remainder `Y ⊆ E`, vertex-disjoint from `S` and
avoiding `A`.  The `β`-route mirror is `anchoredPairs` (`AnchoredPeel.lean`), the difference being
the full-union source block (rather than a unique anchored component) and the vertex-set avoidance
`Disjoint (polymerSupport Y) A`. -/
noncomputable def fieldSourcePairs (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) : Finset (Finset (Sym2 ι) × Finset (Sym2 ι)) := by
  classical
  exact (fieldSourceConfigs G A ×ˢ G.edgeFinset.powerset).filter
    (fun p => IsPolymerVertexDisjoint p.1 p.2 ∧ Disjoint (polymerSupport p.2) A)

/-! ## The source-peel bijection and inner avoiding-gas reduction -/

/-- **The field numerator as a source-pair sum** (GJ §17.6.1, brick F5-pre-2b): via the bijection
`X ↦ (sourcePartOf A X, avoidPartOf A X)` (inverse `(S, Y) ↦ S ∪ Y`) between `G.edgeFinset.powerset`
and `fieldSourcePairs G A`,
`fieldTwoPointNumℂ G A a b
  = ∑_{(S,Y) ∈ fieldSourcePairs G A} fieldSourceWeightℂ A a b S · fieldPolymerWeightℂ a b Y`.
The five `Finset.sum_bij'` obligations mirror `htSubgraphSum_anchored_peel_component`: membership of
the forward map (`polymerDecomposition_sourcePartOf` +
`isPolymerVertexDisjoint_sourcePartOf_avoidPartOf` + `disjoint_polymerSupport_avoidPartOf`),
membership of the inverse, the left inverse `sourcePartOf_union_avoidPartOf`, the right inverse
(crux helper `polymerDecomposition_union_of_vertexDisjoint` plus the forced touching/avoiding
classification of the two blocks), and the weight factorization
`fieldSourceWeightℂ_union_avoiding`. -/
theorem fieldTwoPointNumℂ_eq_sum_fieldSourcePairs (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ℝ) (b : ℂ) :
    fieldTwoPointNumℂ G A a b
      = ∑ p ∈ fieldSourcePairs G A,
          fieldSourceWeightℂ A a b p.1 * fieldPolymerWeightℂ a b p.2 := by
  classical
  rw [fieldTwoPointNumℂ_eq_sum_fieldSourceWeightℂ]
  refine Finset.sum_bij'
    (fun X _ => (sourcePartOf A X, avoidPartOf A X))
    (fun p _ => p.1 ∪ p.2)
    ?_ ?_ ?_ ?_ ?_
  · -- forward map lands in `fieldSourcePairs`
    intro X hX
    rw [Finset.mem_powerset] at hX
    rw [fieldSourcePairs, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [fieldSourceConfigs, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨(sourcePartOf_subset A X).trans hX, ?_⟩
      intro C hC
      rw [polymerDecomposition_sourcePartOf, Finset.mem_filter] at hC
      exact hC.2
    · rw [Finset.mem_powerset]
      exact (avoidPartOf_subset A X).trans hX
    · exact isPolymerVertexDisjoint_sourcePartOf_avoidPartOf A X
    · exact disjoint_polymerSupport_avoidPartOf A X
  · -- inverse map lands in `G.edgeFinset.powerset`
    intro p hp
    rw [fieldSourcePairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, _, _⟩ := hp
    rw [fieldSourceConfigs, Finset.mem_filter, Finset.mem_powerset] at hp1
    rw [Finset.mem_powerset] at hp2 ⊢
    exact Finset.union_subset hp1.1 hp2
  · -- left inverse `j (i X) = X`
    intro X _hX
    change sourcePartOf A X ∪ avoidPartOf A X = X
    exact sourcePartOf_union_avoidPartOf A X
  · -- right inverse `i (j p) = p`
    intro p hp
    rw [fieldSourcePairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, _hp2⟩, hVD, hpavoid⟩ := hp
    rw [fieldSourceConfigs, Finset.mem_filter, Finset.mem_powerset] at hp1
    have hconfig : ∀ C ∈ polymerDecomposition p.1, ¬ Disjoint (polymerSupport C) A := hp1.2
    have hpd : polymerDecomposition (p.1 ∪ p.2)
        = polymerDecomposition p.1 ∪ polymerDecomposition p.2 :=
      polymerDecomposition_union_of_vertexDisjoint hVD
    have hAvoidComp : ∀ C ∈ polymerDecomposition p.2, Disjoint (polymerSupport C) A := by
      intro C hC
      exact Finset.disjoint_of_subset_left
        (polymerSupport_subset_of_subset (mem_polymerDecomposition_subset hC)) hpavoid
    have hsrc : sourcePartOf A (p.1 ∪ p.2) = p.1 := by
      unfold sourcePartOf
      rw [hpd, Finset.filter_union, Finset.filter_true_of_mem hconfig,
        Finset.filter_false_of_mem (fun C hC => not_not.mpr (hAvoidComp C hC)),
        Finset.union_empty, polymerDecomposition_biUnion_id]
    have havd : avoidPartOf A (p.1 ∪ p.2) = p.2 := by
      unfold avoidPartOf
      rw [hpd, Finset.filter_union, Finset.filter_false_of_mem hconfig,
        Finset.filter_true_of_mem hAvoidComp, Finset.empty_union,
        polymerDecomposition_biUnion_id]
    change (sourcePartOf A (p.1 ∪ p.2), avoidPartOf A (p.1 ∪ p.2)) = p
    rw [hsrc, havd]
  · -- forward-map weight factorization
    intro X _hX
    change fieldSourceWeightℂ A a b X
      = fieldSourceWeightℂ A a b (sourcePartOf A X) * fieldPolymerWeightℂ a b (avoidPartOf A X)
    conv_lhs => rw [← sourcePartOf_union_avoidPartOf A X]
    exact fieldSourceWeightℂ_union_avoiding
      (isPolymerVertexDisjoint_sourcePartOf_avoidPartOf A X) A
      (disjoint_polymerSupport_avoidPartOf A X) a b

open Classical in
/-- **Product-sum split of the source-pair sum** (GJ §17.6.1, brick F5-pre-2b): the source-pair sum
factors into the outer source-configuration sum and, at each source `S`, the inner sum of field
polymer weights over the `A`-avoiding remainders vertex-disjoint from `S`.  The `β`-route mirror is
`anchoredPairs_sum_eq_complex` (`AnchoredPeel.lean`). -/
theorem fieldSourcePairs_sum_eq_inner (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ℝ) (b : ℂ) :
    (∑ p ∈ fieldSourcePairs G A,
        fieldSourceWeightℂ A a b p.1 * fieldPolymerWeightℂ a b p.2)
      = ∑ S ∈ fieldSourceConfigs G A,
          fieldSourceWeightℂ A a b S *
            ∑ Y ∈ G.edgeFinset.powerset.filter
              (fun Y => IsPolymerVertexDisjoint S Y ∧ Disjoint (polymerSupport Y) A),
              fieldPolymerWeightℂ a b Y := by
  classical
  unfold fieldSourcePairs
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.mul_sum, Finset.sum_filter]

open Classical in
/-- **The inner avoiding sum is the vertex-set avoiding partition function** (GJ §17.6.1, brick
F5-pre-2b): for a fixed source `S`, the sum of field polymer weights over remainders `Y ⊆ E`
vertex-disjoint from `S` and avoiding `A` equals the field polymer partition function of the
vertex-set avoiding graph at the `A`-collar `W = polymerSupport S ∪ A`,
`fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b`.  The index set matches
`(GavoidVertex G W).edgeFinset.powerset` by `subset_edgeFinset_GavoidVertex_iff`
(`IsPolymerVertexDisjoint S Y = Disjoint (polymerSupport S) (polymerSupport Y)` combined with
`Disjoint (polymerSupport Y) A` via `Finset.disjoint_union_left`), and the summand is the
`allSubgraphs` term of `fieldPolymerZℂ_eq_allSubgraphs_sumℂ`, definitionally
`fieldPolymerWeightℂ a b Y`.  The `A`-collar coincides with F5-pre-2a's vertex-set `W`. -/
theorem avoidingSum_eq_fieldPolymerZℂ_GavoidVertex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ℝ) (b : ℂ) (S : Finset (Sym2 ι)) :
    (∑ Y ∈ G.edgeFinset.powerset.filter
        (fun Y => IsPolymerVertexDisjoint S Y ∧ Disjoint (polymerSupport Y) A),
      fieldPolymerWeightℂ a b Y)
      = fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b := by
  classical
  rw [fieldPolymerZℂ_eq_allSubgraphs_sumℂ]
  apply Finset.sum_congr
  · ext Y
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powerset,
      subset_edgeFinset_GavoidVertex_iff, Finset.disjoint_union_left]
    constructor
    · rintro ⟨hYG, hVD, hYA⟩
      exact ⟨hYG, hVD, hYA.symm⟩
    · rintro ⟨hYG, hSY, hAY⟩
      exact ⟨hYG, hSY, hAY.symm⟩
  · intro Y _hY
    rfl

/-- **Field numerator source peel** (GJ §17.6.1, brick F5-pre-2b, capstone).  The complex field
two-point numerator groups by its union of `A`-touching source components, each source `S`
contributing its marked source weight times the field polymer partition function of the vertex-set
avoiding graph at the `A`-collar `W = polymerSupport S ∪ A`:
`fieldTwoPointNumℂ G A a b
  = ∑_{S ∈ fieldSourceConfigs G A}
      fieldSourceWeightℂ A a b S · fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b`.
Assembled from the source-peel bijection (`fieldTwoPointNumℂ_eq_sum_fieldSourcePairs`), the
product-sum split (`fieldSourcePairs_sum_eq_inner`) and the inner avoiding-gas reduction
(`avoidingSum_eq_fieldPolymerZℂ_GavoidVertex`).  This per-source factorization — with the collar
matching F5-pre-2a's vertex set — is the input to F5a's volume-uniform geometric ratio bound. -/
theorem fieldTwoPointNumℂ_eq_sum_source_avoid (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (a : ℝ) (b : ℂ) :
    fieldTwoPointNumℂ G A a b
      = ∑ S ∈ fieldSourceConfigs G A,
          fieldSourceWeightℂ A a b S *
            fieldPolymerZℂ (GavoidVertex G (polymerSupport S ∪ A)) a b := by
  classical
  rw [fieldTwoPointNumℂ_eq_sum_fieldSourcePairs, fieldSourcePairs_sum_eq_inner]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [avoidingSum_eq_fieldPolymerZℂ_GavoidVertex]

end IsingModel
