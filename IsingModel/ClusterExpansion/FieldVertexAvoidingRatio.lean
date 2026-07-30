import IsingModel.ClusterExpansion.FieldAvoidingRatio
import IsingModel.ClusterExpansion.MayerSumDiffSupportBound
import IsingModel.ClusterExpansion.AvoidingDeleteEdges

/-!
# Vertex-set avoiding-graph field partition ratio bound
(GJ §17.6.1, field cluster expansion, brick F5-pre-2a)

Brick F5-pre-2a of the minimal (pair-only) field cluster-expansion route toward
Glimm–Jaffe (GJ) *Quantum Physics*, 2nd ed., §17.6.1, pp. 313–314 (the `∂/∂h`
infinite-volume differentiability / `h`-analyticity of the two-point function in
the high-temperature window).  This is the **vertex-set generalization** of the
edge-support brick F3 (`FieldAvoidingRatio.lean`): F3 deletes every edge touching
`polymerSupport C` for a *set of edges* `C`, whereas the F5 source peel must delete
every edge touching an *arbitrary vertex set* `W = polymerSupport S ∪ A` (the
`A`-collar), which is in general **not** a polymer support (the observable `A` may
be isolated / non-adjacent).  Hence the vertex-set avoiding graph
`GavoidVertex G W` is unavoidable.

Fix a finite graph `G`, a real coupling `a ≥ 0` and a complex field `b`.  Write
`Zᶠ(G) = fieldPolymerZℂ G a b`.  For a vertex set `W`,
`GavoidVertex G W = G.deleteEdges (touchVertexEdges G W)` is `G` with every edge
touching `W` deleted.  With `M = max 1 ‖Complex.tanh b‖`, the inflated per-site
activity is `t_∗ = M²·|tanh a|`, `r_∗ = Δ²·e·t_∗` (`Δ = G.maxDegree`), and the
local Kotecký–Preiss constant is `κ_Δ = (1−r_∗)⁻¹·(1−ρ_∗)⁻²` with the
connected-gas ratio `ρ_∗ = 8 r_∗/(1−r_∗)²` (support constant `c = 2`).

The headline (`fieldPolymerZℂ_GavoidVertex_div_norm_le_exp`) is the
volume-uniform ratio bound `‖Zᶠ(GavoidVertex G W)/Zᶠ(G)‖ ≤ exp(κ_Δ·W.card)`.  The
exponent is `W.card` (the general-vertex-set analogue of F3's
`|polymerSupport C|`), and `κ_Δ` depends only on `Δ`, `t_∗`, `c = 2`, **not** on
the volume `|ι|`, which lets the ratio bound survive the infinite-volume limit
and feed the completed small-coupling holomorphic local-limit assembly.  Any
broader use in a real infinite-volume derivative theorem remains unresolved
under #4790.  The delete-edges
machinery is re-derived here over a raw vertex set `W` (mirroring
`AvoidingDeleteEdges.lean` + `FieldAvoidingRatio.lean` with `polymerSupport C`
replaced by `W`); the bridge `Gavoid_eq_GavoidVertex_polymerSupport` records that
F3's edge-support graph is the special case `W = polymerSupport C`.

## References
- Friedli–Velenik §5.4, Theorem 5.4, p. 224, supplies the polymer-gas
  convergence result.
- Kotecký–Preiss, Comm. Math. Phys. **103** (1986) 491–498, Theorem 1, supplies
  only the abstract convergence criterion.
- Glimm–Jaffe §18.4, Proposition 18.4.2, pp. 332–333, is a
  continuum P(φ)₂ analogy only; not a lattice-Ising source.
-/

namespace IsingModel

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The vertex-set delete-edges graph -/

/-- Edges of `G` that touch the vertex set `W` (mirror of `touchEdges` with
`polymerSupport C` replaced by an arbitrary vertex set `W`). -/
noncomputable def touchVertexEdges (G : SimpleGraph ι) [Fintype G.edgeSet]
    (W : Finset ι) : Finset (Sym2 ι) := by
  classical
  exact G.edgeFinset.filter (fun e => ∃ v : ι, v ∈ e ∧ v ∈ W)

/-- The graph obtained from `G` by deleting every edge that touches the vertex set `W`
(mirror of `Gavoid` with `polymerSupport C` replaced by `W`). -/
noncomputable def GavoidVertex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (W : Finset ι) : SimpleGraph ι :=
  G.deleteEdges (touchVertexEdges G W : Set (Sym2 ι))

/-- **`Gavoid` is the vertex-set avoiding graph at the polymer support** (GJ §17.6.1, brick
F5-pre-2a).  The F3 edge-support avoiding graph `Gavoid G C` is definitionally the vertex-set
avoiding graph `GavoidVertex G (polymerSupport C)`, since `touchEdges G C` selects exactly the
edges touching `polymerSupport C`.  This bridge lets the general vertex-set machinery specialize
back to F3. -/
theorem Gavoid_eq_GavoidVertex_polymerSupport (G : SimpleGraph ι) [Fintype G.edgeSet]
    (C : Finset (Sym2 ι)) :
    Gavoid G C = GavoidVertex G (polymerSupport C) := rfl

/-- The deleted graph has decidable adjacency (classically; only used for `degree`/`maxDegree`). -/
noncomputable instance instDecidableRelGavoidVertexAdj (G : SimpleGraph ι) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (W : Finset ι) :
    DecidableRel (GavoidVertex G W).Adj := by
  classical
  dsimp [GavoidVertex]
  infer_instance

/-- The deleted graph has a finite edge set, inherited (by subset) from the finite edge set of
`G` — independent of any `DecidableRel` instance. -/
noncomputable instance instFintypeGavoidVertexEdgeSet (G : SimpleGraph ι) [Fintype G.edgeSet]
    (W : Finset ι) : Fintype (GavoidVertex G W).edgeSet := by
  classical
  dsimp [GavoidVertex]
  exact ((Set.toFinite G.edgeSet).subset
    (SimpleGraph.edgeSet_subset_edgeSet.mpr
      (G.deleteEdges_le (touchVertexEdges G W : Set (Sym2 ι))))).fintype

/-- Membership in `touchVertexEdges`: an edge is selected exactly when it is an edge of `G` and
touches the vertex set `W`. -/
theorem mem_touchVertexEdges (G : SimpleGraph ι) [Fintype G.edgeSet]
    {W : Finset ι} {e : Sym2 ι} :
    e ∈ touchVertexEdges G W ↔
      e ∈ G.edgeFinset ∧ ∃ v : ι, v ∈ e ∧ v ∈ W := by
  classical
  unfold touchVertexEdges
  rw [Finset.mem_filter]

/-- The edge finset of `GavoidVertex G W` is the edge finset of `G` with `touchVertexEdges G W`
removed.  Proved instance-independently via `mem_edgeFinset` to avoid the `Fintype.edgeSet`
diamond. -/
theorem edgeFinset_GavoidVertex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (W : Finset ι) :
    (GavoidVertex G W).edgeFinset = G.edgeFinset \ touchVertexEdges G W := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
  change e ∈ (G.deleteEdges (touchVertexEdges G W : Set (Sym2 ι))).edgeSet ↔ _
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Finset.mem_coe]

/-- Membership in the edge finset of `GavoidVertex G W`: an edge survives exactly when it is an
edge of `G` and none of its vertices lies in `W`. -/
theorem mem_edgeFinset_GavoidVertex_iff (G : SimpleGraph ι) [Fintype G.edgeSet]
    {W : Finset ι} {e : Sym2 ι} :
    e ∈ (GavoidVertex G W).edgeFinset ↔
      e ∈ G.edgeFinset ∧ ∀ v ∈ e, v ∉ W := by
  classical
  rw [edgeFinset_GavoidVertex, Finset.mem_sdiff, mem_touchVertexEdges]
  constructor
  · rintro ⟨heG, hnot⟩
    refine ⟨heG, ?_⟩
    intro v hve hvW
    exact hnot ⟨heG, v, hve, hvW⟩
  · rintro ⟨heG, havoid⟩
    refine ⟨heG, ?_⟩
    rintro ⟨_, v, hve, hvW⟩
    exact havoid v hve hvW

/-- Disjointness of `W` from the vertex support of `Y` is equivalent to every edge of `Y`
avoiding `W`. -/
theorem disjoint_vertexSet_polymerSupport_iff_forall_edge_avoids
    {W : Finset ι} {E : Finset (Sym2 ι)} :
    Disjoint W (polymerSupport E) ↔ ∀ e ∈ E, ∀ v ∈ e, v ∉ W := by
  classical
  constructor
  · intro h e heE v hve hvW
    have hvE : v ∈ polymerSupport E := mem_polymerSupport.mpr ⟨e, heE, hve⟩
    exact (Finset.disjoint_left.mp h) hvW hvE
  · intro h
    rw [Finset.disjoint_left]
    intro v hvW hvE
    obtain ⟨e, heE, hve⟩ := mem_polymerSupport.mp hvE
    exact h e heE v hve hvW

/-- A set of edges is contained in `GavoidVertex G W` exactly when it is contained in `G` and its
vertex support is disjoint from `W`. -/
theorem subset_edgeFinset_GavoidVertex_iff (G : SimpleGraph ι) [Fintype G.edgeSet]
    (W : Finset ι) (Y : Finset (Sym2 ι)) :
    Y ⊆ (GavoidVertex G W).edgeFinset ↔
      Y ⊆ G.edgeFinset ∧ Disjoint W (polymerSupport Y) := by
  classical
  constructor
  · intro hY
    refine ⟨?_, ?_⟩
    · intro e heY
      exact ((mem_edgeFinset_GavoidVertex_iff G).mp (hY heY)).1
    · rw [disjoint_vertexSet_polymerSupport_iff_forall_edge_avoids]
      intro e heY
      exact ((mem_edgeFinset_GavoidVertex_iff G).mp (hY heY)).2
  · rintro ⟨hYG, hdisj⟩ e heY
    rw [mem_edgeFinset_GavoidVertex_iff]
    exact ⟨hYG heY,
      (disjoint_vertexSet_polymerSupport_iff_forall_edge_avoids
        (W := W) (E := Y)).mp hdisj e heY⟩

/-- Deleting the edges that touch a vertex set `W` cannot increase maximum degree. -/
theorem maxDegree_GavoidVertex_le (G : SimpleGraph ι) [Fintype G.edgeSet]
    [DecidableRel G.Adj] (W : Finset ι) :
    (GavoidVertex G W).maxDegree ≤ G.maxDegree := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le (G := GavoidVertex G W) G.maxDegree
  intro v
  have hle : GavoidVertex G W ≤ G := by
    unfold GavoidVertex
    exact G.deleteEdges_le (touchVertexEdges G W : Set (Sym2 ι))
  exact ((GavoidVertex G W).degree_le_of_le hle).trans (G.degree_le_maxDegree v)

/-! ## Connected-polymer characterizations of the vertex-set avoiding graph -/

/-- **Connected polymers of the vertex-set avoiding graph** (GJ §17.6.1, brick F5-pre-2a).  A
connected polymer of `GavoidVertex G W` is exactly a connected polymer of `G` whose edge set is
contained in the surviving edge finset (equivalently, its vertex support is disjoint from `W`).
Vertex-set mirror of `IsConnectedPolymer_Gavoid_iff`. -/
theorem IsConnectedPolymer_GavoidVertex_iff (G : SimpleGraph ι) [Fintype G.edgeSet]
    (W : Finset ι) (P : Finset (Sym2 ι)) :
    IsConnectedPolymer (GavoidVertex G W) P ↔
      IsConnectedPolymer G P ∧ P ⊆ (GavoidVertex G W).edgeFinset := by
  classical
  constructor
  · intro hP
    have hsub := (subset_edgeFinset_GavoidVertex_iff G W P).mp hP.subset
    exact
      ⟨{ nonempty := hP.nonempty
         subset := hsub.1
         connected := hP.connected },
       hP.subset⟩
  · rintro ⟨hP, hsub⟩
    exact
      { nonempty := hP.nonempty
        subset := hsub
        connected := hP.connected }

/-- **The connected-polymer universe of the vertex-set avoiding graph** (GJ §17.6.1, brick
F5-pre-2a).  The connected polymers of `GavoidVertex G W` are the connected polymers of `G`
contained in the surviving edge finset.  Vertex-set mirror of `allConnectedPolymers_Gavoid`. -/
theorem allConnectedPolymers_GavoidVertex (G : SimpleGraph ι) [Fintype G.edgeSet]
    (W : Finset ι) :
    allConnectedPolymers (GavoidVertex G W) =
      (allConnectedPolymers G).filter (fun P => P ⊆ (GavoidVertex G W).edgeFinset) := by
  classical
  ext P
  rw [mem_allConnectedPolymers, Finset.mem_filter, mem_allConnectedPolymers,
    IsConnectedPolymer_GavoidVertex_iff]

/-- **Connected polymers of the vertex-set avoiding graph form a sub-finset** (GJ §17.6.1, brick
F5-pre-2a).  Vertex-set mirror of `allConnectedPolymers_Gavoid_subset`. -/
theorem allConnectedPolymers_GavoidVertex_subset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (W : Finset ι) :
    allConnectedPolymers (GavoidVertex G W) ⊆ allConnectedPolymers G := by
  classical
  letI : Fintype (GavoidVertex G W).edgeSet := instFintypeGavoidVertexEdgeSet G W
  intro P hP
  rw [allConnectedPolymers_GavoidVertex G W] at hP
  exact (Finset.mem_filter.mp hP).1

/-- **The vertex-set avoiding connected cluster sequences embed** (GJ §17.6.1, brick F5-pre-2a).
Vertex-set mirror of `piFinset_allConnectedPolymers_Gavoid_subset`. -/
theorem piFinset_allConnectedPolymers_GavoidVertex_subset
    (G : SimpleGraph ι) [Fintype G.edgeSet] (W : Finset ι) (n : ℕ) :
    Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (GavoidVertex G W)) ⊆
      Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G) := by
  classical
  letI : Fintype (GavoidVertex G W).edgeSet := instFintypeGavoidVertexEdgeSet G W
  exact Fintype.piFinset_subset _ _ (fun _ => allConnectedPolymers_GavoidVertex_subset G W)

/-! ## The field Mayer difference touching decomposition -/

/-- **Field Mayer difference as a product-finset complement sum** (GJ §17.6.1, brick F5-pre-2a).
The `n`-th field Mayer term difference equals the sum over connected cluster sequences of `G` not
already sequences of `GavoidVertex G W`.  Vertex-set mirror of
`fieldMayerExpansionTermℂ_sub_Gavoid_eq_sdiff_sum`. -/
theorem fieldMayerExpansionTermℂ_sub_GavoidVertex_eq_sdiff_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (W : Finset ι) (n : ℕ) (a : ℝ) (b : ℂ) :
    fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (GavoidVertex G W) n a b =
      ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)) \
          (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (GavoidVertex G W))),
        (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂ a b ω := by
  classical
  letI : Fintype (GavoidVertex G W).edgeSet := instFintypeGavoidVertexEdgeSet G W
  let sG : Finset (Fin n → Finset (Sym2 ι)) :=
    Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)
  let sA : Finset (Fin n → Finset (Sym2 ι)) :=
    Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (GavoidVertex G W))
  let f : (Fin n → Finset (Sym2 ι)) → ℂ :=
    fun ω => (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂ a b ω
  have hsub : sA ⊆ sG := by
    dsimp [sA, sG]
    exact piFinset_allConnectedPolymers_GavoidVertex_subset G W n
  have hsum := Finset.sum_sdiff (s₁ := sA) (s₂ := sG) (f := f) hsub
  unfold fieldMayerExpansionTermℂ
  change (∑ ω ∈ sG, f ω) - (∑ ω ∈ sA, f ω) = ∑ ω ∈ sG \ sA, f ω
  rw [← hsum]
  ring

/-- **Membership in the connected product-finset complement** (GJ §17.6.1, brick F5-pre-2a).
A sequence lies in the complement iff all its coordinates are connected polymers of `G` and at
least one is not vertex-disjoint from `W`.  Vertex-set mirror of
`mem_piFinset_sdiff_iff_exists_touching_connected`. -/
theorem mem_piFinset_sdiff_iff_exists_touching_connected_vertex
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    {W : Finset ι} {n : ℕ} {ω : Fin n → Finset (Sym2 ι)} :
    ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)) \
          (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers (GavoidVertex G W))) ↔
      (∀ i, ω i ∈ allConnectedPolymers G) ∧
        ∃ i : Fin n, ¬ Disjoint W (polymerSupport (ω i)) := by
  classical
  letI : Fintype (GavoidVertex G W).edgeSet := instFintypeGavoidVertexEdgeSet G W
  constructor
  · intro h
    rw [Finset.mem_sdiff] at h
    have hG : ∀ i, ω i ∈ allConnectedPolymers G := Fintype.mem_piFinset.mp h.1
    have hnotA : ¬ ∀ i, ω i ∈ allConnectedPolymers (GavoidVertex G W) := by
      intro hA
      exact h.2 (Fintype.mem_piFinset.mpr hA)
    obtain ⟨i, hi⟩ := not_forall.mp hnotA
    refine ⟨hG, i, ?_⟩
    intro hdisj
    apply hi
    rw [allConnectedPolymers_GavoidVertex G W, Finset.mem_filter]
    refine ⟨hG i, ?_⟩
    exact (subset_edgeFinset_GavoidVertex_iff G W (ω i)).mpr
      ⟨(mem_allConnectedPolymers.mp (hG i)).subset, hdisj⟩
  · rintro ⟨hG, ⟨i, htouch⟩⟩
    rw [Finset.mem_sdiff]
    refine ⟨Fintype.mem_piFinset.mpr hG, ?_⟩
    intro hA
    have hiA : ω i ∈ allConnectedPolymers (GavoidVertex G W) := Fintype.mem_piFinset.mp hA i
    rw [allConnectedPolymers_GavoidVertex G W, Finset.mem_filter] at hiA
    have hsubAvoid : ω i ⊆ (GavoidVertex G W).edgeFinset := hiA.2
    have hdisj : Disjoint W (polymerSupport (ω i)) :=
      ((subset_edgeFinset_GavoidVertex_iff G W (ω i)).mp hsubAvoid).2
    exact htouch hdisj

open Classical in
/-- **Field Mayer difference as a touching-cluster sum** (GJ §17.6.1, brick F5-pre-2a).  The
`n`-th field Mayer term difference is the sum over connected cluster sequences with at least one
polymer not vertex-disjoint from `W`.  Vertex-set mirror of
`fieldMayerExpansionTermℂ_sub_Gavoid_eq_touching_sum`. -/
theorem fieldMayerExpansionTermℂ_sub_GavoidVertex_eq_touching_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (W : Finset ι) (n : ℕ) (a : ℝ) (b : ℂ) :
    fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (GavoidVertex G W) n a b =
      ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ Disjoint W (polymerSupport (ω i))),
        (ursellCoefficient ω : ℂ) * fieldClusterSeqActivityℂ a b ω := by
  classical
  letI : Fintype (GavoidVertex G W).edgeSet := instFintypeGavoidVertexEdgeSet G W
  rw [fieldMayerExpansionTermℂ_sub_GavoidVertex_eq_sdiff_sum
    (G := G) (W := W) (n := n) (a := a) (b := b)]
  apply Finset.sum_congr
  · ext ω
    rw [Finset.mem_filter]
    constructor
    · intro h
      have ht :=
        (mem_piFinset_sdiff_iff_exists_touching_connected_vertex
          (G := G) (W := W) (n := n) (ω := ω)).mp h
      exact ⟨(Finset.mem_sdiff.mp h).1, ht.2⟩
    · rintro ⟨hG, htouch⟩
      exact
        (mem_piFinset_sdiff_iff_exists_touching_connected_vertex
          (G := G) (W := W) (n := n) (ω := ω)).mpr
          ⟨Fintype.mem_piFinset.mp hG, htouch⟩
  · intro ω _hω
    rfl

open Classical in
/-- **Norm of the field Mayer difference by the inflated touching sum** (GJ §17.6.1, brick
F5-pre-2a).  The norm of the `n`-th field Mayer term difference is bounded by the touching-cluster
sum at the inflated real activity `t_∗ = M²·|tanh a|` (`M = max 1 ‖Complex.tanh b‖`), via
`norm_fieldClusterSeqActivityℂ_le`.  Vertex-set mirror of
`norm_fieldMayerExpansionTermℂ_sub_Gavoid_le`. -/
theorem norm_fieldMayerExpansionTermℂ_sub_GavoidVertex_le
    (G : SimpleGraph ι) [Fintype G.edgeSet] (W : Finset ι) (n : ℕ) (a : ℝ) (b : ℂ) :
    ‖fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (GavoidVertex G W) n a b‖
      ≤ ∑ ω ∈
        (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ Disjoint W (polymerSupport (ω i))),
        |ursellCoefficient ω|
          * clusterSeqActivity ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|) ω := by
  classical
  rw [fieldMayerExpansionTermℂ_sub_GavoidVertex_eq_touching_sum
    (G := G) (W := W) (n := n) (a := a) (b := b)]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun ω _hω => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_fieldClusterSeqActivityℂ_le a b ω) (abs_nonneg _)

open Classical in
/-- **Connected touching clusters bounded by a vertex-set union** (GJ §17.6.1, brick F5-pre-2a).
If a connected cluster sequence contains a polymer not vertex-disjoint from `W`, some vertex of
`W` lies in the support of one of its coordinates.  Vertex-set mirror of
`touchingConnectedCluster_termAbsSum_le_support_vertex_sum`. -/
theorem touchingConnectedCluster_termAbsSum_le_vertexSet_sum
    (G : SimpleGraph ι) [Fintype G.edgeSet] (W : Finset ι) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    (∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, ¬ Disjoint W (polymerSupport (ω i))),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
  classical
  set S := Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G) with hS
  set a : (Fin n → Finset (Sym2 ι)) → ℝ :=
    fun ω => |ursellCoefficient ω| * clusterSeqActivity t ω with ha
  have hanonneg : ∀ ω, 0 ≤ a ω := by
    intro ω
    exact mul_nonneg (abs_nonneg _) (clusterSeqActivity_nonneg ht ω)
  have hvertexNonneg : ∀ ω, 0 ≤ ∑ v ∈ W,
      if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
    intro ω
    refine Finset.sum_nonneg fun v _ => ?_
    split_ifs with h
    · exact hanonneg ω
    · exact le_refl 0
  have hRHS : (∑ v ∈ W,
        ∑ ω ∈ S.filter (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)), a ω)
      = ∑ ω ∈ S, ∑ v ∈ W,
          if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  refine le_trans ?_ (ge_of_eq hRHS)
  refine le_trans (Finset.sum_le_sum (fun ω hω => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ω _ _ => hvertexNonneg ω))
  rw [Finset.mem_filter] at hω
  obtain ⟨i, hi⟩ := hω.2
  obtain ⟨v, hvW, hvω⟩ := Finset.not_disjoint_iff.mp hi
  calc a ω = if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 := by
        rw [if_pos ⟨i, hvω⟩]
    _ ≤ ∑ v ∈ W,
        if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0 :=
        Finset.single_le_sum
          (f := fun v => if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0)
          (fun v _ => by
            change (0 : ℝ) ≤ if (∃ i : Fin n, v ∈ polymerSupport (ω i)) then a ω else 0
            split_ifs with h; exacts [hanonneg ω, le_refl 0])
          hvW

/-! ## The degree-window transfer, difference bound, and exp-ratio capstone -/

/-- **`c = 2` degree-window transfer to the vertex-set avoiding graph** (GJ §17.6.1, brick
F5-pre-2a).  For a non-negative real activity `A`, the field degree window transfers to
`GavoidVertex G W`, since `(GavoidVertex G W).maxDegree ≤ G.maxDegree`
(`maxDegree_GavoidVertex_le`) shrinks `r = Δ²·e·A` and the connected-gas region is downward
closed (`kpRegion8_downward_closed`).  Vertex-set mirror of `field_gavoid_degree_window`. -/
theorem field_gavoidVertex_degree_window
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (W : Finset ι) {A : ℝ} (hA : 0 ≤ A)
    (hkp : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A))
        / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A)) ^ 2 < 1) :
    ((GavoidVertex G W).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) < 1 ∧
      8 * (((GavoidVertex G W).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A))
        / (1 - ((GavoidVertex G W).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A)) ^ 2 < 1 := by
  classical
  have hfactor : (0 : ℝ) ≤ Real.exp 1 * A := by positivity
  have h0 : 0 ≤ ((GavoidVertex G W).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) := by positivity
  have h12 : ((GavoidVertex G W).maxDegree : ℝ) ^ 2 * (Real.exp 1 * A)
      ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * A) := by
    have hcast : (((GavoidVertex G W).maxDegree : ℝ) ≤ (G.maxDegree : ℝ)) := by
      exact_mod_cast maxDegree_GavoidVertex_le G W
    gcongr
  exact kpRegion8_downward_closed h0 h12 hkp hρwin

/-- **Local KP bound for the field Mayer-sum difference caused by avoiding a vertex set**
(GJ §17.6.1, brick F5-pre-2a).  On the connected-gas degree window at the inflated activity
`t_∗ = M²·|tanh a|` (`M = max 1 ‖Complex.tanh b‖`, `r_∗ = Δ²·e·t_∗`), the norm of the difference
of the full field Mayer sums of `G` and `GavoidVertex G W` is bounded by the local KP constant
`κ_Δ = (1−r_∗)⁻¹(1−ρ_∗)⁻²` (`ρ_∗ = 8 r_∗/(1−r_∗)²`) times `W.card`.  Vertex-set mirror of
`norm_fieldMayerExpansionTermℂ_tsum_sub_Gavoid_le_support_card`; the volume `|ι|` does not enter
`κ_Δ`. -/
theorem norm_fieldMayerExpansionTermℂ_tsum_sub_GavoidVertex_le_card
    (G : SimpleGraph ι) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (W : Finset ι) {a : ℝ} {b : ℂ}
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) < 1)
    (hρ : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2 < 1) :
    ‖(∑' n : ℕ, fieldMayerExpansionTermℂ G n a b)
        - (∑' n : ℕ, fieldMayerExpansionTermℂ (GavoidVertex G W) n a b)‖
      ≤ ((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * W.card := by
  classical
  letI : Fintype (GavoidVertex G W).edgeSet := instFintypeGavoidVertexEdgeSet G W
  letI : DecidableRel (GavoidVertex G W).Adj := instDecidableRelGavoidVertexAdj G W
  set t : ℝ := (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a| with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have habs : |t| = t := abs_of_nonneg ht0
  set κ : ℝ := (1 / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * t)))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * t))
            / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * t)) ^ 2)⁻¹ ^ 2 with hκ
  -- The `|t|`-form window hypotheses feeding the F3-pre moment machinery (`c = 2`).
  have hkp' : (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|) < 1 := by rw [habs]; exact hkp
  have hρ' : 4 * 2 * ((G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|))
      / (1 - (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * |t|)) ^ 2 < 1 := by
    have h8 : (4 : ℝ) * 2 = 8 := by norm_num
    rw [habs, h8]; exact hρ
  have hsupp : ∀ P ∈ allConnectedPolymers G,
      ((polymerSupport P).card : ℝ) ≤ 2 * (P.card : ℝ) := fun P hP =>
    polymerSupport_card_le_two_mul_of_mem_allConnectedPolymers G hP
  -- Field-window window transfer to `GavoidVertex G W` (for its F1 summability).
  obtain ⟨hkpAvoid, hρAvoid⟩ :=
    field_gavoidVertex_degree_window G W (A := (max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)
      (by positivity) (by rw [← ht]; exact hkp) (by rw [← ht]; exact hρ)
  -- Summability of both field Mayer series (F1).
  have hsumG : Summable fun n : ℕ => fieldMayerExpansionTermℂ G n a b :=
    (summable_norm_fieldMayerExpansionTermℂ_of_tail_condition G hkp hρ).of_norm
  have hsumA : Summable fun n : ℕ => fieldMayerExpansionTermℂ (GavoidVertex G W) n a b :=
    (summable_norm_fieldMayerExpansionTermℂ_of_tail_condition (GavoidVertex G W)
      hkpAvoid hρAvoid).of_norm
  have hdiffNorm : Summable fun n : ℕ =>
      ‖fieldMayerExpansionTermℂ G n a b
        - fieldMayerExpansionTermℂ (GavoidVertex G W) n a b‖ :=
    summable_norm_iff.mpr (hsumG.sub hsumA)
  have hnorm_tsum :
      ‖(∑' n : ℕ, fieldMayerExpansionTermℂ G n a b)
          - (∑' n : ℕ, fieldMayerExpansionTermℂ (GavoidVertex G W) n a b)‖
        ≤ ∑' n : ℕ,
          ‖fieldMayerExpansionTermℂ G n a b
            - fieldMayerExpansionTermℂ (GavoidVertex G W) n a b‖ := by
    rw [← hsumG.tsum_sub hsumA]
    exact norm_tsum_le_tsum_norm hdiffNorm
  -- Per-order: bounded by the vertex-set touching sum at activity `t`.
  have hper : ∀ n : ℕ,
      ‖fieldMayerExpansionTermℂ G n a b - fieldMayerExpansionTermℂ (GavoidVertex G W) n a b‖
      ≤ ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    intro n
    refine (norm_fieldMayerExpansionTermℂ_sub_GavoidVertex_le G W n a b).trans ?_
    rw [← ht]
    exact touchingConnectedCluster_termAbsSum_le_vertexSet_sum G W n ht0
  have hper0 : (∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin 0 => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin 0, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    refine Finset.sum_eq_zero fun ω hω => ?_
    rw [Finset.mem_filter] at hω
    obtain ⟨i, _hi⟩ := hω.2
    exact Fin.elim0 i
  -- Per-vertex summability (F3-pre) and the fixed-vertex KP constant `κ`.
  have hsupportSumm : ∀ v : ι, Summable fun n : ℕ =>
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    intro v
    exact summable_fixedVertexGasTouching_termAbsSum_succ G (connectedPolymerGasData G)
      (by norm_num) hsupp v ht0 hkp' hρ'
  have hsupportShiftSumm : ∀ U : Finset ι, Summable fun n : ℕ => ∑ v ∈ U,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    intro U
    classical
    induction U using Finset.induction_on with
    | empty => simp
    | insert v s hvs ih =>
        have hvSumm : Summable fun n : ℕ =>
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
                (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
              |ursellCoefficient ω| * clusterSeqActivity t ω := hsupportSumm v
        simpa [Finset.sum_insert, hvs] using hvSumm.add ih
  have hsupportFullSumm : Summable fun n : ℕ => ∑ v ∈ W,
      ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω :=
    (summable_nat_add_iff 1).mp (hsupportShiftSumm W)
  have hsupportTsum :
      (∑' n : ℕ, ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      = ∑ v ∈ W,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω :=
    Summable.tsum_finsetSum (fun v _hv => hsupportSumm v)
  have hshiftSupport :
      (∑' n : ℕ, ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      = ∑' n : ℕ, ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω := by
    rw [hsupportFullSumm.tsum_eq_zero_add, hper0, zero_add]
  have hsupport_bound :
      (∑' n : ℕ, ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
      ≤ κ * W.card := by
    calc
      (∑' n : ℕ, ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω)
        = ∑' n : ℕ, ∑ v ∈ W,
          ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
            (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
          |ursellCoefficient ω| * clusterSeqActivity t ω := hshiftSupport
      _ = ∑ v ∈ W,
          ∑' n : ℕ,
            ∑ ω ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => allConnectedPolymers G)).filter
              (fun ω => ∃ i : Fin (n + 1), v ∈ polymerSupport (ω i)),
            |ursellCoefficient ω| * clusterSeqActivity t ω := hsupportTsum
      _ ≤ ∑ _v ∈ W, κ := by
          refine Finset.sum_le_sum fun v hv => ?_
          refine (fixedVertexGasTouching_tsum_le G (connectedPolymerGasData G)
            (by norm_num) hsupp v ht0 hkp' hρ').trans_eq ?_
          rw [hκ, habs, show (4 : ℝ) * 2 = 8 from by norm_num]
      _ = κ * W.card := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  calc
    ‖(∑' n : ℕ, fieldMayerExpansionTermℂ G n a b)
        - (∑' n : ℕ, fieldMayerExpansionTermℂ (GavoidVertex G W) n a b)‖
      ≤ ∑' n : ℕ,
          ‖fieldMayerExpansionTermℂ G n a b
            - fieldMayerExpansionTermℂ (GavoidVertex G W) n a b‖ := hnorm_tsum
    _ ≤ ∑' n : ℕ, ∑ v ∈ W,
        ∑ ω ∈ (Fintype.piFinset (fun _ : Fin n => allConnectedPolymers G)).filter
          (fun ω => ∃ i : Fin n, v ∈ polymerSupport (ω i)),
        |ursellCoefficient ω| * clusterSeqActivity t ω :=
        hdiffNorm.tsum_le_tsum hper hsupportFullSumm
    _ ≤ κ * W.card := hsupport_bound
    _ = ((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * W.card := by rw [hκ, ht]

/-- **Vertex-set avoiding-graph field partition ratio bound** (GJ §17.6.1, brick F5-pre-2a,
capstone).  Fix a target coupling `a ∈ Set.Ico 0 A` and a field `b` in the `π/2`-ball
`Metric.ball 0 r` with a uniform bound `‖Complex.tanh z‖ ≤ Mr` (`Mr ≥ 1`), on the field degree
window at radius `ρ` (`hρ0`, `htanhA`, `hkp`, `hρwin`).  Then
`‖fieldPolymerZℂ (GavoidVertex G W) a b / fieldPolymerZℂ G a b‖ ≤ exp(κ_Δ·W.card)`, with the
**volume-uniform** local KP constant `κ_Δ = (1−r_∗)⁻¹(1−ρ_∗)⁻²`
(`r_∗ = Δ²·e·t_∗`, `t_∗ = (max 1 ‖Complex.tanh b‖)²·|tanh a|`, `ρ_∗ = 8 r_∗/(1−r_∗)²`).

Assembly mirrors `fieldPolymerZℂ_Gavoid_div_norm_le_exp` with `polymerSupport C` replaced by the
raw vertex set `W`: F2c (`fieldPolymerZℂ_eq_exp_tsum_of_degree_window`) writes both partitions as
`exp` of their field Mayer sums (on `GavoidVertex G W` via `field_gavoidVertex_degree_window`),
both non-vanishing.  The ratio is `exp(F_av − F_G)`, whose norm `≤ exp‖F_G − F_av‖`, and
`‖F_G − F_av‖ ≤ κ_Δ·W.card` by
`norm_fieldMayerExpansionTermℂ_tsum_sub_GavoidVertex_le_card`.  The special case
`W = polymerSupport C` recovers F3 through `Gavoid_eq_GavoidVertex_polymerSupport`. -/
theorem fieldPolymerZℂ_GavoidVertex_div_norm_le_exp (G : SimpleGraph ι)
    [DecidableRel G.Adj] [Fintype G.edgeSet] (W : Finset ι) {a A r Mr ρ : ℝ} {b : ℂ}
    (ha : a ∈ Set.Ico 0 A) (hr0 : 0 < r) (hrpi : r < Real.pi / 2) (hMr1 : 1 ≤ Mr)
    (hMr : ∀ z : ℂ, ‖z‖ ≤ r → ‖Complex.tanh z‖ ≤ Mr) (hbr : b ∈ Metric.ball 0 r)
    (hρ0 : 0 < ρ) (htanhA : Real.tanh A < ρ)
    (hkp : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) < 1)
    (hρwin : 8 * ((G.maxDegree : ℝ) ^ 2 *
          (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)))
        / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ))) ^ 2 < 1) :
    ‖fieldPolymerZℂ (GavoidVertex G W) a b / fieldPolymerZℂ G a b‖
      ≤ Real.exp (((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * W.card) := by
  classical
  letI : Fintype (GavoidVertex G W).edgeSet := instFintypeGavoidVertexEdgeSet G W
  letI : DecidableRel (GavoidVertex G W).Adj := instDecidableRelGavoidVertexAdj G W
  -- `t_∗ ≤ M²·ρ`, hence the `t_∗` window for `G` from the `ρ`-window.
  have htanh_le : |Real.tanh a| ≤ ρ := by
    rw [abs_of_nonneg (real_tanh_nonneg ha.1)]
    exact le_of_lt (lt_of_le_of_lt (real_tanh_le_tanh (le_of_lt ha.2)) htanhA)
  have h12 : (G.maxDegree : ℝ) ^ 2 *
        (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))
      ≤ (G.maxDegree : ℝ) ^ 2 * (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * ρ)) := by
    gcongr
  have hstar0 : 0 ≤ (G.maxDegree : ℝ) ^ 2 *
      (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)) := by positivity
  obtain ⟨hkp_star, hρ_star⟩ := kpRegion8_downward_closed hstar0 h12 hkp hρwin
  -- The `ρ`-window transfers to `GavoidVertex G W` (for its F2c `exp` identity).
  obtain ⟨hkp_av, hρwin_av⟩ :=
    field_gavoidVertex_degree_window G W (A := (max 1 ‖Complex.tanh b‖) ^ 2 * ρ)
      (by positivity) hkp hρwin
  -- Open both partitions as exponentials of their field Mayer sums.
  have hZG : fieldPolymerZℂ G a b
      = Complex.exp (∑' n, fieldMayerExpansionTermℂ G n a b) :=
    fieldPolymerZℂ_eq_exp_tsum_of_degree_window G ha hr0 hrpi hMr1 hMr hbr hρ0 htanhA hkp hρwin
  have hZA : fieldPolymerZℂ (GavoidVertex G W) a b
      = Complex.exp (∑' n, fieldMayerExpansionTermℂ (GavoidVertex G W) n a b) :=
    fieldPolymerZℂ_eq_exp_tsum_of_degree_window (GavoidVertex G W) ha hr0 hrpi hMr1 hMr hbr hρ0
      htanhA hkp_av hρwin_av
  set FG : ℂ := ∑' n, fieldMayerExpansionTermℂ G n a b with hFG
  set FA : ℂ := ∑' n, fieldMayerExpansionTermℂ (GavoidVertex G W) n a b with hFA
  have hdiff :=
    norm_fieldMayerExpansionTermℂ_tsum_sub_GavoidVertex_le_card G W hkp_star hρ_star
  calc
    ‖fieldPolymerZℂ (GavoidVertex G W) a b / fieldPolymerZℂ G a b‖
        = ‖Complex.exp FA / Complex.exp FG‖ := by rw [hZA, hZG]
    _ = ‖Complex.exp (FA - FG)‖ := by rw [← Complex.exp_sub]
    _ = Real.exp (FA - FG).re := by rw [Complex.norm_exp]
    _ ≤ Real.exp ‖FG - FA‖ := by
        apply Real.exp_le_exp.mpr
        calc (FA - FG).re ≤ ‖FA - FG‖ := Complex.re_le_norm _
          _ = ‖FG - FA‖ := norm_sub_rev FA FG
    _ ≤ Real.exp (((1 / (1 - (G.maxDegree : ℝ) ^ 2 *
            (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))))
          * (1 - 8 * ((G.maxDegree : ℝ) ^ 2 *
                (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|)))
              / (1 - (G.maxDegree : ℝ) ^ 2 *
                  (Real.exp 1 * ((max 1 ‖Complex.tanh b‖) ^ 2 * |Real.tanh a|))) ^ 2)⁻¹ ^ 2)
        * W.card) := Real.exp_le_exp.mpr hdiff

end IsingModel
