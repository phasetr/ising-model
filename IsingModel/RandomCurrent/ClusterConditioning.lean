import IsingModel.RandomCurrent.Core
import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.EdgeFinsetBasic
import IsingModel.RandomCurrent.Switching.SupportGraph

/-!
# Cluster-conditioning weight factorization (ingredients SL-A, SL-B)

Edge-partition factorization of the random-current weight `Current.weight`
(SL-A) and the cluster-extraction + cluster-index reindexing of the pivotal
current sum (SL-B). The weight `∏_e (βJ)^{n_e}/n_e!` is the random-current
weight of Friedli–Velenik, §3.10.6, p. 144; see `RandomCurrent/Core.lean`.

This module implements ingredients **SL-A** and **SL-B** intended to supply the
(future) Lemma 5.1 (cluster-conditioning factorisation). It is a **tracked
ingredient** under the Group 1a authorisation, not an isolated decoration: it is
planned to feed the weight-factorization + cluster-extraction steps of Lemma
5.1, which in turn is aimed at `hLogLip` → the lower-semicontinuity half of GJ
Theorem 17.5.1 (§17.5). That GJ §17.5 reference records the intended downstream
position of these ingredients, not the source of the weight itself (which is
FV §3.10.6, p. 144). The downstream ingredients SL-C (avoiding /
bridge-uniqueness on the undecremented ensemble), SL-D (exterior → `Z`-ratio
collapse), and SL-E
(re-assembly) are not yet implemented: SL-C and SL-D are new mathematics and
require a math-before-code pass before implementation.

## Definitions

The SL-A main statement `Current.weight_edge_partition_factor` splits the
weight product over the induced-graph edge set into a factor over an arbitrary
edge-subset `S` and a factor over its complement. The corollary
`Current.weight_dominant_edge_factor` specialises `S` to a single dominant edge
`e₀`, the algebraic form of the FV §3.10.6 weight used by the
cluster-conditioning factorisation.

The **SL-B** block adds the *component extraction + cluster-index reindexing*
engine of Lemma 5.1's step (i): the deterministic reachable cluster
`Current.reachableCluster` of a root `x` in the support graph, its cut/closure
property `Current.reachableCluster_closed`, the vertex-cluster-to-interior-edge
map `Current.interiorEdges` feeding SL-A (`Current.weight_cluster_interior_factor`),
and the fiberwise reindexing headline `Current.pivotalNumerator_eq_sum_by_cluster`.
SL-B is the cluster-index + interior/exterior connection engine of the (future)
Lemma 5.1 → P2-ii → `hLogLip` → the explicitly-tracked lsc half of GJ Theorem
17.5.1 (§17.5). The genuinely new devices SL-C (avoiding / bridge-uniqueness on
the undecremented ensemble) and SL-D (exterior → `Z`-ratio collapse) live
downstream of SL-B and are follow-ups.

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.10.6,
  p. 144 (random-current weight).
* Glimm–Jaffe, *Quantum Physics*, §17.5 (intended downstream position of these
  ingredients: cluster-conditioning → lsc half of Theorem 17.5.1).
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Edge-partition factorization of the random-current weight**
(ingredient SL-A). For any edge-subset `S` of the induced-graph edge set, the
FV §3.10.6 weight `Current.weight` factors as the product of per-edge factors
over `S` times the product over the complement `Sᶜ`:
\[
  w(n) = \Bigl(\prod_{e \in S} (\beta J)^{n_e}/n_e!\Bigr)
    \cdot \prod_{e \notin S} (\beta J)^{n_e}/n_e!.
\]
This is a **tracked ingredient** intended to supply the weight-factorization
step of the (future) Lemma 5.1 (cluster-conditioning factorisation), aimed
downstream at `hLogLip` → the lsc half of GJ Theorem 17.5.1 (§17.5). Successors
SL-B, …, SL-E are planned to build on it (SL-C/SL-D are new mathematics needing
math-before-code). Holds for all `β, J ∈ ℝ`: it is the pure combinatorial
`Finset.prod_mul_prod_compl` split, requiring no positivity, sign, or ordering
hypothesis. -/
theorem Current.weight_edge_partition_factor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) (n : Current G Λ)
    (S : Finset (inducedGraph G Λ).edgeSet) :
    n.weight G Λ β J
      = (∏ e ∈ S, (β * J) ^ (n e) / ((n e).factorial : ℝ))
        * ∏ e ∈ Sᶜ, (β * J) ^ (n e) / ((n e).factorial : ℝ) := by
  classical
  unfold Current.weight
  exact (Finset.prod_mul_prod_compl S
    (fun e => (β * J) ^ (n e) / ((n e).factorial : ℝ))).symm

/-- **Dominant-edge factorization of the random-current weight**
(ingredient SL-A). Specialising `Current.weight_edge_partition_factor` to the
singleton `{e₀}` separates the FV §3.10.6 weight into the factor of the dominant
edge `e₀` and the product over all remaining edges,
\[
  w(n) = \bigl((\beta J)^{n_{e_0}}/n_{e_0}!\bigr)
    \cdot \prod_{e \neq e_0} (\beta J)^{n_e}/n_e!.
\]
This is the algebraic weight-factorization form intended to supply the (future)
Lemma 5.1 (cluster-conditioning): a **tracked ingredient** aimed downstream at
`hLogLip` → the lsc half of GJ Theorem 17.5.1 (§17.5); SL-B, …, SL-E are
planned to succeed it (SL-C/SL-D are new mathematics). Holds for all
`β, J ∈ ℝ`. -/
theorem Current.weight_dominant_edge_factor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) (n : Current G Λ)
    (e₀ : (inducedGraph G Λ).edgeSet) :
    n.weight G Λ β J
      = ((β * J) ^ (n e₀) / ((n e₀).factorial : ℝ))
        * ∏ e ∈ ({e₀} : Finset (inducedGraph G Λ).edgeSet)ᶜ,
            (β * J) ^ (n e) / ((n e).factorial : ℝ) := by
  classical
  rw [Current.weight_edge_partition_factor G Λ β J n {e₀}, Finset.prod_singleton]

/-! ## SL-B: cluster extraction and cluster-index reindexing of the pivotal sum

The following block is ingredient **SL-B**: the component extraction and
cluster-index reindexing of the random-current pivotal sum. It is the
cluster-index + interior/exterior connection engine of the (future) Lemma 5.1
→ P2-ii → `hLogLip` → the explicitly-tracked lower-semicontinuity half of GJ
Theorem 17.5.1 (§17.5). It is a **tracked ingredient** (Group 1a authorisation),
buildable and axiom-free; the genuinely new devices SL-C (avoiding /
bridge-uniqueness) and SL-D (`Z`-ratio collapse) are follow-ups. The weight is
FV §3.10.6.
-/

/-- **Reachable cluster of a root** (the SL-B index; Lemma 5.1 step (i)). For a
current `n` and root `x ∈ ↑Λ`, `Current.reachableCluster G Λ n x` is the set of
vertices reachable from `x` in the support graph `n.toSimpleGraph`,
\[
  C_x(n) = \{\, v \in \Lambda : x \rightsquigarrow v \text{ in } \mathrm{supp}(n) \,\}
         = \texttt{univ.filter}\,(\lambda v.\ (n.\texttt{toSimpleGraph}).\texttt{Reachable}\ x\ v).
\]
This is the deterministic reachable-filter of `Peeling.lean` (no `ExistsUnique`
or `Classical.choose`: reachability is a relation on the fintype `↑Λ`). Part of
ingredient **SL-B** (cluster-index engine of the future Lemma 5.1 → `hLogLip` →
lsc half of GJ Theorem 17.5.1, §17.5); weight source FV §3.10.6. -/
noncomputable def Current.reachableCluster (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (x : ↑Λ) : Finset ↑Λ := by
  classical
  exact Finset.univ.filter (fun v => (n.toSimpleGraph G Λ).Reachable x v)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Membership in the reachable cluster**: `v ∈ reachableCluster n x` iff `v`
is reachable from `x` in the support graph `n.toSimpleGraph`. Unfolds the
reachable-filter. Part of ingredient **SL-B**. -/
theorem Current.mem_reachableCluster_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (x v : ↑Λ) :
    v ∈ Current.reachableCluster G Λ n x
      ↔ (n.toSimpleGraph G Λ).Reachable x v := by
  classical
  simp only [Current.reachableCluster, Finset.mem_filter, Finset.mem_univ,
    true_and]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **The reachable cluster is reachability-closed** (elementary cut property;
Lemma 5.1 step (i)). If `w ∈ reachableCluster n x` and `w` is adjacent to `w'`
via an active edge of `n` (`n.Adj G Λ w w'`), then `w' ∈ reachableCluster n x`.
Equivalently, no active edge of `n` has exactly one endpoint in the cluster: the
cluster is a cut. This is the closure step `hclosed` of
`Current.sources_reachable_of_sources_eq_pair` (`Peeling.lean`), transported to
a general root. Part of ingredient **SL-B** (cluster-index engine of the future
Lemma 5.1 → `hLogLip` → lsc half of GJ Theorem 17.5.1, §17.5); weight FV §3.10.6. -/
theorem Current.reachableCluster_closed (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (x : ↑Λ) {w w' : ↑Λ}
    (hw : w ∈ Current.reachableCluster G Λ n x)
    (hadj : n.Adj G Λ w w') :
    w' ∈ Current.reachableCluster G Λ n x := by
  rw [Current.mem_reachableCluster_iff] at hw ⊢
  exact hw.trans ((Current.toSimpleGraph_adj_iff G Λ n w w').mpr hadj).reachable

/-- **Interior edge subset of a vertex cluster** (the `C ↦ S_C` map feeding
SL-A; Lemma 5.1 step (i)). For a vertex set `C ∈ Finset ↑Λ`,
`Current.interiorEdges G Λ C` is the set of induced-graph edges both of whose
endpoints lie in `C`,
\[
  S_C = \{\, e \in E : \forall w \in e,\ w \in C \,\}.
\]
This is a deterministic function of the vertex set `C` alone (independent of the
current), supplying the edge subset `S = S_C` to
`Current.weight_edge_partition_factor` (SL-A). Part of ingredient **SL-B**
(cluster-index engine of the future Lemma 5.1 → `hLogLip` → lsc half of GJ
Theorem 17.5.1, §17.5); weight source FV §3.10.6. -/
noncomputable def Current.interiorEdges (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (C : Finset ↑Λ) : Finset (inducedGraph G Λ).edgeSet := by
  classical
  exact Finset.univ.filter (fun e => ∀ w ∈ (e : Sym2 ↑Λ), w ∈ C)

/-- **Cluster interior/exterior weight split** (SL-A ↔ SL-B interface; Lemma 5.1
step (i)). Feeding the interior edge subset `S_C = interiorEdges C` into the
SL-A edge-partition factorization `Current.weight_edge_partition_factor` yields,
at a fixed cluster value `C`, the interior/exterior split of the FV §3.10.6
weight
\[
  w(n) = \Bigl(\prod_{e \in S_C} (\beta J)^{n_e}/n_e!\Bigr)
    \cdot \prod_{e \notin S_C} (\beta J)^{n_e}/n_e!.
\]
This is the sole SL-A ↔ SL-B interface: SL-B supplies the
vertex-cluster-determined `S_C`; SL-A supplies the algebraic split. Part of
ingredient **SL-B** (cluster-index engine of the future Lemma 5.1 → `hLogLip` →
lsc half of GJ Theorem 17.5.1, §17.5); weight source FV §3.10.6. -/
theorem Current.weight_cluster_interior_factor (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (β J : ℝ) (n : Current G Λ)
    (C : Finset ↑Λ) :
    n.weight G Λ β J
      = (∏ e ∈ Current.interiorEdges G Λ C,
            (β * J) ^ (n e) / ((n e).factorial : ℝ))
        * ∏ e ∈ (Current.interiorEdges G Λ C)ᶜ,
            (β * J) ^ (n e) / ((n e).factorial : ℝ) :=
  Current.weight_edge_partition_factor G Λ β J n (Current.interiorEdges G Λ C)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Cluster-index reindexing of the pivotal sum** (the SL-B headline; Lemma
5.1 step (i)). For any finite index set `𝓜 : Finset (Current G Λ)` and any
summand `F : Current G Λ → ℝ`, the sum over `𝓜` reorganises as an outer sum over
the admissible cluster values `C` of the map
`M ↦ reachableCluster (M − 1_{e₀}) x` (where `1_{e₀} = fromEdgeFinset {e₀}` and
`M − 1_{e₀}` is the edge-subtracted, i.e. truncated, current: `Current` values
are `ℕ`-valued, so the subtraction is truncated at `0` and any `M` with
`M e₀ = 0` is left unchanged) times an inner sum over the currents
with that cluster:
\[
  \sum_{M \in \mathcal M} F(M)
    = \sum_{C \in \mathcal C} \sum_{\substack{M \in \mathcal M\\ C_x(M') = C}} F(M),
  \qquad \mathcal C = \{\, C_x(M') : M \in \mathcal M \,\}.
\]
This is the standard fiber partition of a finite sum along
`M ↦ reachableCluster (M − 1_{e₀}) x` (mathlib `Finset.sum_fiberwise_of_maps_to`
over the image partition); no current-specific input beyond
`Current.reachableCluster` being a well-defined `Finset ↑Λ`-valued function is
used, so the statement holds for an *arbitrary* index set `𝓜`. Specialising
`F(M) = 1[Piv_{e₀}^{xy}(M)] · D(M)` reorganises the pivotal numerator into the
boxed inner double-sum of Lemma 5.1's step (i); on that pivotal support `e₀`
carries a current so the truncated subtraction is honest (`M e₀ ≥ 1`). Part of
ingredient **SL-B** (cluster-index engine of the future Lemma 5.1 → `hLogLip` →
lsc half of GJ Theorem 17.5.1, §17.5); weight source FV §3.10.6. -/
theorem Current.pivotalNumerator_eq_sum_by_cluster (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (x : ↑Λ) (e₀ : (inducedGraph G Λ).edgeSet)
    (𝓜 : Finset (Current G Λ)) (F : Current G Λ → ℝ) :
    ∑ M ∈ 𝓜, F M
      = ∑ C ∈ 𝓜.image
            (fun M => Current.reachableCluster G Λ
              (M - Current.fromEdgeFinset G Λ {e₀}) x),
          ∑ M ∈ 𝓜.filter
              (fun M => Current.reachableCluster G Λ
                (M - Current.fromEdgeFinset G Λ {e₀}) x = C), F M := by
  classical
  exact (Finset.sum_fiberwise_of_maps_to
    (fun M hM => Finset.mem_image_of_mem _ hM) F).symm

end Ambient

end IsingModel
