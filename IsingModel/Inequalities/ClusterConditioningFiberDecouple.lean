import IsingModel.Inequalities.ClusterConditioningFiberFubini

/-!
# SL-D brick D1b part 2a: reachableCluster decoupling, block-source bridge, block summability

This module implements the **decoupling foundation** of ingredient **SL-D, brick
D1b part 2a** (`.self-local/tex/rc-oz-lemma51-SLD1b-part2.tex`, §②/④(S)/④-summability):
the three standalone bricks that the SL-D₁-completion (part 2b: the restriction/gluing
bijection `Φ` and the weight-level `tsum` Fubini `Σ_C = (βJ)·Ξ_int·Ξ_ext`) rests on.

## Contents

* `Current.reachableCluster_confined_eq` — the **interior-confinement decoupling
  lemma** (spec Lemma 2.1 / `lem:confine`). Under (c1) `m ≤ N` and `m = N` on the
  interior edge block `interiorEdges C`, (c2) `reachableCluster N x = C`, and (c3)
  every active edge of `N` with an endpoint in `C` is interior, the reachable cluster
  of the root `x` is unchanged on passing from `N` to `m`:
  `reachableCluster m x = C`. The `⊆` inclusion is `toSimpleGraph_mono_of_le`
  monotonicity; the `⊇` inclusion is the sole genuinely new step of part 2a — a
  reachability (`Walk`) induction closing `reachableCluster m x` under `N`-adjacencies
  confined to `C`, structurally mirroring `Current.reachableCluster_closed`.
* `Current.sources_eq_sourcesOn_of_supported` — the **block-source bridge**
  (spec ④(S)): a current supported in an edge subset `S` has global source set equal
  to its `S`-restricted source set, `sources n = sourcesOn S n`.
* `Current.summable_block_weight_if_sourcesOn` — the **block-summability lemma**
  (spec ④-summability): the block-restricted, source-constrained weight family
  `n ↦ 1[restrictOn S n = n ∧ sourcesOn S n = A] · ∏_{e ∈ S} (βJ)^{n_e}/n_e!` is
  summable. Proved via the non-private weight-dominated-summability sibling
  `Current.summable_of_le_weight` (added co-located in `Peeling.lean` to reuse the
  private partial-sum machinery), using that under `restrictOn S n = n` the off-`S`
  factors are `1`, so the block product equals the full weight and is dominated by it.

## Honest status: part 2a = decoupling foundation only, SL-D₂ still gated

D1b part 2a is the **foundation** of SL-D₁ completion (the part 2b `Φ`/`tsum` Fubini);
it is an explicitly **tracked ingredient** (Group 1a, SL-D₁), on the downstream path
to the (future) Lemma 5.1 → P2-ii → `hLogLip` → the lower-semicontinuity half of GJ
Theorem 17.5.1 (§17.5, issue #4386 / thread #4418). It does **not** build the bijection
`Φ` nor the Fubini identity (part 2b) — none of those objects are introduced here — and
it does **not** touch the exterior → two-point collapse (SL-D₂: conditioned-switching /
subgraph-current), which **awaits explicit user authorisation**; `A_ext` stays an
*ambient* block weight sum. **D1b therefore does NOT complete Lemma 5.1**: SL-D₂ remains
the gate. The weight `Current.weight` is `∏_e (βJ)^{n_e}/n_e!`, the random-current
weight of Friedli–Velenik, eq. (3.45).

## References

* Friedli–Velenik, *Statistical Mechanics of Lattice Systems*, §3.7, eq. (3.45).
* Glimm–Jaffe, *Quantum Physics* (2nd ed.), Theorem 17.5.1, p. 312 (lsc half,
  issue #4386 / thread #4418).
* Aizenman (1982), Lemma 4.1; Fernández–Fröhlich–Sokal (1992), Ch. 12.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Interior confinement of the reachable cluster** (SL-D₁ brick D1b part 2a,
spec Lemma 2.1 / `lem:confine`; the load-bearing new step of part 2a). Let
`m, N : Current G Λ` and a root `x : ↑Λ` satisfy, for a fixed cluster value
`C : Finset ↑Λ`:

* `(c1_le)` `m ≤ N` pointwise, and `(c1_agree)` `m e = N e` for every interior edge
  `e ∈ interiorEdges C`;
* `(c2)` `reachableCluster N x = C`;
* `(c3)` every active edge of `N` incident to `C` is interior: for `e ∈ N.support`,
  if some endpoint of `e` lies in `C`, then `e ∈ interiorEdges C`.

Then `reachableCluster m x = C`. The `⊆` inclusion is support-graph monotonicity
(`Current.toSimpleGraph_mono_of_le` + `SimpleGraph.Reachable.mono`), giving
`reachableCluster m x ⊆ reachableCluster N x = C`. The `⊇` inclusion is a
reachability (`Walk`) induction: `reachableCluster m x` contains `x` and, since it
sits inside `C` (by `⊆`), each `N`-adjacency step out of it is witnessed by an edge
incident to `C`, hence interior (c3), hence carrying `m e = N e ≠ 0` (c1), so it is
already an `m`-adjacency and the cluster is closed under it
(`Current.reachableCluster_closed`); walking along any `N`-path from `x` to a vertex
of `C` (c2) therefore stays inside `reachableCluster m x`. No subgraph current is
formed; everything is ambient. Part of ingredient **SL-D₁** brick D1b part 2a
(tracked ingredient, Group 1a; part 2b `Φ`/Fubini is the follow-up, and the SL-D₂
conditioned-switching core awaits explicit user authorisation); weight FV (3.45). -/
theorem Current.reachableCluster_confined_eq (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (m N : Current G Λ) (C : Finset ↑Λ) (x : ↑Λ)
    (c1_le : m ≤ N)
    (c1_agree : ∀ e ∈ Current.interiorEdges G Λ C, m e = N e)
    (c2 : Current.reachableCluster G Λ N x = C)
    (c3 : ∀ e ∈ N.support G Λ, (∃ w ∈ (e : Sym2 ↑Λ), w ∈ C) →
      e ∈ Current.interiorEdges G Λ C) :
    Current.reachableCluster G Λ m x = C := by
  -- `⊆`: reachability is monotone in the current.
  have hsub : Current.reachableCluster G Λ m x ⊆ Current.reachableCluster G Λ N x := by
    intro w hw
    rw [Current.mem_reachableCluster_iff] at hw ⊢
    exact hw.mono (Current.toSimpleGraph_mono_of_le G Λ c1_le)
  have hRsub : Current.reachableCluster G Λ m x ⊆ C := c2 ▸ hsub
  -- `⊇`: walk induction confining the cluster of `x` to `C`.
  have key : ∀ u v : ↑Λ, (N.toSimpleGraph G Λ).Walk u v →
      u ∈ Current.reachableCluster G Λ m x → v ∈ Current.reachableCluster G Λ m x := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons u mid v hadj q ih =>
        intro hu
        refine ih ?_
        rw [Current.toSimpleGraph_adj_iff] at hadj
        obtain ⟨hne, e, he, hue, hmide⟩ := hadj
        have huC : u ∈ C := hRsub hu
        have heInt : e ∈ Current.interiorEdges G Λ C := c3 e he ⟨u, hue, huC⟩
        have hNe : N e ≠ 0 := (Current.mem_support_iff G Λ N e).mp he
        have hme_ne : m e ≠ 0 := by rw [c1_agree e heInt]; exact hNe
        exact Current.reachableCluster_closed G Λ m x hu
          ⟨hne, e, (Current.mem_support_iff G Λ m e).mpr hme_ne, hue, hmide⟩
  refine Finset.Subset.antisymm hRsub ?_
  intro v hv
  have hreachN : v ∈ Current.reachableCluster G Λ N x := by rw [c2]; exact hv
  obtain ⟨p⟩ := (Current.mem_reachableCluster_iff G Λ N x v).mp hreachN
  exact key x v p
    ((Current.mem_reachableCluster_iff G Λ m x x).mpr (SimpleGraph.Reachable.refl x))

omit [DecidableEq V] in
/-- **Block-source bridge** (SL-D₁ brick D1b part 2a, spec ④(S)). If a current `n`
is supported in an edge subset `S` (`n.support ⊆ S`, i.e. every edge off `S` is
inactive), then its global source set equals its `S`-restricted source set,
`sources n = sourcesOn S n`. Reason: for every vertex `v`, the off-`S` summands of
`Current.parity` carry the factor `n e = 0` and vanish, so `parity n v = parityOn S n v`;
the source filters (odd-parity vertices) then coincide. Used in part 2b ③(b)(iii) to
read a block-supported exterior current's global source set as its exterior block
source set. Part of ingredient **SL-D₁** brick D1b part 2a (tracked ingredient,
Group 1a; part 2b `Φ`/Fubini follow-up, SL-D₂ awaits explicit user authorisation);
weight FV (3.45). -/
theorem Current.sources_eq_sourcesOn_of_supported (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (S : Finset (inducedGraph G Λ).edgeSet) (n : Current G Λ)
    (hsupp : n.support G Λ ⊆ S) :
    n.sources G Λ = n.sourcesOn G Λ S := by
  ext v
  rw [Current.mem_sources_iff, Current.mem_sourcesOn_iff]
  have hpar : n.parity G Λ v = n.parityOn G Λ S v := by
    unfold Current.parity Current.parityOn
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro e _ heS
    have hne0 : n e = 0 := by
      by_contra h
      exact heS (hsupp ((Current.mem_support_iff G Λ n e).mpr h))
    rw [hne0]; simp
  rw [hpar]

set_option linter.unusedDecidableInType false in
/-- **Block-summability of the source-constrained block weight** (SL-D₁ brick D1b
part 2a, spec ④-summability). For `0 ≤ β J`, an edge subset `S` and a target source
set `A`, the block-restricted, source-constrained weight family
\[
  n \mapsto \mathbf{1}\bigl[\texttt{restrictOn }S\,n = n \wedge \texttt{sourcesOn }S\,n = A\bigr]
    \cdot \prod_{e \in S} (\beta J)^{n_e}/n_e!
\]
is summable over the ambient current type. The block product `∏_{e ∈ S}` is
dominated by the full FV (3.45) weight `Current.weight` under the support constraint
`restrictOn S n = n`: off `S` the current vanishes (`Current.restrictOn_apply_not_mem`),
so the complement factors are all `1` (`Current.weight_edge_partition_factor`) and the
block product equals the full weight; when the constraint fails the summand is `0`, in
either case dominated by the weight. Summability then follows from the weight-dominated
sibling `Current.summable_of_le_weight` (co-located in `Peeling.lean`, reusing the
private bounded-partial-sum machinery `Current.sum_weight_boundedFinset_le` without
exposing it). This is the block-summability input needed for the part 2b product `tsum`
Fubini (`Summable.tsum_mul_tsum`); introduced here as part 2a foundation only. Part of
ingredient **SL-D₁** brick D1b part 2a (tracked ingredient, Group 1a; part 2b
`Φ`/Fubini follow-up, and the SL-D₂ conditioned-switching core awaits explicit user
authorisation); weight FV (3.45). -/
theorem Current.summable_block_weight_if_sourcesOn (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {β J : ℝ} (hβJ : 0 ≤ β * J)
    (S : Finset (inducedGraph G Λ).edgeSet) (A : Finset ↑Λ) :
    Summable (fun n : Current G Λ =>
      if n.restrictOn G Λ S = n ∧ n.sourcesOn G Λ S = A then
        ∏ e ∈ S, (β * J) ^ (n e) / ((n e).factorial : ℝ) else 0) := by
  refine Current.summable_of_le_weight G Λ hβJ _ ?_ ?_
  · -- nonnegativity of the summand
    intro n
    by_cases h : n.restrictOn G Λ S = n ∧ n.sourcesOn G Λ S = A
    · rw [if_pos h]
      exact Finset.prod_nonneg
        (fun e _ => div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _))
    · exact le_of_eq (if_neg h).symm
  · -- domination by the full FV (3.45) weight
    intro n
    by_cases h : n.restrictOn G Λ S = n ∧ n.sourcesOn G Λ S = A
    · rw [if_pos h]
      -- under `restrictOn S n = n`, off-`S` factors are `1`, so `∏_S = weight n`.
      have hw : (∏ e ∈ S, (β * J) ^ (n e) / ((n e).factorial : ℝ))
          = n.weight G Λ β J := by
        unfold Current.weight
        refine Finset.prod_subset (Finset.subset_univ S) (fun e _ heS => ?_)
        have hne0 : n e = 0 := by
          have hz := Current.restrictOn_apply_not_mem G Λ S n heS
          rwa [h.1] at hz
        rw [hne0]; simp
      exact le_of_eq hw
    · rw [if_neg h]; exact Current.weight_nonneg G Λ hβJ n

end Ambient

end IsingModel
