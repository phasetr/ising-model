import IsingModel.Peierls.DartDualComponentImage

/-!
# The separation core from a closed-walk parity hypothesis (FV §3.7.2)

The remaining geometric obligation `dual_component_separates_primal` (`d.right` lies outside the
region `edgeSideComponentDart` built from `d`'s dual component `B`) is reduced here to a single
**discrete-Stokes** input: every closed walk crosses `B` an even number of times.

The reduction is the closed-loop contradiction. If `d.right` were reachable from `d.left` while
avoiding `B`, that avoiding walk together with the direct edge `s(d.left, d.right)` — which lies
in `B` (it is `d`'s own primal edge, and `d` lies in its own component) — would form a closed walk
crossing `B` exactly once, i.e. an odd number of times, contradicting the parity hypothesis.

* `exists_walk_of_reachableAvoidingEdges` — an avoiding reachability gives a walk whose edges
  all avoid `B`.
* `countP_edges_mem_eq_zero_of_forall_not_mem` — such a walk crosses `B` zero times.
* `not_reachableAvoidingEdges_of_even_closed_walk_of_blocked_adj` — under the parity hypothesis, a
  vertex cannot reach an adjacent `B`-blocked neighbour while avoiding `B`.
* `dual_component_separates_primal_of_even_closed_walk` — the separation core from the
  closed-walk parity hypothesis on `B`.

References: Friedli–Velenik, *Statistical Mechanics of Lattice Systems*
(Cambridge, 2017), §3.7.2, pp. 109–116.
-/

namespace IsingModel

open Finset SimpleGraph

variable {ι : Type*} [DecidableEq ι] {G : SimpleGraph ι} {B : Finset (Sym2 ι)}

omit [DecidableEq ι] in
/-- **An avoiding reachability gives an avoiding walk**: from `ReachableAvoidingEdges G B x y` there
is a `G`-walk from `x` to `y` none of whose edges lie in `B`. -/
theorem exists_walk_of_reachableAvoidingEdges {x y : ι} (h : ReachableAvoidingEdges G B x y) :
    ∃ w : G.Walk x y, ∀ e ∈ w.edges, e ∉ B := by
  induction h with
  | refl => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @tail b c _ hbc ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w.concat hbc.1, ?_⟩
    intro e he
    rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append,
      List.mem_singleton] at he
    rcases he with he | rfl
    · exact hw e he
    · exact hbc.2

/-- **An avoiding walk crosses `B` zero times**: if no edge of `l` lies in `B`, the `B`-count is
zero. -/
theorem countP_edges_mem_eq_zero_of_forall_not_mem {l : List (Sym2 ι)}
    (h : ∀ e ∈ l, e ∉ B) : l.countP (fun e => decide (e ∈ B)) = 0 := by
  rw [List.countP_eq_zero]
  intro e he hp
  exact h e he (of_decide_eq_true hp)

/-- **A `B`-blocked adjacent neighbour is unreachable while avoiding `B`**: if `s(x, y) ∈ B`, the
adjacency `x ∼ y` holds, and every closed walk at `x` crosses `B` an even number of times, then
`x` cannot reach `y` while avoiding `B` (else the avoiding walk plus the direct `B`-edge would
close an odd-crossing loop). -/
theorem not_reachableAvoidingEdges_of_even_closed_walk_of_blocked_adj {x y : ι}
    (hadj : G.Adj x y) (hxy : s(x, y) ∈ B)
    (hStokes : ∀ w : G.Walk x x, Even (w.edges.countP (fun e => decide (e ∈ B)))) :
    ¬ ReachableAvoidingEdges G B x y := by
  intro hreach
  obtain ⟨p, hp⟩ := exists_walk_of_reachableAvoidingEdges hreach
  have hp0 : p.edges.countP (fun e => decide (e ∈ B)) = 0 :=
    countP_edges_mem_eq_zero_of_forall_not_mem hp
  have hyx : s(y, x) ∈ B := by rwa [Sym2.eq_swap]
  have hc : (p.concat hadj.symm).edges.countP (fun e => decide (e ∈ B)) = 1 := by
    rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.countP_append, hp0, zero_add]
    simp [hyx]
  have hnot : ¬ Even ((p.concat hadj.symm).edges.countP (fun e => decide (e ∈ B))) := by
    rw [hc]; exact Nat.not_even_one
  exact hnot (hStokes (p.concat hadj.symm))

variable {F Λ : Finset (Fin 2 → ℤ)}

/-- **The separation core from the closed-walk parity hypothesis**: if every closed walk at `d.left`
in the box graph crosses `d`'s dual-component primal edge set `B` an even number of times, then
`d.right` lies outside the region `edgeSideComponentDart` — the remaining geometric obligation
`dual_component_separates_primal`. The direct edge `s(d.left, d.right)` lies in `B` because `d` lies
in its own dual component (`DartReachable.refl`). -/
theorem dual_component_separates_primal_of_even_closed_walk (hFΛ : F ⊆ Λ)
    (hRΛ : ∀ q : BoundaryDart F, q.right ∈ Λ) (d : BoundaryDart F)
    (hStokes : ∀ w : (Ambient.inducedGraph (latticeGraph 2) Λ).Walk
        (⟨d.left, hFΛ d.left_mem⟩ : (↑Λ : Type _))
        (⟨d.left, hFΛ d.left_mem⟩ : (↑Λ : Type _)),
        Even (w.edges.countP
          (fun e => decide (e ∈ dartDualComponentBoxPrimalEdges hFΛ hRΛ d)))) :
    (⟨d.right, hRΛ d⟩ : (↑Λ : Type _)) ∉ edgeSideComponentDart hFΛ hRΛ d := by
  have hxy : BoundaryDart.boxPrimalCutEdge hFΛ hRΛ d ∈
      dartDualComponentBoxPrimalEdges hFΛ hRΛ d :=
    (boxPrimalCutEdge_mem_dartDualComponentBoxPrimalEdges_iff hFΛ hRΛ d d).mpr
      (DartReachable.refl d)
  intro hmem
  exact not_reachableAvoidingEdges_of_even_closed_walk_of_blocked_adj
    (boundaryDart_box_adj_left_right d (hFΛ d.left_mem) (hRΛ d)) hxy hStokes
    (mem_edgeSideComponent_iff.mp hmem)

end IsingModel
