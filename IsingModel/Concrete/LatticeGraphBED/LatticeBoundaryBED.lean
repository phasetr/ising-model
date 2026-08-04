import IsingModel.Concrete.LatticeGraphBED.VertexBoundary

/-!
# Lattice graph bounded edge density split — lattice boundary cardinalities and bounded edge density

Part of the split lattice-graph bounded-edge-density layer (Issue #1850).
-/

namespace IsingModel

namespace Ambient

open Finset SimpleGraph

/-- **ℤ^d boundary cardinality bound**: on `latticeGraph d`,
`|∂_o^v S| ≤ 2 * d * |S|`. Combines the generic
`SimpleGraph.outerVertexBoundary_card_le_sum_degrees` with the
per-vertex degree bound `latticeGraph_degree_le`. -/
theorem latticeGraph_outerVertexBoundary_card_le
    (d : ℕ) (S : Finset (Fin d → ℤ)) :
    ((IsingModel.latticeGraph d).outerVertexBoundary S).card
      ≤ 2 * d * S.card := by
  refine ((IsingModel.latticeGraph d).outerVertexBoundary_card_le_sum_degrees
    S).trans ?_
  calc (∑ x ∈ S, (IsingModel.latticeGraph d).degree x)
      ≤ ∑ _x ∈ S, 2 * d :=
        Finset.sum_le_sum (fun x _ => latticeGraph_degree_le d x)
    _ = 2 * d * S.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **ℤ^d outer-by-inner boundary linear bound**: on
`latticeGraph d`, `|∂_o^v S| ≤ 2d · |∂_i^v S|`. Combines the
generic `SimpleGraph.outerVertexBoundary_card_le_sum_degrees_innerVertexBoundary`
with the per-vertex degree bound `latticeGraph_degree_le`. Each
inner-boundary vertex contributes at most `2d` outer-boundary
neighbours, giving the linear factor; this is the elementary
max-degree-based bound, not the optimal vertex-isoperimetric
inequality on `ℤ^d`. -/
theorem latticeGraph_outerVertexBoundary_card_le_two_mul_d_mul_innerVertexBoundary_card
    (d : ℕ) (S : Finset (Fin d → ℤ)) :
    ((IsingModel.latticeGraph d).outerVertexBoundary S).card
      ≤ 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
  refine ((IsingModel.latticeGraph d).outerVertexBoundary_card_le_sum_degrees_innerVertexBoundary
    S).trans ?_
  calc (∑ x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S,
          (IsingModel.latticeGraph d).degree x)
      ≤ ∑ _x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S, 2 * d :=
        Finset.sum_le_sum (fun x _ => latticeGraph_degree_le d x)
    _ = 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **ℤ^d edge boundary linear bound**: on `latticeGraph d`,
`|∂^e S| ≤ 2d · |∂_i^v S|`. Combines the generic
`SimpleGraph.edgeBoundary_card_le_sum_degrees_innerVertexBoundary`
with the per-vertex degree bound `latticeGraph_degree_le`. -/
theorem latticeGraph_edgeBoundary_card_le_two_mul_d_mul_innerVertexBoundary_card
    (d : ℕ) (S : Finset (Fin d → ℤ)) :
    ((IsingModel.latticeGraph d).edgeBoundary S).card
      ≤ 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
  refine ((IsingModel.latticeGraph d).edgeBoundary_card_le_sum_degrees_innerVertexBoundary
    S).trans ?_
  calc (∑ x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S,
          (IsingModel.latticeGraph d).degree x)
      ≤ ∑ _x ∈ (IsingModel.latticeGraph d).innerVertexBoundary S, 2 * d :=
        Finset.sum_le_sum (fun x _ => latticeGraph_degree_le d x)
    _ = 2 * d * ((IsingModel.latticeGraph d).innerVertexBoundary S).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **ℤ^d edge boundary outer-side linear bound**: on
`latticeGraph d`, `|∂^e S| ≤ 2d · |∂_o^v S|`. Symmetric companion
to `latticeGraph_edgeBoundary_card_le_two_mul_d_mul_innerVertexBoundary_card`.
Combines the generic
`SimpleGraph.edgeBoundary_card_le_sum_degrees_outerVertexBoundary`
with `latticeGraph_degree_le`. Together with the inner-side
version this yields the strictly stronger combined bound
`|∂^e S| ≤ 2d · min(|∂_i^v S|, |∂_o^v S|)`. -/
theorem latticeGraph_edgeBoundary_card_le_two_mul_d_mul_outerVertexBoundary_card
    (d : ℕ) (S : Finset (Fin d → ℤ)) :
    ((IsingModel.latticeGraph d).edgeBoundary S).card
      ≤ 2 * d * ((IsingModel.latticeGraph d).outerVertexBoundary S).card := by
  refine ((IsingModel.latticeGraph d).edgeBoundary_card_le_sum_degrees_outerVertexBoundary
    S).trans ?_
  calc (∑ y ∈ (IsingModel.latticeGraph d).outerVertexBoundary S,
          (IsingModel.latticeGraph d).degree y)
      ≤ ∑ _y ∈ (IsingModel.latticeGraph d).outerVertexBoundary S, 2 * d :=
        Finset.sum_le_sum (fun y _ => latticeGraph_degree_le d y)
    _ = 2 * d * ((IsingModel.latticeGraph d).outerVertexBoundary S).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Decidable-Adj instance for the induced lattice graph.

Provided explicitly because the generic `instDecidableRel_induce_adj`
does not fire through the `noncomputable def Ambient.inducedGraph`
wrapper automatically.

Issue #4906's completed KEEP decision intentionally keeps this
lattice-specific provider here. On pinned main `c66c6d1b`, the proposed
generic proof body failed to synthesize
`DecidableRel (Ambient.inducedGraph G Λ).Adj`.

**Import-hygiene warning**: this is an *anonymous* instance. Historical
and current source-text occurrence counts are grep proxies, not an actual
consumer population. Changes to its ownership or import reachability
require compiler evidence for affected consumers. No relocation is tracked
or authorized; any future relocation requires a separate issue and new
explicit user authorization. -/
instance (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    DecidableRel (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).Adj :=
  fun ⟨a, _⟩ ⟨b, _⟩ => by
    unfold Ambient.inducedGraph SimpleGraph.induce
    exact inferInstance

/-- Fintype instance for the edge set of the induced lattice graph
on a cubic box.

Provided explicitly to thread through `Ambient.inducedGraph` — the
generic `SimpleGraph.fintypeEdgeSet` would fire directly on
`SimpleGraph.induce` but the `noncomputable def` wrapper masks this.

Issue #4906's completed KEEP decision also intentionally keeps this
lattice-specific provider here. The proposed generic provider overlapped
the selected provider, and their explicit `rfl` comparison failed
definitional equality. Placing the generic provider in
`AmbientLattice.Defs.Core` would expose it to a wider source import closure;
this is not a timing claim.

**Import-hygiene warning**: as above, source-text counts are grep proxies,
not an actual consumer population, and ownership or import-reachability
changes require compiler evidence. No relocation is tracked or authorized;
any future relocation requires a separate issue and new explicit user
authorization. -/
noncomputable instance (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet := by
  haveI : Fintype (↑Λ : Type _) := inferInstance
  haveI : Fintype (Sym2 ↑Λ) := inferInstance
  exact SimpleGraph.fintypeEdgeSet _

/-- **Per-vertex degree bound for the induced lattice graph**: every
vertex in the induced subgraph on `Λ` has degree at most `2 * d`. -/
theorem inducedLatticeGraph_degree_le (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (v : ↑Λ) :
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v ≤ 2 * d := by
  -- degree = |neighborFinset|; each neighbor w has w.val ∈ latticeNeighborEnum d v.val.
  classical
  unfold SimpleGraph.degree
  -- `neighborFinset v` is a Finset of `↑Λ`; its card is bounded by |latticeNeighborEnum d v.val|.
  set nf := (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).neighborFinset v
  have himg : nf.image Subtype.val ⊆ latticeNeighborEnum d v.val := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨⟨x, hx⟩, hxmem, hxval⟩ := hw
    subst hxval
    -- `⟨x, hx⟩ ∈ nf` means adjacency in the induced graph.
    have hadj : (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).Adj v ⟨x, hx⟩ :=
      (SimpleGraph.mem_neighborFinset _ _ _).mp hxmem
    -- Adjacency in `inducedGraph G Λ = G.induce ↑Λ` gives `G.Adj v.val x`.
    have : (IsingModel.latticeGraph d).Adj v.val x := by
      simp only [Ambient.inducedGraph, SimpleGraph.induce_adj] at hadj
      exact hadj
    exact latticeGraph_adj_mem_neighborEnum d v.val x this
  have h_card_img : (nf.image Subtype.val).card ≤ (latticeNeighborEnum d v.val).card :=
    Finset.card_le_card himg
  have h_inj : Set.InjOn Subtype.val (nf : Set ↑Λ) := by
    intro a _ b _ hab
    exact Subtype.ext hab
  have h_card_eq : (nf.image Subtype.val).card = nf.card :=
    Finset.card_image_of_injOn h_inj
  rw [← h_card_eq]
  exact h_card_img.trans (latticeNeighborEnum_card_le d v.val)

/-- **Incident-edge count for two vertices in the induced lattice graph** (Step 155, GJ §17.5):
the number of edges in `inducedGraph (latticeGraph d) Λ` incident to `r` or `s` is at most `4 * d`.

In ℤ^d every vertex has degree ≤ 2d, so edges incident to r or s total ≤ 2d + 2d = 4d.
This converts the tight Lebowitz bound (Step 154) into a bound `J·4d` that stays finite
as |Λ| → ∞, a prerequisite for the infinite-volume β-derivative argument.

Reference: Glimm–Jaffe §17.5 pp.311–312. -/
theorem incidentEdgesFinset_inducedLatticeGraph_card_le
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (r s : ↑Λ) :
    ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.filter
      (fun e => r ∈ e ∨ s ∈ e)).card ≤ 4 * d := by
  classical
  set G := Ambient.inducedGraph (IsingModel.latticeGraph d) Λ
  calc (G.edgeFinset.filter (fun e => r ∈ e ∨ s ∈ e)).card
      = (G.edgeFinset.filter (fun e => r ∈ e) ∪
         G.edgeFinset.filter (fun e => s ∈ e)).card := by
          rw [← Finset.filter_or]
    _ ≤ (G.edgeFinset.filter (fun e => r ∈ e)).card +
        (G.edgeFinset.filter (fun e => s ∈ e)).card :=
          Finset.card_union_le _ _
    _ = G.degree r + G.degree s := by
          simp only [← G.incidenceFinset_eq_filter, G.card_incidenceFinset_eq_degree]
    _ ≤ 2 * d + 2 * d :=
          Nat.add_le_add (inducedLatticeGraph_degree_le d Λ r)
                         (inducedLatticeGraph_degree_le d Λ s)
    _ = 4 * d := by ring

/-- **Handshake bound**: on the induced lattice graph,
`|E| ≤ d · |Λ|`. -/
theorem inducedLatticeGraph_card_edgeFinset_le (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℝ)
      ≤ d * Fintype.card (↑Λ : Type _) := by
  -- 2|E| = ∑ degree ≤ 2d · |V|.
  have hdeg :
      ∑ v : ↑Λ, (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v
        ≤ 2 * d * Fintype.card (↑Λ : Type _) := by
    calc ∑ v : ↑Λ, (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v
        ≤ ∑ _ : ↑Λ, (2 * d : ℕ) :=
          Finset.sum_le_sum (fun v _ => inducedLatticeGraph_degree_le d Λ v)
      _ = Fintype.card (↑Λ : Type _) * (2 * d) := by
          simp [Finset.sum_const, mul_comm]
      _ = 2 * d * Fintype.card (↑Λ : Type _) := by ring
  have hhand :
      (2 * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        : ℕ) = ∑ v, (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).degree v := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hbnd :
      (2 * (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        : ℕ) ≤ 2 * d * Fintype.card (↑Λ : Type _) := by
    rw [hhand]; exact hdeg
  -- Divide by 2 (integer-level): 2|E| ≤ 2d|V| ⇒ |E| ≤ d|V|.
  have : ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
        : ℕ) ≤ d * Fintype.card (↑Λ : Type _) := by
    have h2 : 2 * ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℕ)
      ≤ 2 * (d * Fintype.card (↑Λ : Type _)) := by
      calc 2 * ((Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card : ℕ)
          ≤ 2 * d * Fintype.card (↑Λ : Type _) := hbnd
        _ = 2 * (d * Fintype.card (↑Λ : Type _)) := by ring
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  -- Cast to ℝ.
  exact_mod_cast this

/-- **Bounded edge density for `latticeGraph d` along `cubicExhaustion d`**:
`|E(latticeGraph d [Λ_n])| ≤ d · |Λ_n|` for every `n`. -/
theorem boundedEdgeDensity_latticeGraph_cubicExhaustion (d : ℕ) :
    Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) := by
  refine ⟨(d : ℝ), ?_⟩
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d ((Ambient.cubicExhaustion d).volume n)

end Ambient

end IsingModel
