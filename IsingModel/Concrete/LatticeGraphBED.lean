import IsingModel.Concrete.CubicExhaustion
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Bounded edge density of `latticeGraph d` on cubic boxes

Combining `IsingModel/Concrete/CubicExhaustion.lean` (concrete
`Ambient.Exhaustion (Fin d → ℤ)`) with the lattice graph degree
bound, we prove
`Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d)
(Ambient.cubicExhaustion d)` with constant `c = d`.

## Main theorems

* `latticeGraph_adj_mem_neighborEnum` — every neighbour of `v` in
  `latticeGraph d` lies in a `2d`-element candidate set
  (`Function.update v i (v i ± 1)` over `i : Fin d`).
* `inducedLatticeGraph_degree_le` — induced-graph degree bounded by
  `2 * d` for every vertex.
* `boundedEdgeDensity_latticeGraph_cubicExhaustion` —
  `|E(latticeGraph d [Λ_n])| ≤ d · |Λ_n|`, via handshake.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 67.
-/

namespace IsingModel

namespace Ambient

open Finset SimpleGraph

/-- **Candidate neighbours of `v` in `latticeGraph d`**: for `v : Fin d → ℤ`,
the `2d`-element set `{Function.update v i (v i + 1), Function.update v i (v i - 1)
| i : Fin d}` of possible ℓ¹-distance-1 neighbours. -/
noncomputable def latticeNeighborEnum (d : ℕ) (v : Fin d → ℤ) :
    Finset (Fin d → ℤ) :=
  (Finset.univ : Finset (Fin d)).biUnion (fun i =>
    ({Function.update v i (v i + 1),
      Function.update v i (v i - 1)} : Finset (Fin d → ℤ)))

/-- **Size bound on the neighbour-candidate set**:
`|latticeNeighborEnum d v| ≤ 2 * d`. -/
theorem latticeNeighborEnum_card_le (d : ℕ) (v : Fin d → ℤ) :
    (latticeNeighborEnum d v).card ≤ 2 * d := by
  unfold latticeNeighborEnum
  calc ((Finset.univ : Finset (Fin d)).biUnion (fun i =>
          ({Function.update v i (v i + 1),
            Function.update v i (v i - 1)} : Finset (Fin d → ℤ)))).card
      ≤ ∑ i : Fin d, (({Function.update v i (v i + 1),
                        Function.update v i (v i - 1)} :
                        Finset (Fin d → ℤ)).card) := Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin d, 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.card_insert_le _ _ |>.trans (by simp)
    _ = 2 * d := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-- **Every neighbour of `v` in `latticeGraph d` lies in `latticeNeighborEnum d v`**:
the `Adj` condition `∑ i, |v i - w i| = 1` forces exactly one coordinate
to differ by `±1`, so `w = Function.update v i (v i ± 1)` for some `i`. -/
theorem latticeGraph_adj_mem_neighborEnum (d : ℕ) (v w : Fin d → ℤ)
    (h : (IsingModel.latticeGraph d).Adj v w) :
    w ∈ latticeNeighborEnum d v := by
  -- `h` unfolds to `∑ i, |v i - w i| = 1`.
  have hsum : (∑ i : Fin d, |v i - w i|) = 1 := h
  -- Since the sum of non-negative integers equals 1, exactly one
  -- term is 1 and all others are 0.
  have hnonneg : ∀ i : Fin d, 0 ≤ |v i - w i| := fun i => abs_nonneg _
  -- There exists `i` with `|v i - w i| ≥ 1`, and in fact `= 1`;
  -- for all `j ≠ i`, `|v j - w j| = 0`.
  have hexist : ∃ i : Fin d, |v i - w i| = 1 := by
    by_contra hne
    push Not at hne
    -- Each |v i - w i| is ≠ 1, ≥ 0, integer ⇒ = 0 or ≥ 2.
    -- All zero: sum 0 ≠ 1. Some ≥ 2: sum ≥ 2 ≠ 1.
    have hall : ∀ i, |v i - w i| = 0 ∨ 2 ≤ |v i - w i| := by
      intro i
      specialize hne i
      rcases lt_or_ge (|v i - w i|) 1 with hlt | hge
      · left
        have : |v i - w i| = 0 := by
          have : (0 : ℤ) ≤ |v i - w i| := hnonneg i
          omega
        exact this
      · right
        -- `1 ≤ |·|` and `|·| ≠ 1` means `2 ≤ |·|`.
        omega
    by_cases hallz : ∀ i, |v i - w i| = 0
    · have : (∑ i : Fin d, |v i - w i|) = 0 := by
        rw [Finset.sum_eq_zero]
        intro i _
        exact hallz i
      omega
    · push Not at hallz
      obtain ⟨j, hj⟩ := hallz
      rcases hall j with h0 | h2
      · exact hj h0
      · have : 2 ≤ ∑ i : Fin d, |v i - w i| := by
          calc (2 : ℤ) ≤ |v j - w j| := h2
            _ ≤ ∑ i : Fin d, |v i - w i| :=
                Finset.single_le_sum (f := fun i => |v i - w i|)
                  (fun i _ => hnonneg i) (Finset.mem_univ j)
        omega
  obtain ⟨i, hi⟩ := hexist
  -- The `i`-th coordinate differs by ±1, all others agree.
  have hothers : ∀ j, j ≠ i → v j = w j := by
    intro j hji
    have hsum' : (∑ k : Fin d, |v k - w k|)
        = |v i - w i| + ∑ k ∈ Finset.univ.erase i, |v k - w k| := by
      rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)]
      simp [Finset.sdiff_singleton_eq_erase, add_comm]
    rw [hi, hsum] at hsum'
    have hsum_erase : (∑ k ∈ Finset.univ.erase i, |v k - w k|) = 0 := by omega
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
    have hj_zero : |v j - w j| = 0 := by
      have hnn : ∀ k ∈ Finset.univ.erase i, 0 ≤ |v k - w k| := fun k _ => hnonneg k
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_erase _ hj_mem
    have : v j - w j = 0 := by
      have := abs_eq_zero.mp hj_zero
      exact this
    linarith
  -- Therefore `w = Function.update v i (w i)` and `w i = v i ± 1`.
  have hvi_cases : w i = v i + 1 ∨ w i = v i - 1 := by
    have : |v i - w i| = 1 := hi
    rcases abs_eq (by norm_num : (0:ℤ) ≤ 1) |>.mp this with ha | hb
    · right; linarith
    · left; linarith
  have hw_eq : w = Function.update v i (w i) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_apply, if_neg hk]
      exact (hothers k hk).symm
  unfold latticeNeighborEnum
  rw [Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rcases hvi_cases with h1 | h2
  · rw [Finset.mem_insert, Finset.mem_singleton]
    left
    rw [hw_eq, h1]
  · rw [Finset.mem_insert, Finset.mem_singleton]
    right
    rw [hw_eq, h2]

/-- **`Fintype` instance for the neighbour set of `latticeGraph d`**:
every vertex `v : Fin d → ℤ` has finitely many neighbours,
exhibited as the filter of the candidate set
`latticeNeighborEnum d v` along the adjacency relation. This
upgrades `IsingModel.latticeGraph d` to a `LocallyFinite` simple
graph in mathlib's sense (`SimpleGraph.LocallyFinite` is an
`abbrev` for `∀ v, Fintype (G.neighborSet v)`), unlocking the
unrestricted `neighborFinset` / `degree` API on the infinite
vertex set. Until now the project's `Fintype` reasoning all
happened on the induced subgraph
`(Ambient.inducedGraph (latticeGraph d) Λ)` for finite
`Λ : Finset _`. -/
noncomputable instance latticeGraph_neighborSet_fintype
    (d : ℕ) (v : Fin d → ℤ) :
    Fintype ((IsingModel.latticeGraph d).neighborSet v) :=
  Fintype.ofFinset
    ((latticeNeighborEnum d v).filter ((IsingModel.latticeGraph d).Adj v))
    (fun w => by
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborSet]
      refine ⟨fun h => h.2, fun hadj => ?_⟩
      exact ⟨latticeGraph_adj_mem_neighborEnum d v w hadj, hadj⟩)

/-- **Per-vertex degree bound for the unrestricted `latticeGraph d`**:
every vertex has degree at most `2 * d`. Mirror of the existing
`inducedLatticeGraph_degree_le` (PR #608) on the ambient graph,
made statable by the `LocallyFinite` instance above. The proof
embeds the (now well-defined) `neighborFinset v` into
`latticeNeighborEnum d v` via `latticeGraph_adj_mem_neighborEnum`
and chains `Finset.card_le_card` with the existing
`latticeNeighborEnum_card_le`. -/
theorem latticeGraph_degree_le (d : ℕ) (v : Fin d → ℤ) :
    (IsingModel.latticeGraph d).degree v ≤ 2 * d := by
  have hsubset : (IsingModel.latticeGraph d).neighborFinset v ⊆
      latticeNeighborEnum d v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact latticeGraph_adj_mem_neighborEnum d v w hw
  calc (IsingModel.latticeGraph d).degree v
      = ((IsingModel.latticeGraph d).neighborFinset v).card := rfl
    _ ≤ (latticeNeighborEnum d v).card := Finset.card_le_card hsubset
    _ ≤ 2 * d := latticeNeighborEnum_card_le d v

/-- Decidable-Adj instance for the induced lattice graph.

Provided explicitly because the generic `instDecidableRel_induce_adj`
does not fire through the `noncomputable def Ambient.inducedGraph`
wrapper automatically. -/
instance (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    DecidableRel (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).Adj :=
  fun ⟨a, _⟩ ⟨b, _⟩ => by
    unfold Ambient.inducedGraph SimpleGraph.induce
    exact inferInstance

/-- Fintype instance for the edge set of the induced lattice graph
on a cubic box.

Provided explicitly to thread through `Ambient.inducedGraph` — the
generic `SimpleGraph.fintypeEdgeSet` would fire directly on
`SimpleGraph.induce` but the `noncomputable def` wrapper masks this. -/
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
