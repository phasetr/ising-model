import IsingModel.AmbientLattice
import IsingModel.PartitionFunctionIso
import IsingModel.SumModel
import Mathlib.Data.Finset.Basic

/-!
# Super-additivity of `log Z` on `inducedGraph` over Finset disjoint union

Combining the disjoint-sum super-additivity machinery (PRs #134–#137)
with the graph isomorphism invariance (PR #138), we lift the
super-additivity inequality to `inducedGraph` on an actual
Finset disjoint union `Λ₁ ∪ Λ₂` of the ambient lattice `V`.

## Main declarations

* `IsingModel.inducedGraph_sum_map_le_union` — the transported
  disjoint sum of induced subgraphs is a subgraph of the induced
  subgraph on the union.
* `IsingModel.partitionFunction_inducedGraph_disjUnion_super_multiplicative`
  — the multiplicative form
  `Z_{inducedGraph G Λ₁} · Z_{inducedGraph G Λ₂}
    ≤ Z_{inducedGraph G (Λ₁ ∪ Λ₂)}` for ferromagnetic `p`.
* `IsingModel.log_partitionFunction_inducedGraph_disjUnion_super_additive`
  — the log form
  `log Z_{inducedGraph G Λ₁} + log Z_{inducedGraph G Λ₂}
    ≤ log Z_{inducedGraph G (Λ₁ ∪ Λ₂)}` for ferromagnetic `p`.
-/

namespace IsingModel

open Ambient

variable {V : Type*} [DecidableEq V]

/-- For disjoint `Λ₁, Λ₂ : Finset V`, the `Sum.inl`/`Sum.inr`
pushforward of the disjoint sum of induced subgraphs on `Λ₁, Λ₂`
(viewed as a graph on `↑Λ₁ ⊕ ↑Λ₂`) sits inside the induced
subgraph on `Λ₁ ∪ Λ₂` (after transport along
`Equiv.Finset.union`). -/
theorem inducedGraph_sum_map_le_union (G : SimpleGraph V)
    {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂) :
    ((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)).map
        (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding
      ≤ inducedGraph G (Λ₁ ∪ Λ₂) := by
  intro a b hab
  rw [SimpleGraph.map_adj'] at hab
  obtain ⟨_hne, x, y, hxy, hx, hy⟩ := hab
  rcases x with ⟨x, hx₁⟩ | ⟨x, hx₂⟩ <;>
    rcases y with ⟨y, hy₁⟩ | ⟨y, hy₂⟩
  · -- inl, inl
    subst hx; subst hy
    simpa [inducedGraph, SimpleGraph.induce] using hxy
  · -- inl, inr: disjoint sum graph has no such edge
    simp [SimpleGraph.sum_adj] at hxy
  · -- inr, inl: disjoint sum graph has no such edge
    simp [SimpleGraph.sum_adj] at hxy
  · -- inr, inr
    subst hx; subst hy
    simpa [inducedGraph, SimpleGraph.induce] using hxy

/-- **Super-multiplicative form** of `Z` on `inducedGraph` over
Finset disjoint union (Glimm–Jaffe §4.6 Prop 4.6.1 Step 5 body,
multiplicative form): for disjoint `Λ₁, Λ₂ : Finset V` and
ferromagnetic `p`,
```
Z_{inducedGraph G Λ₁}(p) · Z_{inducedGraph G Λ₂}(p)
  ≤ Z_{inducedGraph G (Λ₁ ∪ Λ₂)}(p).
```

Mirrors `partitionFunction_mul_le_of_sum_le` (PR #137) in the
ambient-lattice setting. -/
theorem partitionFunction_inducedGraph_disjUnion_super_multiplicative
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunction (inducedGraph G Λ₁) p
        * partitionFunction (inducedGraph G Λ₂) p
      ≤ partitionFunction (inducedGraph G (Λ₁ ∪ Λ₂)) p := by
  classical
  calc partitionFunction (inducedGraph G Λ₁) p
          * partitionFunction (inducedGraph G Λ₂) p
      = partitionFunction
          ((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)) p :=
        (partitionFunction_sum _ _ _).symm
    _ = partitionFunction
          (((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)).map
            (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding) p :=
        (partitionFunction_map_equiv _ _ _).symm
    _ ≤ partitionFunction (inducedGraph G (Λ₁ ∪ Λ₂)) p :=
        partitionFunction_monotone_subgraph
          (inducedGraph_sum_map_le_union G hd) p hf

/-- **Super-additivity of `log Z` on `inducedGraph` over Finset
disjoint union** (Glimm–Jaffe §4.6 Prop 4.6.1 Step 5 body):
for disjoint `Λ₁, Λ₂ : Finset V` and ferromagnetic `p`,
```
log Z_{inducedGraph G Λ₁}(p) + log Z_{inducedGraph G Λ₂}(p)
  ≤ log Z_{inducedGraph G (Λ₁ ∪ Λ₂)}(p).
```

Proof chain.
1. By PR #136 `log_partitionFunction_sum`, the LHS equals
   `log Z_{(inducedGraph G Λ₁).sum (inducedGraph G Λ₂)}`.
2. By PR #138 `log_partitionFunction_map_equiv`, pushing the
   disjoint sum along `(Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding`
   leaves `log Z` unchanged.
3. The pushforward is a subgraph of `inducedGraph G (Λ₁ ∪ Λ₂)`
   by `inducedGraph_sum_map_le_union`.
4. Ferromagnetic subgraph monotonicity of `log Z`
   (`log_partitionFunction_monotone_subgraph`, PR #137 refactor)
   closes. -/
theorem log_partitionFunction_inducedGraph_disjUnion_super_additive
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunction (inducedGraph G Λ₁) p)
      + Real.log (partitionFunction (inducedGraph G Λ₂) p)
    ≤ Real.log (partitionFunction (inducedGraph G (Λ₁ ∪ Λ₂)) p) := by
  classical
  calc Real.log (partitionFunction (inducedGraph G Λ₁) p)
          + Real.log (partitionFunction (inducedGraph G Λ₂) p)
      = Real.log (partitionFunction
          ((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)) p) :=
        (log_partitionFunction_sum _ _ _).symm
    _ = Real.log (partitionFunction
          (((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)).map
            (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding) p) :=
        (log_partitionFunction_map_equiv _ _ _).symm
    _ ≤ Real.log (partitionFunction (inducedGraph G (Λ₁ ∪ Λ₂)) p) :=
        log_partitionFunction_monotone_subgraph
          (inducedGraph_sum_map_le_union G hd) p hf

end IsingModel
