import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.PartitionFunctionIso
import IsingModel.SumModel
import IsingModel.AmbientLatticeSumFreeEnergy
import IsingModel.AmbientLatticeSumGeFerromagnetic
import IsingModel.AmbientLatticeSumLogZ
import IsingModel.AmbientLatticeSumFInfHSymMono
import Mathlib.Analysis.Subadditive
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
* `IsingModel.Ambient.partitionFunctionΛ_disjUnion_super_multiplicative` /
  `IsingModel.Ambient.log_partitionFunctionΛ_disjUnion_super_additive` —
  wrappers expressed in the `partitionFunctionΛ` / log form.
* `IsingModel.Ambient.card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty`
  — the identity `|Λ| · freeEnergyΛ Λ = log Z_Λ` for nonempty `Λ`.
* `IsingModel.Ambient.freeEnergyΛ_weighted_super_additive_of_nonempty`
  — weighted super-additivity
  `|Λ₁| · f_{Λ₁} + |Λ₂| · f_{Λ₂} ≤ |Λ₁ ∪ Λ₂| · f_{Λ₁ ∪ Λ₂}`
  for disjoint nonempty `Λ₁, Λ₂`.
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

set_option linter.unusedFintypeInType false in
/-- **Monotonicity step `log Z_Λ₁ ≤ log Z_{Λ₁ ∪ Λ₂}`** for disjoint
`Λ₁, Λ₂` under ferromagnetic parameters.

Proof: `log Z_Λ₁ ≤ log Z_Λ₁ + log Z_Λ₂` (since `log Z_Λ₂ ≥ 0` by
`log_partitionFunction_nonneg_of_ferromagnetic`), and the right-hand
side is `≤ log Z_{Λ₁ ∪ Λ₂}` by the Step 5 super-additivity
(`log_partitionFunction_inducedGraph_disjUnion_super_additive`). The
`[Fintype (inducedGraph G Λ₂).edgeSet]` instance is used internally
via the super-additivity lemma even though it does not appear in the
conclusion. -/
theorem log_partitionFunction_inducedGraph_le_of_disjoint_union
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunction (inducedGraph G Λ₁) p)
      ≤ Real.log (partitionFunction (inducedGraph G (Λ₁ ∪ Λ₂)) p) := by
  calc Real.log (partitionFunction (inducedGraph G Λ₁) p)
      ≤ Real.log (partitionFunction (inducedGraph G Λ₁) p)
          + Real.log (partitionFunction (inducedGraph G Λ₂) p) :=
        le_add_of_nonneg_right
          (log_partitionFunction_nonneg_of_ferromagnetic _ p hf)
    _ ≤ Real.log (partitionFunction (inducedGraph G (Λ₁ ∪ Λ₂)) p) :=
        log_partitionFunction_inducedGraph_disjUnion_super_additive
          G hd p hf

set_option linter.unusedFintypeInType false in
/-- Multiplicative form: `Z_{Λ₁} ≤ Z_{Λ₁ ∪ Λ₂}` for disjoint
`Λ₁, Λ₂` under ferromagnetic parameters. -/
theorem partitionFunction_inducedGraph_le_of_disjoint_union
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunction (inducedGraph G Λ₁) p
      ≤ partitionFunction (inducedGraph G (Λ₁ ∪ Λ₂)) p :=
  (Real.log_le_log_iff (partitionFunction_pos _ _)
    (partitionFunction_pos _ _)).mp
    (log_partitionFunction_inducedGraph_le_of_disjoint_union G hd p hf)

/-- **Induced union splits as a disjoint sum when there are no cross edges**:
for disjoint `Λ₁, Λ₂ : Finset V` with no `G`-edge between `Λ₁` and `Λ₂`, the
induced subgraph on the union equals the transported disjoint sum of the two
induced subgraphs. Upgrades `inducedGraph_sum_map_le_union` to an equality: the
`≤` direction is that lemma; the `≥` direction holds because, with no cross
edges, every edge of `inducedGraph G (Λ₁ ∪ Λ₂)` has both endpoints in the same
part. This is the structural fact behind the component factorization of a
bond-deleted (fully separated) finite-volume system (Issue #2965, Phase A). -/
theorem inducedGraph_sum_map_eq_union_of_no_cross (G : SimpleGraph V)
    {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    (hcross : ∀ a ∈ Λ₁, ∀ b ∈ Λ₂, ¬ G.Adj a b) :
    ((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)).map
        (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding
      = inducedGraph G (Λ₁ ∪ Λ₂) := by
  refine le_antisymm (inducedGraph_sum_map_le_union G hd) ?_
  intro a b hab
  have hGadj : G.Adj (a : V) (b : V) := hab
  rw [SimpleGraph.map_adj]
  rcases Finset.mem_union.mp a.2 with ha | ha <;>
    rcases Finset.mem_union.mp b.2 with hb | hb
  · exact ⟨Sum.inl ⟨↑a, ha⟩, Sum.inl ⟨↑b, hb⟩, by
      simpa [SimpleGraph.sum_adj, inducedGraph, SimpleGraph.induce] using hGadj,
      by simp, by simp⟩
  · exact absurd hGadj (hcross _ ha _ hb)
  · exact absurd hGadj.symm (hcross _ hb _ ha)
  · exact ⟨Sum.inr ⟨↑a, ha⟩, Sum.inr ⟨↑b, hb⟩, by
      simpa [SimpleGraph.sum_adj, inducedGraph, SimpleGraph.induce] using hGadj,
      by simp, by simp⟩

set_option linter.unusedFintypeInType false in
/-- **Component factorization of an induced-union correlation under no cross
edges** (stated on the transported disjoint sum): for disjoint `Λ₁, Λ₂` with no
`G`-edge between them, an observable supported on `Λ₁` has the same correlation
in the transported disjoint sum (which equals `inducedGraph G (Λ₁ ∪ Λ₂)` by
`inducedGraph_sum_map_eq_union_of_no_cross`) as in the induced subgraph on `Λ₁`
alone. Combines `correlation_map_equiv` (iso transport) with
`correlation_sum_inl` (disjoint-sum factorization).

This is the bridge from a fully separated (bond-deleted) finite-volume system to
the isolated-component correlation (Issue #2965, Phase A). The result is stated
on `(... ).map (Equiv.Finset.union ...)` rather than directly on
`inducedGraph G (Λ₁ ∪ Λ₂)` because rewriting the graph through the equality would
require transporting the `Fintype edgeSet` instance; the equality lemma above
records that the two graphs coincide. -/
theorem correlation_inducedGraph_sum_map_inl (G : SimpleGraph V)
    {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)).map
      (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ₁ : Type _)) :
    correlation (((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)).map
        (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding) p
        ((A.map ⟨Sum.inl, Sum.inl_injective⟩).map
          (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding)
      = correlation (inducedGraph G Λ₁) p A := by
  rw [correlation_map_equiv, correlation_sum_inl]

/-- **Correlation is invariant under graph equality**, regardless of which
`Fintype edgeSet` instance is used: if `G₁ = G₂` then their correlations agree.
Correlation depends on the graph only through `edgeFinset` (inside the
Hamiltonian's interaction energy), and `edgeFinset` is instance-independent
since it coerces to `edgeSet`. This lets one transport correlations across the
graph equalities of this file (e.g. `inducedGraph_sum_map_eq_union_of_no_cross`)
without the `Fintype` motive obstruction that blocks `rw`. -/
theorem correlation_congr_of_eq {W : Type*} [Fintype W] [DecidableEq W]
    {G₁ G₂ : SimpleGraph W}
    [inst₁ : Fintype G₁.edgeSet] [inst₂ : Fintype G₂.edgeSet]
    (h : G₁ = G₂) (p : IsingParams ℝ) (A : Finset W) :
    correlation G₁ p A = correlation G₂ p A := by
  subst h
  -- After `subst`, both sides are the same graph; the only residual difference is
  -- the `Fintype G₁.edgeSet` instance the Hamiltonian's interaction energy feeds to
  -- `edgeFinset`. Since `edgeFinset` coerces to the instance-free `edgeSet`, the two
  -- edge finsets are equal, which `simp` propagates through `correlation`.
  have hef : @SimpleGraph.edgeFinset _ G₁ inst₁ = @SimpleGraph.edgeFinset _ G₁ inst₂ := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset]
  simp only [correlation, gibbsExpectation, partitionFunction, boltzmannWeight,
    hamiltonian, interactionEnergy, hef]

set_option linter.unusedFintypeInType false in
/-- **Component factorization of an induced-union correlation (union form)**:
the bridge of `correlation_inducedGraph_sum_map_inl` transported onto
`inducedGraph G (Λ₁ ∪ Λ₂)` itself, via `inducedGraph_sum_map_eq_union_of_no_cross`
and `correlation_congr_of_eq` (which absorbs the `Fintype` instance change). For
disjoint `Λ₁, Λ₂` with no `G`-edge between them, an observable supported on `Λ₁`
has the same correlation in the induced subgraph on the union as in the induced
subgraph on `Λ₁` alone — the component-factorization bridge in the form directly
usable for exhaustion stages (Issue #2965, Phase A). -/
theorem correlation_inducedGraph_union_inl_of_no_cross (G : SimpleGraph V)
    {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    (hcross : ∀ a ∈ Λ₁, ∀ b ∈ Λ₂, ¬ G.Adj a b)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (((inducedGraph G Λ₁).sum (inducedGraph G Λ₂)).map
      (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (A : Finset (↑Λ₁ : Type _)) :
    correlation (inducedGraph G (Λ₁ ∪ Λ₂)) p
        ((A.map ⟨Sum.inl, Sum.inl_injective⟩).map
          (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding)
      = correlation (inducedGraph G Λ₁) p A :=
  Eq.trans
    (correlation_congr_of_eq
      (inducedGraph_sum_map_eq_union_of_no_cross G hd hcross).symm p
      ((A.map ⟨Sum.inl, Sum.inl_injective⟩).map
        (Equiv.Finset.union Λ₁ Λ₂ hd).toEmbedding))
    (correlation_inducedGraph_sum_map_inl G hd p A)

end IsingModel
