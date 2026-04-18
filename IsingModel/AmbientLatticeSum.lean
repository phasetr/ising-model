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

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- Wrapper of `partitionFunction_inducedGraph_disjUnion_super_multiplicative`
at the `partitionFunctionΛ` API level. -/
theorem partitionFunctionΛ_disjUnion_super_multiplicative
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ G Λ₁ p * partitionFunctionΛ G Λ₂ p
      ≤ partitionFunctionΛ G (Λ₁ ∪ Λ₂) p :=
  IsingModel.partitionFunction_inducedGraph_disjUnion_super_multiplicative
    G hd p hf

/-- Wrapper of
`log_partitionFunction_inducedGraph_disjUnion_super_additive` at the
`partitionFunctionΛ` API level. -/
theorem log_partitionFunctionΛ_disjUnion_super_additive
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ G Λ₁ p)
      + Real.log (partitionFunctionΛ G Λ₂ p)
    ≤ Real.log (partitionFunctionΛ G (Λ₁ ∪ Λ₂) p) :=
  IsingModel.log_partitionFunction_inducedGraph_disjUnion_super_additive
    G hd p hf

/-- Identity `|Λ| · freeEnergyΛ G Λ p = log (partitionFunctionΛ G Λ p)`
for nonempty `Λ`. Unfolds `freeEnergy = |ι|⁻¹ · log Z` and cancels
`(Λ.card : ℝ) > 0` against its inverse via `field_simp`. The
`Nonempty` hypothesis is needed at the proof level to rule out the
`|Λ| = 0` degenerate case (where the identity still holds but the
cancellation step does not apply uniformly). -/
theorem card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) :
    (Λ.card : ℝ) * freeEnergyΛ G Λ p
      = Real.log (partitionFunctionΛ G Λ p) := by
  unfold freeEnergyΛ IsingModel.freeEnergy
  rw [Fintype.card_coe]
  have hne_card : (Λ.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
  -- Clear `(Λ.card : ℝ)⁻¹` against the outer `Λ.card` using `hne_card`.
  field_simp
  rfl

/-- **Weighted super-additivity of the free energy density** on
disjoint Finset unions (nonempty case):
```
|Λ₁| · freeEnergyΛ G Λ₁ p + |Λ₂| · freeEnergyΛ G Λ₂ p
  ≤ |Λ₁ ∪ Λ₂| · freeEnergyΛ G (Λ₁ ∪ Λ₂) p
```
for disjoint nonempty `Λ₁, Λ₂` and ferromagnetic `p`.

This is the Finset-weighted form of the Step 5 super-additivity
inequality, suitable as input for a Fekete-style convergence
argument. -/
theorem freeEnergyΛ_weighted_super_additive_of_nonempty
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V}
    (hne₁ : Λ₁.Nonempty) (hne₂ : Λ₂.Nonempty) (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ₁.card : ℝ) * freeEnergyΛ G Λ₁ p
      + (Λ₂.card : ℝ) * freeEnergyΛ G Λ₂ p
    ≤ ((Λ₁ ∪ Λ₂).card : ℝ) * freeEnergyΛ G (Λ₁ ∪ Λ₂) p := by
  have hne_union : (Λ₁ ∪ Λ₂).Nonempty := hne₁.mono Finset.subset_union_left
  rw [card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty G hne₁,
      card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty G hne₂,
      card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty G hne_union]
  exact log_partitionFunctionΛ_disjUnion_super_additive G hd p hf

set_option linter.unusedFintypeInType false in
/-- Wrapper at the `partitionFunctionΛ` API level:
for disjoint `Λ₁, Λ₂`, `log Z_{Λ₁} ≤ log Z_{Λ₁ ∪ Λ₂}` under
ferromagnetic parameters. -/
theorem log_partitionFunctionΛ_le_of_disjoint_union
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Real.log (partitionFunctionΛ G Λ₁ p)
      ≤ Real.log (partitionFunctionΛ G (Λ₁ ∪ Λ₂) p) :=
  IsingModel.log_partitionFunction_inducedGraph_le_of_disjoint_union
    G hd p hf

set_option linter.unusedFintypeInType false in
/-- Multiplicative form at the `partitionFunctionΛ` API level:
for disjoint `Λ₁, Λ₂`, `Z_{Λ₁} ≤ Z_{Λ₁ ∪ Λ₂}` under ferromagnetic
parameters. -/
theorem partitionFunctionΛ_le_of_disjoint_union
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    partitionFunctionΛ G Λ₁ p ≤ partitionFunctionΛ G (Λ₁ ∪ Λ₂) p :=
  IsingModel.partitionFunction_inducedGraph_le_of_disjoint_union
    G hd p hf

/-- `partitionFunctionΛ` respects Finset equality.
Proved by substituting the equation away and using subsingleton
uniqueness of the Fintype instance on the (now-equal) edge set. -/
theorem partitionFunctionΛ_congr_finset
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V} (h : Λ₁ = Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    (p : IsingParams ℝ) :
    partitionFunctionΛ G Λ₁ p = partitionFunctionΛ G Λ₂ p := by
  subst h
  congr
  exact Subsingleton.elim _ _

set_option linter.unusedFintypeInType false in
/-- **`partitionFunctionAlongExhaustion` is monotone in `n`**
along any `Exhaustion Λ` under ferromagnetic parameters.

Proof chain:
1. `Λ.mono` gives `Λ.volume n ⊆ Λ.volume (n + 1)`;
2. Split `Λ.volume (n + 1) = Λ.volume n ⊔ (Λ.volume (n + 1) \ Λ.volume n)`
   using `Finset.union_sdiff_of_subset`;
3. Apply PR #142 `partitionFunctionΛ_le_of_disjoint_union` to the
   disjoint split;
4. Transport the resulting RHS back via
   `partitionFunctionΛ_congr_finset`. -/
theorem partitionFunctionAlongExhaustion_monotone_volume
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ m, Fintype (inducedGraph G (Λ.volume m)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ)
    [Fintype (inducedGraph G (Λ.volume (n + 1) \ Λ.volume n)).edgeSet] :
    partitionFunctionAlongExhaustion G Λ p n
      ≤ partitionFunctionAlongExhaustion G Λ p (n + 1) := by
  have hsub : Λ.volume n ⊆ Λ.volume (n + 1) := Λ.mono (Nat.le_succ n)
  have hd : Disjoint (Λ.volume n) (Λ.volume (n + 1) \ Λ.volume n) :=
    Finset.disjoint_sdiff
  have hunion : Λ.volume n ∪ (Λ.volume (n + 1) \ Λ.volume n)
      = Λ.volume (n + 1) := Finset.union_sdiff_of_subset hsub
  haveI : Fintype (inducedGraph G (Λ.volume n ∪
      (Λ.volume (n + 1) \ Λ.volume n))).edgeSet := by
    rw [hunion]; infer_instance
  have key := partitionFunctionΛ_le_of_disjoint_union G hd p hf
  have heq := partitionFunctionΛ_congr_finset G hunion p
  -- Rewrite `partitionFunctionAlongExhaustion` to `partitionFunctionΛ`
  -- (definitional), then chain.
  change partitionFunctionΛ G (Λ.volume n) p
    ≤ partitionFunctionΛ G (Λ.volume (n + 1)) p
  calc partitionFunctionΛ G (Λ.volume n) p
      ≤ partitionFunctionΛ G (Λ.volume n ∪
          (Λ.volume (n + 1) \ Λ.volume n)) p := key
    _ = partitionFunctionΛ G (Λ.volume (n + 1)) p := heq

set_option linter.unusedFintypeInType false in
/-- Log form of `partitionFunctionAlongExhaustion_monotone_volume`. -/
theorem log_partitionFunctionAlongExhaustion_monotone_volume
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ m, Fintype (inducedGraph G (Λ.volume m)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ)
    [Fintype (inducedGraph G (Λ.volume (n + 1) \ Λ.volume n)).edgeSet] :
    Real.log (partitionFunctionAlongExhaustion G Λ p n)
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ p (n + 1)) :=
  Real.log_le_log (partitionFunctionΛ_pos G (Λ.volume n) p)
    (partitionFunctionAlongExhaustion_monotone_volume G Λ p hf n)

set_option linter.unusedFintypeInType false in
/-- **`partitionFunctionAlongExhaustion` is `Monotone`** along any
Exhaustion for ferromagnetic parameters. Packages the step-wise
`partitionFunctionAlongExhaustion_monotone_volume` as a
`Monotone` predicate, ready for use with mathlib convergence
lemmas (`Monotone.tendsto_atTop_of_bddAbove`, etc.). -/
theorem partitionFunctionAlongExhaustion_monotone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ m, Fintype (inducedGraph G (Λ.volume m)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ.volume (n + 1) \ Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Monotone (partitionFunctionAlongExhaustion G Λ p) :=
  monotone_nat_of_le_succ fun n =>
    partitionFunctionAlongExhaustion_monotone_volume G Λ p hf n

set_option linter.unusedFintypeInType false in
/-- `Monotone` form for `log Z` along an Exhaustion. -/
theorem log_partitionFunctionAlongExhaustion_monotone
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ m, Fintype (inducedGraph G (Λ.volume m)).edgeSet]
    [∀ n, Fintype (inducedGraph G (Λ.volume (n + 1) \ Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Monotone (fun n => Real.log (partitionFunctionAlongExhaustion G Λ p n)) :=
  monotone_nat_of_le_succ fun n =>
    log_partitionFunctionAlongExhaustion_monotone_volume G Λ p hf n

set_option linter.unusedFintypeInType false in
/-- `freeEnergyΛ` weighted form of the disjoint-union monotonicity:
for nonempty `Λ₁` disjoint from `Λ₂`,
`|Λ₁| · freeEnergyΛ Λ₁ ≤ |Λ₁ ∪ Λ₂| · freeEnergyΛ (Λ₁ ∪ Λ₂)`
under ferromagnetic parameters.

Derived from `card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty`
(PR #140) together with `log_partitionFunctionΛ_le_of_disjoint_union`
(PR #142). -/
theorem card_mul_freeEnergyΛ_le_of_disjoint_union
    (G : SimpleGraph V) {Λ₁ Λ₂ : Finset V}
    (hne₁ : Λ₁.Nonempty) (hd : Disjoint Λ₁ Λ₂)
    [Fintype (inducedGraph G Λ₁).edgeSet]
    [Fintype (inducedGraph G Λ₂).edgeSet]
    [Fintype (inducedGraph G (Λ₁ ∪ Λ₂)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ₁.card : ℝ) * freeEnergyΛ G Λ₁ p
      ≤ ((Λ₁ ∪ Λ₂).card : ℝ) * freeEnergyΛ G (Λ₁ ∪ Λ₂) p := by
  have hne_union : (Λ₁ ∪ Λ₂).Nonempty := hne₁.mono Finset.subset_union_left
  rw [card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty G hne₁,
      card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty G hne_union]
  exact log_partitionFunctionΛ_le_of_disjoint_union G hd p hf

/-- **Uniform upper bound on `freeEnergyInfinite` under bounded edge density**:
the per-n bound of PR #123 lifts to `limsup`:
`freeEnergyInfinite G Λ p ≤ log 2 + |β|·(|J|·c + |h|)` for ferromagnetic `p`.

Proof outline.
1. By `Exhaustion.exhaust`, any vertex of a nonempty `V` is
   eventually in `Λ.volume n`, so `(Λ.volume n).Nonempty` holds
   eventually (atTop).
2. Apply the per-n upper bound
   `freeEnergyAlongExhaustion_le_uniform_upper_bound` under the
   eventual hypothesis — this gives the `∀ᶠ`-form of the bound.
3. For `Filter.IsCoboundedUnder (· ≤ ·)`, use the (ferromagnetic)
   lower bound `freeEnergyAlongExhaustion_ge_log_two_cosh`.
4. `Filter.limsup_le_of_le` concludes. -/
theorem freeEnergyInfinite_le_uniform_upper_bound
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G Λ p ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
  -- Eventual nonemptiness from exhaust.
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨N, hN⟩ := Λ.exhaust {v}
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact ⟨v, hN n hn (Finset.mem_singleton_self v)⟩
  have hbound : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ p n
        ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) := by
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne
  have hbdd_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ p) := by
    refine ⟨Real.log (2 * Real.cosh (p.β * p.h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      (J := p.J) (h := p.h) (β := p.β) G Λ hf.hJ hf.hh hf.hβ n hne
  exact Filter.limsup_le_of_le hbdd_below.isCoboundedUnder_le hbound

/-- **Uniform lower bound on `freeEnergyInfinite` under ferromagnetic**:
the per-n sharp lower bound of PR #125 lifts to `limsup`:
`log(2·cosh(β·h)) ≤ freeEnergyInfinite G Λ p`.

Proof outline:
1. `Λ.exhaust {v}` gives eventual `(Λ.volume n).Nonempty`.
2. The ferromagnetic per-n lower bound
   `freeEnergyAlongExhaustion_ge_log_two_cosh` provides the
   `∀ᶠ`-form of the lower bound.
3. The `BoundedEdgeDensity`-based upper bound of PR #123 provides
   `IsBoundedUnder (· ≤ ·)` (needed by `le_limsup_of_frequently_le`).
4. `Filter.le_limsup_of_frequently_le` concludes. -/
theorem freeEnergyInfinite_ge_log_two_cosh
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log (2 * Real.cosh (p.β * p.h))
      ≤ freeEnergyInfinite G Λ p := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨N, hN⟩ := Λ.exhaust {v}
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact ⟨v, hN n hn (Finset.mem_singleton_self v)⟩
  have hlower : ∀ᶠ n in Filter.atTop,
      Real.log (2 * Real.cosh (p.β * p.h))
        ≤ freeEnergyAlongExhaustion G Λ p n := by
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      (J := p.J) (h := p.h) (β := p.β) G Λ hf.hJ hf.hh hf.hβ n hne
  have hbdd_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ p) := by
    refine ⟨Real.log 2 + |p.β| * (|p.J| * c + |p.h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ p hc n hne
  exact Filter.le_limsup_of_frequently_le hlower.frequently hbdd_above

/-- **Corollary**: `log 2 ≤ freeEnergyInfinite G Λ p` under the same
hypotheses as `freeEnergyInfinite_ge_log_two_cosh`.

Follows from `cosh (β h) ≥ cosh 0 = 1` (`Real.one_le_cosh`), which
gives `2 · cosh (β h) ≥ 2` and hence
`log (2 · cosh (β h)) ≥ log 2`. -/
theorem freeEnergyInfinite_ge_log_two
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    Real.log 2 ≤ freeEnergyInfinite G Λ p := by
  have h_cosh_ge_one : (1 : ℝ) ≤ Real.cosh (p.β * p.h) :=
    Real.one_le_cosh _
  have h_le : Real.log 2 ≤ Real.log (2 * Real.cosh (p.β * p.h)) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    linarith
  exact h_le.trans
    (freeEnergyInfinite_ge_log_two_cosh G Λ p hf hc)

/-- **Strict positivity** of `freeEnergyInfinite` under the standard
ferromagnetic + `BoundedEdgeDensity` + `[Nonempty V]` setup:
`0 < freeEnergyInfinite G Λ p`.

Follows from `freeEnergyInfinite_ge_log_two` together with
`Real.log_pos` at `2 > 1`. -/
theorem freeEnergyInfinite_pos
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 < freeEnergyInfinite G Λ p :=
  (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le
    (freeEnergyInfinite_ge_log_two G Λ p hf hc)

/-- **Nonnegativity** of `freeEnergyInfinite` under the standard
hypotheses. Immediate from strict positivity. -/
theorem freeEnergyInfinite_nonneg
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    0 ≤ freeEnergyInfinite G Λ p :=
  (freeEnergyInfinite_pos G Λ p hf hc).le

set_option linter.unusedFintypeInType false in
/-- **`freeEnergyInfinite` is monotone in the ambient subgraph**:
for `G₁ ≤ G₂` and ferromagnetic `p`,
`freeEnergyInfinite G₁ Λ p ≤ freeEnergyInfinite G₂ Λ p`
(under suitable boundedness hypotheses used internally to control
the `limsup`).

Proof: apply `Filter.limsup_le_limsup` to the per-n
`freeEnergyAlongExhaustion_monotone_ambient_subgraph`. The
`IsCoboundedUnder` side is discharged via the ferromagnetic lower
bound `freeEnergyAlongExhaustion_ge_log_two_cosh`; the
`IsBoundedUnder` side via the `BoundedEdgeDensity`-driven upper
bound `freeEnergyAlongExhaustion_le_uniform_upper_bound`. -/
theorem freeEnergyInfinite_monotone_ambient_subgraph
    [Nonempty V] {G₁ G₂ : SimpleGraph V} (h : G₁ ≤ G₂)
    (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G₁ (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph G₂ (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G₂ (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite G₁ Λ p ≤ freeEnergyInfinite G₂ Λ p := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨N, hN⟩ := Λ.exhaust {v}
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact ⟨v, hN n hn (Finset.mem_singleton_self v)⟩
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G₁ Λ p n
        ≤ freeEnergyAlongExhaustion G₂ Λ p n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_ambient_subgraph h Λ p hf n
  have hbdd_below_G₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G₁ Λ p) := by
    refine ⟨Real.log (2 * Real.cosh (p.β * p.h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      (J := p.J) (h := p.h) (β := p.β) G₁ Λ hf.hJ hf.hh hf.hβ n hne
  have hbdd_above_G₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G₂ Λ p) := by
    refine ⟨Real.log 2 + |p.β| * (|p.J| * c + |p.h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G₂ Λ p hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_G₁.isCoboundedUnder_le hbdd_above_G₂

/-- **Along-exhaustion h-evenness at limsup**:
`freeEnergyInfinite G Λ ⟨J, -h, β⟩ = freeEnergyInfinite G Λ ⟨J, h, β⟩`.
Lifts `freeEnergyAlongExhaustion_neg_h` pointwise to `limsup`. -/
theorem freeEnergyInfinite_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) :
    freeEnergyInfinite G Λ (⟨J, -h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergyInfinite
  congr 1
  funext n
  exact freeEnergyAlongExhaustion_neg_h G Λ J h β n

/-- **`|h|`-form at limsup**:
`freeEnergyInfinite G Λ ⟨J, h, β⟩ = freeEnergyInfinite G Λ ⟨J, |h|, β⟩`.
Lifts `freeEnergyAlongExhaustion_eq_abs_h` pointwise to `limsup`. -/
theorem freeEnergyInfinite_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) :
    freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) := by
  unfold freeEnergyInfinite
  congr 1
  funext n
  exact freeEnergyAlongExhaustion_eq_abs_h G Λ J h β n

end Ambient

end IsingModel
