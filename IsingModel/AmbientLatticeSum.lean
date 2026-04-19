import IsingModel.AmbientLattice
import IsingModel.PartitionFunctionIso
import IsingModel.SumModel
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

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **`freeEnergyΛ ≥ log(2·cosh(β·h))`** for ferromagnetic on nonempty `Λ`.
Wrapper of `IsingModel.freeEnergy_ge_log_two_cosh`. -/
theorem freeEnergyΛ_ge_log_two_cosh
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) := by
  exact IsingModel.freeEnergy_ge_log_two_cosh _ hJ hh hβ hne.fintype_card_coe_pos

/-- **`freeEnergyΛ ≥ log 2`** for ferromagnetic on nonempty `Λ`.
Thin wrapper of base-layer
`IsingModel.freeEnergy_ge_log_two_of_ferromagnetic`. -/
theorem freeEnergyΛ_ge_log_two
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) :
    Real.log 2 ≤ freeEnergyΛ G Λ (⟨J, h, β⟩ : IsingParams ℝ) :=
  IsingModel.freeEnergy_ge_log_two_of_ferromagnetic
    (inducedGraph G Λ) _ ⟨hJ, hh, hβ⟩ hne.fintype_card_coe_pos

/-- **`freeEnergyΛ ≥ 0`** for ferromagnetic on nonempty `Λ`.
Thin wrapper of base-layer
`IsingModel.freeEnergy_nonneg_of_ferromagnetic`. -/
theorem freeEnergyΛ_nonneg_of_ferromagnetic
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ G Λ p :=
  IsingModel.freeEnergy_nonneg_of_ferromagnetic
    (inducedGraph G Λ) p hf hne.fintype_card_coe_pos

/-- **`partitionFunctionΛ ≥ 1`** for ferromagnetic parameters:
lifts PR #141 `partitionFunction_ge_one_of_ferromagnetic` to the
`partitionFunctionΛ` API level. -/
theorem partitionFunctionΛ_ge_one_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ G Λ p :=
  IsingModel.partitionFunction_ge_one_of_ferromagnetic _ p hf

/-- **`partitionFunctionAlongExhaustion ≥ 1`** for ferromagnetic
parameters: pointwise lift of PR #141
`partitionFunction_ge_one_of_ferromagnetic`. -/
theorem partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_ge_one_of_ferromagnetic G (Λ.volume n) p hf

/-- Log form: `log Z ≥ 0` along any exhaustion under ferromagnetic `p`. -/
theorem log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion G Λ p n) :=
  IsingModel.log_partitionFunction_nonneg_of_ferromagnetic _ p hf

/-- **`partitionFunctionΛ ≥ 2^|Λ|`** for ferromagnetic parameters:
lifts `partitionFunction_ge_two_pow_card_of_ferromagnetic`
to the `partitionFunctionΛ` API level.

Strictly sharper than `partitionFunctionΛ_ge_one_of_ferromagnetic`
for nonempty `Λ`. -/
theorem partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card ≤ partitionFunctionΛ G Λ p := by
  have h := IsingModel.partitionFunction_ge_two_pow_card_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- Log form at `Λ` level: `|Λ| · log 2 ≤ log (partitionFunctionΛ G Λ p)`
for ferromagnetic. -/
theorem log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2 ≤ Real.log (partitionFunctionΛ G Λ p) := by
  have h := IsingModel.log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- **`partitionFunctionAlongExhaustion ≥ 2^|Λ.volume n|`** for
ferromagnetic parameters: pointwise lift. -/
theorem partitionFunctionAlongExhaustion_ge_two_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 : ℝ) ^ (Λ.volume n).card ≤ partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic G (Λ.volume n) p hf

/-- **Sharp form at `Λ` level**: `(2·cosh(βh))^|Λ| ≤ partitionFunctionΛ G Λ p`
for ferromagnetic. Thin wrapper of
`IsingModel.partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic`. -/
theorem partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Λ.card ≤ partitionFunctionΛ G Λ p := by
  have h := IsingModel.partitionFunction_ge_two_cosh_pow_card_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- **Sharp form along exhaustion**:
`(2·cosh(βh))^|Λ.volume n| ≤ partitionFunctionAlongExhaustion G Λ p n`
for ferromagnetic. Pointwise lift. -/
theorem partitionFunctionAlongExhaustion_ge_two_cosh_pow_card_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 * Real.cosh (p.β * p.h)) ^ (Λ.volume n).card
      ≤ partitionFunctionAlongExhaustion G Λ p n :=
  partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic G (Λ.volume n) p hf

/-- Log form along exhaustion: `|Λ.volume n| · log 2 ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ p n) := by
  have h := IsingModel.log_partitionFunction_ge_card_mul_log_two_of_ferromagnetic
    (inducedGraph G (Λ.volume n)) p hf
  rwa [Fintype.card_coe] at h

/-- Sharp form at `Λ` level: `|Λ| · log(2·cosh(βh)) ≤ log (partitionFunctionΛ G Λ p)`
for ferromagnetic. Thin wrapper of
`log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic`. -/
theorem log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionΛ G Λ p) := by
  have h := IsingModel.log_partitionFunction_ge_card_mul_log_two_cosh_of_ferromagnetic
    (inducedGraph G Λ) p hf
  rwa [Fintype.card_coe] at h

/-- Sharp form along exhaustion:
`|Λ.volume n| · log(2·cosh(βh)) ≤ log Z_n`. Pointwise lift. -/
theorem log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_cosh_of_ferromagnetic
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionAlongExhaustion G Λ p n) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic G (Λ.volume n) p hf

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
for nonempty `Λ`. Thin wrapper of the base-layer
`IsingModel.card_mul_freeEnergy_eq_log_partitionFunction` via
`Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem card_mul_freeEnergyΛ_eq_log_partitionFunctionΛ_of_nonempty
    (G : SimpleGraph V) {Λ : Finset V} (hne : Λ.Nonempty)
    [Fintype (inducedGraph G Λ).edgeSet]
    (p : IsingParams ℝ) :
    (Λ.card : ℝ) * freeEnergyΛ G Λ p
      = Real.log (partitionFunctionΛ G Λ p) := by
  have h := IsingModel.card_mul_freeEnergy_eq_log_partitionFunction
    (inducedGraph G Λ) p hne.fintype_card_coe_pos
  rwa [Fintype.card_coe] at h

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
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
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

/-- **`freeEnergyInfinite` is the limit when `freeEnergyAlongExhaustion`
converges**: if the sequence `n ↦ freeEnergyAlongExhaustion G Λ p n`
has a limit `L`, then `freeEnergyInfinite G Λ p = L`.

Follows from `freeEnergyInfinite := Filter.limsup …` and
`Filter.Tendsto.limsup_eq` (convergent sequence's `limsup` equals its
limit).

Infrastructure for the pending §4.6 Prop 4.6.1 Fekete convergence:
once convergence is established, this gives the value equation for
`freeEnergyInfinite`. -/
theorem freeEnergyInfinite_eq_of_tendsto
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion G Λ p)
      Filter.atTop (nhds L)) :
    freeEnergyInfinite G Λ p = L := by
  unfold freeEnergyInfinite
  exact h.limsup_eq

/-- **GJ §4.6 Prop 4.6.1 (Fekete convergence of free energy density)**:
under a super-additivity hypothesis on `log Z` along the exhaustion and
the cardinality additivity `|Λ_{m+n}| = |Λ_m| + |Λ_n|`,
`freeEnergyAlongExhaustion G Λ p` converges to `freeEnergyInfinite G Λ p`.

Mathematical content: apply `Subadditive.tendsto_lim` (mathlib Fekete)
to the negated sequence `u_n := -log Z_{Λ.volume n}`. Under
`hcard_add` we have `|Λ_n| = n · |Λ_1|`, whence
`freeEnergyAlongExhaustion G Λ p n = -(u_n / n) / |Λ_1|` for `n ≥ 1`.
The Fekete limit `u_n / n → ℓ` translates to
`freeEnergyAlongExhaustion → -ℓ / |Λ_1|`, and
`freeEnergyInfinite_eq_of_tendsto` identifies the limit with
`freeEnergyInfinite`.

Hypotheses:
* `hcard_add`: `|Λ_{m+n}| = |Λ_m| + |Λ_n|` (additive cardinality along the tower).
* `hsuper`: `log Z_{Λ_m} + log Z_{Λ_n} ≤ log Z_{Λ_{m+n}}` (`log Z` super-additive).
* `hbdd`: `freeEnergyAlongExhaustion` bounded above (provided e.g. by
  `freeEnergyAlongExhaustion_le_uniform_upper_bound` under
  `BoundedEdgeDensity`).
* `hcard_one`: `|Λ_1| ≠ 0` (non-degenerate base step).

The hypothesis bundle is the natural formalisation of "disjoint-tower"
exhaustion: on a lattice with translation symmetry, a box-like
exhaustion of a fixed block size satisfies `hcard_add` and `hsuper`
(the latter from `log_partitionFunctionΛ_disjUnion_super_additive`).
This completes the **Fekete step** of GJ §4.6 Prop 4.6.1
(partial → Done in this hypothesis regime). -/
theorem freeEnergyAlongExhaustion_tendsto_of_superadditive
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n, Real.log (partitionFunctionΛ G (Λ.volume m) p)
                      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
                      ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hbdd : BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p)))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p) Filter.atTop
      (nhds (freeEnergyInfinite G Λ p)) := by
  set u : ℕ → ℝ := fun n => -Real.log (partitionFunctionΛ G (Λ.volume n) p)
    with hu_def
  -- 1. `u` is subadditive.
  have hsub : Subadditive u := by
    intro m n
    have := hsuper m n
    simp only [hu_def]
    linarith
  -- 2. `(Λ.volume n).card = n * (Λ.volume 1).card`.
  have hcard0 : (Λ.volume 0).card = 0 := by
    have h : (Λ.volume 0).card = (Λ.volume 0).card + (Λ.volume 0).card := by
      have := hcard_add 0 0; simpa using this
    omega
  have hcard_mul : ∀ n, (Λ.volume n).card = n * (Λ.volume 1).card := by
    intro n
    induction n with
    | zero =>
      rw [hcard0, Nat.zero_mul]
    | succ n ih =>
      calc (Λ.volume (n + 1)).card
          = (Λ.volume n).card + (Λ.volume 1).card := hcard_add n 1
        _ = n * (Λ.volume 1).card + (Λ.volume 1).card := by rw [ih]
        _ = (n + 1) * (Λ.volume 1).card := by ring
  -- 3. `(Λ.volume 1).card > 0` as a real number.
  have hcard1_pos : (0 : ℝ) < ((Λ.volume 1).card : ℝ) := by
    have : 0 < (Λ.volume 1).card := Nat.pos_of_ne_zero hcard_one
    exact_mod_cast this
  have hcard1_ne : ((Λ.volume 1).card : ℝ) ≠ 0 := hcard1_pos.ne'
  -- 4. Bound below `u n / n`.
  obtain ⟨C, hC⟩ := hbdd
  have hpos_cardC : 0 ≤ ((Λ.volume 1).card : ℝ) * max C 0 := by
    have hm : 0 ≤ max C 0 := le_max_right _ _
    have hc : 0 ≤ ((Λ.volume 1).card : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg hc hm
  have hbdd_below : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨-((Λ.volume 1).card : ℝ) * max C 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    change -((Λ.volume 1).card : ℝ) * max C 0 ≤ u n / (n : ℝ)
    by_cases hn : n = 0
    · -- At n = 0: u 0 / 0 = 0 ≥ -card_1 * max C 0 since max C 0 ≥ 0.
      subst hn
      rw [Nat.cast_zero, div_zero]
      linarith
    · -- For n ≥ 1: derive `u n / n = -card_1 * freeEnergyAlongExhaustion n`
      -- from `card_n = n * card_1` and the definition of freeEnergyΛ.
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn'
      have hn_ne : (n : ℝ) ≠ 0 := hn_real.ne'
      have hcardn : ((Λ.volume n).card : ℝ)
          = (n : ℝ) * ((Λ.volume 1).card : ℝ) := by
        exact_mod_cast hcard_mul n
      have hfe_unfold :
          freeEnergyAlongExhaustion G Λ p n
            = (((Λ.volume n).card : ℝ))⁻¹
              * Real.log (partitionFunctionΛ G (Λ.volume n) p) := by
        simp only [freeEnergyAlongExhaustion]
        unfold freeEnergyΛ IsingModel.freeEnergy partitionFunctionΛ
        rw [Fintype.card_coe]
      have hfe_val : freeEnergyAlongExhaustion G Λ p n ≤ C :=
        hC ⟨n, rfl⟩
      have hrel : u n / (n : ℝ)
          = -((Λ.volume 1).card : ℝ) * freeEnergyAlongExhaustion G Λ p n := by
        rw [hfe_unfold, hcardn]
        change -Real.log (partitionFunctionΛ G (Λ.volume n) p) / (n : ℝ)
            = -((Λ.volume 1).card : ℝ)
              * (((n : ℝ) * ((Λ.volume 1).card : ℝ))⁻¹
                * Real.log (partitionFunctionΛ G (Λ.volume n) p))
        field_simp
      rw [hrel]
      have hmax : freeEnergyAlongExhaustion G Λ p n ≤ max C 0 :=
        hfe_val.trans (le_max_left _ _)
      nlinarith
  -- 5. Apply Fekete.
  have htendsto_quot : Filter.Tendsto (fun n => u n / (n : ℝ)) Filter.atTop
      (nhds hsub.lim) :=
    hsub.tendsto_lim hbdd_below
  -- 6. Translate to freeEnergyAlongExhaustion via the ratio relation.
  set L : ℝ := -hsub.lim / ((Λ.volume 1).card : ℝ) with hL_def
  have htendsto_feAE : Filter.Tendsto (freeEnergyAlongExhaustion G Λ p)
      Filter.atTop (nhds L) := by
    have htendsto_target : Filter.Tendsto
        (fun n => -(u n / (n : ℝ)) / ((Λ.volume 1).card : ℝ))
        Filter.atTop (nhds L) := by
      rw [hL_def]
      exact (htendsto_quot.neg).div_const _
    refine htendsto_target.congr' ?_
    refine (Filter.eventually_ge_atTop 1).mono ?_
    intro n hn
    -- For n ≥ 1: freeEnergy_n = -(u n / n) / card_1
    have hn_pos : 0 < n := hn
    have hn_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hn_ne : (n : ℝ) ≠ 0 := hn_real.ne'
    have hcardn : ((Λ.volume n).card : ℝ)
        = (n : ℝ) * ((Λ.volume 1).card : ℝ) := by
      exact_mod_cast hcard_mul n
    have hfe_unfold :
        freeEnergyAlongExhaustion G Λ p n
          = (((Λ.volume n).card : ℝ))⁻¹
            * Real.log (partitionFunctionΛ G (Λ.volume n) p) := by
      simp only [freeEnergyAlongExhaustion]
      unfold freeEnergyΛ IsingModel.freeEnergy partitionFunctionΛ
      rw [Fintype.card_coe]
    rw [hfe_unfold, hcardn]
    change -(u n / (n : ℝ)) / ((Λ.volume 1).card : ℝ)
      = (((n : ℝ) * ((Λ.volume 1).card : ℝ))⁻¹
          * Real.log (partitionFunctionΛ G (Λ.volume n) p))
    simp only [hu_def]
    field_simp
  -- 7. Identify L with freeEnergyInfinite.
  have hL_eq : freeEnergyInfinite G Λ p = L :=
    freeEnergyInfinite_eq_of_tendsto G Λ p htendsto_feAE
  rw [hL_eq]
  exact htendsto_feAE

/-- **GJ §4.6 Prop 4.6.1, disjoint-tower + `BoundedEdgeDensity` form**:
under a super-additivity hypothesis on `log Z` along a disjoint-tower
exhaustion (`hcard_add`, `hsuper`, `hcard_one`) and bounded edge
density along the exhaustion, `freeEnergyAlongExhaustion G Λ p`
converges to `freeEnergyInfinite G Λ p`.

This is a strict relaxation of
`freeEnergyAlongExhaustion_tendsto_of_superadditive`: the explicit
`hbdd : BddAbove (Set.range (freeEnergyAlongExhaustion G Λ p))`
hypothesis is discharged automatically via
`BddAbove_freeEnergyAlongExhaustion_range` under
`BoundedEdgeDensity`.  No other hypothesis is added; in particular
neither this theorem nor `BddAbove_freeEnergyAlongExhaustion_range`
needs `Ferromagnetic p`.

Reference: Glimm–Jaffe, *Quantum Physics*, 2nd ed., Springer 1987,
§4.6 Prop 4.6.1, p. 64. This is a formal weaker variant of the
proposition as stated in GJ: the bundled hypotheses replace the
translation-invariance framework that GJ uses implicitly. -/
theorem freeEnergyAlongExhaustion_tendsto_of_disjoint_tower
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hcard_add : ∀ m n, (Λ.volume (m + n)).card
                          = (Λ.volume m).card + (Λ.volume n).card)
    (hsuper : ∀ m n, Real.log (partitionFunctionΛ G (Λ.volume m) p)
                      + Real.log (partitionFunctionΛ G (Λ.volume n) p)
                      ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p))
    (hcard_one : (Λ.volume 1).card ≠ 0) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p) Filter.atTop
      (nhds (freeEnergyInfinite G Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_superadditive G Λ p
    hcard_add hsuper
    (BddAbove_freeEnergyAlongExhaustion_range G Λ p hBED)
    hcard_one

/-- **Bundle of disjoint-tower hypotheses** for `freeEnergyAlongExhaustion`
Fekete convergence (GJ §4.6 Prop 4.6.1 p. 64).

Packages the three exhaustion-structural hypotheses required by
`freeEnergyAlongExhaustion_tendsto_of_disjoint_tower`:

* `card_add`: `|Λ_{m+n}| = |Λ_m| + |Λ_n|` (additive cardinality).
* `super`: `log Z_{Λ_m} + log Z_{Λ_n} ≤ log Z_{Λ_{m+n}}`
  (super-additivity of `log Z` along the tower).
* `card_one`: `|Λ_1| ≠ 0` (non-degenerate base step).

The bundle is indexed by a `SimpleGraph V`, an `Exhaustion V`, and
`IsingParams ℝ`; it does not depend on any probabilistic / ferromagnetic
content — that enters separately through `BoundedEdgeDensity` when
needed.

Intended use: future PRs will provide concrete instances under
translation invariance (GJ §4.6 p. 64 style) so that the user does
not need to supply the three hypotheses by hand. -/
structure DisjointTowerHypotheses
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) : Prop where
  /-- Additive cardinality along the tower:
  `|Λ_{m+n}| = |Λ_m| + |Λ_n|` for all `m, n`. -/
  card_add : ∀ m n, (Λ.volume (m + n)).card
                      = (Λ.volume m).card + (Λ.volume n).card
  /-- Super-additivity of `log Z` along the tower:
  `log Z_{Λ_m} + log Z_{Λ_n} ≤ log Z_{Λ_{m+n}}`. -/
  super : ∀ m n, Real.log (partitionFunctionΛ G (Λ.volume m) p)
                  + Real.log (partitionFunctionΛ G (Λ.volume n) p)
                  ≤ Real.log (partitionFunctionΛ G (Λ.volume (m + n)) p)
  /-- Non-degenerate base step: `|Λ_1| ≠ 0`. -/
  card_one : (Λ.volume 1).card ≠ 0

/-- **Bundled-hypothesis wrapper for Prop 4.6.1 (disjoint-tower +
`BoundedEdgeDensity`)** (GJ §4.6 Prop 4.6.1 p. 64).

Same content as `freeEnergyAlongExhaustion_tendsto_of_disjoint_tower`,
but takes the three structural hypotheses as a single
`DisjointTowerHypotheses` record for API-site convenience. -/
theorem freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (h : DisjointTowerHypotheses G Λ p) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p) Filter.atTop
      (nhds (freeEnergyInfinite G Λ p)) :=
  freeEnergyAlongExhaustion_tendsto_of_disjoint_tower G Λ p
    hBED h.card_add h.super h.card_one

/-- **Eventually constant ⇒ `freeEnergyInfinite` equals the constant.**

If `∀ᶠ n in atTop, freeEnergyAlongExhaustion G Λ p n = c`, then
`freeEnergyInfinite G Λ p = c`. Direct corollary of
`freeEnergyInfinite_eq_of_tendsto`: an eventually-constant sequence
tends to that constant (`Filter.tendsto_const_nhds` via
`Filter.Tendsto.congr'`).

Generalization of the argument in `freeEnergyInfinite_beta_zero` /
`_zero_params` which handle the always-constant (all-stages-nonempty)
case. -/
theorem freeEnergyInfinite_of_eventually_const
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion G Λ p n = c) :
    freeEnergyInfinite G Λ p = c := by
  refine freeEnergyInfinite_eq_of_tendsto G Λ p ?_
  exact tendsto_const_nhds.congr' (h.mono (fun _ hn => hn.symm))

/-- **β=0 infinite-volume closed form, weakened eventual form**:
`∀ᶠ n in atTop, (Λ.volume n).Nonempty ⇒ freeEnergyInfinite G Λ ⟨J, h, 0⟩ = log 2`.

Weakening of `freeEnergyInfinite_beta_zero` (`∀ n` → `∀ᶠ n`).
The eventual hypothesis is automatic under `[Infinite V]` via
`Exhaustion.eventually_volume_nonempty`.

Uses `freeEnergyInfinite_of_eventually_const` with the per-stage
`freeEnergyAlongExhaustion_beta_zero`. -/
theorem freeEnergyInfinite_beta_zero_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 := by
  apply freeEnergyInfinite_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_beta_zero G Λ J h n hn

/-- **J=h=0 infinite-volume closed form, weakened eventual form**:
`∀ᶠ n in atTop, (Λ.volume n).Nonempty ⇒ freeEnergyInfinite G Λ ⟨0, 0, β⟩ = log 2`.

Weakening of `freeEnergyInfinite_zero_params` (`∀ n` → `∀ᶠ n`). -/
theorem freeEnergyInfinite_zero_params_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
  apply freeEnergyInfinite_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_zero_params G Λ β n hn

/-- **J=0 infinite-volume closed form (graph-independent)**:
`∀ᶠ n in atTop, (Λ.volume n).Nonempty ⇒
 freeEnergyInfinite G Λ ⟨0, h, β⟩ = log (2·cosh(β·h))`.

Graph independence: since the interaction term vanishes at `J = 0`,
the `freeEnergy` agrees with that of the `⊥` graph at each stage.
Direct application of `freeEnergyInfinite_of_eventually_const` with
the stagewise `freeEnergyAlongExhaustion_J_zero`. -/
theorem freeEnergyInfinite_J_zero_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    freeEnergyInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) := by
  apply freeEnergyInfinite_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_J_zero G Λ h β n hn

/-- **Generic Tendsto helper**: if the stagewise `freeEnergyAlongExhaustion`
sequence is eventually equal to `c`, then it tends to `c`. Factors the
`tendsto_const_nhds.congr'` + `filter_upwards` pattern out of the
specific `_J_zero` / `_beta_zero` / `_zero_params` Tendsto lemmas. -/
theorem freeEnergyAlongExhaustion_tendsto_of_eventually_const
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion G Λ p n = c) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ p)
      Filter.atTop (nhds c) :=
  tendsto_const_nhds.congr' (h.mono (fun _ hn => hn.symm))

/-- **`freeEnergyAlongExhaustion` at J=0 converges (Tendsto form)**:
assuming eventually `(Λ.volume n).Nonempty`, the sequence
`n ↦ freeEnergyAlongExhaustion G Λ ⟨0, h, β⟩ n` tends to
`log(2·cosh(β·h))` in the topology on `ℝ`.

First non-trivial ∞-volume convergence under the scope update
(CLAUDE.local.md: 無限系も対象). The J=0 slice sidesteps the
translation-invariance issue of the general Fekete program because
the stagewise sequence is eventually constant (PR #174
`freeEnergyAlongExhaustion_J_zero`); then via
`freeEnergyAlongExhaustion_tendsto_of_eventually_const`. -/
theorem freeEnergyAlongExhaustion_J_zero_tendsto_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * h)))) := by
  apply freeEnergyAlongExhaustion_tendsto_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_J_zero G Λ h β n hn

/-- **β=0 slice ∞-vol Tendsto**: `∀ᶠ n, (Λ.volume n).Nonempty ⇒
Tendsto (freeEnergyAlongExhaustion G Λ ⟨J, h, 0⟩) atTop (𝓝 (log 2))`.

Companion to `_J_zero_tendsto_of_eventually_nonempty` (PR #178):
at β=0 the stagewise sequence is eventually constantly `log 2`
(PR #132 `freeEnergyAlongExhaustion_beta_zero`). -/
theorem freeEnergyAlongExhaustion_beta_zero_tendsto_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ
        (⟨J, h, 0⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) := by
  apply freeEnergyAlongExhaustion_tendsto_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_beta_zero G Λ J h n hn

/-- **J=h=0 slice ∞-vol Tendsto**: `∀ᶠ n, (Λ.volume n).Nonempty ⇒
Tendsto (freeEnergyAlongExhaustion G Λ ⟨0, 0, β⟩) atTop (𝓝 (log 2))`.

Companion to `_J_zero_tendsto_of_eventually_nonempty` (PR #178):
at J=h=0 the stagewise sequence is eventually constantly `log 2`
(`freeEnergyAlongExhaustion_zero_params`). -/
theorem freeEnergyAlongExhaustion_zero_params_tendsto_of_eventually_nonempty
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ)
    (hne : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty) :
    Filter.Tendsto (freeEnergyAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ))
      Filter.atTop (nhds (Real.log 2)) := by
  apply freeEnergyAlongExhaustion_tendsto_of_eventually_const G Λ
  filter_upwards [hne] with n hn using
    freeEnergyAlongExhaustion_zero_params G Λ β n hn

/-- **β=0 slice closed form under `[Nonempty V]`**: drops the
explicit `eventually_volume_nonempty` hypothesis via
`Exhaustion.eventually_volume_nonempty`. -/
theorem freeEnergyInfinite_beta_zero_of_nonempty
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) :
    freeEnergyInfinite G Λ (⟨J, h, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyInfinite_beta_zero_of_eventually_nonempty G Λ J h
    Λ.eventually_volume_nonempty

/-- **J=h=0 slice closed form under `[Nonempty V]`**: drops the
explicit `eventually_volume_nonempty` hypothesis. -/
theorem freeEnergyInfinite_zero_params_of_nonempty
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) :
    freeEnergyInfinite G Λ (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergyInfinite_zero_params_of_eventually_nonempty G Λ β
    Λ.eventually_volume_nonempty

/-- **J=0 slice closed form under `[Nonempty V]`**: drops the
explicit `eventually_volume_nonempty` hypothesis. -/
theorem freeEnergyInfinite_J_zero_of_nonempty
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) :
    freeEnergyInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = Real.log (2 * Real.cosh (β * h)) :=
  freeEnergyInfinite_J_zero_of_eventually_nonempty G Λ h β
    Λ.eventually_volume_nonempty

/-- **Infinite-volume J=0 graph-independence**:
`freeEnergyInfinite G Λ ⟨0, h, β⟩ = freeEnergyInfinite ⊥ Λ ⟨0, h, β⟩`
for any ambient graph `G, Λ`, any `h, β`.

Lift of `freeEnergyAlongExhaustion_eq_bot_at_J_zero` (PR #176): the
stagewise graph independence propagates through `Filter.limsup` since
the two sequences are pointwise equal. -/
theorem freeEnergyInfinite_eq_bot_at_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Fintype (inducedGraph (⊥ : SimpleGraph V) (Λ.volume n)).edgeSet]
    (h β : ℝ) :
    freeEnergyInfinite G Λ (⟨0, h, β⟩ : IsingParams ℝ)
      = freeEnergyInfinite (⊥ : SimpleGraph V) Λ
          (⟨0, h, β⟩ : IsingParams ℝ) := by
  unfold freeEnergyInfinite
  congr 1
  funext n
  exact freeEnergyAlongExhaustion_eq_bot_at_J_zero G Λ h β n

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
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
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
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
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

set_option linter.unusedFintypeInType false in
/-- **J-direction monotonicity of `freeEnergyInfinite`**: for fixed
`h ≥ 0`, `β > 0`, the limsup free energy is monotone in
`J ∈ Set.Ici 0`.

Lifts `freeEnergyAlongExhaustion_monotone_J` pointwise via
`Filter.limsup_le_limsup`, using the ferromagnetic lower bound and
`BoundedEdgeDensity` upper bound to control the required
`IsCoboundedUnder` / `IsBoundedUnder` hypotheses. -/
theorem freeEnergyInfinite_monotone_J
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun J : ℝ => freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  intro J₁ hJ₁ J₂ _ hJle
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hJ₁nn : (0 : ℝ) ≤ J₁ := hJ₁
  have hJ₂nn : (0 : ℝ) ≤ J₂ := hJ₁nn.trans hJle
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ (⟨J₁, h, β⟩ : IsingParams ℝ) n
        ≤ freeEnergyAlongExhaustion G Λ (⟨J₂, h, β⟩ : IsingParams ℝ) n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_J G Λ hh hβ n hJ₁nn hJ₂nn hJle
  have hbdd_below_J₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J₁, h, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log (2 * Real.cosh (β * h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      G Λ hJ₁nn hh hβ n hne
  have hbdd_above_J₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J₂, h, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log 2 + |β| * (|J₂| * c + |h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ _ hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_J₁.isCoboundedUnder_le hbdd_above_J₂

set_option linter.unusedFintypeInType false in
/-- **h-direction monotonicity of `freeEnergyInfinite`**: for fixed
`J ≥ 0`, `β > 0`, the limsup free energy is monotone in
`h ∈ Set.Ici 0`. Lifts `freeEnergyAlongExhaustion_monotone_h`. -/
theorem freeEnergyInfinite_monotone_h
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun h : ℝ => freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ici 0) := by
  intro h₁ hh₁ h₂ _ hhle
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hh₁nn : (0 : ℝ) ≤ h₁ := hh₁
  have hh₂nn : (0 : ℝ) ≤ h₂ := hh₁nn.trans hhle
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_h G Λ hJ hβ n hh₁nn hh₂nn hhle
  have hbdd_below_h₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log (2 * Real.cosh (β * h₁)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      G Λ hJ hh₁nn hβ n hne
  have hbdd_above_h₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log 2 + |β| * (|J| * c + |h₂|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ _ hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_h₁.isCoboundedUnder_le hbdd_above_h₂

set_option linter.unusedFintypeInType false in
/-- **β-direction monotonicity of `freeEnergyInfinite`**: for fixed
`J ≥ 0`, `h ≥ 0`, the limsup free energy is monotone in
`β ∈ Set.Ioi 0`. Lifts `freeEnergyAlongExhaustion_monotone_beta`. -/
theorem freeEnergyInfinite_monotone_beta
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _)) :
    MonotoneOn
      (fun β : ℝ => freeEnergyInfinite G Λ (⟨J, h, β⟩ : IsingParams ℝ))
      (Set.Ioi 0) := by
  intro β₁ hβ₁ β₂ _ hβle
  have heventually : ∀ᶠ n in Filter.atTop, (Λ.volume n).Nonempty :=
    Λ.eventually_volume_nonempty
  have hβ₁pos : (0 : ℝ) < β₁ := hβ₁
  have hβ₂pos : (0 : ℝ) < β₂ := hβ₁pos.trans_le hβle
  have hle : ∀ᶠ n in Filter.atTop,
      freeEnergyAlongExhaustion G Λ (⟨J, h, β₁⟩ : IsingParams ℝ) n
        ≤ freeEnergyAlongExhaustion G Λ (⟨J, h, β₂⟩ : IsingParams ℝ) n := by
    apply Filter.Eventually.of_forall
    intro n
    exact freeEnergyAlongExhaustion_monotone_beta G Λ hJ hh n hβ₁pos hβ₂pos hβle
  have hbdd_below_β₁ : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h, β₁⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log (2 * Real.cosh (β₁ * h)), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_ge_log_two_cosh
      G Λ hJ hh hβ₁pos n hne
  have hbdd_above_β₂ : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (freeEnergyAlongExhaustion G Λ (⟨J, h, β₂⟩ : IsingParams ℝ)) := by
    refine ⟨Real.log 2 + |β₂| * (|J| * c + |h|), ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [heventually] with n hne
    exact freeEnergyAlongExhaustion_le_uniform_upper_bound G Λ _ hc n hne
  exact Filter.limsup_le_limsup hle hbdd_below_β₁.isCoboundedUnder_le hbdd_above_β₂

set_option linter.unusedFintypeInType false in
/-- **`|h|`-monotonicity of `freeEnergyInfinite`**: for fixed
`J ≥ 0`, `β > 0`, `freeEnergyInfinite` is monotone in `|h|`.
Composition of `freeEnergyInfinite_eq_abs_h` and
`freeEnergyInfinite_monotone_h` on `Set.Ici 0`. -/
theorem freeEnergyInfinite_monotone_abs_h
    [Nonempty V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {J β : ℝ} (hJ : 0 ≤ J) (hβ : 0 < β) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((inducedGraph G (Λ.volume n)).edgeFinset.card : ℝ) ≤
        c * Fintype.card (↑(Λ.volume n) : Type _))
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) :
    freeEnergyInfinite G Λ (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ freeEnergyInfinite G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) := by
  rw [freeEnergyInfinite_eq_abs_h G Λ J h₁ β,
      freeEnergyInfinite_eq_abs_h G Λ J h₂ β]
  exact freeEnergyInfinite_monotone_h G Λ hJ hβ hc
    (Set.mem_Ici.mpr (abs_nonneg h₁)) (Set.mem_Ici.mpr (abs_nonneg h₂)) hh

/-- **`log Z` tends to `∞` along any exhaustion of an infinite ambient
type**, under ferromagnetic parameters.

Direct application of the pointwise bound
`log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic`
(PR #165): `|Λ.volume n| · log 2 ≤ log Z_n` for every `n`. Combined
with `Exhaustion.tendsto_card_atTop` (|Λ.volume n| → ∞) and
`log 2 > 0`, the lower bound tends to `∞`; `Filter.tendsto_atTop_mono`
lifts this to `log Z_n → ∞`. -/
theorem log_partitionFunctionAlongExhaustion_tendsto_atTop
    [Infinite V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto
      (fun n => Real.log (partitionFunctionAlongExhaustion G Λ p n))
      Filter.atTop Filter.atTop := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h_card_tendsto :
      Filter.Tendsto (fun n => ((Λ.volume n).card : ℝ) * Real.log 2)
        Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop.comp Λ.tendsto_card_atTop).atTop_mul_const
      hlog2_pos
  exact Filter.tendsto_atTop_mono
    (fun n => log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic
      G Λ p hf n)
    h_card_tendsto

/-- **`Z` tends to `∞` along any exhaustion of an infinite ambient
type**, under ferromagnetic parameters. Follows from
`log_partitionFunctionAlongExhaustion_tendsto_atTop` via
`Real.tendsto_exp_atTop`. -/
theorem partitionFunctionAlongExhaustion_tendsto_atTop
    [Infinite V] (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    Filter.Tendsto (partitionFunctionAlongExhaustion G Λ p)
      Filter.atTop Filter.atTop := by
  have h_log := log_partitionFunctionAlongExhaustion_tendsto_atTop G Λ p hf
  have h_comp := Real.tendsto_exp_atTop.comp h_log
  refine (Filter.tendsto_congr ?_).mp h_comp
  intro n
  exact Real.exp_log (IsingModel.partitionFunction_pos _ _)

end Ambient

end IsingModel
