import IsingModel.AmbientLatticeSum.InducedUnion

/-!
# Super-additivity and volume monotonicity of the partition function and the free energy

Statements about a finite volume `Λ : Finset V` inside an arbitrary ambient graph
`G : SimpleGraph V`, read through `partitionFunctionΛ G Λ p` and `freeEnergyΛ G Λ p`, the
partition function and the free energy of the subgraph that `Λ` induces, and through
`partitionFunctionAlongExhaustion G Λ p`, which reads the former at the stage volume
`Λ.volume n` of an exhaustion. Every statement takes `[DecidableEq V]` and a `Fintype`
instance on the induced edge set of each volume it names.

Merging two disjoint volumes can only raise the partition function, its logarithm and the
free energy weighted by the volume's cardinality; the unweighted `freeEnergyΛ` is compared
across a union nowhere here. For disjoint `Λ₁` and `Λ₂` under `Ferromagnetic p` the
partition function is super-multiplicative across the union and its logarithm
super-additive; the first piece's value is at most the union's, in the multiplicative and in
the logarithmic form alike; and the free energy weighted by the volume's cardinality obeys
the same two comparisons, under nonemptiness of the pieces each comparison names — both
pieces in the two-piece super-additivity, the first piece alone in the comparison against
the union.

Two statements stand outside that regime and assume no sign condition on `p` at all:
`partitionFunctionΛ` is unchanged when the volume is replaced by an equal one, and on a
nonempty volume the cardinality-weighted free energy equals the logarithm of the partition
function.

Along an exhaustion the same disjoint-union comparison, applied to the shell
`Λ.volume (n + 1) \ Λ.volume n`, makes both the partition function and its logarithm
non-decreasing from a stage to its successor and `Monotone` in the stage, under
`Ferromagnetic p`. Those statements therefore take a `Fintype` instance on the shell's
induced edge set alongside the stagewise one — for the single stage named where the
successor form needs it, and as a family in the `Monotone` form. Along its growth axis an
`Exhaustion` requires only `Monotone`, never strict increase, so the shell may be empty.
-/

namespace IsingModel

open Ambient

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

This is the Finset-weighted form of the disjoint-union super-additivity
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
3. Apply `partitionFunctionΛ_le_of_disjoint_union` to the
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
together with `log_partitionFunctionΛ_le_of_disjoint_union`. -/
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

end Ambient

end IsingModel
