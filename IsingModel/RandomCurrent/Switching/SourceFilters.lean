import IsingModel.RandomCurrent.Switching.PairClosedForms

/-!
# Source-conditioned pair and sub-current Finsets

`Current.pairFinset_with_sources G Λ n A B` filters the pairs of currents summing to `n` on
`inducedGraph G Λ`, the subgraph of `G` that `Λ` induces, keeping those whose first component
has source set exactly `A` and whose second has source set exactly `B`.
`Current.subFinset_with_source G Λ n A` filters the currents bounded by `n`, keeping those
whose source set is exactly `A`. The graph `G : SimpleGraph V` and the finite volume
`Λ : Finset V` are arbitrary throughout.

Membership in each unfolds to the defining conjunction: a pair lies in the first exactly when
its two components add up to `n` and carry the prescribed source sets, and a current lies in
the second exactly when it is bounded by `n` and carries the prescribed source set. The
second `Finset` is contained in `Current.subFinset G Λ n`.

The two families are related under the hypothesis `symmDiff (n.sources G Λ) A = B`. Under it,
the source-conditioned pair `Finset` is the image of the source-conditioned sub-current
`Finset` under `m ↦ (m, n - m)`; sums over the two agree after that substitution; and the sum
of the product of the two weights factors as the weight of `n` times the sum of
`Current.jointFactor G Λ m (n - m)` over the source-conditioned sub-current `Finset`.

A second hypothesis shape occurs, written with a different argument order:
`symmDiff A B ≠ n.sources G Λ`. Under it the source-conditioned pair `Finset` is empty, and
the same weight sum is therefore `0`.

At the zero current these Finsets degenerate. With its prescribed source set empty, the
sub-current `Finset` is the singleton of the zero current, and it is empty as soon as that
prescribed source set is nonempty. With both prescribed source sets empty, the pair `Finset`
is the singleton of the pair of zero currents, and it is empty as soon as one of the two
prescribed source sets is nonempty.

The joint-factor sum and the pair-weight sum are each bounded above. The sum of
`Current.jointFactor G Λ m (n - m)` over the source-conditioned sub-current `Finset` is at
most `2` raised to the sum of `n e` over all edges, under no hypothesis at all. Under
`symmDiff (n.sources G Λ) A = B` together with `0 ≤ β * J`, the source-conditioned
pair-weight sum is at most the weight of `n` times that same power; that is the only
statement in this module which constrains `β` or `J`.

Exchanging the two prescribed source sets corresponds to `Prod.swap` on the pairs: the image
of the pair `Finset` under `Prod.swap` is the pair `Finset` with `A` and `B` exchanged, sums
transform accordingly, and the two cardinalities agree.

Every statement here takes `[DecidableEq V]`, `[Fintype (inducedGraph G Λ).edgeSet]` and
`[DecidableEq ↥Λ]`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Source-conditioned pair-Finset**: pairs `(n₁, n₂) ∈ pairFinset n`
filtered by `n₁.HasSources A ∧ n₂.HasSources B`. The LHS / RHS data
type for source-bijection statements of the switching lemma
(Aizenman 1982 Lemma 3.2, p. 7 / FV §3.10.6). -/
noncomputable def Current.pairFinset_with_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ) :
    Finset (Current G Λ × Current G Λ) := by
  classical
  exact (Current.pairFinset G Λ n).filter
    (fun p => p.1.HasSources G Λ A ∧ p.2.HasSources G Λ B)

set_option linter.unusedDecidableInType false in
/-- **Membership in `pairFinset_with_sources`**:
`(n₁, n₂) ∈ pairFinset_with_sources n A B
  ↔ n₁ + n₂ = n ∧ n₁.HasSources A ∧ n₂.HasSources B`. -/
theorem Current.mem_pairFinset_with_sources_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (p : Current G Λ × Current G Λ) :
    p ∈ Current.pairFinset_with_sources G Λ n A B
      ↔ p.1 + p.2 = n ∧ p.1.HasSources G Λ A ∧ p.2.HasSources G Λ B := by
  classical
  unfold Current.pairFinset_with_sources
  simp only [Finset.mem_filter, Current.mem_pairFinset_iff]

set_option linter.unusedDecidableInType false in
/-- **Empty when source XOR doesn't match**: if `symmDiff A B ≠ sources n`,
then `pairFinset_with_sources n A B = ∅`. The constraint
`(n₁, n₂)` with `sources n₁ = A`, `sources n₂ = B`, `n₁ + n₂ = n`
forces `sources n = symmDiff A B` (`add_sources_eq`). -/
theorem Current.pairFinset_with_sources_eq_empty_of_sources_mismatch
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (h : symmDiff A B ≠ n.sources G Λ) :
    Current.pairFinset_with_sources G Λ n A B = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Current.mem_pairFinset_with_sources_iff] at hp
  obtain ⟨hsum, hA, hB⟩ := hp
  apply h
  change p.1.sources G Λ = A at hA
  change p.2.sources G Λ = B at hB
  rw [show n = p.1 + p.2 from hsum.symm, Current.add_sources_eq, hA, hB]

/-- **Source-conditioned subFinset**: `(subFinset n).filter (fun m => m.HasSources A)`.
The dual to `pairFinset_with_sources` (PR #877) via the pair-bijection
`m ↦ (m, n - m)` (PR #868). -/
noncomputable def Current.subFinset_with_source
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    Finset (Current G Λ) := by
  classical
  exact (Current.subFinset G Λ n).filter (fun m => m.HasSources G Λ A)

set_option linter.unusedDecidableInType false in
/-- **Membership in `subFinset_with_source`**:
`m ∈ subFinset_with_source n A ↔ m ≤ n ∧ m.HasSources A`. -/
theorem Current.mem_subFinset_with_source_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) (m : Current G Λ) :
    m ∈ Current.subFinset_with_source G Λ n A
      ↔ m ≤ n ∧ m.HasSources G Λ A := by
  classical
  unfold Current.subFinset_with_source
  simp only [Finset.mem_filter, Current.mem_subFinset_iff]

set_option linter.unusedDecidableInType false in
/-- **`subFinset_with_source` is a subset of `subFinset`**: by definition
as a filter. -/
theorem Current.subFinset_with_source_subset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    Current.subFinset_with_source G Λ n A ⊆ Current.subFinset G Λ n := by
  classical
  unfold Current.subFinset_with_source
  exact Finset.filter_subset _ _

set_option linter.unusedDecidableInType false in
/-- **Bridge: `pairFinset_with_sources` is the image of `subFinset_with_source`
under `m ↦ (m, n - m)`** (when sources XOR matches): if
`symmDiff (sources n) A = B`, then `pairFinset_with_sources n A B
= (subFinset_with_source n A).image (fun m => (m, n - m))`.
Combines pair-bijection (PR #868), `sub_add_cancel_of_le` (PR #867),
`sub_sources_eq_symmDiff` (PR #870). -/
theorem Current.pairFinset_with_sources_eq_image_subFinset_with_source
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) :
    Current.pairFinset_with_sources G Λ n A B
      = (Current.subFinset_with_source G Λ n A).image (fun m => (m, n - m)) := by
  ext p
  rw [Current.mem_pairFinset_with_sources_iff, Finset.mem_image]
  constructor
  · rintro ⟨hsum, hA, hB⟩
    refine ⟨p.1, ?_, ?_⟩
    · rw [Current.mem_subFinset_with_source_iff]
      refine ⟨?_, hA⟩
      rw [← hsum]
      exact Current.le_self_add_right G Λ p.1 p.2
    · ext
      · rfl
      · rename_i e
        simp only [Current.sub_apply]
        have heq : p.1 e + p.2 e = n e := by
          have h := congrFun hsum e
          simpa [Pi.add_apply] using h
        omega
  · rintro ⟨m, hm, rfl⟩
    rw [Current.mem_subFinset_with_source_iff] at hm
    obtain ⟨hle, hsrc⟩ := hm
    refine ⟨Current.add_sub_cancel_of_le G Λ hle, hsrc, ?_⟩
    -- Goal: (n - m).HasSources G Λ B
    rw [Current.sub_hasSources_iff G Λ hle]
    change m.sources G Λ = A at hsrc
    rw [hsrc]
    exact hAB

set_option linter.unusedDecidableInType false in
/-- **Sum reindexing for source-conditioned pair-Finset**:
when `symmDiff (sources n) A = B`,
`∑ p ∈ pairFinset_with_sources n A B, f p
  = ∑ m ∈ subFinset_with_source n A, f (m, n - m)`.
By the image identity (`pairFinset_with_sources_eq_image_subFinset_with_source`)
+ `Finset.sum_image` on the injective map. -/
theorem Current.sum_pairFinset_with_sources_eq_sum_subFinset_with_source
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B)
    (f : Current G Λ × Current G Λ → ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B, f p
      = ∑ m ∈ Current.subFinset_with_source G Λ n A, f (m, n - m) := by
  rw [Current.pairFinset_with_sources_eq_image_subFinset_with_source G Λ n A B hAB]
  rw [Finset.sum_image]
  intro m₁ _ m₂ _ h
  exact congrArg Prod.fst h

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-weight scaling identity** (analog of PR #876
for source-filtered pairs): under `symmDiff (sources n) A = B`,
\[
∑_{p ∈ \text{pairFinset\_with\_sources}\ n\ A\ B}
  \text{weight}\ p.1 \cdot \text{weight}\ p.2
 = \text{weight}\ n \cdot
   ∑_{m ∈ \text{subFinset\_with\_source}\ n\ A}
     \text{jointFactor}\ m\ (n - m).
\]
Apply PR #879 bridge (sum reindexing) + per-summand
`weight_mul_weight_eq_weight_add_mul_jointFactor` (PR #845) +
`add_sub_cancel_of_le` (PR #867: `m + (n - m) = n` for `m ≤ n`),
factored via `Finset.mul_sum`. The source-conditioned version of the
central scaling identity for the switching lemma. -/
theorem Current.sum_pairFinset_with_sources_weight_mul_weight
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      = Current.weight G Λ β J n
        * ∑ m ∈ Current.subFinset_with_source G Λ n A,
            Current.jointFactor G Λ m (n - m) := by
  rw [Current.sum_pairFinset_with_sources_eq_sum_subFinset_with_source
        G Λ n A B hAB, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Current.mem_subFinset_with_source_iff] at hm
  obtain ⟨hle, _⟩ := hm
  rw [Current.weight_mul_weight_eq_weight_add_mul_jointFactor,
      Current.add_sub_cancel_of_le G Λ hle]

set_option linter.unusedDecidableInType false in
/-- **Mismatch corollary**: when `symmDiff A B ≠ sources n`, the
source-conditioned pair-weight sum is `0` (empty Finset).
By `pairFinset_with_sources_eq_empty_of_sources_mismatch` (PR #877). -/
theorem Current.sum_pairFinset_with_sources_weight_mul_weight_of_mismatch
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (h : symmDiff A B ≠ n.sources G Λ) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2 = 0 := by
  rw [Current.pairFinset_with_sources_eq_empty_of_sources_mismatch
        G Λ n A B h, Finset.sum_empty]

set_option linter.unusedDecidableInType false in
/-- **`subFinset_with_source 0 ∅ = {0}`**: the only `m ≤ 0` is `m = 0`
(`subFinset_zero`, PR #871), and `0.sources = ∅` (`zero_sources`). -/
theorem Current.subFinset_with_source_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    Current.subFinset_with_source G Λ (0 : Current G Λ) ∅ = {0} := by
  classical
  ext m
  rw [Current.mem_subFinset_with_source_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hle, hsrc⟩
    have : m ∈ Current.subFinset G Λ 0 :=
      (Current.mem_subFinset_iff G Λ 0 m).mpr hle
    rw [Current.subFinset_zero] at this
    exact Finset.mem_singleton.mp this
  · rintro rfl
    refine ⟨?_, ?_⟩
    · exact fun _ => Nat.zero_le _
    · exact Current.zero_sources G Λ

set_option linter.unusedDecidableInType false in
/-- **`subFinset_with_source 0 A = ∅` for `A ≠ ∅`**: the only `m ≤ 0`
is `m = 0`, but `0.sources = ∅ ≠ A`. -/
theorem Current.subFinset_with_source_zero_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {A : Finset ↑Λ} (hA : A ≠ ∅) :
    Current.subFinset_with_source G Λ (0 : Current G Λ) A = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [Current.mem_subFinset_with_source_iff] at hm
  obtain ⟨hle, hsrc⟩ := hm
  apply hA
  change m.sources G Λ = A at hsrc
  have hmem : m ∈ Current.subFinset G Λ 0 :=
    (Current.mem_subFinset_iff G Λ 0 m).mpr hle
  rw [Current.subFinset_zero] at hmem
  obtain rfl := Finset.mem_singleton.mp hmem
  rw [Current.zero_sources] at hsrc
  exact hsrc.symm

set_option linter.unusedDecidableInType false in
/-- **`pairFinset_with_sources 0 ∅ ∅ = {(0, 0)}`**: only `(0, 0)`
satisfies `n₁ + n₂ = 0` and both source-free. -/
theorem Current.pairFinset_with_sources_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    Current.pairFinset_with_sources G Λ (0 : Current G Λ) ∅ ∅
      = {((0 : Current G Λ), (0 : Current G Λ))} := by
  classical
  ext p
  rw [Current.mem_pairFinset_with_sources_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hsum, _, _⟩
    have hpair : p ∈ Current.pairFinset G Λ 0 :=
      (Current.mem_pairFinset_iff G Λ 0 p).mpr hsum
    rw [Current.pairFinset_zero] at hpair
    exact Finset.mem_singleton.mp hpair
  · rintro rfl
    refine ⟨zero_add 0, ?_, ?_⟩
    · exact Current.zero_sources G Λ
    · exact Current.zero_sources G Λ

set_option linter.unusedDecidableInType false in
/-- **`pairFinset_with_sources 0 A B = ∅` when `A ≠ ∅` or `B ≠ ∅`**:
the only pair summing to `0` is `(0, 0)`, both source-free. -/
theorem Current.pairFinset_with_sources_zero_of_nonempty
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {A B : Finset ↑Λ} (h : A ≠ ∅ ∨ B ≠ ∅) :
    Current.pairFinset_with_sources G Λ (0 : Current G Λ) A B = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Current.mem_pairFinset_with_sources_iff] at hp
  obtain ⟨hsum, hA, hB⟩ := hp
  change p.1.sources G Λ = A at hA
  change p.2.sources G Λ = B at hB
  have hpair : p ∈ Current.pairFinset G Λ 0 :=
    (Current.mem_pairFinset_iff G Λ 0 p).mpr hsum
  rw [Current.pairFinset_zero] at hpair
  obtain rfl := Finset.mem_singleton.mp hpair
  rw [Current.zero_sources] at hA hB
  rcases h with hA' | hB'
  · exact hA' hA.symm
  · exact hB' hB.symm

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned `jointFactor` sum is bounded by the unrestricted
closed form**: `∑ m ∈ subFinset_with_source n A, jointFactor m (n - m)
≤ 2^(∑ e, n e)`. By `Finset.sum_le_sum_of_subset_of_nonneg` (filter is a
subset, jointFactor ≥ 0) + PR #875 closed form on the unrestricted sum. -/
theorem Current.sum_subFinset_with_source_jointFactor_le_pow_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    ∑ m ∈ Current.subFinset_with_source G Λ n A,
        Current.jointFactor G Λ m (n - m)
      ≤ (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  rw [← Current.sum_subFinset_jointFactor_compl_eq_pow_two G Λ n]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Current.subFinset_with_source_subset G Λ n A) (fun m _ _ => ?_)
  unfold Current.jointFactor
  refine Finset.prod_nonneg (fun e _ => ?_)
  exact Nat.cast_nonneg _

set_option linter.unusedDecidableInType false in
/-- **Pair-weight bound (corollary)** under `0 ≤ β J` and
`symmDiff sources_n A = B`:
`∑ p ∈ pairFinset_with_sources n A B, weight β J p.1 * weight β J p.2
  ≤ weight β J n * 2^(∑ e, n e)`. By PR #880 (pair-weight identity) +
weight nonneg + the previous theorem. -/
theorem Current.sum_pairFinset_with_sources_weight_mul_weight_le
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B)
    {β J : ℝ} (hβJ : 0 ≤ β * J) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      ≤ Current.weight G Λ β J n
        * (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  rw [Current.sum_pairFinset_with_sources_weight_mul_weight G Λ n A B hAB]
  exact mul_le_mul_of_nonneg_left
    (Current.sum_subFinset_with_source_jointFactor_le_pow_two G Λ n A)
    (Current.weight_nonneg G Λ hβJ n)

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-Finset swap image identity**:
`(pairFinset_with_sources n A B).image Prod.swap = pairFinset_with_sources n B A`.
By `add_comm` on the pair sum and swap of sources A ↔ B. The
source-conditioned analog of PR #874's `pairFinset_image_swap_eq_self`. -/
theorem Current.pairFinset_with_sources_image_swap_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ) :
    (Current.pairFinset_with_sources G Λ n A B).image Prod.swap
      = Current.pairFinset_with_sources G Λ n B A := by
  ext p
  rw [Finset.mem_image, Current.mem_pairFinset_with_sources_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Current.mem_pairFinset_with_sources_iff] at hq
    obtain ⟨hsum, hA, hB⟩ := hq
    refine ⟨?_, hB, hA⟩
    change q.2 + q.1 = n
    rw [add_comm]; exact hsum
  · rintro ⟨hsum, hB, hA⟩
    refine ⟨p.swap, ?_, ?_⟩
    · rw [Current.mem_pairFinset_with_sources_iff]
      refine ⟨?_, hA, hB⟩
      change p.2 + p.1 = n
      rw [add_comm]; exact hsum
    · exact Prod.swap_swap p

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-Finset sum swap invariance**:
`∑ p ∈ pairFinset_with_sources n A B, f p
  = ∑ p ∈ pairFinset_with_sources n B A, f p.swap`.
By the swap image identity + `Finset.sum_image` on the involutive
`Prod.swap`. -/
theorem Current.sum_pairFinset_with_sources_image_swap_eq
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (f : Current G Λ × Current G Λ → ℝ) :
    ∑ p ∈ Current.pairFinset_with_sources G Λ n A B, f p
      = ∑ p ∈ Current.pairFinset_with_sources G Λ n B A, f p.swap := by
  rw [← Current.pairFinset_with_sources_image_swap_eq G Λ n A B]
  rw [Finset.sum_image]
  · simp [Prod.swap_swap]
  · intro a _ b _ h
    exact (Prod.swap_injective h)

set_option linter.unusedDecidableInType false in
/-- **Source-conditioned pair-Finset card symmetry in (A, B)**:
`(pairFinset_with_sources n A B).card = (pairFinset_with_sources n B A).card`.
By the swap image identity + `Finset.card_image_of_injective` on the
injective `Prod.swap`. -/
theorem Current.pairFinset_with_sources_card_eq_swap
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ) :
    (Current.pairFinset_with_sources G Λ n A B).card
      = (Current.pairFinset_with_sources G Λ n B A).card := by
  rw [← Current.pairFinset_with_sources_image_swap_eq G Λ n A B]
  exact (Finset.card_image_of_injective _ Prod.swap_injective).symm

end Ambient
end IsingModel
