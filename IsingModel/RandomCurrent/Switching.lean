import IsingModel.RandomCurrent.BoundedExpansion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Aizenman switching lemma infrastructure

Sub-current operations, pair-Finset parameterizations, joint factors,
source-set algebra, and connectivity results leading to the
Aizenman switching lemma (GJ §5.1 Thm 5.1.2 / FV Thm 9.35).

## References

* Glimm–Jaffe, *Quantum Physics*, §5.1; Friedli–Velenik §3.7.
* Aizenman, M. (1982). Geometric analysis of φ⁴ fields.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Pointwise order on currents**: `n ≤ m` iff `n e ≤ m e` for every edge `e`.
The Pi LE on `Current G Λ` unfolds definitionally to the pointwise order.
Used in the Aizenman switching lemma (Aizenman 1982 Lemma 4.1 / FV §3.7). -/
theorem Current.le_def (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ m ↔ ∀ e, n e ≤ m e := Iff.rfl

omit [DecidableEq V] in
/-- **Zero is the least current**: `(0 : Current G Λ) ≤ n` for any
current `n`. Each component `0 ≤ n e` in `ℕ`. -/
theorem Current.zero_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (0 : Current G Λ) ≤ n := fun _ => Nat.zero_le _

omit [DecidableEq V] in
/-- **Left summand is below the sum**: `n ≤ n + m`, since
`n e ≤ n e + m e` for every edge `e`. -/
theorem Current.le_self_add_right (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ n + m := fun _ => Nat.le_add_right _ _

omit [DecidableEq V] in
/-- **Right summand is below the sum**: `n ≤ m + n`, since
`n e ≤ m e + n e` for every edge `e`. -/
theorem Current.le_self_add_left (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n m : Current G Λ) :
    n ≤ m + n := fun _ => Nat.le_add_left _ _

/-- **Finset of currents bounded by `n`**: the `Finset` of currents
`m` with `m ≤ n` pointwise, enumerated via
`Fintype.piFinset (fun e => Finset.range (n e + 1))`. This is the
parameterizing set for the Aizenman switching pair-bijection
`{(n₁, n₂) : n₁ + n₂ = n} ↔ {m : m ≤ n}` (Aizenman 1982 Lemma 4.1 /
FV §3.7). -/
def Current.subFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    Finset (Current G Λ) :=
  Fintype.piFinset (fun e => Finset.range (n e + 1))

set_option linter.unusedDecidableInType false in
/-- **Membership in `subFinset`**: `m ∈ subFinset n ↔ m ≤ n`,
via `Fintype.mem_piFinset` + `Finset.mem_range` + `Nat.lt_succ_iff`. -/
@[simp]
theorem Current.mem_subFinset_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) :
    m ∈ Current.subFinset G Λ n ↔ m ≤ n := by
  unfold Current.subFinset
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_range, Nat.lt_succ_iff]
  rfl

set_option linter.unusedDecidableInType false in
/-- **Cardinality of `subFinset`**:
`#(subFinset n) = ∏_e (n e + 1)`. The number of currents `m ≤ n` is
the product of per-edge multiplicities `n e + 1`, by
`Fintype.card_piFinset` + `Finset.card_range`. The combinatorial
count behind the joint factor `∏_e Nat.choose (n e) (m e)` in
`Current.weight_mul_weight_eq_weight_add_mul_jointFactor`
(PR #845). -/
theorem Current.subFinset_card_eq_prod (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.subFinset G Λ n).card
      = ∏ e : (inducedGraph G Λ).edgeSet, (n e + 1) := by
  unfold Current.subFinset
  rw [Fintype.card_piFinset]
  simp [Finset.card_range]

/-- **Pointwise truncated subtraction** of currents: `(n - m) e := n e - m e`
in `ℕ` (which is `Nat.sub`, cut off at `0`). The truncation primitive
needed for the switching pair-bijection (Aizenman 1982 Lemma 4.1 /
FV §3.7), parameterized by `m ↦ (m, n - m)` for `m ≤ n`. -/
instance Current.instSub (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] : Sub (Current G Λ) :=
  ⟨fun n m => fun e => n e - m e⟩

omit [DecidableEq V] in
/-- **Pointwise sub**: `(n - m) e = n e - m e` (by definition of
`Current.instSub`, which uses `Nat.sub`). -/
@[simp]
theorem Current.sub_apply (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) (e : (inducedGraph G Λ).edgeSet) :
    (n - m) e = n e - m e := rfl

omit [DecidableEq V] in
/-- **Truncation cancels under `m ≤ n`**: `(n - m) + m = n`.
Pointwise via `Nat.sub_add_cancel`. The naming `sub_add_cancel`
follows mathlib's `Nat.sub_add_cancel` / `tsub_add_cancel_of_le`. -/
theorem Current.sub_add_cancel_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    (n - m) + m = n := by
  ext e
  simp [Nat.sub_add_cancel (h e)]

omit [DecidableEq V] in
/-- **Truncation cancels (commuted form) under `m ≤ n`**:
`m + (n - m) = n`. By commutativity + `sub_add_cancel_of_le`. -/
theorem Current.add_sub_cancel_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    m + (n - m) = n := by
  rw [add_comm]
  exact Current.sub_add_cancel_of_le G Λ h

omit [DecidableEq V] in
/-- **Truncated sub is bounded above by the minuend**:
`n - m ≤ n` for any currents `n, m`. Pointwise via `Nat.sub_le`. -/
theorem Current.sub_le_self (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n m : Current G Λ) :
    n - m ≤ n := fun _ => Nat.sub_le _ _

set_option linter.unusedDecidableInType false in
/-- **Pair-Finset of currents summing to `n`**: the `Finset` of pairs
`(n₁, n₂) : Current G Λ × Current G Λ` with `n₁ + n₂ = n`, realized
concretely as `(subFinset n).image (m ↦ (m, n - m))`. The LHS of
the Aizenman switching pair-bijection
`{(n₁, n₂) : n₁ + n₂ = n} ↔ {m : m ≤ n}` (Aizenman 1982 Lemma 4.1 /
FV §3.7). -/
def Current.pairFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    Finset (Current G Λ × Current G Λ) :=
  (Current.subFinset G Λ n).image (fun m => (m, n - m))

set_option linter.unusedDecidableInType false in
/-- **Membership in `pairFinset`**: `(m₁, m₂) ∈ pairFinset n ↔ m₁ + m₂ = n`.
Forward: any pair in the image has the form `(k, n - k)` with `k ≤ n`,
so `k + (n - k) = n` by `add_sub_cancel_of_le`. Backward: from
`m₁ + m₂ = n` we get `m₁ ≤ n` (`le_self_add_right`) and
`m₂ = n - m₁` (pointwise from `m₁ e + m₂ e = n e`), so `(m₁, n - m₁) = (m₁, m₂)`. -/
@[simp]
theorem Current.mem_pairFinset_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (p : Current G Λ × Current G Λ) :
    p ∈ Current.pairFinset G Λ n ↔ p.1 + p.2 = n := by
  unfold Current.pairFinset
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Current.mem_subFinset_iff] at hk
    exact Current.add_sub_cancel_of_le G Λ hk
  · intro hsum
    refine ⟨p.1, ?_, ?_⟩
    · rw [Current.mem_subFinset_iff]
      intro e
      have heq : p.1 e + p.2 e = n e := congrFun hsum e
      exact heq ▸ Nat.le_add_right (p.1 e) (p.2 e)
    · ext
      · rfl
      · rename_i e
        simp only [Current.sub_apply]
        have heq : p.1 e + p.2 e = n e := by
          have h := congrFun hsum e
          simpa [Pi.add_apply] using h
        omega

set_option linter.unusedDecidableInType false in
/-- **`pairFinset` cardinality matches `subFinset`**:
`(pairFinset n).card = (subFinset n).card`, since the defining map
`m ↦ (m, n - m)` is injective (the first coordinate is `m`). -/
theorem Current.pairFinset_card_eq_subFinset_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).card = (Current.subFinset G Λ n).card := by
  unfold Current.pairFinset
  apply Finset.card_image_of_injective
  intro m₁ m₂ h
  exact congrArg Prod.fst h

set_option linter.unusedDecidableInType false in
/-- **`pairFinset` cardinality formula**:
`(pairFinset n).card = ∏ e, (n e + 1)`, by composing
`pairFinset_card_eq_subFinset_card` with `subFinset_card_eq_prod`
(PR #866). The number of pairs `(n₁, n₂)` with `n₁ + n₂ = n` equals
the per-edge product of multiplicities. -/
theorem Current.pairFinset_card_eq_prod (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).card
      = ∏ e : (inducedGraph G Λ).edgeSet, (n e + 1) := by
  rw [Current.pairFinset_card_eq_subFinset_card,
      Current.subFinset_card_eq_prod]

set_option linter.unusedDecidableInType false in
/-- **Sum over `pairFinset` reindexes via `subFinset`**:
`∑ p ∈ pairFinset n, f p = ∑ m ∈ subFinset n, f (m, n - m)`.
The pair-bijection `m ↦ (m, n - m)` is injective, so summing over
the image equals summing pre-image with the function composed with
the bijection (`Finset.sum_image`). The fundamental sum reindexing
behind the Aizenman switching identity (FV §3.7). -/
theorem Current.sum_pairFinset_eq_sum_subFinset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (f : Current G Λ × Current G Λ → ℝ) :
    ∑ p ∈ Current.pairFinset G Λ n, f p
      = ∑ m ∈ Current.subFinset G Λ n, f (m, n - m) := by
  unfold Current.pairFinset
  rw [Finset.sum_image]
  intro m₁ _ m₂ _ h
  exact congrArg Prod.fst h

set_option linter.unusedDecidableInType false in
/-- **Pair-weight identity (Aizenman switching scaling)**: the sum of
`weight β J n₁ · weight β J n₂` over pairs `(n₁, n₂)` with sum `n`
equals `weight β J n` times the sum of `jointFactor m (n - m)` over
`m ≤ n`. By `sum_pairFinset_eq_sum_subFinset`, then per-term
`weight_mul_weight_eq_weight_add_mul_jointFactor` (PR #845) with
`m + (n - m) = n` (PR #867 `add_sub_cancel_of_le`), then
`Finset.mul_sum` to factor out the constant `weight β J n`. -/
theorem Current.sum_pairFinset_weight_mul_weight
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset G Λ n,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      = Current.weight G Λ β J n
        * ∑ m ∈ Current.subFinset G Λ n,
            Current.jointFactor G Λ m (n - m) := by
  rw [Current.sum_pairFinset_eq_sum_subFinset, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Current.mem_subFinset_iff] at hm
  rw [Current.weight_mul_weight_eq_weight_add_mul_jointFactor,
      Current.add_sub_cancel_of_le G Λ hm]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Sources of `n - m` is the symmetric difference under `m ≤ n`**:
`(n - m).sources = symmDiff (sources n) (sources m)` when `m ≤ n`.
Combine `sub_add_cancel_of_le` (PR #867: `(n - m) + m = n`) with
`add_sources_eq` (sources of a sum is symmDiff of summand sources)
and the involution of `symmDiff` on the right. -/
theorem Current.sub_sources_eq_symmDiff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {n m : Current G Λ} (h : m ≤ n) :
    (n - m).sources G Λ
      = symmDiff (n.sources G Λ) (m.sources G Λ) := by
  have h₁ : ((n - m) + m).sources G Λ
              = symmDiff ((n - m).sources G Λ) (m.sources G Λ) :=
    Current.add_sources_eq G Λ (n - m) m
  rw [Current.sub_add_cancel_of_le G Λ h] at h₁
  rw [h₁, symmDiff_assoc, symmDiff_self, symmDiff_bot]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`(n - m).HasSources A` is the symmetric-difference equation under
`m ≤ n`**: `(n - m).HasSources A ↔ symmDiff (sources n) (sources m) = A`.
By unfolding `HasSources` and `sub_sources_eq_symmDiff`. -/
theorem Current.sub_hasSources_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    {n m : Current G Λ} (h : m ≤ n) (A : Finset ↑Λ) :
    (n - m).HasSources G Λ A
      ↔ symmDiff (n.sources G Λ) (m.sources G Λ) = A := by
  unfold Current.HasSources
  rw [Current.sub_sources_eq_symmDiff G Λ h]

omit [DecidableEq V] in
/-- **`n - 0 = n`**: subtracting the zero current is the identity. -/
@[simp]
theorem Current.sub_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    n - (0 : Current G Λ) = n := by
  ext e
  simp

omit [DecidableEq V] in
/-- **`0 - n = 0`**: truncated subtraction (`Nat.sub`) at the zero
current pointwise is `0 - n e = 0`. -/
@[simp]
theorem Current.zero_sub (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (0 : Current G Λ) - n = 0 := by
  ext e
  simp

omit [DecidableEq V] in
/-- **`n - n = 0`**: pointwise `n e - n e = 0` in `ℕ`. -/
@[simp]
theorem Current.sub_self (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    n - n = (0 : Current G Λ) := by
  ext e
  simp

set_option linter.unusedDecidableInType false in
/-- **`subFinset 0 = {0}`**: the only current `m ≤ 0` is `m = 0`,
since each component `m e ≤ 0` forces `m e = 0`. By `Finset.ext`
+ `mem_subFinset_iff` + `Finset.mem_singleton`. -/
theorem Current.subFinset_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Current.subFinset G Λ (0 : Current G Λ) = {0} := by
  ext m
  rw [Current.mem_subFinset_iff, Finset.mem_singleton]
  constructor
  · intro h
    ext e
    have := h e
    simp only [Pi.zero_apply, Nat.le_zero] at this
    exact this
  · rintro rfl
    intro _
    simp

set_option linter.unusedDecidableInType false in
/-- **`(0, n) ∈ pairFinset n`**: the trivial pair `(0, n)` lies in
the pair-Finset since `0 + n = n`. -/
theorem Current.zero_mem_pairFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    ((0 : Current G Λ), n) ∈ Current.pairFinset G Λ n := by
  rw [Current.mem_pairFinset_iff]
  exact zero_add n

set_option linter.unusedDecidableInType false in
/-- **`(n, 0) ∈ pairFinset n`**: the trivial pair `(n, 0)` lies in
the pair-Finset since `n + 0 = n`. -/
theorem Current.self_mem_pairFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (n, (0 : Current G Λ)) ∈ Current.pairFinset G Λ n := by
  rw [Current.mem_pairFinset_iff]
  exact add_zero n

set_option linter.unusedDecidableInType false in
/-- **`pairFinset 0 = {(0, 0)}`**: the only pair `(n₁, n₂)` summing
to `0` is `(0, 0)`, since both components must vanish. -/
theorem Current.pairFinset_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Current.pairFinset G Λ (0 : Current G Λ)
      = {((0 : Current G Λ), (0 : Current G Λ))} := by
  ext p
  rw [Current.mem_pairFinset_iff, Finset.mem_singleton]
  constructor
  · intro hsum
    have hp1 : p.1 = 0 := by
      ext e
      have h := congrFun hsum e
      simp only [Pi.add_apply, Pi.zero_apply] at h
      change p.1 e = 0
      omega
    have hp2 : p.2 = 0 := by
      ext e
      have h := congrFun hsum e
      simp only [Pi.add_apply, Pi.zero_apply] at h
      change p.2 e = 0
      omega
    rw [Prod.ext_iff]
    exact ⟨hp1, hp2⟩
  · rintro rfl
    simp

omit [DecidableEq V] in
/-- **Double truncation cancels under `m ≤ n`**:
`n - (n - m) = m` when `m ≤ n`. Pointwise via `Nat.sub_sub_self`. -/
theorem Current.sub_sub_self_of_le (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    n - (n - m) = m := by
  ext e
  change n e - (n e - m e) = m e
  exact Nat.sub_sub_self (h e)

set_option linter.unusedDecidableInType false in
/-- **Complement involution preserves `subFinset`**:
`(subFinset n).image (m ↦ n - m) = subFinset n`. Each `m ≤ n` maps
to `n - m ≤ n` (`sub_le_self`); conversely each `k ≤ n` is the
image of `n - k` (since `n - (n - k) = k` by `sub_sub_self_of_le`).
The natural involution corresponding to swapping `(m, n - m) ↔ (n - m, m)`
in the pair-bijection (PR #868). -/
theorem Current.subFinset_image_compl (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.subFinset G Λ n).image (fun m => n - m)
      = Current.subFinset G Λ n := by
  ext k
  rw [Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Current.mem_subFinset_iff] at hm
    rw [Current.mem_subFinset_iff]
    exact Current.sub_le_self G Λ n m
  · intro hk
    rw [Current.mem_subFinset_iff] at hk
    refine ⟨n - k, ?_, ?_⟩
    · rw [Current.mem_subFinset_iff]
      exact Current.sub_le_self G Λ n k
    · exact Current.sub_sub_self_of_le G Λ hk

set_option linter.unusedDecidableInType false in
/-- **`pairFinset` is invariant under `Prod.swap`**:
`(pairFinset n).image Prod.swap = pairFinset n`. By the commutativity
of `+` on currents, `(n₁, n₂) ∈ pairFinset n ↔ (n₂, n₁) ∈ pairFinset n`. -/
theorem Current.pairFinset_image_swap_eq_self
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).image Prod.swap
      = Current.pairFinset G Λ n := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Current.mem_pairFinset_iff] at hq
    rw [Current.mem_pairFinset_iff]
    change q.2 + q.1 = n
    rw [add_comm]; exact hq
  · intro hp
    rw [Current.mem_pairFinset_iff] at hp
    refine ⟨p.swap, ?_, ?_⟩
    · rw [Current.mem_pairFinset_iff]
      change p.2 + p.1 = n
      rw [add_comm]; exact hp
    · exact Prod.swap_swap p

set_option linter.unusedDecidableInType false in
/-- **`pairFinset n` is nonempty**: contains `(n, 0)` since `n + 0 = n`
(`self_mem_pairFinset`, PR #872). -/
theorem Current.pairFinset_nonempty (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    (Current.pairFinset G Λ n).Nonempty :=
  ⟨(n, 0), Current.self_mem_pairFinset G Λ n⟩

omit [DecidableEq V] in
/-- **`jointFactor m (n - m) = ∏ e, C(n e, m e)`** for `m ≤ n`:
since `m + (n - m) = n` pointwise, the binomial argument simplifies. -/
theorem Current.jointFactor_compl_eq_prod_choose
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {n m : Current G Λ} (h : m ≤ n) :
    Current.jointFactor G Λ m (n - m)
      = ∏ e : (inducedGraph G Λ).edgeSet, (Nat.choose (n e) (m e) : ℝ) := by
  unfold Current.jointFactor
  refine Finset.prod_congr rfl (fun e _ => ?_)
  congr 2
  change m e + (n - m) e = n e
  rw [Current.sub_apply]
  exact Nat.add_sub_cancel' (h e)

set_option linter.unusedDecidableInType false in
/-- **Closed-form sum `∑ m ∈ subFinset n, jointFactor m (n - m) = 2^(∑ e, n e)`**:
combine `jointFactor_compl_eq_prod_choose` (per-summand simplification)
with Fubini (`Finset.prod_univ_sum`) and the binomial-row identity
`Nat.sum_range_choose : ∑ k ∈ range (n + 1), C(n, k) = 2^n`, then
`Finset.prod_pow_eq_pow_sum` to reassemble `∏ e, 2^(n e) = 2^(∑ e, n e)`.
The closed form completing PR #869's pair-weight scaling identity. -/
theorem Current.sum_subFinset_jointFactor_compl_eq_pow_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (n : Current G Λ) :
    ∑ m ∈ Current.subFinset G Λ n, Current.jointFactor G Λ m (n - m)
      = (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  have step1 : ∑ m ∈ Current.subFinset G Λ n, Current.jointFactor G Λ m (n - m)
      = ∑ m ∈ Current.subFinset G Λ n,
          ∏ e : (inducedGraph G Λ).edgeSet, (Nat.choose (n e) (m e) : ℝ) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [Current.mem_subFinset_iff] at hm
    exact Current.jointFactor_compl_eq_prod_choose G Λ hm
  rw [step1]
  unfold Current.subFinset
  have fubini :
      ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k ∈ Finset.range (n e + 1), ((n e).choose k : ℝ)
        = ∑ m ∈ Fintype.piFinset (fun e => Finset.range (n e + 1)),
            ∏ e : (inducedGraph G Λ).edgeSet, ((n e).choose (m e) : ℝ) :=
    Finset.prod_univ_sum _ _
  rw [← fubini]
  trans ∏ e : (inducedGraph G Λ).edgeSet, (2 : ℝ) ^ n e
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  · exact Finset.prod_pow_eq_pow_sum _ _ _

set_option linter.unusedDecidableInType false in
/-- **Pair-weight closed form (capstone)**: combining the pair-weight
scaling identity (PR #869) with the joint-factor sum closed form
(PR #875), the random-current pair sum factors completely:
\(∑ p ∈ pairFinset n, weight β J p.1 · weight β J p.2
  = weight β J n · 2^{∑_e n e}\). The single-current weight times an
exponential of the total current degree, with no remaining combinatorial
sum. Useful in switching applications. -/
theorem Current.sum_pairFinset_weight_mul_weight_eq_weight_pow_two
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) (β J : ℝ) :
    ∑ p ∈ Current.pairFinset G Λ n,
        Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2
      = Current.weight G Λ β J n
        * (2 : ℝ) ^ (∑ e : (inducedGraph G Λ).edgeSet, n e) := by
  rw [Current.sum_pairFinset_weight_mul_weight,
      Current.sum_subFinset_jointFactor_compl_eq_pow_two]

/-- **Source-conditioned pair-Finset**: pairs `(n₁, n₂) ∈ pairFinset n`
filtered by `n₁.HasSources A ∧ n₂.HasSources B`. The LHS / RHS data
type for source-bijection statements of the switching lemma
(Aizenman 1982 Lemma 4.1 / FV §3.7). -/
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

set_option linter.unusedDecidableInType false in
/-- **Switching Lemma — cardinality**: when `symmDiff (sources n) A = B`,
the bijection `m ↦ n - m` (involution by `sub_sub_self_of_le`) maps
`subFinset_with_source n A` bijectively to `subFinset_with_source n B`,
hence the two source-conditioned sub-current sets have equal cardinality.
(GJ §5.1 Theorem 5.1.2 / FV Theorem 9.35.) -/
theorem Current.subFinset_with_source_card_switching
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) :
    (Current.subFinset_with_source G Λ n A).card =
      (Current.subFinset_with_source G Λ n B).card := by
  have hBA : symmDiff (n.sources G Λ) B = A := by
    rw [← hAB]; exact symmDiff_symmDiff_cancel_left _ _
  refine Finset.card_nbij' (fun m => n - m) (fun m => n - m) ?_ ?_ ?_ ?_
  · -- forward: m ∈ subFinset_with_source n A → n-m ∈ subFinset_with_source n B
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 B).mpr (by rw [hm.2]; exact hAB)⟩
  · -- backward: m ∈ subFinset_with_source n B → n-m ∈ subFinset_with_source n A
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 A).mpr (by rw [hm.2]; exact hBA)⟩
  · -- left_inv: n-(n-m) = m for m ∈ subFinset_with_source n A
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm
    exact Current.sub_sub_self_of_le G Λ hm.1
  · -- right_inv: n-(n-m) = m for m ∈ subFinset_with_source n B
    intro m hm
    simp only [Finset.mem_coe, Current.mem_subFinset_with_source_iff] at hm
    exact Current.sub_sub_self_of_le G Λ hm.1

set_option linter.unusedDecidableInType false in
/-- **Switching Lemma — weighted sum**: when `symmDiff (sources n) A = B`,
the bijection `m ↦ n - m` preserves the function `m ↦ w(m) * w(n - m)`
(since `w(n-m) * w(n-(n-m)) = w(n-m) * w(m)` by `sub_sub_self_of_le` + `mul_comm`),
so the weighted sums over `subFinset_with_source n A` and `subFinset_with_source n B` are equal.
(GJ §5.1 Theorem 5.1.2 / FV Theorem 9.35.) -/
theorem Current.sum_subFinset_with_source_weight_mul_weight_switching
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A B : Finset ↑Λ)
    (hAB : symmDiff (n.sources G Λ) A = B) {β J : ℝ} :
    ∑ m ∈ Current.subFinset_with_source G Λ n A,
        m.weight G Λ β J * (n - m).weight G Λ β J =
      ∑ m ∈ Current.subFinset_with_source G Λ n B,
        m.weight G Λ β J * (n - m).weight G Λ β J := by
  have hBA : symmDiff (n.sources G Λ) B = A := by
    rw [← hAB]; exact symmDiff_symmDiff_cancel_left _ _
  refine Finset.sum_nbij' (fun m => n - m) (fun m => n - m) ?_ ?_ ?_ ?_ ?_
  · -- forward
    intro m hm
    rw [Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 B).mpr (by rw [hm.2]; exact hAB)⟩
  · -- backward
    intro m hm
    rw [Current.mem_subFinset_with_source_iff] at hm ⊢
    exact ⟨Current.sub_le_self G Λ n m,
           (Current.sub_hasSources_iff G Λ hm.1 A).mpr (by rw [hm.2]; exact hBA)⟩
  · -- left_inv
    intro m hm
    exact Current.sub_sub_self_of_le G Λ
      ((Current.mem_subFinset_with_source_iff G Λ n A m).mp hm).1
  · -- right_inv
    intro m hm
    exact Current.sub_sub_self_of_le G Λ
      ((Current.mem_subFinset_with_source_iff G Λ n B m).mp hm).1
  · -- value: w(m)*w(n-m) = w(n-m)*w(n-(n-m)) = w(n-m)*w(m)
    intro m hm
    rw [Current.sub_sub_self_of_le G Λ
        ((Current.mem_subFinset_with_source_iff G Λ n A m).mp hm).1, mul_comm]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Membership in `Current.support`**: `e ∈ n.support ↔ n e ≠ 0`.
By definitional unfolding of `support := univ.filter (n e ≠ 0)`. -/
theorem Current.mem_support_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (e : (inducedGraph G Λ).edgeSet) :
    e ∈ n.support G Λ ↔ n e ≠ 0 := by
  classical
  unfold Current.support
  simp [Finset.mem_filter]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Sub support is bounded by minuend support**:
`(n - m).support ⊆ n.support`. If `(n - m) e ≠ 0` then `n e - m e > 0`
(truncated `Nat.sub`), so `n e > m e ≥ 0`, hence `n e ≠ 0`. -/
theorem Current.support_sub_subset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n m : Current G Λ) :
    (n - m).support G Λ ⊆ n.support G Λ := by
  intro e he
  rw [Current.mem_support_iff] at he ⊢
  rw [Current.sub_apply] at he
  omega

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Empty support characterizes zero**: `n.support = ∅ ↔ n = 0`.
Forward: every edge has `n e = 0` so `n = 0` by extensionality.
Backward: `support_zero`. -/
theorem Current.support_eq_empty_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    n.support G Λ = ∅ ↔ n = 0 := by
  constructor
  · intro h
    ext e
    have : e ∉ n.support G Λ := by rw [h]; exact Finset.notMem_empty e
    rw [Current.mem_support_iff, not_not] at this
    rw [this]
    rfl
  · rintro rfl
    exact Current.support_zero G Λ

/-- **Current adjacency**: vertices `u, v ∈ ↑Λ` are *adjacent in `n`*
iff they are distinct and connected by an edge in `n.support` (i.e.
some `e` with `n e ≠ 0` containing both `u` and `v`). The vertex
adjacency relation of the multigraph defined by `n`'s active edges,
the foundation for the connectivity-based Aizenman switching argument
(Aizenman 1982 Lemma 4.1 / FV §3.7). -/
def Current.Adj (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (u v : ↑Λ) : Prop :=
  u ≠ v ∧ ∃ e ∈ n.support G Λ,
    u ∈ (e : Sym2 ↑Λ) ∧ v ∈ (e : Sym2 ↑Λ)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Current adjacency is irreflexive**: a vertex is never adjacent to itself. -/
theorem Current.Adj_irrefl (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (u : ↑Λ) :
    ¬ n.Adj G Λ u u := by
  rintro ⟨huu, _⟩
  exact huu rfl

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Current adjacency is symmetric**: `n.Adj u v → n.Adj v u`. -/
theorem Current.Adj_symm (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {u v : ↑Λ} (h : n.Adj G Λ u v) :
    n.Adj G Λ v u := by
  obtain ⟨hne, e, he, hu, hv⟩ := h
  exact ⟨hne.symm, e, he, hv, hu⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Zero current has no adjacencies**: `(0 : Current).Adj u v ↔ False`,
since `support 0 = ∅`. -/
theorem Current.Adj_of_zero_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (u v : ↑Λ) :
    (0 : Current G Λ).Adj G Λ u v ↔ False := by
  unfold Current.Adj
  constructor
  · rintro ⟨_, e, he, _, _⟩
    rw [Current.support_zero] at he
    exact (Finset.notMem_empty e he).elim
  · intro h; exact h.elim

/-- **`Current.toSimpleGraph`**: the `SimpleGraph` on `↑Λ` whose
adjacency relation is `Current.Adj` (active-edge adjacency in the
multigraph defined by `n`). The first-class `SimpleGraph` object
enabling mathlib's connectivity / path / component APIs needed for
the switching lemma. -/
def Current.toSimpleGraph (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) : SimpleGraph ↑Λ where
  Adj := n.Adj G Λ
  symm := fun _ _ h => Current.Adj_symm G Λ n h
  loopless := ⟨fun u h => Current.Adj_irrefl G Λ n u h⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`toSimpleGraph` adjacency unfolding**:
`(n.toSimpleGraph).Adj u v ↔ n.Adj u v` (definitional). -/
@[simp]
theorem Current.toSimpleGraph_adj_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (u v : ↑Λ) :
    (n.toSimpleGraph G Λ).Adj u v ↔ n.Adj G Λ u v := Iff.rfl

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Zero current's `toSimpleGraph` is the empty graph**: by
`Adj_of_zero_iff` (no adjacencies), the SimpleGraph is `⊥`. -/
theorem Current.toSimpleGraph_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ] :
    (0 : Current G Λ).toSimpleGraph G Λ = (⊥ : SimpleGraph ↑Λ) := by
  ext u v
  rw [Current.toSimpleGraph_adj_iff, Current.Adj_of_zero_iff]
  simp [SimpleGraph.bot_adj]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`toSimpleGraph` is a subgraph of `inducedGraph`**:
`n.toSimpleGraph G Λ ≤ inducedGraph G Λ`. Each adjacency in
`n.toSimpleGraph` arises from a support edge `e ∈ n.support`, which
satisfies `e.val ∈ (inducedGraph G Λ).edgeSet`; combined with vertex
membership and distinctness, this gives `inducedGraph.Adj` via
`SimpleGraph.adj_iff_exists_edge`. -/
theorem Current.toSimpleGraph_le_inducedGraph
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    n.toSimpleGraph G Λ ≤ inducedGraph G Λ := by
  intro u v h
  rw [Current.toSimpleGraph_adj_iff] at h
  obtain ⟨hne, e, _, hu, hv⟩ := h
  rw [SimpleGraph.adj_iff_exists_edge]
  exact ⟨hne, (e : Sym2 ↑Λ), e.2, hu, hv⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **A source vertex is incident to an active edge**: if
`v ∈ n.sources`, then there exists an edge `e ∈ n.support` containing
`v`. The foundation for the Aizenman switching argument: the boundary
vertices of a current are non-isolated in the active-edge multigraph.
(Aizenman 1982 Lemma 4.1 / FV §3.7.) -/
theorem Current.exists_support_edge_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    ∃ e ∈ n.support G Λ, v ∈ (e : Sym2 ↑Λ) := by
  classical
  by_contra habs
  push Not at habs
  rw [Current.mem_sources_iff] at hv
  apply hv
  rw [Current.parity_eq_degreeAt]
  have hdeg : n.degreeAt G Λ v = 0 := by
    unfold Current.degreeAt
    refine Finset.sum_eq_zero ?_
    intro e _
    by_cases hve : v ∈ (e : Sym2 ↑Λ)
    · rw [if_pos hve]
      by_contra hne
      exact habs e ((Current.mem_support_iff G Λ n e).mpr hne) hve
    · rw [if_neg hve]
  rw [hdeg]
  simp

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **A source vertex has a `Current.Adj` neighbour**: if
`v ∈ n.sources`, then there exists `u` with `n.Adj G Λ u v`, i.e.
`v` is not isolated in `n.toSimpleGraph`. A foundational step toward
the switching lemma's path argument (Aizenman 1982 / FV §3.7):
non-isolation of source vertices is the base case for constructing
walks from source to source in the active-edge graph. Path existence
itself is a downstream consequence, not established here. -/
theorem Current.exists_adj_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    ∃ u, n.Adj G Λ u v := by
  obtain ⟨e, he_supp, hve⟩ := Current.exists_support_edge_of_mem_sources G Λ n hv
  refine ⟨Sym2.Mem.other hve, ?_, e, he_supp, Sym2.other_mem hve, hve⟩
  exact SimpleGraph.edge_other_ne _ e.2 hve

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Isolated vertices are not sources**: the contrapositive of
`exists_adj_of_mem_sources`. If no `u` is `Current.Adj`-adjacent to
`v`, then `v ∉ n.sources`. Convenient downstream when excluding
potential sources via local isolation. -/
theorem Current.not_mem_sources_of_isolated
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : ∀ u, ¬ n.Adj G Λ u v) :
    v ∉ n.sources G Λ := by
  intro hmem
  obtain ⟨u, hadj⟩ := Current.exists_adj_of_mem_sources G Λ n hmem
  exact hv u hadj

/-- **Active edges incident to a vertex**: for a current `n` and a
vertex `v : ↑Λ`, the Finset of edges `e ∈ n.support` containing `v`.
The Finset form of `exists_support_edge_of_mem_sources`, usable in
downstream counting / partitioning arguments for the switching lemma
(Aizenman 1982 / FV §3.7). -/
noncomputable def Current.supportAt (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    Finset ((inducedGraph G Λ).edgeSet) :=
  (n.support G Λ).filter (fun e => v ∈ (e : Sym2 ↑Λ))

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Membership in `Current.supportAt`**: `e ∈ n.supportAt v ↔
e ∈ n.support ∧ v ∈ (e : Sym2 ↑Λ)`. -/
theorem Current.mem_supportAt_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) (e : (inducedGraph G Λ).edgeSet) :
    e ∈ n.supportAt G Λ v ↔ e ∈ n.support G Λ ∧ v ∈ (e : Sym2 ↑Λ) := by
  classical
  unfold Current.supportAt
  exact Finset.mem_filter

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`supportAt` is contained in `support`**: edges at a vertex are
in particular active edges. -/
theorem Current.supportAt_subset_support (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    n.supportAt G Λ v ⊆ n.support G Λ := by
  classical
  unfold Current.supportAt
  exact Finset.filter_subset _ _

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Source vertices have non-empty `supportAt`**: the Finset form
of `exists_support_edge_of_mem_sources`. If `v ∈ n.sources`, then
`(n.supportAt v).Nonempty`. -/
theorem Current.supportAt_nonempty_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    (n.supportAt G Λ v).Nonempty := by
  obtain ⟨e, he_supp, hve⟩ := Current.exists_support_edge_of_mem_sources G Λ n hv
  exact ⟨e, (Current.mem_supportAt_iff G Λ n v e).mpr ⟨he_supp, hve⟩⟩

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`degreeAt` equals the sum of `n` over `supportAt`**: the
ℕ-valued total incident degree is recovered by summing `n e` over
the Finset of active incident edges at `v`. The definitional
expression over all edges with an `if`-guard contracts to the
support-restricted sum, since edges contributing zero (either not
incident to `v` or with `n e = 0`) vanish. -/
theorem Current.degreeAt_eq_sum_supportAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    n.degreeAt G Λ v = ∑ e ∈ n.supportAt G Λ v, n e := by
  classical
  unfold Current.degreeAt
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro e he
    rw [Current.mem_supportAt_iff] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.2⟩
  · intro e he he'
    rw [Finset.mem_filter] at he
    rw [Current.mem_supportAt_iff] at he'
    push Not at he'
    by_contra hne
    exact he' ((Current.mem_support_iff G Λ n e).mpr hne) he.2

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`supportAt` cardinality is bounded by `degreeAt`**: each
active incident edge contributes at least `1` to `n.degreeAt v`
(since `n e ≠ 0` on the support gives `n e ≥ 1` in ℕ), so the
edge count is at most the total degree. -/
theorem Current.card_supportAt_le_degreeAt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    (n.supportAt G Λ v).card ≤ n.degreeAt G Λ v := by
  rw [Current.degreeAt_eq_sum_supportAt, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro e he
  rw [Current.mem_supportAt_iff, Current.mem_support_iff] at he
  exact Nat.one_le_iff_ne_zero.mpr he.1

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **`degreeAt` is positive at a source**: `v ∈ n.sources` forces
at least one active incident edge (step 94), and by the
`supportAt`↔`degreeAt` bridge the total degree is at least that
edge's count, which is positive. -/
theorem Current.degreeAt_pos_of_mem_sources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) {v : ↑Λ} (hv : v ∈ n.sources G Λ) :
    0 < n.degreeAt G Λ v := by
  have hne := Current.supportAt_nonempty_of_mem_sources G Λ n hv
  have hcard : 0 < (n.supportAt G Λ v).card := Finset.card_pos.mpr hne
  exact lt_of_lt_of_le hcard (Current.card_supportAt_le_degreeAt G Λ n v)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Edge vertex set has cardinality two**: each edge `e` in the
`inducedGraph G Λ` edgeSet has `(e : Sym2 ↑Λ).toFinset.card = 2`,
since edges are non-diagonal. The building block for the multigraph
handshake identity. -/
theorem Current.edgeSet_toFinset_card_eq_two
    (G : SimpleGraph V) (Λ : Finset V)
    [DecidableEq ↑Λ]
    (e : (inducedGraph G Λ).edgeSet) :
    (e : Sym2 ↑Λ).toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag _
    (SimpleGraph.not_isDiag_of_mem_edgeSet _ e.2)

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Multigraph handshake identity**: `∑_v n.degreeAt v
= 2 * ∑_e n e`. Each edge of multiplicity `n e` contributes to the
degree of its two endpoints, so the vertex-side total degree is
exactly twice the edge-side total multiplicity. Specialization of
`Current.sum_degreeAt_smul` at `M := ℕ`, `f := fun _ => 1`, combined
with `edgeSet_toFinset_card_eq_two`. -/
theorem Current.sum_degreeAt_eq_two_mul_total
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    ∑ v : ↑Λ, n.degreeAt G Λ v
      = 2 * ∑ e : (inducedGraph G Λ).edgeSet, n e := by
  classical
  unfold Current.degreeAt
  rw [Finset.sum_comm]
  have key : ∀ (e : (inducedGraph G Λ).edgeSet),
      (∑ v : ↑Λ, if v ∈ (e : Sym2 ↑Λ) then n e else 0) = 2 * n e := by
    intro e
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    congr 1
    have hfilter : ((Finset.univ : Finset ↑Λ).filter
        (fun v => v ∈ (e : Sym2 ↑Λ)))
          = (e : Sym2 ↑Λ).toFinset := by
      ext v
      simp [Sym2.mem_toFinset]
    rw [hfilter]
    exact Current.edgeSet_toFinset_card_eq_two G Λ e
  simp_rw [key]
  rw [← Finset.mul_sum]

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Sum of parities over all vertices is zero in `ZMod 2`**: an
immediate `ZMod 2` consequence of the handshake identity, since
`2 * X` casts to zero. This is the mod-2 form of "the number of
odd-degree vertices is even", used in the next step to establish
`Even (sources).card` (switching-lemma prerequisite). -/
theorem Current.sum_parity_eq_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) :
    ∑ v : ↑Λ, n.parity G Λ v = (0 : ZMod 2) := by
  simp only [Current.parity_eq_degreeAt]
  rw [← Nat.cast_sum, Current.sum_degreeAt_eq_two_mul_total]
  push_cast
  rw [show (2 : ZMod 2) = 0 from by decide]
  ring

omit [DecidableEq V] in
set_option linter.unusedDecidableInType false in
/-- **Indicator cast to `ZMod 2` equals parity**: since `parity v`
takes values only in `{0, 1} ⊆ ZMod 2`, the ℕ-valued indicator
`if parity v ≠ 0 then 1 else 0` casts back to `parity v`. -/
theorem Current.cast_indicator_parity
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (v : ↑Λ) :
    ((if n.parity G Λ v ≠ 0 then 1 else 0 : ℕ) : ZMod 2) = n.parity G Λ v := by
  generalize n.parity G Λ v = p
  fin_cases p <;> decide

end Ambient
end IsingModel
