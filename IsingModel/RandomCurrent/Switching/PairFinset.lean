import IsingModel.RandomCurrent.Switching.Core

/-!
# The Finset of ordered pairs of currents with a prescribed sum

`Current.pairFinset G Λ n` is the `Finset` of ordered pairs of currents on
`inducedGraph G Λ`, the subgraph of `G` that `Λ` induces, whose sum is `n`, for an arbitrary
`G : SimpleGraph V` and an arbitrary finite volume `Λ : Finset V`. It is defined as the image
of `Current.subFinset G Λ n`, the currents bounded by `n` in the pointwise order, under
`m ↦ (m, n - m)`, and its membership predicate is stated without reference to that image: a
pair belongs to it exactly when its two components add up to `n`.

Its cardinality equals that of `Current.subFinset G Λ n`, and in closed form it is the
product over the edges of `n e + 1`.

Summation transports along the same map: for a real-valued `f` on pairs, the sum of `f` over
the pair `Finset` equals the sum of `f (m, n - m)` over the currents bounded by `n`. Taking
for `f` the function sending a pair `p` to
`Current.weight G Λ β J p.1 * Current.weight G Λ β J p.2` gives a factored form — the weight
of `n` times the sum, over the currents bounded by `n`, of
`Current.jointFactor G Λ m (n - m)` — for arbitrary real `β` and `J`.

Every statement here takes `[DecidableEq V]` together with
`[Fintype (inducedGraph G Λ).edgeSet]`, and none carries a hypothesis.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

set_option linter.unusedDecidableInType false in
/-- **Pair-Finset of currents summing to `n`**: the `Finset` of pairs
`(n₁, n₂) : Current G Λ × Current G Λ` with `n₁ + n₂ = n`, realized
concretely as `(subFinset n).image (m ↦ (m, n - m))`. The LHS of
the Aizenman switching pair-bijection
`{(n₁, n₂) : n₁ + n₂ = n} ↔ {m : m ≤ n}` (Aizenman 1982 Lemma 3.2, p. 7 /
FV §3.10.6). -/
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
behind the Aizenman switching identity (FV §3.10.6). -/
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

end Ambient
end IsingModel
