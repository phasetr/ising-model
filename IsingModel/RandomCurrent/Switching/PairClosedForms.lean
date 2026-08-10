import IsingModel.RandomCurrent.Switching.PairFinset

/-!
# Truncated differences of currents, degenerate cases, and closed forms

Source-set algebra of the truncated difference of two currents on `inducedGraph G Λ`, the
subgraph of `G` that `Λ` induces, the values `Current.subFinset` and `Current.pairFinset`
take at the zero current, the images that fix them, and the closed form of the joint-factor
sum. The graph `G : SimpleGraph V` and the finite volume `Λ : Finset V` are arbitrary
throughout.

Subtraction of currents is pointwise truncated subtraction in `ℕ`. Under `m ≤ n` the source
set of `n - m` is the symmetric difference of the source sets of `n` and of `m`, and the
prescribed-source form of the same fact reads: `n - m` has source set `A` exactly when that
symmetric difference equals `A`. With no order hypothesis, `n - 0` is `n`, `0 - n` is the
zero current and `n - n` is the zero current; under `m ≤ n`, subtracting `n - m` from `n`
returns `m`.

At the zero current `Current.subFinset G Λ 0` is the singleton of the zero current and
`Current.pairFinset G Λ 0` the singleton of the pair of zero currents. For every `n`, both
`(0, n)` and `(n, 0)` belong to `Current.pairFinset G Λ n`, and that `Finset` is nonempty.

Each of `Current.subFinset G Λ n` and `Current.pairFinset G Λ n` is fixed by an image: the
image of the first under `m ↦ n - m` is the first again, and the image of the second under
`Prod.swap` is the second again.

For `m ≤ n` the joint factor of `m` and `n - m` is the product over the edges of the binomial
coefficients `(n e).choose (m e)`, cast to `ℝ`. Summing it over the currents bounded by `n`
gives `2` raised to the sum of `n e` over all edges; that statement needs no order
hypothesis, because the summation range already imposes one. The pair-weight sum then has a
fully closed form: the sum, over the pairs of currents summing to `n`, of the product of the
two weights is the weight of `n` times `2` raised to that same exponent, for arbitrary real
`β` and `J`.

Every statement here takes `[Fintype (inducedGraph G Λ).edgeSet]`. `[DecidableEq V]` is taken
by exactly those statements that mention `Current.subFinset` or `Current.pairFinset`, and
`[DecidableEq ↥Λ]` by exactly those that mention `Current.sources` or `Current.HasSources`.
The only hypothesis occurring anywhere in this module is `m ≤ n`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

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


end Ambient
end IsingModel
