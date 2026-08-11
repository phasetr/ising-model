import IsingModel.RandomCurrent.BoundedExpansion.JointWeights

/-!
# Bounded random-current convergence

Mechanical child split from `RandomCurrent/BoundedExpansion.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Real exponential as a real Taylor `tsum`**:
\(Real.exp x = ∑' n, x^n / n!\). Local convenience wrapper
composing `Real.exp_eq_exp_ℝ` (Real.exp matches `NormedSpace.exp`)
and `NormedSpace.exp_eq_tsum_div` (the `exp = ∑' n, x^n / n!`
formula in `CharZero` algebras). Bridges `Real.exp` and the
bounded Taylor partial-sum form used in
`Config.sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum`
(#841) for the random-current expansion (FV §3.10.6). -/
theorem Real.exp_eq_tsum_div_factorial (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ]
  exact congrFun NormedSpace.exp_eq_tsum_div x

/-- **Real Taylor partial sum converges to `Real.exp`**:
\(∑_{k ≤ N} x^k / k! → Real.exp x\) as `N → ∞`. The first analytic
limit step toward `N → ∞` in the bounded random-current expansion
(FV §3.10.6). Combines `Real.exp_eq_tsum_div_factorial` with
`Real.summable_pow_div_factorial` and `Summable.tendsto_sum_tsum_nat`,
shifting the index from `range N` to `range (N+1)` via
`tendsto_add_atTop_nat 1`. -/
theorem Real.tendsto_partial_sum_atTop_exp (x : ℝ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), x ^ k / (k.factorial : ℝ))
      Filter.atTop (nhds (Real.exp x)) := by
  rw [Real.exp_eq_tsum_div_factorial]
  have h_summable : Summable (fun k : ℕ => x ^ k / (k.factorial : ℝ)) :=
    Real.summable_pow_div_factorial x
  exact (Summable.tendsto_sum_tsum_nat h_summable).comp
    (Filter.tendsto_add_atTop_nat 1)

omit [DecidableEq V] in
/-- **Edge-product of Taylor partial sums converges to product of
exponentials**: as `N → ∞`,
\(∏_e ∑_{k ≤ N} (β J σ_e)^k / k! → ∏_e Real.exp (β J σ_e)\).
The finite product is continuous in each factor (`tendsto_finset_prod`),
and each per-edge factor converges by
`Real.tendsto_partial_sum_atTop_exp` (#851). The `Fin (N+1)` sum
matches the `range (N+1)` sum via `Fin.sum_univ_eq_sum_range`.
Second analytic step toward the `N → ∞` limit of the bounded
random-current expansion (FV §3.10.6). -/
theorem Config.tendsto_prod_Fin_partial_sum_atTop_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (σ : ↑Λ → Spin) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N + 1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
              / (((k : ℕ).factorial : ℝ)))
      Filter.atTop
      (nhds
        (∏ e : (inducedGraph G Λ).edgeSet,
          Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)))) := by
  -- Convert Fin (N+1) sums to range (N+1) sums.
  have hconv : ∀ N : ℕ,
      (∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N + 1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
              / (((k : ℕ).factorial : ℝ)))
        = ∏ e : (inducedGraph G Λ).edgeSet,
            ∑ k ∈ Finset.range (N + 1),
              (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ k
                / ((k.factorial : ℝ)) := by
    intro N
    refine Finset.prod_congr rfl (fun e _ => ?_)
    exact Fin.sum_univ_eq_sum_range
      (fun k => (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ k
                  / ((k.factorial : ℝ))) (N + 1)
  simp_rw [hconv]
  refine tendsto_finset_prod _ (fun e _ => ?_)
  exact Real.tendsto_partial_sum_atTop_exp _

omit [DecidableEq V] in
/-- **Sum-σ-A × edge-product partial sum → sum-σ-A × edge-product exp**:
as `N → ∞`,
\(∑_σ σ_A · ∏_e ∑_{k ≤ N} (β J σ_e)^k / k!
  → ∑_σ σ_A · ∏_e Real.exp (β J σ_e)\).
The third analytic step in the `N → ∞` limit, combining
`tendsto_prod_Fin_partial_sum_atTop_prod_exp` (#852, per-σ
edge-product convergence) with `Tendsto.const_mul` (σ_A is
`N`-independent) and `tendsto_finset_sum` (finite σ-sum is
continuous). Bridges the bounded random-current expansion with
the actual Boltzmann weight `Z · ⟨σ_A⟩` (FV §3.10.6). -/
theorem Config.tendsto_sum_spinA_prod_partial_sum_atTop_sum_spinA_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (A : Finset ↑Λ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ σ : ↑Λ → Spin,
        (∏ a ∈ A, ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            ∑ k : Fin (N + 1),
              (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
                / (((k : ℕ).factorial : ℝ)))
      Filter.atTop
      (nhds
        (∑ σ : ↑Λ → Spin,
          (∏ a ∈ A, ((σ a).toSign : ℝ))
          * ∏ e : (inducedGraph G Λ).edgeSet,
              Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)))) := by
  refine tendsto_finset_sum _ (fun σ _ => ?_)
  exact (Config.tendsto_prod_Fin_partial_sum_atTop_prod_exp G Λ β J σ).const_mul _

omit [DecidableEq V] in
/-- **Bounded `CurrentBounded.weightSum` × `2^|Λ|` converges to
the Boltzmann sum**: as `N → ∞`,
\(2^|Λ| · CurrentBounded.weightSum N A β J
  → ∑_σ σ_A · ∏_e Real.exp (β J σ_e)\).
Combines `sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum`
(#841) with
`tendsto_sum_spinA_prod_partial_sum_atTop_sum_spinA_prod_exp`
(#853). Closes the LHS-side `N → ∞` limit, connecting the
bounded random-current sum to the actual Ising Boltzmann weight
`Z · ⟨σ_A⟩` (FV §3.10.6). -/
theorem Config.tendsto_pow_card_mul_currentBounded_weightSum_atTop_sum_spinA_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (A : Finset ↑Λ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (2 : ℝ) ^ (Fintype.card ↑Λ) * CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop
      (nhds
        (∑ σ : ↑Λ → Spin,
          (∏ a ∈ A, ((σ a).toSign : ℝ))
          * ∏ e : (inducedGraph G Λ).edgeSet,
              Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)))) := by
  have hbridge :
      (fun N : ℕ =>
        (2 : ℝ) ^ (Fintype.card ↑Λ) * CurrentBounded.weightSum G Λ N A β J)
      = fun N : ℕ => ∑ σ : ↑Λ → Spin,
        (∏ a ∈ A, ((σ a).toSign : ℝ))
        * ∏ e : (inducedGraph G Λ).edgeSet,
            ∑ k : Fin (N + 1),
              (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ (k : ℕ)
                / (((k : ℕ).factorial : ℝ)) := by
    funext N
    exact (Config.sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum
      G Λ β J N A).symm
  rw [hbridge]
  exact Config.tendsto_sum_spinA_prod_partial_sum_atTop_sum_spinA_prod_exp G Λ β J A

omit [DecidableEq V] in
/-- **`CurrentBounded.toCurrent` is injective**: two bounded
currents with the same `Current` representative agree as
functions, hence as bounded currents (`Fin (N+1)` is determined
by `.val`). -/
theorem CurrentBounded.toCurrent_injective (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet] {N : ℕ} :
    Function.Injective
      (CurrentBounded.toCurrent G Λ : CurrentBounded G Λ N → Current G Λ) := by
  intro n₁ n₂ h
  funext e
  apply Fin.ext
  exact congrFun h e

/-- **`Current.boundedFinset N`**: the `Finset` of currents
\(n : Current G Λ\) with \(n e ≤ N\) for every edge \(e\),
realised as the image of `CurrentBounded G Λ N` under `toCurrent`.
The natural `Finset` filtration of `Current G Λ` whose limit
covers all currents (every current has finite max value since the
edge set is finite). Foundation for the RHS-side `N → ∞` limit
of the random-current expansion (FV §3.10.6). -/
noncomputable def Current.boundedFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] (N : ℕ) :
    Finset (Current G Λ) := by
  classical
  exact (Finset.univ : Finset (CurrentBounded G Λ N)).image
    (CurrentBounded.toCurrent G Λ)

/-- **Membership in `boundedFinset N`**: \(n ∈ boundedFinset N\)
iff every edge value satisfies \(n e ≤ N\). -/
theorem Current.mem_boundedFinset_iff (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (N : ℕ) (n : Current G Λ) :
    n ∈ Current.boundedFinset G Λ N ↔ ∀ e : (inducedGraph G Λ).edgeSet, n e ≤ N := by
  unfold Current.boundedFinset
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨nB, rfl⟩ e
    change ((nB e).val : ℕ) ≤ N
    exact Nat.lt_succ_iff.mp (nB e).is_lt
  · intro hbound
    refine ⟨fun e => ⟨n e, ?_⟩, ?_⟩
    · exact Nat.lt_succ_iff.mpr (hbound e)
    · funext e
      rfl

/-- **`boundedFinset` is monotone in `N`**:
\(N_1 ≤ N_2 → boundedFinset\,N_1 ⊆ boundedFinset\,N_2\).
A larger bound includes more currents. Direct via
`mem_boundedFinset_iff`. -/
theorem Current.boundedFinset_mono (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    Current.boundedFinset G Λ N₁ ⊆ Current.boundedFinset G Λ N₂ := by
  intro n hn
  rw [Current.mem_boundedFinset_iff] at hn ⊢
  exact fun e => le_trans (hn e) h

/-- **Every current eventually lies in some `boundedFinset N`**:
for every `n : Current G Λ`, there exists `N : ℕ` such that
\(n ∈ boundedFinset N\). Concretely take
\(N = max_{e} n e\) (the supremum over the finite edge set).
The cofinality property of the filtration. -/
theorem Current.exists_mem_boundedFinset (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (n : Current G Λ) :
    ∃ N : ℕ, n ∈ Current.boundedFinset G Λ N := by
  classical
  refine ⟨Finset.univ.sup n, ?_⟩
  rw [Current.mem_boundedFinset_iff]
  intro e
  exact Finset.le_sup (Finset.mem_univ e)

/-- **`boundedFinset` is cofinal in `Filter.atTop` on
`Finset (Current G Λ)`**: for every finset `s` of currents,
eventually `s ⊆ boundedFinset N` (take `N` = max bound across all
currents in `s` and all edges). Bridges the ℕ-indexed `atTop`
filter with the unconditional summation filter on `Finset`. -/
theorem Current.tendsto_boundedFinset_atTop_finsetAtTop
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] :
    Filter.Tendsto (Current.boundedFinset G Λ)
      Filter.atTop (Filter.atTop : Filter (Finset (Current G Λ))) := by
  classical
  rw [Filter.tendsto_atTop_atTop]
  intro s
  refine ⟨s.sup (fun n => Finset.univ.sup n), ?_⟩
  intro M hM n hn
  rw [Current.mem_boundedFinset_iff]
  intro e
  calc n e ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ e)
    _ ≤ s.sup (fun n => Finset.univ.sup n) := Finset.le_sup hn
    _ ≤ M := hM

/-- **Summable partial sums over `boundedFinset` converge to
`tsum`**: under `Summable f`, the partial sums
\(∑ n ∈ boundedFinset N, f n → ∑' n, f n\) as `N → ∞`. Composing
the cofinal sequence (`tendsto_boundedFinset_atTop_finsetAtTop`)
with `Summable.hasSum`. -/
theorem Summable.tendsto_sum_boundedFinset
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {f : Current G Λ → α} (hf : Summable f) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Current.boundedFinset G Λ N, f n)
      Filter.atTop (nhds (∑' n, f n)) :=
  hf.hasSum.comp (Current.tendsto_boundedFinset_atTop_finsetAtTop G Λ)

/-- **Bounded weight sum as sum over `boundedFinset`**: rewrite
\(CurrentBounded.weightSum N A β J\) as a sum over the image
finset \(boundedFinset N\) of currents. Uses `Finset.sum_bij`
with `toCurrent` as the bijection. Bridges the bounded sum (over
`CurrentBounded N` as Fintype) with the `Current G Λ`-indexed
Finset sum used in subsequent N → ∞ arguments. -/
theorem CurrentBounded.weightSum_eq_sum_boundedFinset (G : SimpleGraph V)
    (Λ : Finset V) [Fintype (inducedGraph G Λ).edgeSet]
    [DecidableEq ↑Λ] (N : ℕ) (A : Finset ↑Λ) (β J : ℝ) :
    CurrentBounded.weightSum G Λ N A β J
      = ∑ n ∈ Current.boundedFinset G Λ N,
          if n.sources G Λ = A then n.weight G Λ β J else 0 := by
  classical
  unfold CurrentBounded.weightSum
  refine Finset.sum_bij
    (fun (nB : CurrentBounded G Λ N) _ => CurrentBounded.toCurrent G Λ nB)
    ?_ ?_ ?_ ?_
  · -- maps into boundedFinset
    intro nB _
    rw [Current.mem_boundedFinset_iff]
    intro e
    exact Nat.lt_succ_iff.mp (nB e).is_lt
  · -- injective on Finset.univ
    intro nB₁ _ nB₂ _ hbij
    exact CurrentBounded.toCurrent_injective G Λ hbij
  · -- surjective onto boundedFinset
    intro n hn
    rw [Current.mem_boundedFinset_iff] at hn
    refine ⟨fun e => ⟨n e, Nat.lt_succ_iff.mpr (hn e)⟩, Finset.mem_univ _, ?_⟩
    funext e; rfl
  · -- summand match
    intro nB _
    rfl

set_option linter.unusedDecidableInType false in
/-- **RHS-side `N → ∞` limit capstone**: under summability of the
weight-with-source-condition function,
\(CurrentBounded.weightSum N A β J → Current.weightSum A β J\) as
`N → ∞`. Combines `weightSum_eq_sum_boundedFinset` (#858) with
`Summable.tendsto_sum_boundedFinset` (#857). Together with
the LHS-side limit (#854), gives
`Current.weightSum A β J = (1/2^|Λ|) · ∑_σ σ_A · ∏_e Real.exp (β J σ_e)`
under summability — the random-current expression of the Ising
correlation function (FV §3.10.6). -/
theorem CurrentBounded.tendsto_weightSum_atTop_currentWeightSum
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (A : Finset ↑Λ)
    (hf : Summable (fun n : Current G Λ =>
      if n.sources G Λ = A then n.weight G Λ β J else 0)) :
    Filter.Tendsto (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop (nhds (Current.weightSum G Λ A β J)) := by
  have h_eq : ∀ N, CurrentBounded.weightSum G Λ N A β J
              = ∑ n ∈ Current.boundedFinset G Λ N,
                  if n.sources G Λ = A then n.weight G Λ β J else 0 :=
    fun N => CurrentBounded.weightSum_eq_sum_boundedFinset G Λ N A β J
  simp_rw [h_eq]
  unfold Current.weightSum
  exact Summable.tendsto_sum_boundedFinset G Λ hf

set_option linter.unusedDecidableInType false in
/-- **`CurrentBounded.weightSum` is monotone in `N`** under
non-negative coupling: \(N_1 ≤ N_2 →
CurrentBounded.weightSum N_1 A β J ≤ CurrentBounded.weightSum N_2 A β J\).
A larger bound includes more (non-negative) summands. Combines
`weightSum_eq_sum_boundedFinset` with `boundedFinset_mono` and
`Finset.sum_le_sum_of_subset_of_nonneg`. -/
theorem CurrentBounded.weightSum_mono (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    CurrentBounded.weightSum G Λ N₁ A β J
      ≤ CurrentBounded.weightSum G Λ N₂ A β J := by
  rw [CurrentBounded.weightSum_eq_sum_boundedFinset,
    CurrentBounded.weightSum_eq_sum_boundedFinset]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Current.boundedFinset_mono G Λ h) (fun n _ _ => ?_)
  split_ifs
  · exact Current.weight_nonneg G Λ hβJ n
  · exact le_refl 0

set_option linter.unusedDecidableInType false in
/-- **Monotone convergence of `CurrentBounded.weightSum`** under
non-negative coupling and bounded-above hypothesis:
\(Tendsto (fun N => CurrentBounded.weightSum N A β J) atTop
  (nhds (⨆ N, CurrentBounded.weightSum N A β J))\).
Combines `CurrentBounded.weightSum_mono` (#860) with
`tendsto_atTop_ciSup`. Avoids the explicit `Summable` hypothesis
of `tendsto_weightSum_atTop_currentWeightSum` (#859). -/
theorem CurrentBounded.tendsto_weightSum_atTop_iSup
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J)
    (hbdd : BddAbove (Set.range (fun N =>
      CurrentBounded.weightSum G Λ N A β J))) :
    Filter.Tendsto (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop
      (nhds (⨆ N : ℕ, CurrentBounded.weightSum G Λ N A β J)) :=
  tendsto_atTop_ciSup
    (fun _ _ h => CurrentBounded.weightSum_mono G Λ A hβJ h) hbdd

/-- **Real Taylor partial sum is bounded by `Real.exp`** for
non-negative arguments: for `x ≥ 0`,
\(∑_{k ≤ N} x^k / k! ≤ Real.exp x\). Direct via
`Real.exp_eq_tsum_div_factorial` (#850),
`Real.summable_pow_div_factorial` (mathlib), and
`Summable.sum_le_tsum`. The per-edge upper bound foundation for
the BddAbove of `CurrentBounded.weightSum` under non-negative
coupling. -/
theorem Real.partial_sum_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), x ^ k / (k.factorial : ℝ) ≤ Real.exp x := by
  rw [Real.exp_eq_tsum_div_factorial]
  refine Summable.sum_le_tsum _ (fun k _ => ?_)
    (Real.summable_pow_div_factorial x)
  exact div_nonneg (pow_nonneg hx k) (Nat.cast_nonneg _)

set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **`CurrentBounded.weightSum` is uniformly bounded by
`Real.exp (β J)^|edgeSet|`** under non-negative coupling.
\(CurrentBounded.weightSum N A β J ≤ Real.exp (β * J) ^ |edgeSet|\)
for every `N`. The N-independent bound, providing a concrete
`BddAbove` for `tendsto_weightSum_atTop_iSup` (#861). Combines:
(1) drop indicator (sum monotone), (2) `Fintype.prod_sum` (bounded
sum equals product of partial sums), (3) per-edge
`Real.partial_sum_le_exp_of_nonneg` (#862), (4) `Finset.prod_le_prod`
monotonicity, (5) `Finset.prod_const` for `∏ exp = exp^card`. -/
theorem CurrentBounded.weightSum_le_exp_pow_card
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (N : ℕ) (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    CurrentBounded.weightSum G Λ N A β J
      ≤ Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet := by
  -- Step 1: Drop the indicator (each summand bounded above by weight when present).
  have h1 : CurrentBounded.weightSum G Λ N A β J
            ≤ ∑ n : CurrentBounded G Λ N, (n.toCurrent G Λ).weight G Λ β J := by
    unfold CurrentBounded.weightSum
    refine Finset.sum_le_sum (fun n _ => ?_)
    split_ifs
    · exact le_refl _
    · exact Current.weight_nonneg G Λ hβJ _
  -- Step 2: Fintype.prod_sum gives ∑_n ∏_e (β J)^(n e) / (n e)!
  --                              = ∏_e ∑_k (β J)^k / k! (via toCurrent unfolding).
  have h2 : ∑ n : CurrentBounded G Λ N, (n.toCurrent G Λ).weight G Λ β J
          = ∏ e : (inducedGraph G Λ).edgeSet,
              ∑ k : Fin (N + 1), (β * J)^(k : ℕ) / (((k : ℕ).factorial : ℝ)) := by
    symm
    exact Fintype.prod_sum
      (κ := fun _ : (inducedGraph G Λ).edgeSet => Fin (N + 1))
      (fun _ k => (β * J)^(k : ℕ) / (((k : ℕ).factorial : ℝ)))
  -- Step 3: per-edge partial sum bounded by exp.
  have h3 : ∏ e : (inducedGraph G Λ).edgeSet,
              ∑ k : Fin (N + 1), (β * J)^(k : ℕ) / (((k : ℕ).factorial : ℝ))
          ≤ ∏ _e : (inducedGraph G Λ).edgeSet, Real.exp (β * J) := by
    refine Finset.prod_le_prod (fun e _ => ?_) (fun e _ => ?_)
    · refine Finset.sum_nonneg (fun k _ => ?_)
      exact div_nonneg (pow_nonneg hβJ _) (Nat.cast_nonneg _)
    · have hpartial := Real.partial_sum_le_exp_of_nonneg hβJ N
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (β * J)^k / ((k.factorial : ℝ))) (N + 1)] at hpartial
      exact hpartial
  -- Step 4: ∏_e exp(β J) = exp(β J)^|edgeSet|
  have h4 : ∏ _e : (inducedGraph G Λ).edgeSet, Real.exp (β * J)
          = Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet := by
    rw [Finset.prod_const, Finset.card_univ]
  exact h1.trans (h2.le.trans (h3.trans h4.le))

set_option linter.unusedDecidableInType false in
/-- **Unconditional monotone-convergence of `CurrentBounded.weightSum`**:
under non-negative coupling `0 ≤ β J` (without external BddAbove
hypothesis), `Tendsto (fun N => CurrentBounded.weightSum N A β J)
atTop (nhds (⨆ N, CurrentBounded.weightSum N A β J))`.
Combines `tendsto_weightSum_atTop_iSup` (#861) with
`weightSum_le_exp_pow_card` (#863), the latter discharging the
`BddAbove` hypothesis with the explicit bound
`exp(β J)^|edgeSet|`. -/
theorem CurrentBounded.tendsto_weightSum_atTop_iSup_of_nonneg
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    Filter.Tendsto (fun N : ℕ => CurrentBounded.weightSum G Λ N A β J)
      Filter.atTop
      (nhds (⨆ N : ℕ, CurrentBounded.weightSum G Λ N A β J)) := by
  refine CurrentBounded.tendsto_weightSum_atTop_iSup G Λ A hβJ ?_
  refine ⟨Real.exp (β * J) ^ Fintype.card (inducedGraph G Λ).edgeSet, ?_⟩
  rintro x ⟨N, rfl⟩
  exact CurrentBounded.weightSum_le_exp_pow_card G Λ N A hβJ

set_option linter.unusedDecidableInType false in
/-- **Random-current expression of the Ising correlation function**
(unconditional, under non-negative coupling): for `0 ≤ β J`,
\(2^|Λ| · (⨆_N CurrentBounded.weightSum N A β J)
  = ∑_σ σ_A · ∏_e Real.exp (β J σ_e)\).
The bidirectional limit capstone: by `tendsto_nhds_unique`,
combines the LHS-side limit (#854) with the unconditional RHS-side
monotone-convergence limit (#864) — no external `Summable` or
`BddAbove` hypothesis needed (the bound `exp(β J)^|edgeSet|`
established in #863 discharges it). The random-current expression
of the Ising correlation function `Z · ⟨σ_A⟩` (FV §3.10.6, p. 144)
in `iSup` form. -/
theorem CurrentBounded.pow_card_mul_iSup_weightSum_eq_sum_spinA_prod_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) {β J : ℝ} (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ↑Λ
        * (⨆ N : ℕ, CurrentBounded.weightSum G Λ N A β J)
      = ∑ σ : ↑Λ → Spin,
          (∏ a ∈ A, ((σ a).toSign : ℝ))
          * ∏ e : (inducedGraph G Λ).edgeSet,
              Real.exp (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) := by
  refine tendsto_nhds_unique
    ((CurrentBounded.tendsto_weightSum_atTop_iSup_of_nonneg
      G Λ A hβJ).const_mul _)
    (Config.tendsto_pow_card_mul_currentBounded_weightSum_atTop_sum_spinA_prod_exp
      G Λ β J A)

end Ambient
end IsingModel
