import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.WeightZero

/-!
# Bounded random-current Taylor partial sums

Mechanical child split from `RandomCurrent/BoundedExpansion.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Real-valued edge spin product**: for a spin configuration
`σ : W → Spin` and an edge `e : Sym2 W`, the product of
`(σ v).toSign : ℝ` over `v ∈ e.toFinset`. For a non-loop edge
`e = s(u, w)` this is `(σ u).toSign * (σ w).toSign ∈ {-1, +1}`;
for a (nonexistent in a `SimpleGraph`) loop edge `e = s(v, v)` it
is just `(σ v).toSign ∈ {-1, +1}`. The per-edge factor in the
Taylor expansion `exp(β J σ_u σ_w) = ∑_k (β J σ_u σ_w)^k / k!`
feeding the random-current representation (FV §3.7). -/
noncomputable def Config.spinEdgeProduct {W : Type*} [DecidableEq W]
    (σ : W → Spin) (e : Sym2 W) : ℝ :=
  e.toFinset.prod (fun v => ((σ v).toSign : ℝ))

/-- **Squared edge spin product on a non-loop edge is `1`**: for a
non-diagonal `e : Sym2 W`, `(spinEdgeProduct σ e)^2 = 1`. Since
`(σ v).toSign ∈ {-1, +1}` for each endpoint, the product of two
such values squared is `1`. The ±1 control feeding absolute
convergence of the Taylor series. -/
theorem Config.spinEdgeProduct_mul_self_of_not_isDiag {W : Type*}
    [DecidableEq W] (σ : W → Spin) (e : Sym2 W) (he : ¬ e.IsDiag) :
    (Config.spinEdgeProduct σ e) ^ 2 = 1 := by
  unfold Config.spinEdgeProduct
  refine Sym2.inductionOn e (fun u w hne => ?_) he
  -- e = s(u, w), non-diag ↔ u ≠ w
  rw [Sym2.toFinset_mk_eq]
  rw [Sym2.mk_isDiag_iff] at hne
  rw [Finset.prod_insert (Finset.notMem_singleton.mpr hne),
    Finset.prod_singleton]
  -- ((σ u).toSign * (σ w).toSign)^2 = ((σ u).toSign)^2 * ((σ w).toSign)^2
  rw [mul_pow]
  -- ((σ v).toSign : ℝ)^2 = 1 for all v
  have h_one : ∀ v : W, ((σ v).toSign : ℝ)^2 = 1 := by
    intro v
    have := Spin.toSign_sq (σ v)
    exact_mod_cast this
  rw [h_one, h_one]; norm_num

/-- **Edge spin product is `±1` on a non-loop edge**: for a
non-diagonal `e : Sym2 W`,
`spinEdgeProduct σ e = 1 ∨ spinEdgeProduct σ e = -1`. Direct
corollary of `spinEdgeProduct_mul_self_of_not_isDiag` via
`sq_eq_one_iff`. -/
theorem Config.spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag
    {W : Type*} [DecidableEq W] (σ : W → Spin) (e : Sym2 W)
    (he : ¬ e.IsDiag) :
    Config.spinEdgeProduct σ e = 1 ∨ Config.spinEdgeProduct σ e = -1 :=
  sq_eq_one_iff.mp (Config.spinEdgeProduct_mul_self_of_not_isDiag σ e he)

/-- **Edge spin product has absolute value `1` on a non-loop
edge**: \(|spinEdgeProduct σ e| = 1\) for non-diagonal `e`.
Feeding absolute convergence of the Taylor series for
`exp(β J σ_u σ_w)`. -/
theorem Config.abs_spinEdgeProduct_of_not_isDiag {W : Type*}
    [DecidableEq W] (σ : W → Spin) (e : Sym2 W) (he : ¬ e.IsDiag) :
    |Config.spinEdgeProduct σ e| = 1 := by
  rcases Config.spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag σ e he with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

omit [DecidableEq V] in
/-- **Squared edge spin product on `inducedGraph` edge is `1`**:
edgeSet variant of `spinEdgeProduct_mul_self_of_not_isDiag`,
auto-deriving non-diagonality from `not_isDiag_of_mem_edgeSet`. -/
theorem Config.spinEdgeProduct_inducedGraph_mul_self
    (G : SimpleGraph V) (Λ : Finset V) [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (e : (inducedGraph G Λ).edgeSet) :
    (Config.spinEdgeProduct σ (e : Sym2 ↑Λ)) ^ 2 = 1 :=
  Config.spinEdgeProduct_mul_self_of_not_isDiag σ _
    ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e.2)

omit [DecidableEq V] in
/-- **Edge spin product on `inducedGraph` edge is `±1`**: edgeSet
variant of `spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag`. -/
theorem Config.spinEdgeProduct_inducedGraph_eq_one_or_neg_one
    (G : SimpleGraph V) (Λ : Finset V) [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (e : (inducedGraph G Λ).edgeSet) :
    Config.spinEdgeProduct σ (e : Sym2 ↑Λ) = 1 ∨
      Config.spinEdgeProduct σ (e : Sym2 ↑Λ) = -1 :=
  Config.spinEdgeProduct_eq_one_or_neg_one_of_not_isDiag σ _
    ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e.2)

omit [DecidableEq V] in
/-- **Edge spin product on `inducedGraph` edge has |·| = 1**:
edgeSet variant of `abs_spinEdgeProduct_of_not_isDiag`. -/
theorem Config.abs_spinEdgeProduct_inducedGraph
    (G : SimpleGraph V) (Λ : Finset V) [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (e : (inducedGraph G Λ).edgeSet) :
    |Config.spinEdgeProduct σ (e : Sym2 ↑Λ)| = 1 :=
  Config.abs_spinEdgeProduct_of_not_isDiag σ _
    ((inducedGraph G Λ).not_isDiag_of_mem_edgeSet e.2)

omit [DecidableEq V] in
/-- **Source-free spin sum in `spinEdgeProduct` form**:
`∑_σ ∏_e (spinEdgeProduct σ e)^(n e)
  = 2^|Λ|` if `n.IsSourceFree`, else `0`. Restatement of
`Config.sum_prod_spin_pow_degreeAt_isSourceFree` using the named
\`Config.spinEdgeProduct\`. -/
theorem Config.sum_prod_spinEdgeProduct_pow_isSourceFree
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) [Decidable (n.IsSourceFree G Λ)] :
    (∑ σ : ↑Λ → Spin, ∏ e : (inducedGraph G Λ).edgeSet,
        (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e))
      = if n.IsSourceFree G Λ
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 :=
  Config.sum_prod_spin_pow_degreeAt_isSourceFree G Λ n

omit [DecidableEq V] in
/-- **A-source spin sum in `spinEdgeProduct` form**:
`∑_σ σ_A · ∏_e (spinEdgeProduct σ e)^(n e)
  = 2^|Λ|` if `n.HasSources A`, else `0`. Restatement of
`Config.sum_spinA_prod_spin_pow_hasSources` using the named
\`Config.spinEdgeProduct\`. -/
theorem Config.sum_spinA_prod_spinEdgeProduct_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (∏ e : (inducedGraph G Λ).edgeSet,
          (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)))
      = if n.HasSources G Λ A
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 :=
  Config.sum_spinA_prod_spin_pow_hasSources G Λ n A

omit [DecidableEq V] in
/-- **Per-current σ-sum with weight**: at fixed current `n` and
source set `A`,
`∑_σ σ_A · weight β J n · ∏_e (spinEdgeProduct σ e)^(n e)
  = weight β J n · 2^|Λ|` if `n.HasSources A`, else `0`. The
per-current contribution to the random-current expression of
`⟨σ_A⟩^Λ` (FV §3.7). -/
theorem Config.sum_spinA_weight_prod_spinEdgeProduct_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (n.weight G Λ β J
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)))
      = if n.HasSources G Λ A
        then n.weight G Λ β J * (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  -- Pull the σ-independent weight out of the σ-sum.
  have heq : ∀ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (n.weight G Λ β J
        * ∏ e : (inducedGraph G Λ).edgeSet,
            (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e))
      = n.weight G Λ β J *
        ((∏ a ∈ A, ((σ a).toSign : ℝ))
         * ∏ e : (inducedGraph G Λ).edgeSet,
            (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)) := by
    intro σ; ring
  rw [Finset.sum_congr rfl (fun σ _ => heq σ), ← Finset.mul_sum,
    Config.sum_spinA_prod_spinEdgeProduct_pow_hasSources]
  by_cases hA : n.HasSources G Λ A
  · rw [if_pos hA, if_pos hA]
  · rw [if_neg hA, if_neg hA, mul_zero]

omit [DecidableEq V] in
/-- **Per-current σ-sum in Taylor-coefficient form**: at fixed
current `n` and source set `A`,
`∑_σ σ_A · ∏_e (β J · spinEdgeProduct σ e)^(n e) / (n e)!
  = weight β J n · 2^|Λ|` if `n.HasSources A`, else `0`. The
per-current contribution to the random-current expansion of
`Z · ⟨σ_A⟩` in the standard Taylor-coefficient form
(FV §3.7, eq. (3.45)). -/
theorem Config.sum_spinA_prod_taylor_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)
            / ((n e).factorial : ℝ))
      = if n.HasSources G Λ A
        then n.weight G Λ β J * (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  have heq : ∀ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)
            / ((n e).factorial : ℝ)
      = (∏ a ∈ A, ((σ a).toSign : ℝ))
        * (n.weight G Λ β J
          * ∏ e : (inducedGraph G Λ).edgeSet,
              (Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(n e)) := by
    intro σ
    rw [← Current.weight_mul_prod_pow G Λ β J n
      (fun e => Config.spinEdgeProduct σ (e : Sym2 ↑Λ))]
  rw [Finset.sum_congr rfl (fun σ _ => heq σ)]
  exact Config.sum_spinA_weight_prod_spinEdgeProduct_pow_hasSources
    G Λ β J n A

omit [DecidableEq V] in
/-- **Edge product of Taylor partial sums = current-bounded sum**:
the Fubini swap
`∏_e ∑_{k ≤ N} (β J · spinEdgeProduct σ e)^k / k!
  = ∑_{n : CurrentBounded N} ∏_e (β J · spinEdgeProduct σ e)^(n e) / (n e)!`.
The finite analogue (using `Fintype.prod_sum`) of the infinite
Taylor expansion that links the partition function to the
random-current sum (FV §3.7). -/
theorem Config.prod_sum_taylor_eq_sum_currentBounded
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (N : ℕ) (σ : ↑Λ → Spin) :
    (∏ e : (inducedGraph G Λ).edgeSet,
       ∑ k : Fin (N+1),
         (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
           / (((k : ℕ)).factorial : ℝ))
     = ∑ n : CurrentBounded G Λ N,
         ∏ e : (inducedGraph G Λ).edgeSet,
           (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^((n e : ℕ))
             / (((n e : ℕ)).factorial : ℝ) :=
  Fintype.prod_sum (κ := fun _ : (inducedGraph G Λ).edgeSet => Fin (N+1))
    (fun e k =>
      (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
        / (((k : ℕ)).factorial : ℝ))

omit [DecidableEq V] in
/-- **Bounded random-current expansion of `∑_σ σ_A · ∏_e Taylor
partial sum`**: the finite-`N` analogue of the random-current
expansion of `Z · ⟨σ_A⟩` (FV §3.7, eq. (3.45)),
\(∑_σ σ_A · ∏_e ∑_{k ≤ N} (β J σ_e)^k / k!
  = ∑_{n : CurrentBounded N} [n.toCurrent.HasSources A]
     · weight β J n.toCurrent · 2^|Λ|\).
Combines `prod_sum_taylor_eq_sum_currentBounded` with
`sum_spinA_prod_taylor_pow_hasSources`. -/
theorem Config.sum_spinA_prod_taylor_partialSum_eq_sum_currentBounded
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (N : ℕ) (A : Finset ↑Λ)
    [∀ n : CurrentBounded G Λ N,
      Decidable ((n.toCurrent G Λ).HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N+1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
              / (((k : ℕ)).factorial : ℝ))
      = ∑ n : CurrentBounded G Λ N,
          if (n.toCurrent G Λ).HasSources G Λ A
          then (n.toCurrent G Λ).weight G Λ β J * (2 : ℝ)^(Fintype.card ↑Λ)
          else 0 := by
  -- Step 1: replace inner edge product with sum over CurrentBounded.
  simp_rw [Config.prod_sum_taylor_eq_sum_currentBounded G Λ β J N _]
  -- ∑_σ σ_A · ∑_n (∏_e ...)
  -- Step 2: distribute σ_A through the inner sum, then swap σ-sum and n-sum.
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Step 3: each inner ∑_σ σ_A · (∏_e ...) is exactly per-current Taylor sum.
  exact Finset.sum_congr rfl (fun n _ =>
    Config.sum_spinA_prod_taylor_pow_hasSources G Λ β J
      (n.toCurrent G Λ) A)

omit [DecidableEq V] in
/-- **Bounded random-current expansion via `CurrentBounded.weightSum`**:
clean reformulation of `sum_spinA_prod_taylor_partialSum_eq_sum_currentBounded`
collecting the indicator+weight sum into the existing
`CurrentBounded.weightSum` definition,
\(∑_σ σ_A · ∏_e ∑_{k ≤ N} (β J σ_e)^k / k!
  = 2^|Λ| · CurrentBounded.weightSum N A β J\). The finite-`N`
analogue ready for the `N → ∞` limit step (FV §3.7, eq. (3.45)). -/
theorem Config.sum_spinA_prod_taylor_partialSum_eq_pow_card_mul_currentBounded_weightSum
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (β J : ℝ) (N : ℕ) (A : Finset ↑Λ) :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * ∏ e : (inducedGraph G Λ).edgeSet,
          ∑ k : Fin (N+1),
            (β * J * Config.spinEdgeProduct σ (e : Sym2 ↑Λ))^(k : ℕ)
              / (((k : ℕ)).factorial : ℝ))
      = (2 : ℝ)^(Fintype.card ↑Λ)
        * CurrentBounded.weightSum G Λ N A β J := by
  classical
  rw [Config.sum_spinA_prod_taylor_partialSum_eq_sum_currentBounded G Λ β J N A]
  unfold CurrentBounded.weightSum Current.HasSources
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs <;> ring

end Ambient
end IsingModel
