import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.ASourceSpinSums

/-!
# Prescribed-source spin sum, degenerate weight sums, and a per-edge weight factorization

Statements about a current `n` on `inducedGraph G Λ`, the subgraph of `G` that `Λ` induces,
for an arbitrary `G : SimpleGraph V` and an arbitrary finite volume `Λ : Finset V`.

For a vertex `Finset A`, the sum over all spin configurations `σ : ↥Λ → Spin` of the product
of the spin signs over `A` times the product, over the edges, of the product of the spin
signs over the endpoint `Finset` of the edge raised to the multiplicity `n e`, is
`2 ^ Fintype.card ↥Λ` when `n` has source set exactly `A`, and `0` otherwise; that statement
takes a `[Decidable (n.HasSources G Λ A)]` instance.

`Current.weightSum G Λ A β J` is recorded on the parameter slices where one of its two real
parameters is `0`: it is `1` when `A` is empty and `0` otherwise, once with `β` set to `0`
and `J` left arbitrary, once with `J` set to `0` and `β` left arbitrary. Neither of those
statements constrains the remaining parameter.

For an arbitrary real-valued function `x` on the edges, `Current.weight G Λ β J n` times the
product over the edges of `x e` raised to `n e` equals the product over the edges of
`(β * J * x e)` raised to `n e`, each factor divided by the factorial of `n e`. This holds
for arbitrary real `β` and `J`.

Every statement here takes `[Fintype (inducedGraph G Λ).edgeSet]` and none carries a
hypothesis; the factorization statement is the only one that does not take
`[DecidableEq ↥Λ]`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **A-source spin sum at fixed current — `HasSources` form**:
\(∑_σ σ_A · ∏_e (e.toFinset.prod σ.toSign)^n e
  = 2^|Λ|\) if `n.HasSources A`, else `0`. Final form combining
`Config.sum_spinA_prod_spin_pow_eq_pow_card_iff` and
`Current.even_indicator_add_degreeAt_iff_hasSources`; the
A-source per-current spin-sum identity in its final form,
ready to feed into the random-current expression of
`⟨σ_A⟩^Λ` (FV §3.7). -/
theorem Config.sum_spinA_prod_spin_pow_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ)
    [Decidable (n.HasSources G Λ A)] :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod
            (fun v => ((σ v).toSign : ℝ))) ^ n e))
      = if n.HasSources G Λ A
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  rw [Config.sum_spinA_prod_spin_pow_eq_pow_card_iff]
  exact if_congr
    (Current.even_indicator_add_degreeAt_iff_hasSources G Λ n A) rfl rfl

omit [DecidableEq V] in
/-- **`weightSum` at zero β collapses to indicator on `A = ∅`**:
\(Current.weightSum\,A\,0\,J = 1\) if `A = ∅`, else `0`. At zero
coupling, only the zero current contributes (its source set is
`∅`); uses `Current.weight_beta_zero` and `tsum_eq_single`. -/
theorem Current.weightSum_beta_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) (J : ℝ) :
    Current.weightSum G Λ A 0 J = if A = ∅ then 1 else 0 := by
  classical
  unfold Current.weightSum
  -- Only n = 0 contributes since weight 0 J n = 0 for n ≠ 0.
  have h_single : ∀ n : Current G Λ, n ≠ 0 →
      (if n.sources G Λ = A then n.weight G Λ 0 J else 0) = 0 := by
    intro n hn
    by_cases hsr : n.sources G Λ = A
    · rw [if_pos hsr, Current.weight_beta_zero, if_neg hn]
    · rw [if_neg hsr]
  rw [tsum_eq_single (0 : Current G Λ) h_single,
    Current.zero_sources, Current.zero_weight]
  exact if_congr eq_comm rfl rfl

omit [DecidableEq V] in
/-- **`weightSum` at zero J collapses to indicator on `A = ∅`**:
\(Current.weightSum\,A\,β\,0 = 1\) if `A = ∅`, else `0`.
Symmetric counterpart of `weightSum_beta_zero`. -/
theorem Current.weightSum_J_zero (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (A : Finset ↑Λ) (β : ℝ) :
    Current.weightSum G Λ A β 0 = if A = ∅ then 1 else 0 := by
  classical
  unfold Current.weightSum
  have h_single : ∀ n : Current G Λ, n ≠ 0 →
      (if n.sources G Λ = A then n.weight G Λ β 0 else 0) = 0 := by
    intro n hn
    by_cases hsr : n.sources G Λ = A
    · rw [if_pos hsr, Current.weight_J_zero, if_neg hn]
    · rw [if_neg hsr]
  rw [tsum_eq_single (0 : Current G Λ) h_single,
    Current.zero_sources, Current.zero_weight]
  exact if_congr eq_comm rfl rfl

omit [DecidableEq V] in
/-- **Weight × edge-product of powers**: for any edge-indexed
`x : edgeSet → ℝ`,
`weight β J n · (∏_e (x e)^(n e)) = ∏_e (β * J * x e)^(n e) / (n e)!`.
The per-current summand identity bridging \`weight\` with the
per-edge Taylor terms `(β J σ_u σ_w)^k / k!`, preparing the
random-current expansion of the partition function
(FV §3.7, eq. (3.45)). -/
theorem Current.weight_mul_prod_pow (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (β J : ℝ) (n : Current G Λ)
    (x : (inducedGraph G Λ).edgeSet → ℝ) :
    n.weight G Λ β J * (∏ e : (inducedGraph G Λ).edgeSet, (x e)^(n e))
      = ∏ e : (inducedGraph G Λ).edgeSet,
          (β * J * x e)^(n e) / ((n e).factorial : ℝ) := by
  unfold Current.weight
  rw [← Finset.prod_mul_distrib]
  congr 1
  ext e
  rw [mul_pow]
  ring


end Ambient
end IsingModel
