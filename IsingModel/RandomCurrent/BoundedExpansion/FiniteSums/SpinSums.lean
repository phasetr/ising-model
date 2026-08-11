import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.BoundedWeights

/-!
# Spin sums of sign powers and of sign products over a finite index type

Sums of the integer sign `(· : Spin).toSign` cast to `ℝ`: one sign raised to an exponent and
summed over the two spins, and products of signs — over the whole index type with per-site
exponents, or over a `Finset` of that type without exponents — summed over all spin
configurations. No statement here mentions a graph, a finite volume or a current: the
statements indexed by a type range over an arbitrary `ι` carrying `[Fintype ι]` and
`[DecidableEq ι]`, and the one about a single spin carries no instance binder at all.

Summing the sign of one spin raised to `k` over the two spins gives `2` when `k` is even and
`0` when `k` is odd. Forming the product over the index type of `((σ v).toSign : ℝ)` raised
to `k v` and summing over all `σ : ι → Spin` gives `2 ^ Fintype.card ι` when every exponent
`k v` is even, and `0` as soon as one exponent is odd. Each is stated as a single
`if`-`then`-`else` equality, hence as a complete case split rather than as a one-sided bound.

A further statement replaces the exponent family by membership in a `Finset`. It is written
`IsingModel.spinProduct A σ`, the product of `((σ i).toSign : ℝ)` over `i ∈ A` for
`A : Finset ι`, and says that the sum of that product over all configurations is
`2 ^ Fintype.card ι` when `A` is empty and `0` otherwise.

No statement here carries a hypothesis.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Spin sum of `toSign` powers**: for any `k : ℕ`,
`∑ s : Spin, ((s.toSign : ℝ))^k = 2` if `k` is even, else `0`.
This is the elementary spin-sum identity that drives the
random-current expansion of `Z` and `⟨σ_A⟩^Λ`: summing over a
single spin gives `2` (when the cumulative power is even) or `0`
(when odd). -/
theorem Spin.sum_toSign_pow_real (k : ℕ) :
    (∑ s : Spin, ((s.toSign : ℝ))^k) = if Even k then 2 else 0 := by
  have hu : (Finset.univ : Finset Spin) = {Spin.up, Spin.down} := by decide
  rw [hu, Finset.sum_pair (by decide : Spin.up ≠ Spin.down)]
  have hup : ((Spin.up.toSign : ℤ) : ℝ) = 1 := by simp [Spin.toSign]
  have hdown : ((Spin.down.toSign : ℤ) : ℝ) = -1 := by simp [Spin.toSign]
  rw [hup, hdown, one_pow]
  by_cases hk : Even k
  · rw [if_pos hk, hk.neg_one_pow]; norm_num
  · rw [if_neg hk]
    have hodd : Odd k := Nat.not_even_iff_odd.mp hk
    rw [hodd.neg_one_pow]; norm_num

/-- **Multi-vertex spin sum**: for any `k : ι → ℕ` on a Fintype `ι`,
`∑ σ : ι → Spin, ∏ v : ι, ((σ v).toSign : ℝ)^(k v) = 2^(Fintype.card ι)`
when every `k v` is even, else `0`. The Fubini-style sum-product
swap reduces to per-vertex sums (`Spin.sum_toSign_pow_real`); each
factor is `2` (even exponent) or `0` (odd exponent), so the product
is `2^|ι|` when all even, else `0`. The central spin-sum step of
the random-current expansion (FV §3.10.6). -/
theorem Config.sum_prod_toSign_pow_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) :
    (∑ σ : ι → Spin, ∏ v : ι, ((σ v).toSign : ℝ)^(k v))
      = if ∀ v : ι, Even (k v) then 2^(Fintype.card ι) else 0 := by
  have hfubini : (∑ σ : ι → Spin, ∏ v : ι, ((σ v).toSign : ℝ)^(k v))
      = ∏ v : ι, ∑ s : Spin, ((s.toSign : ℝ))^(k v) :=
    (Fintype.prod_sum (κ := fun _ => Spin)
      (fun v s => ((s.toSign : ℝ))^(k v))).symm
  rw [hfubini]
  simp_rw [Spin.sum_toSign_pow_real]
  -- Goal: ∏ v, (if Even (k v) then 2 else 0) = if (∀ v, Even (k v)) then 2^|ι| else 0
  by_cases h : ∀ v : ι, Even (k v)
  · rw [if_pos h]
    rw [Finset.prod_congr rfl (fun v _ => if_pos (h v))]
    simp [Finset.prod_const, Finset.card_univ]
  · rw [if_neg h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    rw [if_neg hv]

/-- **Sum of `spinProduct A`**: for any Finset `A`,
`∑ σ : ι → Spin, spinProduct A σ = 2^(Fintype.card ι)` if `A = ∅`,
else `0`. The basic spin-sum identity feeding into the
random-current expansion of `Z = ∑_σ exp(-βH)` and
`⟨σ_A⟩^Λ = (∑_σ σ^A · exp(-βH)) / Z` (FV §3.10.6). Direct corollary
of `Config.sum_prod_toSign_pow_real` with the indicator exponent
`k v := if v ∈ A then 1 else 0`. -/
theorem Config.sum_spinProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) :
    (∑ σ : ι → Spin, IsingModel.spinProduct A σ)
      = if A = ∅ then 2^(Fintype.card ι) else 0 := by
  have hrw : ∀ σ : ι → Spin, IsingModel.spinProduct A σ
      = ∏ v : ι, ((σ v).toSign : ℝ)^(if v ∈ A then 1 else 0) := by
    intro σ
    unfold IsingModel.spinProduct
    rw [show (A : Finset ι) = (Finset.univ : Finset ι).filter (· ∈ A) by
      ext v; simp]
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    by_cases hv : v ∈ A
    · simp [hv]
    · simp [hv]
  simp_rw [hrw]
  rw [Config.sum_prod_toSign_pow_real]
  -- Goal: if (∀ v, Even (if v ∈ A then 1 else 0)) then 2^|ι| else 0 = if A = ∅ then 2^|ι| else 0
  congr 1
  refine propext ?_
  constructor
  · intro h
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    have := h v
    rw [if_pos hv] at this
    exact (Nat.not_even_one this).elim
  · intro hAempty v
    by_cases hv : v ∈ A
    · rw [hAempty] at hv
      exact absurd hv (Finset.notMem_empty v)
    · rw [if_neg hv]
      exact ⟨0, rfl⟩


end Ambient
end IsingModel
