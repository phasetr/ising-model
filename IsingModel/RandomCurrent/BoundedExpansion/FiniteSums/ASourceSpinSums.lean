import IsingModel.RandomCurrent.BoundedExpansion.FiniteSums.SourceFreeSpinSums

/-!
# The spin sum against a vertex-subset sign product, and its prescribed-source form

The spin sum at a fixed current `n`, multiplied by the product of the spin signs over a
vertex `Finset A`, and the condition characterizing when that sum is nonzero.

For a spin configuration `σ : ↥Λ → Spin`, the product of `((σ a).toSign : ℝ)` over `a ∈ A` is
rewritten as a product over all of `↥Λ` whose factor at `v` is `((σ v).toSign : ℝ)` raised to
the indicator exponent `if v ∈ A then 1 else 0`. That statement is the only one here that
mentions no graph: it is stated for a `Λ : Finset V` under explicitly bound `[Fintype ↥Λ]`
and `[DecidableEq ↥Λ]` instances.

Multiplying that product by the product, over the edges of `inducedGraph G Λ`, the subgraph
of `G` that `Λ` induces, of the product of the spin signs over the endpoint `Finset` of the
edge raised to the multiplicity `n e`, gives a single product over vertices whose exponent at
`v` is the indicator of `A` at `v` plus the total incident degree `Current.degreeAt G Λ n v`.

Summing the left-hand side of that identity — the sign product over `A` times the edge
product — over all spin configurations gives `2 ^ Fintype.card ↥Λ` when that exponent is even
at every vertex, and `0` otherwise, as a single `if`-`then`-`else` equality. Evenness at
every vertex is in turn equivalent to `n` having source set exactly `A`. Since
`2 ^ Fintype.card ↥Λ` is positive in `ℝ` for every value of the cardinality, and since
neither statement carries a hypothesis, the sum is nonzero precisely at those currents whose
source set is `A`, for every `G`, every `Λ` and every `A`.

Every statement here takes `[DecidableEq ↥Λ]` and none carries a hypothesis; the statements
that mention the graph take `[Fintype (inducedGraph G Λ).edgeSet]`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Subset spin-product as per-vertex indicator power**: for any
spin configuration `σ : ↑Λ → Spin` and subset `A ⊆ ↑Λ`,
`∏_{a ∈ A} ((σ a).toSign : ℝ) = ∏_v ((σ v).toSign : ℝ)^(1_A v)`.
The indicator-power form needed to combine `σ_A` with the
per-vertex spin powers in the random-current expansion of
`⟨σ_A⟩^Λ` (FV §3.10.6). -/
theorem Config.prod_subset_eq_prod_pow_indicator
    (Λ : Finset V) [Fintype ↑Λ] [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (A : Finset ↑Λ) :
    (∏ a ∈ A, ((σ a).toSign : ℝ))
      = ∏ v : ↑Λ, ((σ v).toSign : ℝ)^(if v ∈ A then 1 else 0) := by
  classical
  -- ∏_v σ.toSign(v)^(if v ∈ A then 1 else 0)
  --   = ∏_v if v ∈ A then σ.toSign(v) else 1
  --   = (univ.filter (· ∈ A)).prod σ.toSign
  --   = A.prod σ.toSign
  have hpow : ∀ v : ↑Λ,
      ((σ v).toSign : ℝ)^(if v ∈ A then (1 : ℕ) else 0)
        = if v ∈ A then ((σ v).toSign : ℝ) else 1 := by
    intro v
    by_cases hv : v ∈ A <;> simp [hv]
  simp_rw [hpow]
  rw [← Finset.prod_filter]
  congr 1
  ext v
  simp

omit [DecidableEq V] in
/-- **`σ_A` × spin-edge product as single per-vertex power**:
`σ_A · ∏_e (e.toFinset.prod σ.toSign)^n e
  = ∏_v ((σ v).toSign : ℝ)^((1_A v) + degreeAt n v)`.
Combines the indicator-power form of `σ_A` with the per-vertex
power form of the spin-edge product, ready to apply
`Config.sum_prod_toSign_pow_real` for the A-source spin sum
(FV §3.10.6). -/
theorem Config.spinA_mul_prod_spin_pow_eq_prod_pow_sum
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (σ : ↑Λ → Spin) (n : Current G Λ) (A : Finset ↑Λ) :
    (∏ a ∈ A, ((σ a).toSign : ℝ))
    * (∏ e : (inducedGraph G Λ).edgeSet,
        ((e : Sym2 ↑Λ).toFinset.prod
          (fun v => ((σ v).toSign : ℝ))) ^ n e)
      = ∏ v : ↑Λ, ((σ v).toSign : ℝ) ^
          ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v) := by
  rw [Config.prod_subset_eq_prod_pow_indicator Λ σ A,
    ← Config.prod_pow_spin_degreeAt G Λ σ n,
    ← Finset.prod_mul_distrib]
  congr 1
  ext v
  rw [← pow_add]

omit [DecidableEq V] in
/-- **A-source spin sum at fixed current — degree+indicator
form**: at fixed current `n` and source set `A ⊆ ↑Λ`,
`∑_σ σ_A · ∏_e (e.toFinset.prod σ.toSign)^n e
  = 2^|Λ|` if `(1_A v) + degreeAt n v` is even at every vertex,
else `0`. Combines `spinA_mul_prod_spin_pow_eq_prod_pow_sum`
with `Config.sum_prod_toSign_pow_real`. -/
theorem Config.sum_spinA_prod_spin_pow_eq_pow_card_iff
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    (∑ σ : ↑Λ → Spin,
      (∏ a ∈ A, ((σ a).toSign : ℝ))
      * (∏ e : (inducedGraph G Λ).edgeSet,
          ((e : Sym2 ↑Λ).toFinset.prod
            (fun v => ((σ v).toSign : ℝ))) ^ n e))
      = if (∀ v : ↑Λ,
            Even ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v))
        then (2 : ℝ)^(Fintype.card ↑Λ) else 0 := by
  simp_rw [Config.spinA_mul_prod_spin_pow_eq_prod_pow_sum G Λ _ n A]
  exact Config.sum_prod_toSign_pow_real
    (k := fun v => (if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v)

omit [DecidableEq V] in
/-- **Even (`1_A v + degreeAt n v`) at every vertex ↔
`n.HasSources A`**: a current `n` has source set exactly `A` iff
`(1_A v) + degreeAt n v` is even at every vertex. The A-source
analogue of `even_degreeAt_iff_isSourceFree`. -/
theorem Current.even_indicator_add_degreeAt_iff_hasSources
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet] [DecidableEq ↑Λ]
    (n : Current G Λ) (A : Finset ↑Λ) :
    (∀ v : ↑Λ,
        Even ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v))
      ↔ n.HasSources G Λ A := by
  classical
  unfold Current.HasSources
  -- Each summand: Even (1_A v + degreeAt n v)
  --   ↔ ((1_A v + degreeAt n v : ℕ) : ZMod 2) = 0
  --   ↔ (1_A v : ZMod 2) + parity n v = 0
  --   ↔ parity n v = -(1_A v : ZMod 2) = (1_A v : ZMod 2)  (char 2)
  have hper : ∀ v : ↑Λ,
      Even ((if v ∈ A then (1 : ℕ) else 0) + n.degreeAt G Λ v)
        ↔ n.parity G Λ v = (if v ∈ A then (1 : ZMod 2) else 0) := by
    intro v
    rw [even_iff_two_dvd, ← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [← Current.parity_eq_degreeAt]
    -- Goal: (if v ∈ A then 1 else 0 : ZMod 2) + parity n v = 0
    --       ↔ parity n v = if v ∈ A then 1 else 0
    by_cases hvA : v ∈ A
    · simp only [if_pos hvA]
      -- (1 : ZMod 2) + parity = 0 ↔ parity = 1
      have h2 : ∀ x : ZMod 2, 1 + x = 0 ↔ x = 1 := by decide
      exact h2 _
    · simp only [if_neg hvA]
      -- (0 : ZMod 2) + parity = 0 ↔ parity = 0
      simp
  rw [forall_congr' hper]
  -- ∀ v, parity n v = (if v ∈ A then 1 else 0 : ZMod 2) ↔ sources n = A
  have hZMod2 : ∀ x : ZMod 2, x ≠ 0 ↔ x = 1 := by decide
  constructor
  · intro h
    ext v
    rw [Current.mem_sources_iff, h v]
    by_cases hvA : v ∈ A
    · simp only [if_pos hvA]
      exact iff_of_true ((hZMod2 1).mpr rfl) hvA
    · simp only [if_neg hvA]
      exact iff_of_false (by simp) hvA
  · intro h v
    have hmem : (v ∈ n.sources G Λ) ↔ (v ∈ A) := by rw [h]
    rw [Current.mem_sources_iff] at hmem
    by_cases hvA : v ∈ A
    · rw [if_pos hvA]
      exact (hZMod2 _).mp (hmem.mpr hvA)
    · rw [if_neg hvA]
      by_contra hne
      exact hvA (hmem.mp hne)


end Ambient
end IsingModel
