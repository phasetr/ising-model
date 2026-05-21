import IsingModel.Conditioning.HighTempClosed

/-!
# Correlation Closed Forms

This module is part of the split `IsingModel.Conditioning` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Correlation closed form (FV §3.7.3 eq. (3.46)) -/

/-- **`spinProduct` as vertex-power**: for any `A : Finset ι`,
`∏_{a ∈ A} (σ a).toSign = ∏_v (σ v).toSign^(if v ∈ A then 1 else 0)`. -/
private theorem spinProduct_eq_prod_pow_indicator
    (A : Finset ι) (σ : Config ι) :
    spinProduct A σ
      = ∏ v : ι, ((σ v).toSign : ℝ) ^ (if v ∈ A then (1 : ℕ) else 0) := by
  classical
  unfold spinProduct
  rw [show (A : Finset ι) = (Finset.univ : Finset ι).filter (· ∈ A) by
    ext v; simp]
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  by_cases hv : v ∈ A <;> simp [hv]

/-- **σ-sum of `spinProduct A · edgeSpin product`**: for `X ⊆ G.edgeFinset`,
`∑_σ spinProduct A σ · ∏_{e ∈ X} edgeSpin σ e = 2^|ι|` if the parity
of every vertex `v` matches `(v ∈ A)` (i.e. `deg_X v + 1_A v` is even),
else `0`. The σ_A-weighted parity step underlying FV (3.46). -/
private theorem sum_spinProduct_mul_prod_edgeSpin_eq_pow_card_or_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (X : Finset (Sym2 ι))
    (hX : X ⊆ G.edgeFinset) (A : Finset ι) :
    (∑ σ : Config ι,
      spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
      = if (∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card))
        then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  -- Combine the indicator-power form of σ_A with the edge → vertex-power
  -- bridge from Step 283.
  have hcombine : ∀ σ : Config ι,
      spinProduct A σ * (∏ e ∈ X, edgeSpin (K := ℝ) σ e)
        = ∏ v : ι, ((σ v).toSign : ℝ) ^
            ((if v ∈ A then (1 : ℕ) else 0)
             + (X.filter (v ∈ ·)).card) := by
    intro σ
    rw [spinProduct_eq_prod_pow_indicator A σ,
        prod_edgeSpin_eq_prod_pow_filter_card G X hX σ,
        ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [← pow_add]
  simp_rw [hcombine]
  exact sum_prod_toSign_pow_real
    (k := fun v => (if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)

/-- **Numerator high-temperature expansion (h = 0)**: for any `A : Finset ι`,
`∑_σ spinProduct A σ · boltzmannWeight G ⟨J,0,β⟩ σ
  = 2^|ι| · cosh(βJ)^|E| · ∑_{X ⊆ E : every v has parity (v ∈ A)} tanh(βJ)^|X|`,
where the parity condition `(v ∈ A)` means `deg_X v + 1_A v` is even.
Companion to `partitionFunction_high_temp_expansion_h_zero_closed`
for the numerator of `correlation G ⟨J,0,β⟩ A`. -/
private theorem sum_spinProduct_boltzmannWeight_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    (∑ σ : Config ι,
      spinProduct A σ * boltzmannWeight G ⟨J, 0, β⟩ σ)
      = (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card := by
  -- Same skeleton as `partitionFunction_high_temp_expansion_h_zero_closed`
  -- but carrying a `spinProduct A σ` factor.
  have hboltz_h_zero : ∀ σ : Config ι,
      boltzmannWeight G ⟨J, 0, β⟩ σ
        = ∏ e ∈ G.edgeFinset, Real.exp (β * J * edgeSpin σ e) := by
    intro σ
    unfold boltzmannWeight hamiltonian interactionEnergy externalFieldEnergy
    rw [show -β *
            (-J * ∑ e ∈ G.edgeFinset, edgeSpin σ e
              + -(0 : ℝ) * ∑ i : ι, Spin.sign ℝ (σ i))
          = (β * J) * (∑ e ∈ G.edgeFinset, edgeSpin σ e) from by ring,
        Finset.mul_sum, Real.exp_sum]
  simp_rw [hboltz_h_zero]
  have hedge_decomp : ∀ σ : Config ι, ∀ e ∈ G.edgeFinset,
      Real.exp (β * J * edgeSpin σ e) =
        Real.cosh (β * J) * (1 + Real.tanh (β * J) * edgeSpin σ e) := by
    intros σ e _
    rw [exp_edgeSpin_decomp, Real.tanh_eq_sinh_div_cosh]
    have hcosh_ne : Real.cosh (β * J) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp
  simp_rw [fun σ =>
    Finset.prod_congr rfl (hedge_decomp σ)]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  -- ∑_σ spinProduct A σ · cosh^|E| · ∏_e (1 + ...) = cosh^|E| · ∑_σ spinProduct A σ · ∏_e (1+...)
  rw [show (∑ σ : Config ι, spinProduct A σ *
        (Real.cosh (β * J) ^ G.edgeFinset.card *
          ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e)))
      = Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ σ : Config ι, spinProduct A σ *
          ∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring]
  -- Subset expansion
  have hexpand : ∀ σ : Config ι,
      (∏ e ∈ G.edgeFinset, (1 + Real.tanh (β * J) * edgeSpin σ e))
        = ∑ X ∈ G.edgeFinset.powerset,
            ∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e) := fun σ =>
    Finset.prod_one_add G.edgeFinset
  simp_rw [hexpand]
  -- Pull tanh^|X| out
  have hpull : ∀ σ : Config ι, ∀ X : Finset (Sym2 ι),
      (∏ e ∈ X, (Real.tanh (β * J) * edgeSpin σ e))
        = Real.tanh (β * J) ^ X.card *
            (∏ e ∈ X, edgeSpin (K := ℝ) σ e) := by
    intros σ X
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp_rw [hpull]
  -- Distribute spinProduct A σ over the X-sum
  rw [show (∑ σ : Config ι, spinProduct A σ *
        ∑ X ∈ G.edgeFinset.powerset,
          Real.tanh (β * J) ^ X.card * (∏ e ∈ X, edgeSpin (K := ℝ) σ e))
      = ∑ σ : Config ι,
        ∑ X ∈ G.edgeFinset.powerset,
          spinProduct A σ * (Real.tanh (β * J) ^ X.card *
            ∏ e ∈ X, edgeSpin (K := ℝ) σ e) by
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Finset.mul_sum]]
  -- Swap σ ↔ X and pull tanh^|X| out further
  rw [Finset.sum_comm]
  rw [show (∑ X ∈ G.edgeFinset.powerset, ∑ σ : Config ι,
        spinProduct A σ * (Real.tanh (β * J) ^ X.card *
          ∏ e ∈ X, edgeSpin (K := ℝ) σ e))
      = ∑ X ∈ G.edgeFinset.powerset,
        Real.tanh (β * J) ^ X.card *
          ∑ σ : Config ι,
            spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e by
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring]
  -- Apply parity collapse
  have hparity : ∀ X ∈ G.edgeFinset.powerset,
      (∑ σ : Config ι,
        spinProduct A σ * ∏ e ∈ X, edgeSpin (K := ℝ) σ e)
        = if (∀ v : ι,
              Even ((if v ∈ A then (1 : ℕ) else 0)
                    + (X.filter (v ∈ ·)).card))
          then (2 : ℝ) ^ Fintype.card ι else 0 := fun X hX =>
    sum_spinProduct_mul_prod_edgeSpin_eq_pow_card_or_zero G X
      (Finset.mem_powerset.mp hX) A
  rw [Finset.sum_congr rfl
    (fun X hX => by rw [hparity X hX])]
  -- Distribute and collapse via filter
  have hdist : ∀ X : Finset (Sym2 ι),
      Real.tanh (β * J) ^ X.card *
          (if (∀ v : ι,
                Even ((if v ∈ A then (1 : ℕ) else 0)
                      + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι else 0)
        = (if (∀ v : ι,
                Even ((if v ∈ A then (1 : ℕ) else 0)
                      + (X.filter (v ∈ ·)).card))
            then (2 : ℝ) ^ Fintype.card ι * Real.tanh (β * J) ^ X.card
            else 0) := fun X => by
    by_cases h : ∀ v : ι, Even ((if v ∈ A then (1 : ℕ) else 0)
                                + (X.filter (v ∈ ·)).card)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  simp_rw [hdist]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  ring

/-- **Correlation closed form at h = 0 — Friedli–Velenik §3.7.3 eq. (3.46)**:
\[
\langle \sigma_A \rangle_{\beta, 0} =
  \frac{\sum_{X \subseteq E,\, \partial X = A} \tanh(\beta J)^{|X|}}
       {\sum_{X \subseteq E,\, \partial X = \emptyset} \tanh(\beta J)^{|X|}},
\]
where the boundary condition `∂X = A` is encoded as
`∀ v, Even ((1_A v) + (X.filter (v ∈ ·)).card)` (i.e. the parity
of the X-degree at every vertex `v` matches whether `v ∈ A`).

The `2^{|\iota|} \cdot (\cosh \beta J)^{|E|}` prefactor cancels between
numerator and denominator. Combines
`partitionFunction_high_temp_expansion_h_zero_closed` (Step 283) with
`sum_spinProduct_boltzmannWeight_h_zero_closed`.

References: GJ §18.3; FV §3.7.3 eq. (3.46), p. 117 (2017 ed.). -/
theorem correlation_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) :
    correlation G ⟨J, 0, β⟩ A =
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card) /
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card) := by
  unfold correlation gibbsExpectation
  rw [sum_spinProduct_boltzmannWeight_h_zero_closed G J β A,
      partitionFunction_high_temp_expansion_h_zero_closed G J β]
  -- Now: (Z_closed)⁻¹ * N_closed = N_subsum / Z_subsum
  set N_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι,
        Even ((if v ∈ A then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hN_sub
  set Z_sub : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hZ_sub
  -- Goal: ((2^|ι|·cosh^|E|·Z_sub))⁻¹ · (2^|ι|·cosh^|E|·N_sub) = N_sub / Z_sub
  have hcommon_pos :
      (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card := by
    apply mul_pos
    · exact pow_pos (by norm_num) _
    · exact pow_pos (Real.cosh_pos _) _
  have hcommon_ne : (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card ≠ 0 :=
    hcommon_pos.ne'
  field_simp

/-! ### Handshake lemma for arbitrary edge subsets

For `X ⊆ G.edgeFinset` on a `SimpleGraph` (edges non-diagonal),
`∑_v (X.filter (v ∈ ·)).card = 2 · |X|`, the standard handshake
identity. Combined with `Finset.even_sum_iff_even_card_odd`, this
gives that the number of odd `X`-degree vertices is always even —
the parity argument behind the FV (3.46) Z₂ symmetry. -/

/-- **Handshake lemma for arbitrary edge subsets**: for `X ⊆ G.edgeFinset`
on a `SimpleGraph` (so all edges are non-diagonal),
`∑_v (X.filter (v ∈ ·)).card = 2 · |X|`. -/
private theorem sum_filter_card_eq_two_mul_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    ∑ v : ι, (X.filter (v ∈ ·)).card = 2 * X.card := by
  classical
  -- per-v rewrite: card filter = ∑ over X of indicator
  have hper_v : ∀ v : ι,
      (X.filter (v ∈ ·)).card = ∑ e ∈ X, (if v ∈ e then 1 else 0) := by
    intro v
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [hper_v]
  rw [Finset.sum_comm]
  -- inner sum: ∑_v (if v ∈ e then 1 else 0) = e.toFinset.card = 2 (non-diag)
  have hinner : ∀ e ∈ X,
      ∑ v : ι, (if v ∈ e then (1 : ℕ) else 0) = 2 := by
    intros e he
    have heq :
        (∑ v : ι, if v ∈ e then (1 : ℕ) else 0)
          = ((Finset.univ : Finset ι).filter (· ∈ e)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [heq]
    have hf_eq : (Finset.univ : Finset ι).filter (· ∈ e) = e.toFinset := by
      ext v; simp
    rw [hf_eq]
    have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet
      (G.mem_edgeFinset.mp (hX he))
    exact e.card_toFinset_of_not_isDiag hnd
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring

/-- **Even count of odd-degree vertices**: for `X ⊆ G.edgeFinset`,
`Even |{v | Odd (X.filter (v ∈ ·)).card}|`. The number of vertices with
odd `X`-degree is always even. Direct consequence of the handshake
identity `∑_v deg_X v = 2|X|` plus `Finset.even_sum_iff_even_card_odd`. -/
private theorem even_card_odd_filter_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (X : Finset (Sym2 ι)) (hX : X ⊆ G.edgeFinset) :
    Even ((Finset.univ : Finset ι).filter
      (fun v => Odd ((X.filter (v ∈ ·)).card))).card := by
  have hsum := sum_filter_card_eq_two_mul_card G X hX
  have h_even : Even (∑ v : ι, (X.filter (v ∈ ·)).card) := by
    rw [hsum]; exact ⟨X.card, by ring⟩
  exact (Finset.even_sum_iff_even_card_odd _).mp h_even

/-- **FV (3.46) numerator filter is empty for odd-cardinality A**:
the filtered powerset
`{X ⊆ G.edgeFinset : ∀ v, Even ((1_A v) + (X.filter (v ∈ ·)).card)}`
is *empty* whenever `|A|` is odd.

Direct consequence of the handshake lemma: for any `X` in this filter,
the condition forces `{v | Odd (deg_X v)} = A`, but the LHS has even
cardinality (handshake), so `|A|` even — contradicting odd `|A|`.

A sharper version of `sum_high_temp_numerator_h_zero_odd_card_eq_zero`
(Step 291): instead of "the sum vanishes", we show "the index set is
empty". Independent of the `correlation_odd_vanish` Z₂-flip argument. -/
theorem high_temp_numerator_filter_eq_empty_of_odd_card
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (A : Finset ι) (hA_odd : Odd A.card) :
    G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro X hX
  rw [Finset.mem_filter, Finset.mem_powerset] at hX
  obtain ⟨hXsub, hcond⟩ := hX
  -- Translate hcond: ∂X = A (set of v with odd X-degree = A)
  have hboundary_eq_A :
      (Finset.univ : Finset ι).filter
          (fun v => Odd ((X.filter (v ∈ ·)).card)) = A := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hodd
      by_contra hvA
      have := hcond v
      rw [if_neg hvA, zero_add] at this
      exact (Nat.not_even_iff_odd.mpr hodd) this
    · intro hvA
      have := hcond v
      rw [if_pos hvA] at this
      rw [show (1 : ℕ) + (X.filter (v ∈ ·)).card
            = (X.filter (v ∈ ·)).card + 1 from Nat.add_comm _ _,
          Nat.even_add_one, Nat.not_even_iff_odd] at this
      exact this
  have h_even := even_card_odd_filter_card G X hXsub
  rw [hboundary_eq_A] at h_even
  exact (Nat.not_even_iff_odd.mpr hA_odd) h_even

/-! ### Z₂ symmetry from FV (3.46): odd-cardinality numerator sum vanishes -/

/-- **FV (3.46) numerator vanishes for odd-cardinality A**: the FV (3.46)
numerator `∑_{X : ∂X = A} tanh(βJ)^|X|` equals `0` for any `A` of odd
cardinality.

Direct combinatorial proof via `high_temp_numerator_filter_eq_empty_of_odd_card`
(Step 297): the filter indexing the numerator is *literally empty*
because the handshake lemma `∑_v deg_X v = 2|X|` forces `|∂X|` even,
so no `X` satisfies `∂X = A` when `|A|` is odd. The empty sum is `0`. -/
theorem sum_high_temp_numerator_h_zero_odd_card_eq_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) (hA_odd : Odd A.card) :
    ∑ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ A then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card = 0 := by
  rw [high_temp_numerator_filter_eq_empty_of_odd_card G A hA_odd,
      Finset.sum_empty]

/-- **FV (3.46) at `A = ∅` reduces to `1`**: a consistency check that
the closed form `correlation_high_temp_expansion_h_zero_closed`
specializes at `A = ∅` to `1`, matching `correlation_empty`.
At `A = ∅`, the numerator filter condition `∀v, Even ((1_∅ v) + deg_X v)`
simplifies to `∀v, Even (deg_X v)` (same as the denominator), so the
numerator equals the denominator, giving `correlation = N/D = 1`.

Requires `0 ≤ β * J` to ensure the denominator is strictly positive
(via `one_le_sum_pow_tanh_even_subgraph`, Step 295). -/
theorem correlation_high_temp_h_zero_at_empty_A
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    correlation G ⟨J, 0, β⟩ (∅ : Finset ι) = 1 := by
  rw [correlation_high_temp_expansion_h_zero_closed]
  -- Numerator filter at A = ∅: condition `∀v, Even ((1_∅ v) + ...)` becomes `∀v, Even (deg_X v)`
  have hnum_eq_den :
      G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ (∅ : Finset ι) then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card))
        = G.edgeFinset.powerset.filter
            (fun X : Finset (Sym2 ι) =>
              ∀ v : ι, Even ((X.filter (v ∈ ·)).card)) := by
    refine Finset.filter_congr ?_
    intro X _
    constructor
    · intro h v
      have hv := h v
      simp only [Finset.notMem_empty, if_false, zero_add] at hv
      exact hv
    · intro h v
      have hv := h v
      simp only [Finset.notMem_empty, if_false, zero_add]
      exact hv
  rw [hnum_eq_den]
  have hden_pos := one_le_sum_pow_tanh_even_subgraph G J β hβJ
  exact div_self (lt_of_lt_of_le zero_lt_one hden_pos).ne'

/-- **Correlation nonnegativity at h = 0 from FV (3.46)**: under
`0 ≤ β * J`, `0 ≤ correlation G ⟨J, 0, β⟩ A` for any `A : Finset ι`.

Alternate derivation of GKS-I (`gks_first` / `correlation_nonneg_of_ferromagnetic`)
from the FV (3.46) closed form: numerator and denominator are both
sums of `tanh(βJ)^|X|` with `tanh(βJ) ≥ 0` (from `0 ≤ βJ`), hence
both nonneg; the denominator is strictly positive (deduced from
`partitionFunction_pos`), so the ratio is `≥ 0`. -/
theorem correlation_high_temp_h_zero_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ A := by
  rw [correlation_high_temp_expansion_h_zero_closed]
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  -- Numerator nonneg: sum of tanh^|X| ≥ 0
  have hnum_nn :
      0 ≤ ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
    Finset.sum_nonneg (fun X _ => pow_nonneg htanh_nn _)
  -- Denominator nonneg: same sum, different filter
  have hden_nn :
      0 ≤ ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) => ∀ v : ι,
            Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card :=
    Finset.sum_nonneg (fun X _ => pow_nonneg htanh_nn _)
  exact div_nonneg hnum_nn hden_nn

/-- **Correlation upper bound by FV (3.46) numerator at `h = 0` (GJ §18.7
foundation)**: under `0 ≤ β·J`,
\[
\langle \sigma_A \rangle_{\beta, 0}
  \le \sum_{X \subseteq E,\, \partial X = A} \tanh(\beta J)^{|X|}.
\]

Combines `correlation_high_temp_expansion_h_zero_closed` (FV (3.46)) with:
- numerator nonneg under `0 ≤ tanh(β·J)`;
- denominator `≥ 1` (Step 295 `one_le_sum_pow_tanh_even_subgraph`,
  using that the empty subgraph contributes `1`).

Reduces the §18.7 capstone (exponential decay
`|⟨σ_iσ_j⟩| ≤ C · tanh(β·J)^{d(i,j)}`) to a *numerator-only* estimate.

References: GJ §18.7; FV §3.7.3 eq. (3.46), p. 117 (2017 ed.). -/
theorem correlation_high_temp_h_zero_le_numerator
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (A : Finset ι) :
    correlation G ⟨J, 0, β⟩ A ≤
      ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι,
            Even ((if v ∈ A then (1 : ℕ) else 0)
                  + (X.filter (v ∈ ·)).card)),
        Real.tanh (β * J) ^ X.card := by
  rw [correlation_high_temp_expansion_h_zero_closed]
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  set N : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ A then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hN_def
  set D : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hD_def
  have hN_nn : 0 ≤ N :=
    Finset.sum_nonneg (fun X _ => pow_nonneg htanh_nn _)
  have h_one_le_D : 1 ≤ D := one_le_sum_pow_tanh_even_subgraph G J β hβJ
  have h_D_pos : 0 < D := lt_of_lt_of_le zero_lt_one h_one_le_D
  -- N / D ≤ N / 1 = N because D ≥ 1 and N ≥ 0
  have h_step : N / D ≤ N / 1 :=
    div_le_div_of_nonneg_left hN_nn zero_lt_one h_one_le_D
  rw [div_one] at h_step
  exact h_step

/-- **Pair numerator filter forces `1 ≤ |X|` (GJ §18.7 foundation)**:
for any `i j : ι`, every `X` in the FV (3.46) numerator filter for
`A = {i, j}` satisfies `1 ≤ X.card`.

The empty subgraph cannot occur: at `v = i` (which lies in `A = {i, j}`),
the constraint `Even (1 + (X.filter (i ∈ ·)).card)` forces
`(X.filter (i ∈ ·)).card` to be **odd**; if `X = ∅` this would give
`(X.filter (i ∈ ·)).card = 0`, even, and `1 + 0 = 1` is *not* even —
contradiction.

Note that `i ≠ j` is *not* needed: when `i = j`, `A = {i}` and the same
parity argument at `v = i` excludes `X = ∅`.

Building block toward the §18.7 capstone graph-distance bound
`d_G(i, j) ≤ X.card`. -/
theorem evenSubgraph_pair_boundary_card_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card))) :
    1 ≤ X.card := by
  rcases Finset.mem_filter.mp hX with ⟨_, hparity⟩
  rcases Nat.eq_zero_or_pos X.card with h | h
  · exfalso
    have hX_empty : X = ∅ := Finset.card_eq_zero.mp h
    have h_at_i := hparity i
    have hi_mem : i ∈ ({i, j} : Finset ι) := Finset.mem_insert_self i {j}
    rw [hX_empty] at h_at_i
    simp [hi_mem] at h_at_i
  · exact h

omit [Fintype ι] in
/-- **Erase-edge filter card transition (GJ §18.7 foundation)**:
for `X : Finset (Sym2 ι)`, `e ∈ X`, and any vertex `v`,
\[
|\{X' \in X \mid v \in X'\}|
  = |\{X' \in X.\mathrm{erase}\,e \mid v \in X'\}|
    + [v \in e],
\]
i.e., erasing `e` decreases the per-vertex filter card by `1` exactly
when `v` is incident to `e`, and leaves it unchanged otherwise.

Encodes the parity-flip behaviour `∂(X.erase e) = ∂X △ e` underlying
the inductive proof of `d_G(i, j) ≤ |X|` (planned Step 571+).

Proof: combine `Finset.filter_erase` (filter and erase commute) with
case analysis on whether `v ∈ e`. -/
theorem filter_mem_card_erase
    (X : Finset (Sym2 ι)) (e : Sym2 ι) (hX : e ∈ X) (v : ι) :
    (X.filter (v ∈ ·)).card =
      ((X.erase e).filter (v ∈ ·)).card + (if v ∈ e then 1 else 0) := by
  classical
  rw [Finset.filter_erase]
  by_cases hv : v ∈ e
  · have h_e_in_filter : e ∈ X.filter (v ∈ ·) :=
      Finset.mem_filter.mpr ⟨hX, hv⟩
    rw [Finset.card_erase_of_mem h_e_in_filter, if_pos hv]
    have h_pos : 0 < (X.filter (v ∈ ·)).card := Finset.card_pos.mpr ⟨e, h_e_in_filter⟩
    omega
  · have h_e_notin_filter : e ∉ X.filter (v ∈ ·) := by
      intro h_in
      exact hv (Finset.mem_filter.mp h_in).2
    rw [Finset.erase_eq_of_notMem h_e_notin_filter, if_neg hv, Nat.add_zero]

/-- **Pair-boundary numerator: `i` is incident to some edge in `X`
(GJ §18.7 foundation)**: for any `X` in the FV (3.46) numerator filter
for `A = {i, j}`, there exists an edge `e ∈ X` with `i ∈ e`.

Direct from the parity constraint at `v = i`: since `i ∈ A`, we get
`Even (1 + (X.filter (i ∈ ·)).card)`, forcing the filter card to be
**odd**, hence `≥ 1`, hence non-empty.

Building block toward the §18.7 graph-distance lower bound
`d_G(i, j) ≤ X.card` via induction on `X.card`. -/
theorem evenSubgraph_pair_boundary_exists_edge_incident_to
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card))) :
    ∃ e ∈ X, i ∈ e := by
  rcases Finset.mem_filter.mp hX with ⟨_, hparity⟩
  have h_at_i := hparity i
  have hi_mem : i ∈ ({i, j} : Finset ι) := Finset.mem_insert_self i {j}
  rw [if_pos hi_mem] at h_at_i
  -- h_at_i : Even (1 + (X.filter (i ∈ ·)).card)
  -- Hence (X.filter (i ∈ ·)).card is odd, hence ≥ 1
  have h_filter_card_pos : 0 < (X.filter (i ∈ ·)).card := by
    rcases Nat.eq_zero_or_pos (X.filter (i ∈ ·)).card with h_zero | h_pos
    · exfalso
      rw [h_zero] at h_at_i
      simp at h_at_i
    · exact h_pos
  -- Filter is non-empty, pick any element
  obtain ⟨e, he⟩ := Finset.card_pos.mp h_filter_card_pos
  rcases Finset.mem_filter.mp he with ⟨he_in_X, he_contains_i⟩
  exact ⟨e, he_in_X, he_contains_i⟩

/-- **Card-1 case of pair-boundary numerator: `X = {s(i,j)}` and
`G.Adj i j` (GJ §18.7 foundation)**: if `i ≠ j`, `X.card = 1`, and `X`
is in the FV (3.46) numerator filter for `A = {i, j}`, then
`X = {s(i, j)}` and `i, j` are adjacent in `G`.

Establishes the base case for the inductive `d_G(i, j) ≤ X.card`
proof: when `X.card = 1`, the unique edge in `X` connects `i` and `j`
directly, so the graph distance is `≤ 1 = X.card`.

Proof: from Step 569 applied to both `i` and `j` (using
symmetry of `A = {i, j}` for the second invocation), the unique edge
in `X` must contain both `i` and `j`. Since `i ≠ j`, this edge is
exactly `s(i, j)`. Membership in `G.edgeFinset` gives `G.Adj i j`. -/
theorem evenSubgraph_pair_boundary_card_one_adj
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) (hij : i ≠ j)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X' : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X'.filter (v ∈ ·)).card)))
    (hcard : X.card = 1) :
    X = {s(i, j)} ∧ G.Adj i j := by
  classical
  obtain ⟨e, hX_eq⟩ := Finset.card_eq_one.mp hcard
  -- Step 569 at (i, j): ∃ e' ∈ X, i ∈ e'. With X = {e}, e' = e, so i ∈ e.
  obtain ⟨e_i, he_i, hi_in⟩ :=
    evenSubgraph_pair_boundary_exists_edge_incident_to G i j X hX
  rw [hX_eq, Finset.mem_singleton] at he_i
  rw [he_i] at hi_in
  -- Symmetry: A = {i, j} = {j, i}, so we can apply Step 569 with (j, i).
  have hX_swap : X ∈ G.edgeFinset.powerset.filter
      (fun X' : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({j, i} : Finset ι) then (1 : ℕ) else 0)
              + (X'.filter (v ∈ ·)).card)) := by
    have h_set_eq : ({j, i} : Finset ι) = ({i, j} : Finset ι) := by
      ext x; simp [or_comm]
    rw [h_set_eq]; exact hX
  obtain ⟨e_j, he_j, hj_in⟩ :=
    evenSubgraph_pair_boundary_exists_edge_incident_to G j i X hX_swap
  rw [hX_eq, Finset.mem_singleton] at he_j
  rw [he_j] at hj_in
  -- e contains both i and j; since i ≠ j, e = s(i, j)
  have he_eq : e = s(i, j) := by
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp hi_in with hi_eq | hi_eq
      · subst hi_eq
        rcases Sym2.mem_iff.mp hj_in with hj_eq | hj_eq
        · exact absurd hj_eq.symm hij
        · subst hj_eq; rfl
      · subst hi_eq
        rcases Sym2.mem_iff.mp hj_in with hj_eq | hj_eq
        · subst hj_eq; exact Sym2.eq_swap
        · exact absurd hj_eq.symm hij
  -- X ⊆ G.edgeFinset gives e ∈ G.edgeFinset, so G.Adj i j
  have hX_sub : X ⊆ G.edgeFinset :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hX).1
  rw [hX_eq] at hX_sub
  have he_in_G : e ∈ G.edgeFinset := hX_sub (Finset.mem_singleton_self _)
  rw [he_eq, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he_in_G
  refine ⟨?_, he_in_G⟩
  rw [hX_eq, he_eq]

/-- **Parity transition for `X.erase s(i, k)` when `∂X = {i, j}`,
`k ∉ {i, j}` (GJ §18.7 foundation)**: under `i ≠ j`, `k ≠ i`, `k ≠ j`,
if `X` is in the FV (3.46) numerator filter for `A = {i, j}` and
`s(i, k) ∈ X`, then `X.erase s(i, k)` is in the FV (3.46) numerator
filter for `A' = {k, j}`.

The boundary "moves" from `{i, j}` to `{k, j}`: erasing the edge
`s(i, k)` flips parity at both endpoints `i` and `k` (Step 570),
turning `i`'s odd degree into even (so `i` leaves the boundary) and
`k`'s even degree into odd (so `k` joins the boundary). The vertex
`j`'s parity is preserved.

The mod-2 identity verified: for every `v`,
`[v ∈ {i, j}] + [v ∈ s(i, k)] ≡ [v ∈ {k, j}] (mod 2)`. -/
theorem evenSubgraph_pair_boundary_erase_swap
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j k : ι) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X' : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X'.filter (v ∈ ·)).card)))
    (he_in : s(i, k) ∈ X) :
    X.erase s(i, k) ∈ G.edgeFinset.powerset.filter
      (fun X' : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({k, j} : Finset ι) then (1 : ℕ) else 0)
              + (X'.filter (v ∈ ·)).card)) := by
  classical
  rcases Finset.mem_filter.mp hX with ⟨h_pow, h_par⟩
  refine Finset.mem_filter.mpr ⟨?_, fun v => ?_⟩
  · exact Finset.mem_powerset.mpr
      ((Finset.erase_subset _ _).trans (Finset.mem_powerset.mp h_pow))
  · have h_par_v := h_par v
    have h_step570 := filter_mem_card_erase X (s(i, k)) he_in v
    rw [h_step570] at h_par_v
    -- Both indicators concretely:
    have h_v_in_e_iff : v ∈ (s(i, k) : Sym2 ι) ↔ v = i ∨ v = k := Sym2.mem_iff
    have h_in_ij_iff : v ∈ ({i, j} : Finset ι) ↔ v = i ∨ v = j := by simp
    have h_in_kj_iff : v ∈ ({k, j} : Finset ι) ↔ v = k ∨ v = j := by simp
    -- Compute the indicator parity sum: [v ∈ {i, j}] + [v ∈ s(i, k)] + [v ∈ {k, j}]
    -- has the same parity for all v (always even, by case analysis).
    -- Strategy: express both sides via the "X.erase ...".filter card and
    -- reduce to comparing indicator sums.
    by_cases hvi : v = i
    · -- v = i: indicators (1, 1, 0)
      have h1 : v ∈ ({i, j} : Finset ι) := by rw [hvi]; exact Finset.mem_insert_self _ _
      have h2 : v ∈ (s(i, k) : Sym2 ι) := by rw [hvi]; exact Sym2.mem_mk_left _ _
      have h3 : v ∉ ({k, j} : Finset ι) := by
        intro hv_in
        rw [h_in_kj_iff, hvi] at hv_in
        rcases hv_in with heq | heq
        · exact hki heq.symm
        · exact hij heq
      rw [if_pos h1, if_pos h2] at h_par_v
      rw [if_neg h3]
      -- h_par_v : Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card + 1))
      -- Goal: Even (0 + ((X.erase s(i,k)).filter (v ∈ ·)).card)
      have h_eq_orig : (1 : ℕ) + (((X.erase s(i, k)).filter (v ∈ ·)).card + 1) =
          ((X.erase s(i, k)).filter (v ∈ ·)).card + 2 := by ring
      rw [h_eq_orig] at h_par_v
      have h_eq_goal : (0 : ℕ) + ((X.erase s(i, k)).filter (v ∈ ·)).card =
          ((X.erase s(i, k)).filter (v ∈ ·)).card := by ring
      rw [h_eq_goal]
      exact (Nat.even_add.mp h_par_v).mpr (by decide : Even 2)
    · by_cases hvj : v = j
      · -- v = j: indicators (1, 0, 1) — note j ≠ i, j ≠ k so j ∉ s(i, k)
        have h1 : v ∈ ({i, j} : Finset ι) := by rw [hvj]; simp
        have h2 : v ∉ (s(i, k) : Sym2 ι) := by
          intro hv_in
          rw [h_v_in_e_iff, hvj] at hv_in
          rcases hv_in with heq | heq
          · exact hij heq.symm
          · exact hkj heq.symm
        have h3 : v ∈ ({k, j} : Finset ι) := by rw [hvj]; simp
        rw [if_pos h1, if_neg h2] at h_par_v
        rw [if_pos h3]
        -- h_par_v : Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card + 0))
        -- Goal: Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card)
        simpa using h_par_v
      · by_cases hvk : v = k
        · -- v = k: indicators (0, 1, 1) — k ∉ {i, j}, k ∈ s(i, k), k ∈ {k, j}
          have h1 : v ∉ ({i, j} : Finset ι) := by
            intro hv_in
            rw [h_in_ij_iff, hvk] at hv_in
            rcases hv_in with heq | heq
            · exact hki heq
            · exact hkj heq
          have h2 : v ∈ (s(i, k) : Sym2 ι) := by rw [hvk]; exact Sym2.mem_mk_right _ _
          have h3 : v ∈ ({k, j} : Finset ι) := by rw [hvk]; exact Finset.mem_insert_self _ _
          rw [if_neg h1, if_pos h2] at h_par_v
          rw [if_pos h3]
          -- h_par_v : Even (0 + ((X.erase s(i,k)).filter (v ∈ ·)).card + 1))
          -- Goal: Even (1 + ((X.erase s(i,k)).filter (v ∈ ·)).card)
          have h_eq_orig : (0 : ℕ) + (((X.erase s(i, k)).filter (v ∈ ·)).card + 1) =
              ((X.erase s(i, k)).filter (v ∈ ·)).card + 1 := by ring
          have h_eq_goal : (1 : ℕ) + ((X.erase s(i, k)).filter (v ∈ ·)).card =
              ((X.erase s(i, k)).filter (v ∈ ·)).card + 1 := by ring
          rw [h_eq_orig] at h_par_v
          rw [h_eq_goal]
          exact h_par_v
        · -- v ∉ {i, j, k}: indicators (0, 0, 0)
          have h1 : v ∉ ({i, j} : Finset ι) := by
            intro hv_in
            rw [h_in_ij_iff] at hv_in
            rcases hv_in with heq | heq
            · exact hvi heq
            · exact hvj heq
          have h2 : v ∉ (s(i, k) : Sym2 ι) := by
            intro hv_in
            rw [h_v_in_e_iff] at hv_in
            rcases hv_in with heq | heq
            · exact hvi heq
            · exact hvk heq
          have h3 : v ∉ ({k, j} : Finset ι) := by
            intro hv_in
            rw [h_in_kj_iff] at hv_in
            rcases hv_in with heq | heq
            · exact hvk heq
            · exact hvj heq
          rw [if_neg h1, if_neg h2] at h_par_v
          rw [if_neg h3]
          simpa using h_par_v

/-- **Pair-boundary graph-distance bound (GJ §18.7 capstone, key step)**:
under `∂X = {i, j}` (i.e. `X` is in the FV (3.46) numerator filter for
`A = {i, j}`), the graph distance satisfies `G.dist i j ≤ X.card`.

Strong induction on `X.card`, building an explicit walk:
- `i = j`: walk = `nil`, length `0 ≤ X.card` (and `dist_self = 0`).
- `i ≠ j`, `X.card ≥ 1` (Step 567): pick `e = s(i, k) ∈ X` (Step 569),
  giving `G.Adj i k` (since `e ∈ G.edgeFinset`).
  - `k = j`: walk = `cons hadj nil`, length `1 ≤ X.card`.
  - `k ≠ j`: erase `e`. Parity transition (Step 572) gives
    `∂(X.erase e) = {k, j}`. IH on `X.erase e` (with
    `(X.erase e).card < X.card`) yields a walk `k → j` of length
    `≤ X.card - 1`. Prepend the `i → k` edge to get a walk `i → j` of
    length `≤ X.card`.

Combined with Step 568 (numerator counting via `tanh(β·J)^|X|`) and a
`tanh(β·J)^k ≤ tanh(β·J)^{d_G(i,j)}` reduction (using `|X| ≥ d_G(i, j)`
shown here), gives the §18.7 capstone exponential decay
`⟨σ_iσ_j⟩ ≤ ... · tanh(β·J)^{d_G(i,j)}` at high temperature. -/
theorem evenSubgraph_pair_boundary_dist_le
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι)
    (X : Finset (Sym2 ι))
    (hX : X ∈ G.edgeFinset.powerset.filter
        (fun X' : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X'.filter (v ∈ ·)).card))) :
    G.dist i j ≤ X.card := by
  classical
  -- Reduce to constructing a walk of bounded length, then apply dist_le.
  suffices h : ∀ (n : ℕ) (i' j' : ι) (X' : Finset (Sym2 ι)),
      i' ≠ j' → X'.card = n →
      X' ∈ G.edgeFinset.powerset.filter
          (fun X'' : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ ({i', j'} : Finset ι) then (1 : ℕ) else 0)
                  + (X''.filter (v ∈ ·)).card)) →
      ∃ p : G.Walk i' j', p.length ≤ X'.card by
    by_cases hij : i = j
    · subst hij
      rw [G.dist_self]
      exact Nat.zero_le _
    · obtain ⟨p, hp⟩ := h X.card i j X hij rfl hX
      exact (G.dist_le p).trans hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i' j' X' hij' hcard hX'
    have h_card_pos : 1 ≤ X'.card := evenSubgraph_pair_boundary_card_pos G i' j' X' hX'
    -- Pick edge incident to i' (Step 569)
    obtain ⟨e, he_in, hi_in⟩ :=
      evenSubgraph_pair_boundary_exists_edge_incident_to G i' j' X' hX'
    -- Other endpoint k via Sym2.Mem.other
    have he_eq : s(i', Sym2.Mem.other hi_in) = e := Sym2.other_spec hi_in
    have hX_sub : X' ⊆ G.edgeFinset :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hX').1
    have he_in_G : e ∈ G.edgeFinset := hX_sub he_in
    have he_in_edgeSet : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he_in_G
    have he_not_diag : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet he_in_edgeSet
    have hk_ne_i : Sym2.Mem.other hi_in ≠ i' := Sym2.other_ne he_not_diag hi_in
    -- G.Adj i' k from e = s(i', k) ∈ G.edgeSet
    have hadj_ik : G.Adj i' (Sym2.Mem.other hi_in) := by
      have h_in : s(i', Sym2.Mem.other hi_in) ∈ G.edgeSet := he_eq.symm ▸ he_in_edgeSet
      rwa [SimpleGraph.mem_edgeSet] at h_in
    -- Case: k = j' or k ≠ j'
    by_cases hk_eq : Sym2.Mem.other hi_in = j'
    · -- k = j': single-edge walk of length 1
      have hadj_ij : G.Adj i' j' := hk_eq ▸ hadj_ik
      refine ⟨SimpleGraph.Walk.cons hadj_ij SimpleGraph.Walk.nil, ?_⟩
      rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      -- goal: 0 + 1 ≤ X'.card
      omega
    · -- k ≠ j': erase e, recurse via parity transition (Step 572)
      have h_erase_card : (X'.erase e).card = n - 1 := by
        rw [Finset.card_erase_of_mem he_in, hcard]
      have h_erase_lt : (X'.erase e).card < n := by
        rw [h_erase_card]; omega
      -- Convert e back to s(i', k) for Step 572 application
      have he_actual : e = s(i', Sym2.Mem.other hi_in) := he_eq.symm
      have he_in' : s(i', Sym2.Mem.other hi_in) ∈ X' := he_actual ▸ he_in
      have hX_swap : X'.erase s(i', Sym2.Mem.other hi_in) ∈
          G.edgeFinset.powerset.filter
            (fun X'' : Finset (Sym2 ι) => ∀ v : ι,
              Even ((if v ∈ ({Sym2.Mem.other hi_in, j'} : Finset ι) then (1 : ℕ) else 0)
                    + (X''.filter (v ∈ ·)).card)) :=
        evenSubgraph_pair_boundary_erase_swap G i' j' (Sym2.Mem.other hi_in)
          hij' hk_ne_i hk_eq X' hX' he_in'
      -- Convert the erase to use e
      have hX_swap' : (X'.erase e) ∈ G.edgeFinset.powerset.filter
          (fun X'' : Finset (Sym2 ι) => ∀ v : ι,
            Even ((if v ∈ ({Sym2.Mem.other hi_in, j'} : Finset ι) then (1 : ℕ) else 0)
                  + (X''.filter (v ∈ ·)).card)) := by
        rwa [← he_actual] at hX_swap
      -- Apply IH
      obtain ⟨p_kj, hp_kj⟩ := ih (X'.erase e).card h_erase_lt
        (Sym2.Mem.other hi_in) j' (X'.erase e) hk_eq rfl hX_swap'
      -- Build walk i' → j' as cons (i' → k) (k → j')
      refine ⟨SimpleGraph.Walk.cons hadj_ik p_kj, ?_⟩
      rw [SimpleGraph.Walk.length_cons, h_erase_card] at *
      omega

/-- **§18.7 capstone — `{i,j}`-correlation exponential decay at
`h = 0`**: under `0 ≤ β·J`,
\[
\langle \sigma_{\{i, j\}} \rangle_{\beta, 0}
  \le 2^{|E|} \cdot \tanh(\beta J)^{d_G(i, j)}.
\]

For `i ≠ j` this is GJ §18.7's high-temperature exponential decay of
the two-point function `⟨σ_iσ_j⟩` in graph distance `d_G(i, j)`. When
`i = j`, `{i, j} = {i}` (singleton) and `d_G(i, i) = 0`, so the bound
specialises to the trivial `⟨σ_i⟩ ≤ 2^{|E|}`.

Proof (combines Steps 566, 568-style counting, and 573):
1. Step 566 reduces to the numerator: `correlation ≤ N`.
2. Each contributing `X` satisfies `G.dist i j ≤ X.card` (Step 573),
   hence `tanh(β·J)^{X.card} ≤ tanh(β·J)^{G.dist i j}` since
   `0 ≤ tanh(β·J) ≤ 1`.
3. `N ≤ |F| · tanh(β·J)^{G.dist i j} ≤ 2^{|E|} · tanh(β·J)^{G.dist i j}`
   since the filter is a subset of `G.edgeFinset.powerset` whose
   cardinality is `2^{|E|}`.

References: GJ §18.7; FV §3.7.3 eq. (3.46), p. 117 (2017 ed.). -/
theorem correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh_pow_dist
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.tanh (β * J) ^ G.dist i j := by
  classical
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have htanh_le_one : Real.tanh (β * J) ≤ 1 := (Real.tanh_lt_one _).le
  have htanh_pow_nn : 0 ≤ Real.tanh (β * J) ^ G.dist i j := pow_nonneg htanh_nn _
  -- Step 566: correlation ≤ N
  have h_step1 := correlation_high_temp_h_zero_le_numerator
    G J β hβJ ({i, j} : Finset ι)
  -- Step 2: each X in numerator filter has tanh^|X| ≤ tanh^{G.dist i j}
  set F : Finset (Finset (Sym2 ι)) :=
    G.edgeFinset.powerset.filter (fun X' : Finset (Sym2 ι) => ∀ v : ι,
      Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
            + (X'.filter (v ∈ ·)).card)) with hF_def
  have h_term_le : ∀ X ∈ F, Real.tanh (β * J) ^ X.card
      ≤ Real.tanh (β * J) ^ G.dist i j := by
    intro X hX
    have h_dist_le : G.dist i j ≤ X.card :=
      evenSubgraph_pair_boundary_dist_le G i j X hX
    exact pow_le_pow_of_le_one htanh_nn htanh_le_one h_dist_le
  -- Step 3: ∑ ≤ |F| · tanh^{G.dist i j} ≤ 2^|E| · tanh^{G.dist i j}
  have h_sum_le_card_smul : (∑ X ∈ F, Real.tanh (β * J) ^ X.card)
      ≤ F.card • (Real.tanh (β * J) ^ G.dist i j) :=
    Finset.sum_le_card_nsmul F _ _ h_term_le
  have h_F_subset : F ⊆ G.edgeFinset.powerset := Finset.filter_subset _ _
  have h_F_card_le : F.card ≤ G.edgeFinset.powerset.card :=
    Finset.card_le_card h_F_subset
  have h_powerset_card : G.edgeFinset.powerset.card = 2 ^ G.edgeFinset.card :=
    Finset.card_powerset _
  have h_F_card_le_two_pow : F.card ≤ 2 ^ G.edgeFinset.card := by
    rw [← h_powerset_card]; exact h_F_card_le
  have h_smul_eq : F.card • (Real.tanh (β * J) ^ G.dist i j) =
      (F.card : ℝ) * Real.tanh (β * J) ^ G.dist i j := by
    rw [nsmul_eq_mul]
  rw [h_smul_eq] at h_sum_le_card_smul
  have h_smul_le : (F.card : ℝ) * Real.tanh (β * J) ^ G.dist i j
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.tanh (β * J) ^ G.dist i j := by
    apply mul_le_mul_of_nonneg_right _ htanh_pow_nn
    exact_mod_cast h_F_card_le_two_pow
  exact h_step1.trans (h_sum_le_card_smul.trans h_smul_le)

end IsingModel
