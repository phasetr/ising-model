import IsingModel.Conditioning.CorrelationClosed.Handshake

/-!
# Correlation closed form split — Z2 symmetry: odd-cardinality numerator vanishes

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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


end IsingModel
