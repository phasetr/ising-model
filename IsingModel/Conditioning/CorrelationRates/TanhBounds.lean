import IsingModel.Conditioning.CorrelationRates.ExpRate

/-!
# Correlation rates split — tanh pair bound, special values, and singleton variants

Part of the split high-temperature correlation-rates layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pair correlation weak upper bound `≤ 2^|E| · tanh(β·J)` at `h = 0`
(GJ §18.7 weak upper bound)**: under `0 ≤ β·J`,
\[
\langle \sigma_i \sigma_j \rangle_{\beta, 0}
  \le 2^{|E|} \cdot \tanh(\beta J).
\]

A weak quantitative version of GJ §18.7 / FV §3.7.3 — *not* yet
exponential decay in graph distance, but the natural companion to the
single-edge tanh **lower** bound `tanh / 2^|E| ≤ ⟨σ_iσ_j⟩` (Step 386).

Proof:
1. Step 566 reduces to numerator-only: `correlation ≤ N`.
2. Each contributing `X` has `1 ≤ |X|` (Step 567), so
   `tanh(β·J)^|X| ≤ tanh(β·J)^1 = tanh(β·J)` since
   `0 ≤ tanh(β·J) ≤ 1` (`Real.tanh_lt_one`).
3. `N ≤ |filter| · tanh(β·J) ≤ 2^|E| · tanh(β·J)` since the filter is
   a subset of `G.edgeFinset.powerset` whose cardinality is `2^|E|`.

References: GJ §18.7; FV §3.7.3 eq. (3.46), p. 117 (2017 ed.). -/
theorem correlation_high_temp_h_zero_at_pair_le_two_pow_edges_mul_tanh
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.tanh (β * J) := by
  classical
  have htanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have htanh_le_one : Real.tanh (β * J) ≤ 1 := (Real.tanh_lt_one _).le
  -- Step 566: correlation ≤ N
  have h_step1 := correlation_high_temp_h_zero_le_numerator
    G J β hβJ ({i, j} : Finset ι)
  -- Step 2: each X in numerator filter satisfies |X| ≥ 1, so tanh^|X| ≤ tanh
  set F : Finset (Finset (Sym2 ι)) :=
    G.edgeFinset.powerset.filter (fun X : Finset (Sym2 ι) => ∀ v : ι,
      Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
            + (X.filter (v ∈ ·)).card)) with hF_def
  have h_term_le : ∀ X ∈ F, Real.tanh (β * J) ^ X.card ≤ Real.tanh (β * J) := by
    intro X hX
    have hX_card_pos : 1 ≤ X.card :=
      evenSubgraph_pair_boundary_card_pos G i j X hX
    have h_pow_le : Real.tanh (β * J) ^ X.card ≤ Real.tanh (β * J) ^ 1 :=
      pow_le_pow_of_le_one htanh_nn htanh_le_one hX_card_pos
    rwa [pow_one] at h_pow_le
  -- Step 3: ∑ over F of tanh^|X| ≤ |F| · tanh ≤ 2^|E| · tanh
  have h_sum_le_card_smul : (∑ X ∈ F, Real.tanh (β * J) ^ X.card)
      ≤ F.card • Real.tanh (β * J) :=
    Finset.sum_le_card_nsmul F _ _ h_term_le
  -- |F| ≤ |powerset| = 2^|E|
  have h_F_subset : F ⊆ G.edgeFinset.powerset := Finset.filter_subset _ _
  have h_F_card_le : F.card ≤ G.edgeFinset.powerset.card :=
    Finset.card_le_card h_F_subset
  have h_powerset_card : G.edgeFinset.powerset.card = 2 ^ G.edgeFinset.card :=
    Finset.card_powerset _
  have h_F_card_le_two_pow : F.card ≤ 2 ^ G.edgeFinset.card := by
    rw [← h_powerset_card]; exact h_F_card_le
  -- Convert nsmul to mul
  have h_smul_eq : F.card • Real.tanh (β * J) =
      (F.card : ℝ) * Real.tanh (β * J) := by
    rw [nsmul_eq_mul]
  rw [h_smul_eq] at h_sum_le_card_smul
  have h_smul_le : (F.card : ℝ) * Real.tanh (β * J)
      ≤ (2 : ℝ) ^ G.edgeFinset.card * Real.tanh (β * J) := by
    apply mul_le_mul_of_nonneg_right _ htanh_nn
    exact_mod_cast h_F_card_le_two_pow
  -- Combine
  exact h_step1.trans (h_sum_le_card_smul.trans h_smul_le)

/-- **Z₂ symmetry of correlations at h = 0 from FV (3.46) + handshake**:
for any `A : Finset ι` of odd cardinality, `correlation G ⟨J, 0, β⟩ A = 0`.

A direct combinatorial proof going through:
1. `correlation_high_temp_expansion_h_zero_closed` (FV (3.46), Step 284)
2. `high_temp_numerator_filter_eq_empty_of_odd_card` (Step 297) — the
   numerator filter is *literally empty* by edge-vertex handshake.
3. `Finset.sum_empty`: empty sum is `0`; `0 / x = 0`.

Independent of `correlation_odd_vanish` (the standard spin-flip Z₂
argument). Provides a fully closed-form / combinatorial alternative. -/
theorem correlation_high_temp_h_zero_odd_card_eq_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (A : Finset ι) (hA_odd : Odd A.card) :
    correlation G ⟨J, 0, β⟩ A = 0 := by
  rw [correlation_high_temp_expansion_h_zero_closed,
      high_temp_numerator_filter_eq_empty_of_odd_card G A hA_odd,
      Finset.sum_empty, zero_div]

/-- **Pair correlation nonnegativity at h = 0 from FV (3.46)**: under
`0 ≤ β·J`, `0 ≤ ⟨σ_i σ_j⟩_{β,0}` for any `i, j : ι`.
Direct specialization of `correlation_high_temp_h_zero_nonneg` (Step 293)
at A = {i, j}. -/
theorem correlation_high_temp_h_zero_at_pair_nonneg
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) :=
  correlation_high_temp_h_zero_nonneg G J β hβJ {i, j}

/-- **Pair correlation ≤ 1 at h = 0**: `⟨σ_i σ_j⟩_{β,0} ≤ 1`.
Specialization of the general `correlation_le_one`. -/
theorem correlation_high_temp_h_zero_at_pair_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i j : ι) :
    correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  correlation_le_one G ⟨J, 0, β⟩ {i, j}

/-- **Pair correlation sandwich at h = 0**: under `0 ≤ β·J`,
`0 ≤ ⟨σ_i σ_j⟩_{β,0} ≤ 1`. Combines Steps 340 and 341. -/
theorem correlation_high_temp_h_zero_at_pair_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (i j : ι) :
    0 ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ∧
      correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) ≤ 1 :=
  ⟨correlation_high_temp_h_zero_at_pair_nonneg G J β hβJ i j,
   correlation_high_temp_h_zero_at_pair_le_one G J β i j⟩

/-- **Pair correlation at J = 0, h = 0 vanishes**: at `J = 0, h = 0`,
`⟨σ_i σ_j⟩ = 0` for any `i, j : ι`. Direct from `correlation_J_zero`
which gives `⟨σ_A⟩ = tanh(β · h)^|A|`; at `h = 0` and `A = {i, j}`
(nonempty), this gives `0`. -/
theorem correlation_high_temp_h_zero_at_pair_J_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (i j : ι) :
    correlation G ⟨0, 0, β⟩ ({i, j} : Finset ι) = 0 := by
  classical
  rw [correlation_J_zero, mul_zero, Real.tanh_zero]
  have hcard_pos : 0 < ({i, j} : Finset ι).card := by
    rw [Finset.card_pos]; exact ⟨i, by simp⟩
  exact zero_pow hcard_pos.ne'

/-- **Pair correlation at β = 0, h = 0 vanishes**: at `β = 0, h = 0`,
`⟨σ_i σ_j⟩ = 0` for any `i, j : ι`. Direct from
`correlation_beta_zero_vanish_of_nonempty_A`. -/
theorem correlation_high_temp_h_zero_at_pair_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (i j : ι) :
    correlation G ⟨J, 0, 0⟩ ({i, j} : Finset ι) = 0 := by
  refine correlation_beta_zero_vanish_of_nonempty_A G J 0 {i, j} ?_
  exact ⟨i, by simp⟩

/-- **Singleton magnetization at J = 0, h = 0 vanishes**: at `J = 0, h = 0`,
`⟨σ_i⟩ = 0`. -/
theorem correlation_high_temp_h_zero_at_singleton_J_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (β : ℝ) (i : ι) :
    correlation G ⟨0, 0, β⟩ ({i} : Finset ι) = 0 := by
  classical
  rw [correlation_J_zero, mul_zero, Real.tanh_zero, Finset.card_singleton,
      pow_one]

/-- **Singleton magnetization at β = 0, h = 0 vanishes**: at `β = 0, h = 0`,
`⟨σ_i⟩ = 0`. -/
theorem correlation_high_temp_h_zero_at_singleton_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J : ℝ) (i : ι) :
    correlation G ⟨J, 0, 0⟩ ({i} : Finset ι) = 0 :=
  correlation_beta_zero_vanish_of_nonempty_A G J 0 {i} ⟨i, by simp⟩

/-- **Singleton magnetization absolute bound at h = 0 from FV (3.46)**:
`|⟨σ_i⟩_{β,0}| ≤ 1`. Combined with Step 331 (`⟨σ_i⟩ = 0`), this is
trivially `0 ≤ 1` but useful as a conventional restatement. -/
theorem correlation_high_temp_h_zero_at_singleton_abs_le_one
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (i : ι) :
    |correlation G ⟨J, 0, β⟩ ({i} : Finset ι)| ≤ 1 :=
  abs_correlation_le_one G ⟨J, 0, β⟩ {i}


end IsingModel
