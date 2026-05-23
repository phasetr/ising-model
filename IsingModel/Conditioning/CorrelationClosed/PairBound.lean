import IsingModel.Conditioning.CorrelationClosed.EvenBoundarySwapDist

/-!
# Correlation closed form split — pair correlation high-temperature distance bound

Part of the split `IsingModel.Conditioning.CorrelationClosed` development.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
