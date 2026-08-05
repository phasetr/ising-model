import IsingModel.Conditioning.CorrelationRates.TanhBounds

/-!
# Correlation rates split — partition/free-energy summaries and tanh lower bounds

Part of the split high-temperature correlation-rates layer (Issue #1850).
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Z complete-summary bundle at h = 0**: under `0 ≤ β·J`, single
statement bundling all known §18.3 properties of `Z` at `h = 0`:
  1. `2^|ι| · cosh(βJ)^|E| ≤ Z` (lower bound from FV (3.45)),
  2. `Z ≤ 2^(|ι|+|E|) · cosh(βJ)^|E|` (upper bound from FV (3.45)),
  3. `Z⟨0, 0, β⟩ = 2^|ι|` (consistency at trivial slice `J = 0`),
  4. `Z⟨J, 0, 0⟩ = 2^|ι|` (consistency at trivial slice `β = 0`).
Useful as a single import for downstream analytic / asymptotic
arguments that need both bounds and trivial-slice values. -/
theorem partitionFunction_high_temp_expansion_h_zero_complete_summary
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ ∧
      partitionFunction G ⟨J, 0, β⟩
        ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
            Real.cosh (β * J) ^ G.edgeFinset.card ∧
      partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Fintype.card ι ∧
      partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        = (2 : ℝ) ^ Fintype.card ι :=
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β,
   partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J⟩

/-- **freeEnergy complete-summary bundle at h = 0**: under `0 < |ι|` and
`0 ≤ β·J`, single statement bundling all known §18.3 properties of
`f` at `h = 0`:
  1. `log 2 + (|E|/|ι|) log cosh(βJ) ≤ f` (lower bound),
  2. `f ≤ log 2 + (|E|/|ι|) log(2·cosh(βJ))` (upper bound),
  3. `f⟨0, 0, β⟩ = log 2` (consistency at trivial slice `J = 0`,
     specialisation of `freeEnergy_J_zero` at `h = 0`),
  4. `f⟨J, 0, 0⟩ = log 2` (consistency at trivial slice `β = 0`).
Useful as a single import for downstream analytic / asymptotic
arguments that need both bounds and trivial-slice values. -/
theorem freeEnergy_high_temp_h_zero_complete_summary
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
      freeEnergy G ⟨J, 0, β⟩
        ≤ Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) ∧
      freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
      freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound G J β hβJ hne,
   by
     have := freeEnergy_J_zero G (0 : ℝ) β hne
     simpa [mul_zero, Real.cosh_zero] using this,
   freeEnergy_beta_zero G J 0 hne⟩

/-- **Single-edge subset is in the FV (3.46) numerator filter at `A = {i, j}`**:
for `i ≠ j` and an edge `e = s(i, j) ∈ G.edgeSet`, the singleton
`{e} ⊆ G.edgeFinset` satisfies the parity predicate: at `v = i, j`,
`1_{v ∈ A} + 1 = 2` is even; at any other `v`, `0 + 0 = 0` is even.
This is the key combinatorial fact behind the single-edge lower bound
`tanh(βJ) ≤ ∑_{X : ∂X = {i,j}} tanh^|X|`. -/
theorem singleton_edge_mem_high_temp_pair_filter
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    ({s(i, j)} : Finset (Sym2 ι)) ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)) := by
  classical
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · -- {s(i, j)} ⊆ G.edgeFinset
    rw [Finset.mem_powerset, Finset.singleton_subset_iff]
    exact (SimpleGraph.mem_edgeFinset).mpr he
  · -- parity predicate holds for every v
    intro v
    by_cases hv : v ∈ ({i, j} : Finset ι)
    · -- v ∈ {i, j}: 1 + 1 = 2 is even
      rw [if_pos hv]
      have : ({s(i, j)} : Finset (Sym2 ι)).filter (v ∈ ·) = {s(i, j)} := by
        rw [Finset.filter_singleton, if_pos]
        rcases Finset.mem_insert.mp hv with hi | hj
        · subst hi; exact Sym2.mem_mk_left _ _
        · rw [Finset.mem_singleton] at hj; subst hj; exact Sym2.mem_mk_right _ _
      rw [this, Finset.card_singleton]; exact ⟨1, rfl⟩
    · -- v ∉ {i, j}: 0 + 0 = 0 is even
      rw [if_neg hv]
      have : ({s(i, j)} : Finset (Sym2 ι)).filter (v ∈ ·) = ∅ := by
        rw [Finset.filter_singleton, if_neg]
        intro hv_in
        apply hv
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact (Sym2.mem_iff.mp hv_in)
      rw [this, Finset.card_empty]; exact ⟨0, rfl⟩

/-- **Pair correlation single-edge tanh lower bound from the free-boundary parity formula.**
under `0 ≤ β·J` and an edge `s(i, j) ∈ G.edgeSet`,
`⟨σ_iσ_j⟩^{⟨J,0,β⟩} ≥ tanh(β·J) / 2^|E|`.

The single edge `e = s(i, j)` contributes `tanh(β·J)` to the project-derived
numerator; the denominator is bounded above by `2^|E|`
(Step 319). Provides a quantitative non-trivial lower bound: at high
temperature, the pair correlation between adjacent sites does not
vanish faster than `tanh(βJ) / 2^|E|`. Compare the two-point representations and bounds in
FV Exercises 3.23--3.25; this coarse adjacent-edge bound is not stated there. -/
theorem correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card
      ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) := by
  classical
  rw [correlation_high_temp_expansion_h_zero_closed]
  -- Goal: tanh / 2^|E| ≤ N / D
  set N : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι,
        Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
              + (X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hN_def
  set D : ℝ := ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card with hD_def
  have h_tanh_nn : 0 ≤ Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg
      (Real.sinh_nonneg_iff.mpr hβJ) (Real.cosh_pos _).le
  have h_one_le_D : 1 ≤ D := one_le_sum_pow_tanh_even_subgraph G J β hβJ
  have h_D_pos : 0 < D := lt_of_lt_of_le zero_lt_one h_one_le_D
  have h_D_le : D ≤ (2 : ℝ) ^ G.edgeFinset.card :=
    sum_pow_tanh_even_subgraph_le_two_pow G J β hβJ
  have h_tanh_le_N : Real.tanh (β * J) ≤ N := by
    -- Singleton edge {s(i,j)} contributes tanh^1 to N; other terms ≥ 0.
    have h_mem := singleton_edge_mem_high_temp_pair_filter G i j hij he
    have h_term_eq : Real.tanh (β * J) ^ ({s(i, j)} : Finset (Sym2 ι)).card =
        Real.tanh (β * J) := by rw [Finset.card_singleton, pow_one]
    have h_terms_nn : ∀ X ∈ G.edgeFinset.powerset.filter
        (fun X : Finset (Sym2 ι) => ∀ v : ι,
          Even ((if v ∈ ({i, j} : Finset ι) then (1 : ℕ) else 0)
                + (X.filter (v ∈ ·)).card)),
        0 ≤ Real.tanh (β * J) ^ X.card := fun X _ => pow_nonneg h_tanh_nn _
    calc Real.tanh (β * J)
        = Real.tanh (β * J) ^ ({s(i, j)} : Finset (Sym2 ι)).card := h_term_eq.symm
      _ ≤ N := Finset.single_le_sum (f := fun X : Finset (Sym2 ι) =>
                Real.tanh (β * J) ^ X.card) h_terms_nn h_mem
  -- tanh / 2^|E| ≤ tanh / D ≤ N / D
  have h_step1 : Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card
      ≤ Real.tanh (β * J) / D :=
    div_le_div_of_nonneg_left h_tanh_nn h_D_pos h_D_le
  have h_step2 : Real.tanh (β * J) / D ≤ N / D :=
    div_le_div_of_nonneg_right h_tanh_le_N h_D_pos.le
  exact h_step1.trans h_step2

/-- **Pair correlation strict positivity from the project-derived adjacent-edge bound.**
under `0 < β·J` and an edge `s(i, j) ∈ G.edgeSet`,
`0 < ⟨σ_iσ_j⟩^{⟨J,0,β⟩}`.

Direct from `correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges`
(Step 386) and `Real.tanh_pos` at `0 < β·J`. Strengthens GKS-I in this
specific setting: the pair correlation between adjacent sites is
*strictly* positive at any non-trivial high-temperature parameters. -/
theorem correlation_high_temp_h_zero_at_pair_pos_of_edge
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    0 < correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) := by
  have h_tanh_pos : 0 < Real.tanh (β * J) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hβJ) (Real.cosh_pos _)
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ G.edgeFinset.card := pow_pos (by norm_num) _
  have h_lb_pos : 0 < Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card :=
    div_pos h_tanh_pos h_pow_pos
  exact lt_of_lt_of_le h_lb_pos
    (correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
      G J β hβJ.le i j hij he)

/-- **Ferromagnetic specialization of the project-derived single-edge tanh lower bound.**
under `0 ≤ J, 0 < β` and an edge `s(i, j) ∈ G.edgeSet`,
`⟨σ_iσ_j⟩^{⟨J,0,β⟩} ≥ tanh(β·J) / 2^|E|`. Bridges the
`Ferromagnetic`-style hypotheses with
`correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges` via
`mul_nonneg hβ.le hJ`. -/
theorem correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    Real.tanh (β * J) / (2 : ℝ) ^ G.edgeFinset.card
      ≤ correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) :=
  correlation_high_temp_h_zero_at_pair_ge_tanh_div_two_pow_edges
    G J β (mul_nonneg hβ.le hJ) i j hij he

/-- **Ferromagnetic specialization of project-derived adjacent-edge strict positivity.**
under `0 < J, 0 < β` and an edge `s(i, j) ∈ G.edgeSet`,
`0 < ⟨σ_iσ_j⟩^{⟨J,0,β⟩}`. Bridges strict-ferromagnetic hypotheses with
`correlation_high_temp_h_zero_at_pair_pos_of_edge` via `mul_pos hβ hJ`. -/
theorem correlation_high_temp_h_zero_at_pair_pos_of_edge_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (i j : ι) (hij : i ≠ j) (he : s(i, j) ∈ G.edgeSet) :
    0 < correlation G ⟨J, 0, β⟩ ({i, j} : Finset ι) :=
  correlation_high_temp_h_zero_at_pair_pos_of_edge
    G J β (mul_pos hβ hJ) i j hij he


end IsingModel
