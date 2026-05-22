import IsingModel.Conditioning.HighTempClosed.ClosedForm

/-!
# High-temperature log bounds

Mechanical child split from `Conditioning/HighTempClosed.lean`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **log Z high-temperature decomposition (GJ §18.3 / FV (3.45))**:
under `0 ≤ β·J`,
`log Z(G; J, 0, β) = |ι| · log 2 + |E| · log(cosh βJ) + log(∑_{X ⊆ E, even-deg} tanh(βJ)^|X|)`.
Direct corollary of FV (3.45) closed form (Step 283) by taking
logarithms; requires the even-subgraph sum to be positive (Step 295). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      = (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ G.edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ι) =>
                  ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  have hpref_pos : (0 : ℝ) <
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos (Real.cosh_pos _) _)
  have hsum_pos : 0 < ∑ X ∈ G.edgeFinset.powerset.filter
      (fun X : Finset (Sym2 ι) =>
        ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
      Real.tanh (β * J) ^ X.card :=
    lt_of_lt_of_le zero_lt_one (one_le_sum_pow_tanh_even_subgraph G J β hβJ)
  rw [Real.log_mul hpref_pos.ne' hsum_pos.ne']
  rw [Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]

/-- **Sharper Z high-temperature upper bound (FV (3.45))**: under
`0 ≤ β·J`,
`Z(G; J, 0, β) ≤ 2^|ι| · exp(β·J·|E|)`.

Tighter than `partitionFunction_high_temp_expansion_h_zero_upper_bound`
(`≤ 2^(|ι|+|E|)·cosh^|E|`) at small `β·J`. Uses
`sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow` (Step 392)
to bound the even-subgraph sum by `(1 + tanh(β·J))^|E|`, then collapses
`cosh^|E| · (1 + tanh)^|E| = (cosh + sinh)^|E| = exp(β·J)^|E|` via
`Real.cosh_add_sinh`. -/
theorem partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  have hsum_le := sum_pow_tanh_even_subgraph_le_one_plus_tanh_pow G J β hβJ
  have hcommon_nn :
      0 ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Real.cosh_pos _).le _)
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hcosh_one_plus_tanh : Real.cosh (β * J) * (1 + Real.tanh (β * J))
      = Real.exp (β * J) := by
    have hne : Real.cosh (β * J) ≠ 0 := hcosh_pos.ne'
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    exact Real.cosh_add_sinh (β * J)
  calc (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card
      ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        (1 + Real.tanh (β * J)) ^ G.edgeFinset.card :=
        mul_le_mul_of_nonneg_left hsum_le hcommon_nn
    _ = (2 : ℝ) ^ Fintype.card ι *
          (Real.cosh (β * J) * (1 + Real.tanh (β * J))) ^ G.edgeFinset.card := by
        rw [mul_pow, mul_assoc]
    _ = (2 : ℝ) ^ Fintype.card ι * Real.exp (β * J) ^ G.edgeFinset.card := by
        rw [hcosh_one_plus_tanh]
    _ = (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **Z high-temperature upper bound from FV (3.45)**: under `0 ≤ β·J`,
`Z(G; J, 0, β) ≤ 2^(|ι|+|E|) · (cosh(βJ))^|E|`.

Pair to `partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286): the FV (3.45) closed form Z = 2^|ι|·cosh^|E|·S with
`1 ≤ S ≤ 2^|E|` (Steps 295/319) gives matching bounds. -/
theorem partitionFunction_high_temp_expansion_h_zero_upper_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
        Real.cosh (β * J) ^ G.edgeFinset.card := by
  rw [partitionFunction_high_temp_expansion_h_zero_closed]
  have hsum_le := sum_pow_tanh_even_subgraph_le_two_pow G J β hβJ
  have hcommon_nn :
      0 ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Real.cosh_pos _).le _)
  calc (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        ∑ X ∈ G.edgeFinset.powerset.filter
          (fun X => ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card
      ≤ (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card *
        (2 : ℝ) ^ G.edgeFinset.card :=
        mul_le_mul_of_nonneg_left hsum_le hcommon_nn
    _ = (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
          Real.cosh (β * J) ^ G.edgeFinset.card := by
        rw [pow_add]; ring

/-- **Sharper log Z high-temperature upper bound (FV (3.45))**: under
`0 ≤ β·J`,
`log Z(G; J, 0, β) ≤ |ι| · log 2 + β·J·|E|`.

Direct from `partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`
(Step 393) by taking logarithms. Globally tighter than the
`(|ι|+|E|) log 2 + |E| · log cosh(βJ)` form derivable from the cosh
upper bound (Step 320). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
  have hZ_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ
  have hZ_pos := partitionFunction_pos G ⟨J, 0, β⟩
  have hubound_pos : (0 : ℝ) <
      (2 : ℝ) ^ Fintype.card ι * Real.exp (β * J * G.edgeFinset.card) :=
    mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  calc Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ Real.log ((2 : ℝ) ^ Fintype.card ι *
            Real.exp (β * J * G.edgeFinset.card)) :=
        (Real.log_le_log_iff hZ_pos hubound_pos).mpr hZ_ub
    _ = Real.log ((2 : ℝ) ^ Fintype.card ι)
        + Real.log (Real.exp (β * J * G.edgeFinset.card)) :=
        Real.log_mul (pow_pos (by norm_num) _).ne' (Real.exp_pos _).ne'
    _ = (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
        rw [Real.log_pow, Real.log_exp]

/-- **Sharper log Z high-temperature sandwich (FV (3.45))**: under
`0 ≤ β·J`,
`|ι| · log 2 + |E| · log cosh(β·J) ≤ log Z ≤ |ι| · log 2 + β·J·|E|`.

Combines `log_partitionFunction_high_temp_expansion_h_zero_closed`
(decomposition; lower part via `1 ≤ ∑ tanh^|X|`) with the sharper
exp upper bound (Step 403). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
  refine ⟨?_, log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ⟩
  -- log Z ≥ |ι| log 2 + |E| log cosh(βJ) from
  -- log Z = |ι| log 2 + |E| log cosh + log(∑) and log(∑) ≥ 0.
  rw [log_partitionFunction_high_temp_expansion_h_zero_closed G J β hβJ]
  have h_one_le_sum := one_le_sum_pow_tanh_even_subgraph G J β hβJ
  have hlog_nn : 0 ≤ Real.log
      (∑ X ∈ G.edgeFinset.powerset.filter
          (fun X : Finset (Sym2 ι) =>
            ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
          Real.tanh (β * J) ^ X.card) :=
    Real.log_nonneg h_one_le_sum
  linarith

/-- **log Z deviation sandwich**: under `0 ≤ β·J`,
`0 ≤ log Z - |ι|·log 2 ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    0 ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2
      ≤ β * J * G.edgeFinset.card := by
  obtain ⟨h_lb, h_ub⟩ := log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β hβJ
  refine ⟨?_, by linarith⟩
  -- log Z ≥ |ι| log 2 from |ι| log 2 + |E|·log cosh(βJ) ≤ log Z and log cosh ≥ 0.
  have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
  have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
    Real.log_nonneg hcosh_ge
  have hedge_nn : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
  have h_corr_nn : 0 ≤ (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) :=
    mul_nonneg hedge_nn hlog_nn
  linarith

/-- **log Z strict deviation under non-trivial high-temperature**:
under `0 < β·J` and `0 < |E|`, `0 < log Z - |ι|·log 2`.

Strict version of the log Z lower bound. Follows from
`|ι|·log 2 + |E|·log cosh(β·J) ≤ log Z` plus `log cosh(β·J) > 0`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hEpos : 0 < G.edgeFinset.card) :
    0 < Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 := by
  obtain ⟨h_lb, _⟩ := log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β hβJ.le
  have hcosh_gt : 1 < Real.cosh (β * J) := by
    rw [show (1 : ℝ) = Real.cosh 0 from Real.cosh_zero.symm]
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_zero, abs_of_pos hβJ]
    exact hβJ
  have hlog_pos : 0 < Real.log (Real.cosh (β * J)) := Real.log_pos hcosh_gt
  have hE_pos : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast hEpos
  have h_corr_pos : 0 < (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) :=
    mul_pos hE_pos hlog_pos
  linarith

/-- **Sharper log Z complete-summary exp bundle**: under `0 ≤ β·J`,
single statement bundling sharper sandwich + trivial-slice values:
  1. `|ι|·log 2 + |E|·log cosh(β·J) ≤ log Z` (lower),
  2. `log Z ≤ |ι|·log 2 + β·J·|E|` (sharper exp upper),
  3. `log Z⟨0, 0, β⟩ = |ι|·log 2` (J = 0 trivial slice),
  4. `log Z⟨J, 0, 0⟩ = |ι|·log 2` (β = 0 trivial slice). -/
theorem log_partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card ∧
    Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp
      G J β hβJ).1
  · exact log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
      G J β hβJ
  · rw [partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero,
        Real.log_pow]
  · rw [partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero,
        Real.log_pow]

/-- **Sharper freeEnergy high-temperature upper bound (FV (3.45))**: under
`0 < |ι|` and `0 ≤ β·J`,
`f(G; J, 0, β) ≤ log 2 + β·J·|E|/|ι|`.

Globally tighter than `freeEnergy_high_temp_h_zero_upper_bound`:
`log(2·cosh(β·J)) = log 2 + log cosh(β·J)` and `log cosh(β·J) ≤ β·J`
(since `cosh(β·J) ≤ exp(β·J)`), so this bound is sharper. Direct
corollary of `partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`
(Step 393) by taking logarithms and dividing by `|ι|`. -/
theorem freeEnergy_high_temp_h_zero_upper_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι := by
  have hZ_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp G J β hβJ
  have hZ_pos := partitionFunction_pos G ⟨J, 0, β⟩
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hne
  have hubound_pos : (0 : ℝ) <
      (2 : ℝ) ^ Fintype.card ι * Real.exp (β * J * G.edgeFinset.card) :=
    mul_pos (pow_pos (by norm_num) _) (Real.exp_pos _)
  have hlog : Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card := by
    calc Real.log (partitionFunction G ⟨J, 0, β⟩)
        ≤ Real.log ((2 : ℝ) ^ Fintype.card ι *
              Real.exp (β * J * G.edgeFinset.card)) :=
          (Real.log_le_log_iff hZ_pos hubound_pos).mpr hZ_ub
      _ = Real.log ((2 : ℝ) ^ Fintype.card ι)
          + Real.log (Real.exp (β * J * G.edgeFinset.card)) :=
          Real.log_mul (pow_pos (by norm_num) _).ne' (Real.exp_pos _).ne'
      _ = (Fintype.card ι : ℝ) * Real.log 2
          + β * J * G.edgeFinset.card := by
          rw [Real.log_pow, Real.log_exp]
  unfold freeEnergy
  rw [show ((Fintype.card ι : ℝ)⁻¹ * Real.log (partitionFunction G ⟨J, 0, β⟩))
        = Real.log (partitionFunction G ⟨J, 0, β⟩) / Fintype.card ι by
        rw [div_eq_inv_mul]]
  rw [div_le_iff₀ hcard_pos, add_mul, mul_comm (Real.log 2) _,
      div_mul_cancel₀ _ hcard_pos.ne']
  linarith


end IsingModel
