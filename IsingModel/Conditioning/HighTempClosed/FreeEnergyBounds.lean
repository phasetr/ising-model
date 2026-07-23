import IsingModel.Conditioning.HighTempClosed.PartitionRatios

/-!
# High-temperature free energy bounds

Mechanical child split from `Conditioning/HighTempClosed.lean`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **freeEnergy high-temperature upper bound from FV (3.45)**: under
`0 < |ι|` and `0 ≤ β·J`,
`freeEnergy(G; J, 0, β) ≤ log 2 + (|E|/|ι|) · log(2 · cosh(β·J))`.

Pair to `freeEnergy_high_temp_h_zero_lower_bound` (Step 288).
Direct from `partitionFunction_high_temp_expansion_h_zero_upper_bound`
(Step 320) by taking logs and dividing by `|ι|`. -/
theorem freeEnergy_high_temp_h_zero_upper_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) := by
  have hZ_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound G J β hβJ
  have hZ_pos := partitionFunction_pos G ⟨J, 0, β⟩
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hubound_pos : (0 : ℝ) <
      (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
      Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos hcosh_pos _)
  -- Take logs
  have hlog : Real.log (partitionFunction G ⟨J, 0, β⟩) ≤
      Real.log ((2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
        Real.cosh (β * J) ^ G.edgeFinset.card) :=
    Real.log_le_log hZ_pos hZ_ub
  -- Simplify the RHS log
  have hlog_rhs :
      Real.log ((2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
        Real.cosh (β * J) ^ G.edgeFinset.card)
        = ((Fintype.card ι : ℝ) + G.edgeFinset.card) * Real.log 2
          + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast; ring
  rw [hlog_rhs] at hlog
  -- Divide by |ι| > 0
  unfold freeEnergy
  have hι_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  rw [show (Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
              Real.log (2 * Real.cosh (β * J)))
        = (Fintype.card ι : ℝ)⁻¹ *
          (((Fintype.card ι : ℝ) + G.edgeFinset.card) * Real.log 2
            + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))) from by
      rw [Real.log_mul (by norm_num) hcosh_pos.ne']
      field_simp; ring]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-- **Z high-temperature sandwich bounds (GJ §18.3 / FV (3.45))**: under
`0 ≤ β·J`,
`2^|ι| · (cosh βJ)^|E| ≤ Z(G; J, 0, β) ≤ 2^(|ι|+|E|) · (cosh βJ)^|E|`.
Combines `partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286) and `partitionFunction_high_temp_expansion_h_zero_upper_bound`
(Step 320) into a single sandwich statement. -/
theorem partitionFunction_high_temp_expansion_h_zero_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩
    ∧ partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
          Real.cosh (β * J) ^ G.edgeFinset.card :=
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound G J β hβJ⟩

omit [DecidableEq ι] in
/-- **Z high-temp bounds consistency**: the FV (3.45) lower bound is
always at most the upper bound:
`2^|ι| · cosh^|E| ≤ 2^(|ι|+|E|) · cosh^|E|`. Trivial sanity check. -/
theorem partitionFunction_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) :
    (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ (2 : ℝ) ^ (Fintype.card ι + G.edgeFinset.card) *
          Real.cosh (β * J) ^ G.edgeFinset.card := by
  have hpref_nn : 0 ≤
      (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (Real.cosh_pos _).le _)
  rw [show (Fintype.card ι + G.edgeFinset.card : ℕ)
      = Fintype.card ι + G.edgeFinset.card from rfl, pow_add]
  calc (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card
      = 1 * ((2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card) := by ring
    _ ≤ (2 : ℝ) ^ G.edgeFinset.card *
        ((2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card) := by
        apply mul_le_mul_of_nonneg_right _ hpref_nn
        exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    _ = (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ G.edgeFinset.card *
        Real.cosh (β * J) ^ G.edgeFinset.card := by ring

/-- **Free-energy lower bound from FV (3.45)** at zero external field:
under `0 < |ι|` and `0 ≤ β * J`,
`log 2 + (|E|/|ι|) · log(cosh(β·J)) ≤ freeEnergy(G, ⟨J, 0, β⟩)`.

A graph-aware sharpening of `freeEnergy_ge_log_two_cosh` specialized
to `h = 0` (where the latter gives only `log 2`): the edge-density
factor `|E|/|ι|` times `log(cosh(βJ)) ≥ 0` is the high-temperature
cluster-expansion bonus. Direct corollary of
`partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286) by taking logs and dividing by `|ι|`. -/
theorem freeEnergy_high_temp_h_zero_lower_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ := by
  have hZ_lb := partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hZ_lb_pos :
      0 < (2 : ℝ) ^ Fintype.card ι * Real.cosh (β * J) ^ G.edgeFinset.card :=
    mul_pos (pow_pos (by norm_num) _) (pow_pos hcosh_pos _)
  -- Take logs
  have hlog : Real.log ((2 : ℝ) ^ Fintype.card ι *
                          Real.cosh (β * J) ^ G.edgeFinset.card)
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) :=
    Real.log_le_log hZ_lb_pos hZ_lb
  -- Simplify LHS
  have hlog_lhs :
      Real.log ((2 : ℝ) ^ Fintype.card ι *
                  Real.cosh (β * J) ^ G.edgeFinset.card)
        = (Fintype.card ι : ℝ) * Real.log 2
          + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J)) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
  rw [hlog_lhs] at hlog
  -- Divide by |ι| > 0
  unfold freeEnergy
  have hι_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  rw [show (Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
              Real.log (Real.cosh (β * J)))
        = (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * Real.log 2
            + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))) from by
      field_simp]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-- **Sharper f high-temperature sandwich (FV (3.45))**: under
`0 < |ι|` and `0 ≤ β·J`,
`log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f ≤ log 2 + β·J·|E|/|ι|`.

Combines `freeEnergy_high_temp_h_zero_lower_bound` with
`freeEnergy_high_temp_h_zero_upper_bound_exp` (Step 394). Globally
sharper than the cosh-based sandwich at the upper side. -/
theorem freeEnergy_high_temp_h_zero_sandwich_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound_exp G J β hβJ hne⟩

/-- **Ferromagnetic sharper Z complete-summary exp bundle**: under
`0 ≤ J, 0 < β`. -/
theorem partitionFunction_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Fintype.card ι *
        Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ ∧
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) ∧
    partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι ∧
    partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
  partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper log Z complete-summary exp bundle**: under
`0 ≤ J, 0 < β`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (Fintype.card ι : ℝ) * Real.log 2
        + (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
      ≤ Real.log (partitionFunction G ⟨J, 0, β⟩) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card ∧
    Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 :=
  log_partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper Z high-temperature sandwich**: under
`0 ≤ J, 0 < β`,
`2^|ι|·cosh^|E| ≤ Z(G;J,0,β) ≤ 2^|ι|·exp(β·J·|E|)`. Bridges
ferromagnetic hypotheses with Step 407 via `mul_nonneg hβ.le hJ`. -/
theorem partitionFunction_high_temp_expansion_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    (2 : ℝ) ^ Fintype.card ι *
        Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ ∧
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper f high-temperature sandwich**: under
`0 < |ι|`, `0 ≤ J, 0 < β`,
`log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f ≤ log 2 + β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_sandwich_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_sandwich_exp G J β
    (mul_nonneg hβ.le hJ) hne

/-- **Sharper f complete-summary bundle**: under `0 < |ι|` and
`0 ≤ β·J`, single statement bundling sharper sandwich + trivial-slice
values:
  1. `log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f` (lower),
  2. `f ≤ log 2 + β·J·|E|/|ι|` (sharper exp upper),
  3. `f⟨0, 0, β⟩ = log 2` (J = 0 trivial slice),
  4. `f⟨J, 0, 0⟩ = log 2` (β = 0 trivial slice).
Useful as a single import for downstream applications. -/
theorem freeEnergy_high_temp_h_zero_complete_summary_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι ∧
    freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound_exp G J β hβJ hne,
   by
     have := freeEnergy_J_zero G (0 : ℝ) β hne
     simpa [mul_zero, Real.cosh_zero] using this,
   freeEnergy_beta_zero G J 0 hne⟩

/-- **Ferromagnetic sharper f complete-summary exp bundle**: under
`0 < |ι|`, `0 ≤ J, 0 < β`. Bridges via `mul_nonneg hβ.le hJ`. -/
theorem freeEnergy_high_temp_h_zero_complete_summary_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩ ∧
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι ∧
    freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 ∧
    freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) = Real.log 2 :=
  freeEnergy_high_temp_h_zero_complete_summary_exp
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Sharper f deviation bound from `log 2`**: under `0 < |ι|` and
`0 ≤ β·J`, `freeEnergy G ⟨J, 0, β⟩ - log 2 ≤ β·J·|E|/|ι|`.

Direct from `freeEnergy_high_temp_h_zero_upper_bound_exp` (Step 394) by
subtracting `log 2`. Quantitative high-temperature deviation estimate. -/
theorem freeEnergy_high_temp_h_zero_deviation_bound_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have h := freeEnergy_high_temp_h_zero_upper_bound_exp G J β hβJ hne
  linarith

/-- **f quantitative continuity at `J = 0` from deviation bound**:
under `0 ≤ β·J` and `0 < |ι|`,
`|f(J, 0, β) - f(0, 0, β)| ≤ β·J·|E|/|ι|`.

`f(0, 0, β) = log 2` from `freeEnergy_zero_params`, so the bound reads
`f - log 2 ≤ β·J·|E|/|ι|` (Step 420). The reverse direction
`f(0, 0, β) - f ≤ 0 ≤ β·J·|E|/|ι|` follows from the cosh-form lower
bound being non-negative under `0 ≤ β·J` (since `log cosh ≥ 0`).

Quantitative right-continuity: as `β·J → 0+` the deviation vanishes. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_J_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have hf0 : freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
    have := freeEnergy_J_zero G (0 : ℝ) β hne
    simpa [mul_zero, Real.cosh_zero] using this
  rw [hf0]
  -- |f - log 2| ≤ β·J·|E|/|ι|
  have h_upper : freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
    freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne
  have h_lower : Real.log 2 ≤ freeEnergy G ⟨J, 0, β⟩ := by
    -- log 2 ≤ log 2 + (|E|/|ι|)·log cosh(βJ) ≤ f, since log cosh ≥ 0
    have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
      freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne
    have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
    have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
      Real.log_nonneg hcosh_ge
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
    have hedge_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) :=
      div_nonneg (Nat.cast_nonneg _) hcard_pos.le
    have h_corr_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
          Real.log (Real.cosh (β * J)) := mul_nonneg hedge_nn hlog_nn
    linarith
  rw [abs_sub_le_iff]
  refine ⟨h_upper, ?_⟩
  have h_dev_nn : (0 : ℝ) ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
    have hedge_nn : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
    have h_num : 0 ≤ β * J * G.edgeFinset.card := mul_nonneg hβJ hedge_nn
    exact div_nonneg h_num hcard_pos.le
  linarith

/-- **f quantitative continuity at `β = 0` from deviation bound**:
under `0 ≤ β·J` and `0 < |ι|`,
`|f(J, 0, β) - f(J, 0, 0)| ≤ β·J·|E|/|ι|`.

`f(J, 0, 0) = log 2` from `freeEnergy_beta_zero`, so the bound is the
same as `f - log 2 ≤ β·J·|E|/|ι|` plus `0 ≤ f - log 2`. Quantitative
right-continuity at `β = 0`. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  rw [freeEnergy_beta_zero G J 0 hne]
  -- Same proof structure as continuity at J=0 since both trivial slices = log 2
  have h_upper : freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
    freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne
  have h_lower : Real.log 2 ≤ freeEnergy G ⟨J, 0, β⟩ := by
    have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
      freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne
    have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
    have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
      Real.log_nonneg hcosh_ge
    have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
    have hedge_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) :=
      div_nonneg (Nat.cast_nonneg _) hcard_pos.le
    have h_corr_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
          Real.log (Real.cosh (β * J)) := mul_nonneg hedge_nn hlog_nn
    linarith
  rw [abs_sub_le_iff]
  refine ⟨h_upper, ?_⟩
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  have hedge_nn : (0 : ℝ) ≤ G.edgeFinset.card := Nat.cast_nonneg _
  have h_num : 0 ≤ β * J * G.edgeFinset.card := mul_nonneg hβJ hedge_nn
  have h_dev_nn : (0 : ℝ) ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
    div_nonneg h_num hcard_pos.le
  linarith

/-- **Ferromagnetic f continuity at `J = 0`**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `|f(J,0,β) - f(0,0,β)| ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_J_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_continuity_at_J_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic f continuity at `β = 0`**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `|f(J,0,β) - f(J,0,0)| ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_continuity_at_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    |freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_continuity_at_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **f deviation sandwich**: under `0 ≤ β·J` and `0 < |ι|`,
`0 ≤ f - log 2 ≤ β·J·|E|/|ι|`.

Combines the lower bound `log 2 ≤ f` (from Step 288 + `cosh ≥ 1`) with
the deviation bound `f - log 2 ≤ β·J·|E|/|ι|` (Step 420). Pins the
free-energy deviation from the trivial slice in a tight non-negative
linear interval. -/
theorem freeEnergy_high_temp_h_zero_deviation_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    0 ≤ freeEnergy G ⟨J, 0, β⟩ - Real.log 2 ∧
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  refine ⟨?_, freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne⟩
  have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
        Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
    freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne
  have hcosh_ge : 1 ≤ Real.cosh (β * J) := Real.one_le_cosh _
  have hlog_nn : 0 ≤ Real.log (Real.cosh (β * J)) :=
    Real.log_nonneg hcosh_ge
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  have hedge_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) :=
    div_nonneg (Nat.cast_nonneg _) hcard_pos.le
  have h_corr_nn : 0 ≤ ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
        Real.log (Real.cosh (β * J)) := mul_nonneg hedge_nn hlog_nn
  linarith

/-- **Ferromagnetic f deviation sandwich**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `0 ≤ f - log 2 ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    0 ≤ freeEnergy G ⟨J, 0, β⟩ - Real.log 2 ∧
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_deviation_sandwich
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic log Z deviation sandwich**: under `0 ≤ J, 0 < β`,
`0 ≤ log Z - |ι|·log 2 ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2
      ≤ β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich
    G J β (mul_nonneg hβ.le hJ)

/-- **f strict deviation under non-trivial high-temperature**: under
`0 < β·J`, `0 < |ι|`, and `0 < |E|`, `0 < f - log 2`.

Strengthens Step 433 lower bound (`0 ≤ f - log 2`) to strict
positivity at non-trivial parameters. Follows from the lower bound
`log 2 + (|E|/|ι|)·log cosh(β·J) ≤ f` plus `log cosh(β·J) > 0` (since
`cosh(β·J) > 1` when `β·J ≠ 0`) plus `|E|/|ι| > 0`. -/
theorem freeEnergy_high_temp_h_zero_deviation_pos
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hne : 0 < Fintype.card ι)
    (hEpos : 0 < G.edgeFinset.card) :
    0 < freeEnergy G ⟨J, 0, β⟩ - Real.log 2 := by
  have h_lb : Real.log 2 + (G.edgeFinset.card : ℝ) / Fintype.card ι *
        Real.log (Real.cosh (β * J)) ≤ freeEnergy G ⟨J, 0, β⟩ :=
    freeEnergy_high_temp_h_zero_lower_bound G J β hβJ.le hne
  have hcosh_gt : 1 < Real.cosh (β * J) := by
    rw [show (1 : ℝ) = Real.cosh 0 from Real.cosh_zero.symm]
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_zero, abs_of_pos hβJ]
    exact hβJ
  have hlog_pos : 0 < Real.log (Real.cosh (β * J)) := Real.log_pos hcosh_gt
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hne
  have hE_pos : (0 : ℝ) < G.edgeFinset.card := by exact_mod_cast hEpos
  have hratio_pos : 0 < (G.edgeFinset.card : ℝ) / Fintype.card ι :=
    div_pos hE_pos hcard_pos
  have h_corr_pos : 0 < ((G.edgeFinset.card : ℝ) / Fintype.card ι) *
        Real.log (Real.cosh (β * J)) := mul_pos hratio_pos hlog_pos
  linarith

/-- **Ferromagnetic f strict deviation**: under `0 < J, 0 < β`,
`0 < |ι|`, `0 < |E|`, `0 < f - log 2`. -/
theorem freeEnergy_high_temp_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hne : 0 < Fintype.card ι)
    (hEpos : 0 < G.edgeFinset.card) :
    0 < freeEnergy G ⟨J, 0, β⟩ - Real.log 2 :=
  freeEnergy_high_temp_h_zero_deviation_pos
    G J β (mul_pos hβ hJ) hne hEpos


end IsingModel
