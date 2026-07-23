import IsingModel.Conditioning.HighTempClosed.LogBounds

/-!
# High-temperature partition ratio bounds

Mechanical child split from `Conditioning/HighTempClosed.lean`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Z strict deviation under non-trivial high-temperature**: under
`0 < β·J` and `0 < |E|`, `(2 : ℝ)^|ι| < Z(G; J, 0, β)`.

Strict version of Step 286 lower bound. Follows from
`partitionFunction_high_temp_expansion_h_zero_lower_bound` plus
strict `1 < cosh(β·J)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_pow_two_lt
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hEpos : 0 < G.edgeFinset.card) :
    (2 : ℝ) ^ Fintype.card ι < partitionFunction G ⟨J, 0, β⟩ := by
  have h_lb := partitionFunction_high_temp_expansion_h_zero_lower_bound
    G J β hβJ.le
  have hcosh_gt : 1 < Real.cosh (β * J) := by
    rw [show (1 : ℝ) = Real.cosh 0 from Real.cosh_zero.symm]
    refine Real.cosh_lt_cosh.mpr ?_
    rw [abs_zero, abs_of_pos hβJ]
    exact hβJ
  have hcosh_pow_gt : 1 < Real.cosh (β * J) ^ G.edgeFinset.card :=
    one_lt_pow₀ hcosh_gt hEpos.ne'
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  have : (2 : ℝ) ^ Fintype.card ι < (2 : ℝ) ^ Fintype.card ι *
      Real.cosh (β * J) ^ G.edgeFinset.card := by
    rw [show (2 : ℝ) ^ Fintype.card ι = (2 : ℝ) ^ Fintype.card ι * 1 from
      (mul_one _).symm]
    rw [mul_one]
    exact (lt_mul_iff_one_lt_right h2_pos).mpr hcosh_pow_gt
  linarith

/-- **Z ratio bound at trivial slice**: under `0 ≤ β·J`,
`Z(G; J, 0, β) / Z(G; 0, 0, β) ≤ exp(β·J·|E|)`.

Combines the sharper Z upper bound `Z(J,0,β) ≤ 2^|ι|·exp(β·J·|E|)`
(Step 393) with the trivial slice `Z(0,0,β) = 2^|ι|` (Step 310). The
ratio measures how much `Z` grows relative to its "free spin"
(non-interacting) value as `J` increases. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  rw [h_J0]
  rw [div_le_iff₀ (pow_pos (by norm_num) _)]
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  calc partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := h_ub
    _ = Real.exp (β * J * G.edgeFinset.card) *
          (2 : ℝ) ^ Fintype.card ι := by ring

/-- **Z ratio bound at β=0 trivial slice**: under `0 ≤ β·J`,
`Z(G; J, 0, β) / Z(G; J, 0, 0) ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_ub := partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  rw [h_β0]
  rw [div_le_iff₀ (pow_pos (by norm_num) _)]
  calc partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) := h_ub
    _ = Real.exp (β * J * G.edgeFinset.card) *
          (2 : ℝ) ^ Fintype.card ι := by ring

/-- **log Z ratio sandwich at J=0 trivial slice**: under `0 ≤ β·J`,
`|E|·log cosh(β·J) ≤ log Z⟨J,0,β⟩ - log Z⟨0,0,β⟩ ≤ β·J·|E|`.

Combines `log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp`
with the trivial slice `log Z⟨0,0,β⟩ = |ι|·log 2`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card := by
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  have h_log : Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_J0, Real.log_pow]
  rw [h_log]
  obtain ⟨h_lb, h_ub⟩ :=
    log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp G J β hβJ
  refine ⟨?_, ?_⟩ <;> linarith

/-- **log Z ratio sandwich at β=0 trivial slice**: under `0 ≤ β·J`,
`|E|·log cosh(β·J) ≤ log Z⟨J,0,β⟩ - log Z⟨J,0,0⟩ ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card := by
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  have h_log : Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_β0, Real.log_pow]
  rw [h_log]
  obtain ⟨h_lb, h_ub⟩ :=
    log_partitionFunction_high_temp_expansion_h_zero_sandwich_exp G J β hβJ
  refine ⟨?_, ?_⟩ <;> linarith

/-- **log Z ratio sandwich bundle**: bundles both J=0 and β=0 sandwiches. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) :=
  ⟨log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G J β hβJ⟩

/-- **log Z ratio bound at J=0 trivial slice**: under `0 ≤ β·J`,
`log Z⟨J, 0, β⟩ - log Z⟨0, 0, β⟩ ≤ β·J·|E|`.

Combines the sharper log Z upper bound (Step 403) with
`log Z⟨0, 0, β⟩ = |ι|·log 2`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card := by
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  have h_log : Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_J0, Real.log_pow]
  rw [h_log]
  linarith [log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ]

/-- **log Z ratio bound at β=0 trivial slice**: under `0 ≤ β·J`,
`log Z⟨J, 0, β⟩ - log Z⟨J, 0, 0⟩ ≤ β·J·|E|`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card := by
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  have h_log : Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      = (Fintype.card ι : ℝ) * Real.log 2 := by
    rw [h_β0, Real.log_pow]
  rw [h_log]
  linarith [log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β hβJ]

/-- **Ferromagnetic log Z ratio bound at J=0**. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_ratio_bound
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic log Z ratio bound at β=0**. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
      ≤ β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G J β (mul_nonneg hβ.le hJ)

/-- **Sharper Z complete-summary exp bundle**: under `0 ≤ β·J`,
single statement bundling sharper sandwich + trivial-slice values:
  1. `2^|ι|·cosh^|E| ≤ Z` (lower),
  2. `Z ≤ 2^|ι|·exp(β·J·|E|)` (sharper exp upper),
  3. `Z⟨0, 0, β⟩ = 2^|ι|` (J = 0 trivial slice),
  4. `Z⟨J, 0, 0⟩ = 2^|ι|` (β = 0 trivial slice).
Useful as a single import for downstream applications. -/
theorem partitionFunction_high_temp_expansion_h_zero_complete_summary_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
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
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound_exp G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β,
   partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J⟩

/-- **Sharper Z high-temperature sandwich (FV (3.45))**: under
`0 ≤ β·J`,
`2^|ι| · (cosh βJ)^|E| ≤ Z(G; J, 0, β) ≤ 2^|ι| · exp(β·J·|E|)`.

Combines `partitionFunction_high_temp_expansion_h_zero_lower_bound`
(Step 286) with `partitionFunction_high_temp_expansion_h_zero_upper_bound_exp`
(Step 393). Globally sharper than the cosh-only sandwich of Step 326. -/
theorem partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    (2 : ℝ) ^ Fintype.card ι *
        Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ ∧
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_lower_bound G J β hβJ,
   partitionFunction_high_temp_expansion_h_zero_upper_bound_exp G J β hβJ⟩

/-- **Z relative-deviation sandwich**: under `0 ≤ β·J`,
`cosh(β·J)^|E| ≤ Z(G; J, 0, β) / 2^|ι| ≤ exp(β·J·|E|)`.

Divides the Z sandwich by `2^|ι|` to give a normalized "deviation" form.
The lower bound `cosh^|E|` matches the contribution of the empty-X term
in FV (3.45); the upper bound `exp(β·J·|E|)` is the linear-`β·J`
exponential. -/
theorem partitionFunction_high_temp_expansion_h_zero_relative_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι ∧
    partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h2_pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι :=
    pow_pos (by norm_num) _
  obtain ⟨h_lb, h_ub⟩ := partitionFunction_high_temp_expansion_h_zero_sandwich_exp
    G J β hβJ
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ h2_pos]; linarith
  · rw [div_le_iff₀ h2_pos]; linarith

/-- **Z ratio sandwich at trivial slice**: under `0 ≤ β·J`,
`cosh(β·J)^|E| ≤ Z(G; J, 0, β) / Z(G; 0, 0, β) ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_J0 : partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_J_zero G β
  rw [h_J0]
  exact partitionFunction_high_temp_expansion_h_zero_relative_sandwich G J β hβJ

/-- **Z ratio sandwich at β=0 trivial slice**: under `0 ≤ β·J`,
`cosh(β·J)^|E| ≤ Z(G; J, 0, β) / Z(G; J, 0, 0) ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) := by
  have h_β0 : partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      = (2 : ℝ) ^ Fintype.card ι :=
    partitionFunction_high_temp_expansion_h_zero_closed_at_beta_zero G J
  rw [h_β0]
  exact partitionFunction_high_temp_expansion_h_zero_relative_sandwich G J β hβJ

/-- **Ferromagnetic Z ratio sandwich at J=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_sandwich
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio sandwich at β=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio upper bound at J=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_bound
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z ratio upper bound at β=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z relative-deviation sandwich**: under `0 ≤ J, 0 < β`,
`cosh(β·J)^|E| ≤ Z / 2^|ι| ≤ exp(β·J·|E|)`. -/
theorem partitionFunction_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ G.edgeFinset.card
      ≤ partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι ∧
    partitionFunction G ⟨J, 0, β⟩ / (2 : ℝ) ^ Fintype.card ι
      ≤ Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_relative_sandwich
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic Z strict deviation**: under `0 < J, 0 < β` and
`0 < |E|`, `2^|ι| < Z`. -/
theorem partitionFunction_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hEpos : 0 < G.edgeFinset.card) :
    (2 : ℝ) ^ Fintype.card ι < partitionFunction G ⟨J, 0, β⟩ :=
  partitionFunction_high_temp_expansion_h_zero_pow_two_lt
    G J β (mul_pos hβ hJ) hEpos

/-- **Ferromagnetic log Z strict deviation**: under `0 < J, 0 < β` and
`0 < |E|`, `0 < log Z - |ι|·log 2`. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hEpos : 0 < G.edgeFinset.card) :
    0 < Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 :=
  log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
    G J β (mul_pos hβ hJ) hEpos

/-- **Ferromagnetic sharper Z high-temperature upper bound**: under
`0 ≤ J, 0 < β`, `Z(G; J, 0, β) ≤ 2^|ι| · exp(β·J·|E|)`. Bridges
ferromagnetic-style hypotheses with Step 393 via `mul_nonneg hβ.le hJ`. -/
theorem partitionFunction_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    partitionFunction G ⟨J, 0, β⟩
      ≤ (2 : ℝ) ^ Fintype.card ι *
          Real.exp (β * J * G.edgeFinset.card) :=
  partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper log Z high-temperature upper bound**: under
`0 ≤ J, 0 < β`, `log Z ≤ |ι|·log 2 + β·J·|E|`. Bridges ferromagnetic
hypotheses with Step 403. -/
theorem log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.log (partitionFunction G ⟨J, 0, β⟩)
      ≤ (Fintype.card ι : ℝ) * Real.log 2
        + β * J * G.edgeFinset.card :=
  log_partitionFunction_high_temp_expansion_h_zero_upper_bound_exp
    G J β (mul_nonneg hβ.le hJ)

/-- **Ferromagnetic sharper f high-temperature upper bound**: under
`0 < |ι|`, `0 ≤ J, 0 < β`, `f ≤ log 2 + β·J·|E|/|ι|`. Bridges
ferromagnetic hypotheses with Step 394. -/
theorem freeEnergy_high_temp_h_zero_upper_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2 + β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_upper_bound_exp
    G J β (mul_nonneg hβ.le hJ) hne


end IsingModel
