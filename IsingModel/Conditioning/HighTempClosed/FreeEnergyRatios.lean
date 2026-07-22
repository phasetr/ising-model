import IsingModel.Conditioning.HighTempClosed.FreeEnergyBounds

/-!
# High-temperature free energy ratio summaries

Mechanical child split from `Conditioning/HighTempClosed.lean`.
-/

namespace IsingModel

open Finset Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **f ratio bound at J=0 trivial slice**: under `0 ≤ β·J` and
`0 < |ι|`, `f(G; J, 0, β) - f(G; 0, 0, β) ≤ β·J·|E|/|ι|`.

Equivalent reformulation of the f deviation bound using the trivial
slice `f(0, 0, β) = log 2`. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have hf0 : freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
    have := freeEnergy_J_zero G (0 : ℝ) β hne
    simpa [mul_zero, Real.cosh_zero] using this
  rw [hf0]
  exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **f ratio bound at β=0 trivial slice**. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  rw [freeEnergy_beta_zero G J 0 hne]
  exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **Ferromagnetic f ratio bound at J=0**. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_ratio_bound G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic f ratio bound at β=0**. -/
theorem freeEnergy_high_temp_h_zero_ratio_bound_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_ratio_bound_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **f ratio sandwich at J=0 trivial slice**: under `0 ≤ β·J` and
`0 < |ι|`, `(|E|/|ι|)·log cosh(β·J) ≤ f⟨J,0,β⟩ - f⟨0,0,β⟩ ≤ β·J·|E|/|ι|`. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  have hf0 : freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) = Real.log 2 := by
    have := freeEnergy_J_zero G (0 : ℝ) β hne
    simpa [mul_zero, Real.cosh_zero] using this
  rw [hf0]
  refine ⟨?_, ?_⟩
  · linarith [freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne]
  · exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **f ratio sandwich at β=0 trivial slice**. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι := by
  rw [freeEnergy_beta_zero G J 0 hne]
  refine ⟨?_, ?_⟩
  · linarith [freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne]
  · exact freeEnergy_high_temp_h_zero_deviation_bound_exp G J β hβJ hne

/-- **f ratio sandwich bundle**: bundles both J=0 and β=0 sandwiches. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  ⟨freeEnergy_high_temp_h_zero_ratio_sandwich G J β hβJ hne,
   freeEnergy_high_temp_h_zero_ratio_sandwich_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic f ratio sandwich bundle**. -/
theorem freeEnergy_high_temp_h_zero_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  freeEnergy_high_temp_h_zero_ratio_sandwich_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Triple ratio sandwich bundle at J=0 trivial slice**: under `0 ≤ β·J`
and `0 < |ι|`, single statement bundling Z, log Z, and f ratio sandwiches
at the J=0 slice. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_sandwich G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_sandwich G J β hβJ hne⟩

/-- **Triple ratio sandwich bundle at β=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_sandwich_beta_zero
     G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_sandwich_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic triple ratio sandwich bundle at J=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic triple ratio sandwich bundle at β=0**. -/
theorem
partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    (Real.cosh (β * J) ^ G.edgeFinset.card
        ≤ partitionFunction G ⟨J, 0, β⟩ /
            partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      partitionFunction G ⟨J, 0, β⟩ /
          partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
          ≤ Real.exp (β * J * G.edgeFinset.card)) ∧
    ((G.edgeFinset.card : ℝ) * Real.log (Real.cosh (β * J))
        ≤ Real.log (partitionFunction G ⟨J, 0, β⟩)
            - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)) ∧
      Real.log (partitionFunction G ⟨J, 0, β⟩)
          - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
          ≤ β * J * G.edgeFinset.card) ∧
    ((G.edgeFinset.card : ℝ) / Fintype.card ι * Real.log (Real.cosh (β * J))
        ≤ freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ) ∧
      freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι) :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_sandwich_bundle_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Triple ratio bound bundle at J=0 trivial slice**: under `0 ≤ β·J`
and `0 < |ι|`, single statement bundling Z, log Z, and f ratio bounds:
  1. `Z⟨J,0,β⟩ / Z⟨0,0,β⟩ ≤ exp(β·J·|E|)`,
  2. `log Z⟨J,0,β⟩ - log Z⟨0,0,β⟩ ≤ β·J·|E|`,
  3. `f⟨J,0,β⟩ - f⟨0,0,β⟩ ≤ β·J·|E|/|ι|`. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_bound G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_bound G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_bound G J β hβJ hne⟩

/-- **Triple ratio bound bundle at β=0 trivial slice**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  ⟨partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero G J β hβJ,
   log_partitionFunction_high_temp_expansion_h_zero_ratio_bound_beta_zero
     G J β hβJ,
   freeEnergy_high_temp_h_zero_ratio_bound_beta_zero G J β hβJ hne⟩

/-- **Ferromagnetic triple ratio bound bundle at J=0**. -/
theorem partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨0, 0, β⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨0, 0, β⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Ferromagnetic triple ratio bound bundle at β=0**. -/
theorem
partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    partitionFunction G ⟨J, 0, β⟩ /
        partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ Real.exp (β * J * G.edgeFinset.card) ∧
    Real.log (partitionFunction G ⟨J, 0, β⟩)
        - Real.log (partitionFunction G (⟨J, 0, 0⟩ : IsingParams ℝ))
        ≤ β * J * G.edgeFinset.card ∧
    freeEnergy G ⟨J, 0, β⟩ - freeEnergy G (⟨J, 0, 0⟩ : IsingParams ℝ)
        ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  partitionFunction_high_temp_expansion_h_zero_triple_ratio_bound_bundle_beta_zero
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Strict deviation bundle**: under `0 < β·J`, `0 < |E|`,
`0 < |ι|`, single statement bundling Z, log Z, and f strict deviations. -/
theorem partitionFunction_high_temp_expansion_h_zero_strict_deviation_bundle
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hne : 0 < Fintype.card ι)
    (hEpos : 0 < G.edgeFinset.card) :
    (2 : ℝ) ^ Fintype.card ι < partitionFunction G ⟨J, 0, β⟩ ∧
    0 < Real.log (partitionFunction G ⟨J, 0, β⟩)
        - (Fintype.card ι : ℝ) * Real.log 2 ∧
    0 < freeEnergy G ⟨J, 0, β⟩ - Real.log 2 :=
  ⟨partitionFunction_high_temp_expansion_h_zero_pow_two_lt G J β hβJ hEpos,
   log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
     G J β hβJ hEpos,
   freeEnergy_high_temp_h_zero_deviation_pos G J β hβJ hne hEpos⟩

/-- **Ferromagnetic sharper f deviation bound**: under `0 ≤ J, 0 < β`
and `0 < |ι|`, `f - log 2 ≤ β·J·|E|/|ι|`. Bridges via
`mul_nonneg hβ.le hJ`. -/
theorem freeEnergy_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩ - Real.log 2
      ≤ β * J * G.edgeFinset.card / Fintype.card ι :=
  freeEnergy_high_temp_h_zero_deviation_bound_exp
    G J β (mul_nonneg hβ.le hJ) hne

/-- **Free-energy high-temperature expansion decomposition (GJ §18.3 / FV (3.45))**:
under `0 < |ι|` and `0 ≤ β·J`,
`freeEnergy(G; J, 0, β) = log 2 + (|E|/|ι|) · log(cosh βJ) + log(∑_{X even} tanh^|X|) / |ι|`.

Direct corollary of `log_partitionFunction_high_temp_expansion_h_zero_closed`
(Step 315) by dividing by `|ι|`. The first two terms recover the
graph-aware lower bound `freeEnergy_high_temp_h_zero_lower_bound`
(Step 288); the third (the `log ∑` term) is the residual contribution
absent from the bound. -/
theorem freeEnergy_high_temp_expansion_h_zero_closed
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    freeEnergy G ⟨J, 0, β⟩
      = Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (Real.cosh (β * J))
        + Real.log
            (∑ X ∈ G.edgeFinset.powerset.filter
                (fun X : Finset (Sym2 ι) =>
                  ∀ v : ι, Even ((X.filter (v ∈ ·)).card)),
              Real.tanh (β * J) ^ X.card) / Fintype.card ι := by
  unfold freeEnergy
  rw [log_partitionFunction_high_temp_expansion_h_zero_closed G J β hβJ]
  have hι_ne : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hne.ne'
  field_simp

/-- **freeEnergy high-temperature sandwich bounds (GJ §18.3 / FV (3.45))**:
under `0 < |ι|` and `0 ≤ β·J`,
`log 2 + (|E|/|ι|) · log(cosh βJ) ≤ f(G; J, 0, β) ≤ log 2 + (|E|/|ι|) · log(2 · cosh βJ)`.
Combines `freeEnergy_high_temp_h_zero_lower_bound` (Step 288) and
`freeEnergy_high_temp_h_zero_upper_bound` (Step 322). -/
theorem freeEnergy_high_temp_h_zero_sandwich
    (G : SimpleGraph ι) [Fintype G.edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Fintype.card ι) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ freeEnergy G ⟨J, 0, β⟩
    ∧ freeEnergy G ⟨J, 0, β⟩
      ≤ Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) :=
  ⟨freeEnergy_high_temp_h_zero_lower_bound G J β hβJ hne,
   freeEnergy_high_temp_h_zero_upper_bound G J β hβJ hne⟩

omit [DecidableEq ι] in
/-- **freeEnergy high-temp bounds consistency**: the FV (3.45) lower
bound is always at most the upper bound:
`log 2 + (|E|/|ι|) · log cosh(βJ) ≤ log 2 + (|E|/|ι|) · log(2·cosh βJ)`.

Trivial sanity check: `log cosh ≤ log(2·cosh) = log 2 + log cosh`,
i.e., `log 2 ≥ 0`. -/
theorem freeEnergy_high_temp_h_zero_lower_le_upper
    (G : SimpleGraph ι) [Fintype G.edgeSet] (J β : ℝ) (_hβJ : 0 ≤ β * J) :
    Real.log 2 +
        (G.edgeFinset.card : ℝ) / Fintype.card ι *
          Real.log (Real.cosh (β * J))
      ≤ Real.log 2
        + (G.edgeFinset.card : ℝ) / Fintype.card ι *
            Real.log (2 * Real.cosh (β * J)) := by
  have hcosh_pos : 0 < Real.cosh (β * J) := Real.cosh_pos _
  have hlog_le : Real.log (Real.cosh (β * J)) ≤ Real.log (2 * Real.cosh (β * J)) := by
    apply Real.log_le_log hcosh_pos
    linarith [Real.one_le_cosh (β * J)]
  have hcoeff_nn : (0 : ℝ) ≤
      (G.edgeFinset.card : ℝ) / Fintype.card ι := by positivity
  linarith [mul_le_mul_of_nonneg_left hlog_le hcoeff_nn]


end IsingModel
