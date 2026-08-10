import IsingModel.AmbientLattice.Defs.HighTempPartition.ExpSummary

/-!
# Λ-restricted high-temperature deviation bounds at zero external field

How far `partitionFunctionΛ`, its logarithm and `freeEnergyΛ` sit above their values at the
degenerate parameter slices, for an arbitrary `G : SimpleGraph V` and an arbitrary finite
volume `Λ : Finset V`. The external field is zero throughout: the parameter records
occurring are `⟨J, 0, β⟩`, `⟨0, 0, β⟩` and `⟨J, 0, 0⟩`. The reference values are
`2 ^ Λ.card` for the partition function, `Λ.card * log 2` for its logarithm and `log 2` for
the free energy; the first two are what the partition function and its logarithm are equal
to at `J = 0` and at `β = 0` alike. The size of a deviation is expressed through the number
of edges of `inducedGraph G Λ`, the subgraph of `G` that `Λ` induces.

Under `0 ≤ β * J` the free energy exceeds `log 2` by a non-negative amount that is at most
`β * J` times the edge count over `Λ.card`, and the logarithm exceeds `Λ.card * log 2` by a
non-negative amount that is at most `β * J` times the edge count. For the partition
function the comparison is a quotient instead of a difference: `partitionFunctionΛ` over
`2 ^ Λ.card` lies between `cosh (β * J)` raised to the edge count and
`exp (β * J * edge count)`. The same bound that controls the free-energy deviation also
controls, in absolute value, the gap between the free energy at `⟨J, 0, β⟩` and the free
energy at either of `⟨0, 0, β⟩` and `⟨J, 0, 0⟩`.

Strengthening `0 ≤ β * J` to `0 < β * J` and asking the induced graph to have at least one
edge yields strict statements: `2 ^ Λ.card` is then strictly below the partition function,
and the two differences are then strictly above `0`.

Both hypothesis shapes recur in a ferromagnetic form, `0 ≤ J` with `0 < β` replacing
`0 ≤ β * J` and `0 < J` with `0 < β` replacing `0 < β * J`; every strict statement has one.
`0 < Λ.card` is assumed by exactly those statements whose conclusion mentions
`freeEnergyΛ`. Every statement takes `[DecidableEq V]` and
`[Fintype (inducedGraph G Λ).edgeSet]`.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-- **Λ-level sharper f deviation bound**: under `0 < |Λ|`, `0 ≤ β·J`,
`f_Λ - log 2 ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_bound_exp
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have h := freeEnergyΛ_high_temp_h_zero_upper_bound_exp
    G Λ J β hβJ hne
  linarith

/-- **Λ-level ferromagnetic f deviation bound**: under `0 ≤ J, 0 < β`,
`f_Λ - log 2 ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_bound_exp_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_bound_exp
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level f continuity at `J = 0`**: under `0 < |Λ|` and `0 ≤ β·J`,
`|f_Λ(⟨J,0,β⟩) - f_Λ(⟨0,0,β⟩)| ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_continuity_at_J_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨0, 0, β⟩ : IsingParams ℝ)|
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_continuity_at_J_zero
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level f continuity at `β = 0`**. -/
theorem freeEnergyΛ_high_temp_h_zero_continuity_at_beta_zero
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    |freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ)
        - freeEnergyΛ G Λ (⟨J, 0, 0⟩ : IsingParams ℝ)|
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_continuity_at_beta_zero
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level f deviation sandwich**: under `0 < |Λ|` and `0 ≤ β·J`,
`0 ≤ f_Λ - log 2 ≤ β·J·|E_Λ|/|Λ|`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) (hne : 0 < Λ.card) :
    0 ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.freeEnergy_high_temp_h_zero_deviation_sandwich
    (inducedGraph G Λ) J β hβJ hcard

/-- **Λ-level ferromagnetic f deviation sandwich**. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) (hne : 0 < Λ.card) :
    0 ≤ freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 ∧
    freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card / Λ.card :=
  freeEnergyΛ_high_temp_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ) hne

/-- **Λ-level log Z deviation sandwich**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    0 ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_deviation_sandwich
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level ferromagnetic log Z deviation sandwich**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    0 ≤ Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 ∧
    Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2
      ≤ β * J * (inducedGraph G Λ).edgeFinset.card :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_sandwich
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 ≤ β * J) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_relative_sandwich
    (inducedGraph G Λ) J β hβJ

/-- **Λ-level ferromagnetic Z relative-deviation sandwich**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) :
    Real.cosh (β * J) ^ (inducedGraph G Λ).edgeFinset.card
      ≤ partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
          (2 : ℝ) ^ Λ.card ∧
    partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) /
        (2 : ℝ) ^ Λ.card
      ≤ Real.exp (β * J * (inducedGraph G Λ).edgeFinset.card) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_relative_sandwich
    G Λ J β (mul_nonneg hβ.le hJ)

/-- **Λ-level f strict deviation**: under `0 < β·J`, `0 < |Λ|`,
`0 < |E_Λ|`, `0 < f_Λ - log 2`. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J) (hne : 0 < Λ.card)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 := by
  have hcard : 0 < Fintype.card (↑Λ : Type _) := by
    rw [Fintype.card_coe]; exact hne
  rw [freeEnergyΛ_apply]
  exact IsingModel.freeEnergy_high_temp_h_zero_deviation_pos
    (inducedGraph G Λ) J β hβJ hcard hEpos

/-- **Λ-level ferromagnetic f strict deviation**. -/
theorem freeEnergyΛ_high_temp_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β) (hne : 0 < Λ.card)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < freeEnergyΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) - Real.log 2 :=
  freeEnergyΛ_high_temp_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) hne hEpos

/-- **Λ-level Z strict deviation**: under `0 < β·J`, `0 < |E_Λ|`,
`2^|Λ| < Z_Λ`. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
      < partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.partitionFunction_high_temp_expansion_h_zero_pow_two_lt
    (inducedGraph G Λ) J β hβJ hEpos

/-- **Λ-level log Z strict deviation**: under `0 < β·J`, `0 < |E_Λ|`,
`0 < log Z_Λ - |Λ|·log 2`. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hβJ : 0 < β * J)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 := by
  rw [partitionFunctionΛ_apply, ← Fintype.card_coe (s := Λ)]
  exact IsingModel.log_partitionFunction_high_temp_expansion_h_zero_deviation_pos
    (inducedGraph G Λ) J β hβJ hEpos

/-- **Λ-level ferromagnetic Z strict deviation**. -/
theorem partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    (2 : ℝ) ^ Λ.card
      < partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_high_temp_expansion_h_zero_pow_two_lt
    G Λ J β (mul_pos hβ hJ) hEpos

/-- **Λ-level ferromagnetic log Z strict deviation**. -/
theorem log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos_ferromagnetic
    (G : SimpleGraph V) (Λ : Finset V)
    [Fintype (inducedGraph G Λ).edgeSet]
    (J β : ℝ) (hJ : 0 < J) (hβ : 0 < β)
    (hEpos : 0 < (inducedGraph G Λ).edgeFinset.card) :
    0 < Real.log (partitionFunctionΛ G Λ (⟨J, 0, β⟩ : IsingParams ℝ))
        - (Λ.card : ℝ) * Real.log 2 :=
  log_partitionFunctionΛ_high_temp_expansion_h_zero_deviation_pos
    G Λ J β (mul_pos hβ hJ) hEpos


end Ambient

end IsingModel
