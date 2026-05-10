import IsingModel.AmbientLattice.SpecialCases.FreeEnergy
import IsingModel.AmbientLattice.SpecialCases.FreeEnergyAnalyticity
import IsingModel.AmbientLattice.SpecialCases.HighTemperature
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureBounds
import IsingModel.AmbientLattice.SpecialCases.HighTemperatureCapstones
import IsingModel.AmbientLattice.SpecialCases.InfiniteVolume
import IsingModel.AmbientLattice.SpecialCases.JointAnalyticity
import IsingModel.AmbientLattice.SpecialCases.JointRegularity
import IsingModel.AmbientLattice.SpecialCases.MayerAnalyticity
import IsingModel.AmbientLattice.SpecialCases.MayerBasicIdentities
import IsingModel.AmbientLattice.SpecialCases.MayerEdgeCases
import IsingModel.AmbientLattice.SpecialCases.MayerExpansionEdgeCases
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonInfrastructure
import IsingModel.AmbientLattice.SpecialCases.MayerEpsilonPositivity
import IsingModel.AmbientLattice.SpecialCases.MayerFilterConnected
import IsingModel.AmbientLattice.SpecialCases.MayerRecurrenceHasSum
import IsingModel.AmbientLattice.SpecialCases.MayerStrictPositivity
import IsingModel.AmbientLattice.SpecialCases.MayerTanhFerromagneticIff
import IsingModel.AmbientLattice.SpecialCases.MayerTrivialCases
import IsingModel.AmbientLattice.SpecialCases.MayerVdBounds
import IsingModel.AmbientLattice.SpecialCases.MayerVdIff
import IsingModel.AmbientLattice.SpecialCases.MayerVdRegularity
import IsingModel.AmbientLattice.SpecialCases.MagnetizationConvergence
import IsingModel.AmbientLattice.SpecialCases.MagnetizationRegularity
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyRegularity
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionGeneralAnalyticity
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionRegularity
import IsingModel.AmbientLattice.SpecialCases.PartitionFreeEnergyPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyAnalyticity
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBasic
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyBounds
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyEpsilonSharpening
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyHighTemperatureBounds
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhBounds
import IsingModel.AmbientLattice.SpecialCases.PolymerFreeEnergyTanhSharpening
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityPointwiseRegularity
import IsingModel.AmbientLattice.SpecialCases.VdPolymerFamiliesAnalyticity
import IsingModel.AmbientLattice.Analyticity

/-!
# Special-case closed forms, h-symmetry, and critical exponents

Uniform upper bounds (BoundedEdgeDensity), closed forms for special
parameter slices (β=0, J=h=0, J=0), h-symmetry / |h|-monotonicity
along an exhaustion, and the critical exponent bounds η≥0, ζ≥0
at infinite volume (GJ §17.7 Thm 17.7.1).

## References

* Glimm–Jaffe, *Quantum Physics*, §4.6, §17.7.
-/

namespace IsingModel
namespace Ambient

open Finset Real
open scoped symmDiff

variable {V : Type*} [DecidableEq V]

/-! ## β = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion β=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n = 2 ^ |Λ.volume n|`
for any `J, h` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_beta_zero` (every
Boltzmann weight collapses to `exp 0 = 1`) with
`card_config_eq_two_pow` and `Fintype.card_coe`. -/
theorem partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, 0⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨J, h, 0⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_beta_zero, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨J, h, 0⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_beta_zero` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_beta_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨J, h, 0⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_beta_zero, Real.log_pow]

/-! ## J = h = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=h=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n = 2 ^ |Λ.volume n|`
for any ambient graph `G, Λ` and any `β`.

Specialization of `IsingModel.partitionFunction_zero_params`
(`Z_G ⟨0,0,β⟩ = Fintype.card (Config ι)`) with `card_config_eq_two_pow`
(`|Config ι| = 2^|ι|`) and `Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, 0, β⟩ : IsingParams ℝ) n
      = (2 : ℝ) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, 0, β⟩ : IsingParams ℝ) = (2 : ℝ) ^ (Λ.volume n).card
  rw [IsingModel.partitionFunction_zero_params, IsingModel.card_config_eq_two_pow,
      Fintype.card_coe]
  push_cast
  rfl

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, 0, β⟩ n)
= |Λ.volume n| · log 2`. Follows from
`partitionFunctionAlongExhaustion_zero_params` via `Real.log_pow`. -/
theorem log_partitionFunctionAlongExhaustion_zero_params
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, 0, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log 2 := by
  rw [partitionFunctionAlongExhaustion_zero_params, Real.log_pow]

/-! ## J = 0 closed form for `partitionFunctionAlongExhaustion` -/

/-- **Along-exhaustion J=0 partition function closed form**:
`partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n = (2·cosh(β·h))^|Λ.volume n|`
for any `h, β` and any ambient graph `G, Λ`.

Specialization of `IsingModel.partitionFunction_J_zero`
(`Z_G ⟨0, h, β⟩ = (2·cosh(β·h))^|ι|`, graph-independent) with
`Fintype.card_coe` (`|↑Λ| = |Λ|`). -/
theorem partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨0, h, β⟩ : IsingParams ℝ) n
      = (2 * Real.cosh (β * h)) ^ (Λ.volume n).card := by
  change partitionFunction (inducedGraph G (Λ.volume n))
      (⟨0, h, β⟩ : IsingParams ℝ) = _
  rw [IsingModel.partitionFunction_J_zero, Fintype.card_coe]

/-- **Log form**: `log (partitionFunctionAlongExhaustion G Λ ⟨0, h, β⟩ n)
= |Λ.volume n| · log (2·cosh(β·h))`. Follows from
`partitionFunctionAlongExhaustion_J_zero` via `Real.log_pow`
(`2·cosh(β·h) > 0`). -/
theorem log_partitionFunctionAlongExhaustion_J_zero
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h β : ℝ) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion G Λ
        (⟨0, h, β⟩ : IsingParams ℝ) n)
      = ((Λ.volume n).card : ℝ) * Real.log (2 * Real.cosh (β * h)) := by
  rw [partitionFunctionAlongExhaustion_J_zero, Real.log_pow]

/-! ## h-symmetry / `|h|`-monotonicity along exhaustion

Specializations of `IsingModel.freeEnergy_neg_h`, `freeEnergy_eq_abs_h`,
and `freeEnergy_monotone_abs_h` (PRs #126–#127) to each stage of the
exhaustion, via the `change` + definitional-unfolding pattern already
used in this file. -/

/-- **Along-exhaustion partition-function h-evenness**:
`partitionFunctionAlongExhaustion G Λ ⟨J, -h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n`. Per-stage lift of
`IsingModel.partitionFunction_neg_h` via the flip involution. -/
theorem partitionFunctionAlongExhaustion_neg_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, -h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_neg_h G (Λ.volume n) J h β

/-- **Along-exhaustion partition-function `|h|`-rewrite**:
`partitionFunctionAlongExhaustion G Λ ⟨J, h, β⟩ n =
partitionFunctionAlongExhaustion G Λ ⟨J, |h|, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_eq_abs_h`. -/
theorem partitionFunctionAlongExhaustion_eq_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J h β : ℝ) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h, β⟩ : IsingParams ℝ) n
      = partitionFunctionAlongExhaustion G Λ (⟨J, |h|, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_eq_abs_h G (Λ.volume n) J h β

/-- **Along-exhaustion ferromagnetic `|h|`-monotonicity of partition
function**: for `J ≥ 0`, `β > 0`, `|h₁| ≤ |h₂|`,
`partitionFunctionAlongExhaustion G Λ ⟨J, h₁, β⟩ n ≤
partitionFunctionAlongExhaustion G Λ ⟨J, h₂, β⟩ n`. Per-stage lift of
`partitionFunctionΛ_monotone_abs_h`. -/
theorem partitionFunctionAlongExhaustion_monotone_abs_h
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β)
    {h₁ h₂ : ℝ} (hh : |h₁| ≤ |h₂|) (n : ℕ) :
    partitionFunctionAlongExhaustion G Λ (⟨J, h₁, β⟩ : IsingParams ℝ) n
      ≤ partitionFunctionAlongExhaustion G Λ (⟨J, h₂, β⟩ : IsingParams ℝ) n :=
  partitionFunctionΛ_monotone_abs_h G (Λ.volume n) J β hJ hβ hh

/-! ### susceptibility parameter-direction convergent (β/h/J → ∞)
along-ex wraps -/

/-- **Along-ex: susceptibility β → ∞ convergence**. Per-stage `n`. -/
theorem susceptibilityAlongExhaustion_convergent_beta_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_beta G (Λ.volume n) J hJ h hh _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, h, (k + 1 : ℝ)⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: susceptibility h → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_convergent_h_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_h G (Λ.volume n) J hJ β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨J, (k : ℝ), β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

/-- **Along-ex: susceptibility J → ∞ convergence**. -/
theorem susceptibilityAlongExhaustion_convergent_J_param
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : V) (n : ℕ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n)
      Filter.atTop (nhds L) := by
  by_cases hi : i ∈ Λ.volume n
  · have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) =
        (fun k : ℕ => susceptibilityΛ G (Λ.volume n)
          (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) ⟨i, hi⟩) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_pos]
    rw [h_eq]
    exact susceptibilityΛ_convergent_J G (Λ.volume n) h hh β hβ _
  · refine ⟨0, ?_⟩
    have h_eq : (fun k : ℕ => susceptibilityAlongExhaustion G Λ
        (⟨(k : ℝ), h, β⟩ : IsingParams ℝ) i n) = (fun _ => 0) := by
      funext k
      unfold susceptibilityAlongExhaustion
      simp only [hi, dif_neg, not_false_iff]
    rw [h_eq]
    exact tendsto_const_nhds

end Ambient
end IsingModel
