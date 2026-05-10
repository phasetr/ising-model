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
import IsingModel.AmbientLattice.SpecialCases.PartitionFunctionClosedForms
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
import IsingModel.AmbientLattice.SpecialCases.SusceptibilityConvergence
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

end Ambient
end IsingModel
