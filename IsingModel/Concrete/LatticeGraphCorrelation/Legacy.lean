import IsingModel.Concrete.LatticeGraphBED
import IsingModel.Concrete.IntLattice
import IsingModel.Concrete.LatticeGraphCorrelation.Complex
import IsingModel.Concrete.LatticeGraphCorrelation.PerStage
import IsingModel.Concrete.LatticeGraphCorrelation.Magnetization
import IsingModel.Concrete.LatticeGraphCorrelation.TwoPoint
import IsingModel.Concrete.LatticeGraphCorrelation.Translation
import IsingModel.Concrete.LatticeGraphCorrelation.Inequalities
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperature
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.HighTemperatureCapstones
import IsingModel.Concrete.LatticeGraphCorrelation.JointAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.JointRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.CubicPseudoMass
import IsingModel.Concrete.LatticeGraphCorrelation.TheoremEtaLe1
import IsingModel.Concrete.LatticeGraphCorrelation.SiteIndepMag
import IsingModel.Concrete.LatticeGraphCorrelation.UniformMag
import IsingModel.Concrete.LatticeGraphCorrelation.Base
import IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeBasics
import IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationMonotonicity
import IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeEnergyBounds
import IsingModel.Concrete.LatticeGraphCorrelation.EnergyClosedForms
import IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumeCorrelationInequalities
import IsingModel.Concrete.LatticeGraphCorrelation.LambdaCorrelationMonotonicity
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationExhaustionLimits
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergySuperadditivity
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionExhaustionBounds
import IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumePartition
import IsingModel.Concrete.LatticeGraphCorrelation.FiniteVolumePartitionBounds
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.CorrelationDecay
import IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergyAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.FreeEnergySpecialCases
import IsingModel.Concrete.LatticeGraphCorrelation.Regularity
import IsingModel.Concrete.LatticeGraphCorrelation.PointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationPointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.MayerAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.MayerBasicIdentities
import IsingModel.Concrete.LatticeGraphCorrelation.MayerEdgeCases
import IsingModel.Concrete.LatticeGraphCorrelation.MayerExpansionEdgeCases
import IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonInfrastructure
import IsingModel.Concrete.LatticeGraphCorrelation.MayerEpsilonPositivity
import IsingModel.Concrete.LatticeGraphCorrelation.MayerFilterConnected
import IsingModel.Concrete.LatticeGraphCorrelation.MayerRecurrenceHasSum
import IsingModel.Concrete.LatticeGraphCorrelation.MayerStrictPositivity
import IsingModel.Concrete.LatticeGraphCorrelation.MayerTanhFerromagneticIff
import IsingModel.Concrete.LatticeGraphCorrelation.MayerTrivialCases
import IsingModel.Concrete.LatticeGraphCorrelation.MayerVdBounds
import IsingModel.Concrete.LatticeGraphCorrelation.MayerVdIff
import IsingModel.Concrete.LatticeGraphCorrelation.MayerVdRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationConvergence
import IsingModel.Concrete.LatticeGraphCorrelation.MagnetizationRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionClosedForms
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionSymmetry
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionGeneralAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFunctionRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyPointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBasic
import IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyBounds
import IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyEpsilonSharpening
import IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyHighTemperatureBounds
import IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhBounds
import IsingModel.Concrete.LatticeGraphCorrelation.PolymerFreeEnergyTanhSharpening
import IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityConvergence
import IsingModel.Concrete.LatticeGraphCorrelation.SusceptibilityPointwiseRegularity
import IsingModel.Concrete.LatticeGraphCorrelation.VdPolymerFamiliesAnalyticity
import IsingModel.TranslationInvariance
import IsingModel.PhaseTransition
import IsingModel.Inequalities.FKG
import IsingModel.ComplexAnalyticity
import IsingModel.Concrete.LatticeGraphCorrelation.Peierls
import IsingModel.AmbientComplexAnalyticity
import IsingModel.AmbientFKG
import IsingModel.AmbientLattice.SpecialCases.Legacy

/-!
# Concrete translation invariance for the ℤ^d Ising correlation

Apply the abstract `correlationInfinite_vaddFinset_of_translationInvariant`
theorem (`TranslationInvariance.lean`, PR #251) to the physical
`d`-dimensional Ising setup
`(IsingModel.latticeGraph d, Ambient.cubicExhaustion d)`:

* `isTranslationInvariant_latticeGraph` (PR #244) supplies the
  `IsTranslationInvariant (Fin d → ℤ) (latticeGraph d)` instance.
* `cubicExhaustion d` (PR #245) supplies the ambient exhaustion.
* The `Fintype (inducedGraph (latticeGraph d) Λ).edgeSet` instance
  (PR #246) supplies the Fintype hypothesis for arbitrary `Λ`.

## Main theorems

* `correlationInfinite_latticeGraph_cubicExhaustion_vaddFinset`:
  `correlationInfinite (latticeGraph d) (cubicExhaustion d) p
  (vaddFinset t A) = correlationInfinite ... p A` (ferromagnetic).
* `magnetizationInfinite_latticeGraph_cubicExhaustion_translation`:
  single-site specialization.

## References

* Glimm–Jaffe, *Quantum Physics* 2nd ed., §4.6, p. 68.
-/

open scoped symmDiff

namespace IsingModel

namespace Ambient

/-- **ℤ^d extendGraphFromΛ₁_le_induce**:
`extendGraphFromΛ₁ (latticeGraph d) Λ₁ Λ₂ ≤ inducedGraph (latticeGraph d) Λ₂`. -/
theorem extendGraphFromΛ₁_le_induce_latticeGraph
    (d : ℕ) (Λ₁ Λ₂ : Finset (Fin d → ℤ)) :
    Ambient.extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂
      ≤ Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₂ :=
  Ambient.extendGraphFromΛ₁_le_induce (IsingModel.latticeGraph d) Λ₁ Λ₂

/-- **ℤ^d correlationΛ_extendGraph_eq**: correlation equality between
the extended graph and the induced Λ₁ subgraph. -/
theorem correlationΛ_latticeGraph_extendGraph_eq
    (d : ℕ) {Λ₁ Λ₂ : Finset (Fin d → ℤ)} (h12 : Λ₁ ⊆ Λ₂)
    [Fintype (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁).edgeSet]
    [Fintype (Ambient.extendGraphFromΛ₁
      (IsingModel.latticeGraph d) Λ₁ Λ₂).edgeSet]
    (p : IsingParams ℝ)
    {A : Finset (Fin d → ℤ)} (hA : A ⊆ Λ₁) :
    IsingModel.correlation
        (Ambient.extendGraphFromΛ₁ (IsingModel.latticeGraph d) Λ₁ Λ₂) p
        (Ambient.liftFinset A (hA.trans h12))
      = IsingModel.correlation
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ₁) p
          (Ambient.liftFinset A hA) :=
  Ambient.correlationΛ_extendGraph_eq (IsingModel.latticeGraph d) h12 p hA

/-- **ℤ^d per-stage explicit upper bound on freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n ≤ Real.log 2 +
      |p.β| * (|p.J| * (Ambient.inducedGraph (IsingModel.latticeGraph d)
          ((Ambient.cubicExhaustion d).volume n)).edgeFinset.card
          + |p.h| * Fintype.card
            (↑((Ambient.cubicExhaustion d).volume n) : Type _))
        / Fintype.card (↑((Ambient.cubicExhaustion d).volume n) : Type _) :=
  freeEnergyAlongExhaustion_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p n hne

/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh n

/-- **ℤ^d per-stage J-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {h : ℝ} (hh : 0 ≤ h) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun J : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_J (IsingModel.latticeGraph d) Λ hh hβ n

/-- **ℤ^d per-stage h-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    MonotoneOn
      (fun h : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ici 0) :=
  freeEnergyAlongExhaustion_monotone_h (IsingModel.latticeGraph d) Λ hJ hβ n

/-- **ℤ^d per-stage β-monotonicity of freeEnergyAlongExhaustion** (any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J : ℝ} (hJ : 0 ≤ J) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    MonotoneOn
      (fun β : ℝ => freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n)
      (Set.Ioi 0) :=
  freeEnergyAlongExhaustion_monotone_beta (IsingModel.latticeGraph d) Λ hJ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion J-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_J
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_J
    (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_h
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_h
    (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β-monotonicity** (any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_beta
    (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ n

/-- **ℤ^d freeEnergyAlongExhaustion ≥ zero_params**: `f(0,0,β) ≤ f(J,h,β)`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ zero_params** analog. -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_zero_params
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β) (n : ℕ) :
    partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨0, 0, β⟩ n
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  partitionFunctionAlongExhaustion_ge_zero_params (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n

/-- **ℤ^d partitionFunctionΛ J-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_J`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_J (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ

/-- **ℤ^d partitionFunctionΛ h-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_h`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh

/-- **ℤ^d partitionFunctionΛ β-monotonicity** (pointwise). Concrete
specialization of `partitionFunctionΛ_monotone_beta`. -/
theorem partitionFunctionΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ)
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ) :=
  partitionFunctionΛ_monotone_beta (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ

/-- **ℤ^d log_partitionFunctionΛ J-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J₁, h, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J₂, h, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_J (IsingModel.latticeGraph d) Λ h β hh hβ hJ₁ hJ

/-- **ℤ^d log_partitionFunctionΛ h-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h₁, β⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h₂, β⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_h (IsingModel.latticeGraph d) Λ J β hJ hβ hh₁ hh

/-- **ℤ^d log_partitionFunctionΛ β-monotonicity** (ferromagnetic, pointwise). -/
theorem log_partitionFunctionΛ_latticeGraph_monotone_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) :
    Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h, β₁⟩ : IsingParams ℝ))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ
          (⟨J, h, β₂⟩ : IsingParams ℝ)) :=
  log_partitionFunctionΛ_monotone_beta (IsingModel.latticeGraph d) Λ J h hJ hh hβ₁ hβ

/-- **ℤ^d log_partitionFunctionAlongExhaustion J-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_J
    (d : ℕ) (h β : ℝ) (hh : 0 ≤ h) (hβ : 0 < β) {J₁ J₂ : ℝ}
    (hJ₁ : 0 ≤ J₁) (hJ : J₁ ≤ J₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J₁, h, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J₂, h, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_J (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) h β hh hβ hJ₁ hJ n

/-- **ℤ^d log_partitionFunctionAlongExhaustion h-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_h
    (d : ℕ) (J β : ℝ) (hJ : 0 ≤ J) (hβ : 0 < β) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh : h₁ ≤ h₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h₁, β⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h₂, β⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_h (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J β hJ hβ hh₁ hh n

/-- **ℤ^d log_partitionFunctionAlongExhaustion β-monotonicity** per stage. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_cubicExhaustion_monotone_beta
    (d : ℕ) (J h : ℝ) (hJ : 0 ≤ J) (hh : 0 ≤ h) {β₁ β₂ : ℝ}
    (hβ₁ : 0 < β₁) (hβ : β₁ ≤ β₂) (n : ℕ) :
    Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) (⟨J, h, β₁⟩ : IsingParams ℝ) n)
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
          (Ambient.cubicExhaustion d) (⟨J, h, β₂⟩ : IsingParams ℝ) n) :=
  log_partitionFunctionAlongExhaustion_monotone_beta (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) J h hJ hh hβ₁ hβ n

/-- **ℤ^d partitionFunctionΛ ≥ 1** (ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_one
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    1 ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_one_of_ferromagnetic (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionΛ ≥ 2^|Λ|** (ferromagnetic, per-Λ). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 : ℝ) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d log partitionFunctionΛ ≥ |Λ|·log 2** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `log Z_Λ ≥ 0`** (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_nonneg
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    0 ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d `freeEnergyΛ = |↑Λ|⁻¹ · log Z_Λ`**. -/
theorem freeEnergyΛ_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Fintype.card (↑Λ : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyΛ = (Λ.card)⁻¹ · log Z_Λ`** (Finset-card form). -/
theorem freeEnergyΛ_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    freeEnergyΛ (IsingModel.latticeGraph d) Λ p
      = (Λ.card : ℝ)⁻¹
        * Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  freeEnergyΛ_eq_inv_Λcard_mul_log (IsingModel.latticeGraph d) Λ p

/-- **ℤ^d `freeEnergyAlongExhaustion = |↑(Λ_n)|⁻¹ · log Z_n`** per stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_card_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_card_mul_log (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyAlongExhaustion = ((Λ.volume n).card)⁻¹ · log Z_n`**. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_inv_Λcard_mul_log
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = ((Λ.volume n).card : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_inv_Λcard_mul_log
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyΛ ≥ 0`** (ferromagnetic, nonempty `Λ`). -/
theorem freeEnergyΛ_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) {Λ : Finset (Fin d → ℤ)} (hne : Λ.Nonempty)
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    0 ≤ freeEnergyΛ (IsingModel.latticeGraph d) Λ p :=
  freeEnergyΛ_nonneg_of_ferromagnetic (IsingModel.latticeGraph d) hne p hf

/-- **ℤ^d `freeEnergyAlongExhaustion ≥ 0`** per stage (ferromagnetic,
nonempty stage, any-Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg_of_ferromagnetic
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

/-- **ℤ^d `freeEnergyAlongExhaustion` as `log Z / card`** (any-Exhaustion):
alternate form of `freeEnergyAlongExhaustion_eq_inv_card_mul_log` using the
Fintype-card expression. -/
theorem freeEnergyAlongExhaustion_latticeGraph_eq_log_div_card
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      = (Fintype.card (↑(Λ.volume n) : Type _) : ℝ)⁻¹
        * Real.log (partitionFunctionAlongExhaustion
            (IsingModel.latticeGraph d) Λ p n) :=
  freeEnergyAlongExhaustion_eq_log_div_card
    (IsingModel.latticeGraph d) Λ p n

/-- **ℤ^d `freeEnergyAlongExhaustion` per-stage upper bound** (any-Exhaustion):
`≤ log 2 + |β|·(|J|·|E_n|+|h|·|V_n|)/|V_n|`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_upper_bound
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n
      ≤ Real.log 2 + |p.β| *
          (|p.J| * (Ambient.inducedGraph (IsingModel.latticeGraph d)
              (Λ.volume n)).edgeFinset.card
            + |p.h| * Fintype.card (↑(Λ.volume n) : Type _))
        / Fintype.card (↑(Λ.volume n) : Type _) :=
  freeEnergyAlongExhaustion_upper_bound
    (IsingModel.latticeGraph d) Λ p n hne

/-- **ℤ^d partitionFunctionΛ ≥ (2 cosh βh)^|Λ|** (sharp, ferromagnetic). -/
theorem partitionFunctionΛ_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ)
    (hf : Ferromagnetic p) :
    (2 * Real.cosh (p.β * p.h)) ^ Λ.card
      ≤ partitionFunctionΛ (IsingModel.latticeGraph d) Λ p :=
  partitionFunctionΛ_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 1** (ferromagnetic, any Exhaustion). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_one_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    1 ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  partitionFunctionAlongExhaustion_ge_one_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log Z_n ≥ 0** (ferromagnetic, any Exhaustion). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg_general
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion
        (IsingModel.latticeGraph d) Λ p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf n

/-- **ℤ^d log partitionFunctionAlongExhaustion ≥ 0** (ferromagnetic). -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    0 ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ 2^|Λ_n|** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_two_pow_card
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 : ℝ) ^ ((Ambient.cubicExhaustion d).volume n).card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_two_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d partitionFunctionAlongExhaustion ≥ (2 cosh βh)^|Λ_n|** (ferromagnetic). -/
theorem partitionFunctionAlongExhaustion_latticeGraph_ge_two_cosh_pow_card
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (2 * Real.cosh (p.β * p.h)) ^ ((Ambient.cubicExhaustion d).volume n).card
      ≤ partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n :=
  partitionFunctionAlongExhaustion_ge_two_cosh_pow_card_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d log Z bound**: `|Λ_n|·log 2 ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (((Ambient.cubicExhaustion d).volume n).card : ℝ) * Real.log 2
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d sharp log Z bound**: `|Λ_n|·log(2 cosh βh) ≤ log Z_n`. -/
theorem log_partitionFunctionAlongExhaustion_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (p : IsingParams ℝ) (hf : Ferromagnetic p) (n : ℕ) :
    (((Ambient.cubicExhaustion d).volume n).card : ℝ)
        * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n) :=
  log_partitionFunctionAlongExhaustion_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p hf n

/-- **ℤ^d sharp log Z_Λ bound**: `|Λ|·log(2 cosh βh) ≤ log Z_Λ` (ferromagnetic). -/
theorem log_partitionFunctionΛ_latticeGraph_ge_card_mul_log_two_cosh
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    (Λ.card : ℝ) * Real.log (2 * Real.cosh (p.β * p.h))
      ≤ Real.log (partitionFunctionΛ (IsingModel.latticeGraph d) Λ p) :=
  log_partitionFunctionΛ_ge_card_mul_log_two_cosh_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf

/-- **ℤ^d freeEnergyInfinite from convergence** (any-Exhaustion): if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_eq_of_tendsto
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence** (any-Exhaustion). -/
theorem freeEnergyInfinite_latticeGraph_of_eventually_const
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) Λ p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d) Λ p h

/-- **ℤ^d freeEnergyInfinite from convergence**: if
`freeEnergyAlongExhaustion` tendsto `L`, then `freeEnergyInfinite = L`. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_eq_of_tendsto
    (d : ℕ) (p : IsingParams ℝ) {L : ℝ}
    (h : Filter.Tendsto (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p) Filter.atTop (nhds L)) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = L :=
  freeEnergyInfinite_eq_of_tendsto (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite of eventually constant sequence**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_of_eventually_const
    (d : ℕ) (p : IsingParams ℝ) {c : ℝ}
    (h : ∀ᶠ n in Filter.atTop, freeEnergyAlongExhaustion
      (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p n = c) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p = c :=
  freeEnergyInfinite_of_eventually_const (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p h

/-- **ℤ^d freeEnergyInfinite uniform upper bound via caller-supplied BED**
(any-Exhaustion): `freeEnergyInfinite ≤ log 2 + |β|·(|J|·c + |h|)`. -/
theorem freeEnergyInfinite_latticeGraph_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {c : ℝ}
    (hc : ∀ n, (Λ.volume n).Nonempty →
      ((Ambient.inducedGraph (IsingModel.latticeGraph d)
          (Λ.volume n)).edgeFinset.card : ℝ)
        ≤ c * Fintype.card (↑(Λ.volume n) : Type _)) :
    freeEnergyInfinite (IsingModel.latticeGraph d) Λ p
      ≤ Real.log 2 + |p.β| * (|p.J| * c + |p.h|) :=
  freeEnergyInfinite_le_uniform_upper_bound
    (IsingModel.latticeGraph d) Λ p hf hc

/-- **ℤ^d freeEnergyInfinite uniform upper bound via BED**. -/
theorem freeEnergyInfinite_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) [Nonempty (Fin d → ℤ)]
    (p : IsingParams ℝ) (hf : Ferromagnetic p) :
    freeEnergyInfinite (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyInfinite_le_uniform_upper_bound (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p hf (c := (d : ℝ)) ?_
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`** (any-Exhaustion,
caller-supplied BED). -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_range
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      Λ p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d) Λ p hBED

/-- **ℤ^d BddAbove range of `freeEnergyAlongExhaustion`**: via BED c=d. -/
theorem BddAbove_freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion
    (d : ℕ) (p : IsingParams ℝ) :
    BddAbove (Set.range (freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) p)) :=
  BddAbove_freeEnergyAlongExhaustion_range (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) p
    (boundedEdgeDensity_latticeGraph_cubicExhaustion d)

/-- **ℤ^d per-stage freeEnergyAlongExhaustion upper bound** using BED c = d. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_le_uniform_upper_bound
    (d : ℕ) (p : IsingParams ℝ) (n : ℕ)
    (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) p n
      ≤ Real.log 2 + |p.β| * (|p.J| * (d : ℝ) + |p.h|) := by
  refine freeEnergyAlongExhaustion_le_uniform_upper_bound
    (IsingModel.latticeGraph d) (Ambient.cubicExhaustion d) p
    (c := (d : ℝ)) ?_ n hne
  intro n _
  exact inducedLatticeGraph_card_edgeFinset_le d
    ((Ambient.cubicExhaustion d).volume n)

/-- **Per-stage lower bound on ℤ^d**: `log 2 ≤ freeEnergyAlongExhaustion` for
ferromagnetic + nonempty stage. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
      (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **Sharp per-stage lower bound on ℤ^d**:
`log(2 cosh(βh)) ≤ freeEnergyAlongExhaustion`. -/
theorem freeEnergyAlongExhaustion_latticeGraph_cubicExhaustion_ge_log_two_cosh
    (d : ℕ) {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : ((Ambient.cubicExhaustion d).volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d)
        (Ambient.cubicExhaustion d) ⟨J, h, β⟩ n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d)
    (Ambient.cubicExhaustion d) hJ hh hβ n hne

/-- **ℤ^d per-stage `log 2 ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log 2 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
      (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

/-- **ℤ^d per-stage `log(2 cosh(βh)) ≤ f_n`** (ferromagnetic, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_ge_log_two_cosh
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    {J h β : ℝ} (hJ : 0 ≤ J) (hh : 0 ≤ h) (hβ : 0 < β)
    (n : ℕ) (hne : (Λ.volume n).Nonempty) :
    Real.log (2 * Real.cosh (β * h))
      ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ
        (⟨J, h, β⟩ : IsingParams ℝ) n :=
  freeEnergyAlongExhaustion_ge_log_two_cosh (IsingModel.latticeGraph d) Λ
    hJ hh hβ n hne

/-- **ℤ^d per-stage `0 ≤ f_n`** (ferromagnetic, nonempty stage, any Exhaustion). -/
theorem freeEnergyAlongExhaustion_latticeGraph_nonneg
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    (p : IsingParams ℝ) (hf : Ferromagnetic p) {n : ℕ}
    (hne : (Λ.volume n).Nonempty) :
    0 ≤ freeEnergyAlongExhaustion (IsingModel.latticeGraph d) Λ p n :=
  freeEnergyAlongExhaustion_nonneg_of_ferromagnetic
    (IsingModel.latticeGraph d) Λ p hf hne

/-! ### susceptibility regularity ℤ^d wraps -/

/-- **ℤ^d Λ: susceptibility Continuous in `h`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Continuous (fun h' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_continuous_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: susceptibility Differentiable in `h`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_field
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun h' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J, h', β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_differentiable_field
    (IsingModel.latticeGraph d) Λ J β i

/-- **ℤ^d Λ: susceptibility Continuous in `J`**. -/
theorem susceptibilityΛ_latticeGraph_continuous_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Continuous (fun J' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_continuous_J
    (IsingModel.latticeGraph d) Λ h β i

/-- **ℤ^d Λ: susceptibility Differentiable in `J`**. -/
theorem susceptibilityΛ_latticeGraph_differentiable_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h β : ℝ) (i : ↑Λ) :
    Differentiable ℝ (fun J' =>
      Ambient.susceptibilityΛ (IsingModel.latticeGraph d) Λ
        (⟨J', h, β⟩ : IsingParams ℝ) i) :=
  Ambient.susceptibilityΛ_differentiable_J
    (IsingModel.latticeGraph d) Λ h β i

/-! ### susceptibility parameter-direction convergent (β/h/J → ∞)
ℤ^d wraps -/

/-- **ℤ^d Λ: susceptibility β → ∞ convergence**. -/
theorem susceptibilityΛ_latticeGraph_convergent_beta
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (h : ℝ) (hh : 0 ≤ h) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => Ambient.susceptibilityΛ (IsingModel.latticeGraph d)
        Λ (⟨J, h, (n + 1 : ℝ)⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityΛ_convergent_beta
    (IsingModel.latticeGraph d) Λ J hJ h hh i

/-- **ℤ^d Λ: susceptibility h → ∞ convergence**. -/
theorem susceptibilityΛ_latticeGraph_convergent_h
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (J : ℝ) (hJ : 0 ≤ J) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => Ambient.susceptibilityΛ (IsingModel.latticeGraph d)
        Λ (⟨J, (n : ℝ), β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityΛ_convergent_h
    (IsingModel.latticeGraph d) Λ J hJ β hβ i

/-- **ℤ^d Λ: susceptibility J → ∞ convergence**. -/
theorem susceptibilityΛ_latticeGraph_convergent_J
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Fintype (inducedGraph (IsingModel.latticeGraph d) Λ).edgeSet]
    (h : ℝ) (hh : 0 ≤ h) (β : ℝ) (hβ : 0 < β) (i : ↑Λ) :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => Ambient.susceptibilityΛ (IsingModel.latticeGraph d)
        Λ (⟨(n : ℝ), h, β⟩ : IsingParams ℝ) i)
      Filter.atTop (nhds L) :=
  Ambient.susceptibilityΛ_convergent_J
    (IsingModel.latticeGraph d) Λ h hh β hβ i

end Ambient

end IsingModel
