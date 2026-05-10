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
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyMonotonicity
import IsingModel.Concrete.LatticeGraphCorrelation.PartitionFreeEnergyBounds
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
