import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Basic

/-!
# Concrete per-direction analyticity wrappers (real and complex)

Narrow child module for the per-direction real and complex analyticity
wrappers on `latticeGraph d`. 12 theorems for `partitionFunction*` /
`freeEnergy*` `analyticAt`/`analyticOn` in `h`, `J`, `β`, plus joint
analyticity wrappers. The theorem names are unchanged from the former
`Complex` declarations.
-/

namespace IsingModel
namespace Ambient


/-! ## Moved: per-direction real analyticity wrappers

The four real per-direction analyticity wrappers
(`partitionFunctionH_analyticAt_latticeGraph`,
`freeEnergyH_analyticOn_latticeGraph`,
`partitionFunctionJ_analyticAt_latticeGraph`,
`freeEnergyJ_analyticOn_latticeGraph`) now live in
`ComplexAnalyticityBasicReal.lean`. -/


/-! #### Complex analyticity (GJ §4.6 Thm 4.6.2)

Direct ℤ^d forwarders for the complex-analyticity package in
`IsingModel/ComplexAnalyticity.lean`: per-variable / joint entire
analyticity of `partitionFunctionComplex`, its `slitPlane`-conditioned
`freeEnergyComplex` counterpart, and the real-complex compatibility
identities. -/

/-! ## Moved: partitionFunctionComplex single-variable analyticAt wrappers

The three single-variable wrappers
`partitionFunctionComplex_analyticAt_h_latticeGraph`,
`partitionFunctionComplex_analyticAt_J_latticeGraph`,
`partitionFunctionComplex_analyticAt_beta_latticeGraph` now live in
`ComplexAnalyticityBasicPartitionSingle.lean`. -/


/-! ## Moved: single-variable freeEnergyComplex wrappers

The three single-variable
`freeEnergyComplex_analyticAt_{h,J,beta}_latticeGraph` wrappers now live in
`ComplexAnalyticityBasicFreeEnergySingle.lean`. -/



/-- **ℤ^d `partitionFunctionComplex` jointly entire in `(J, h, β)`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (z₀ : ℂ × ℂ × ℂ) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) z₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z₀

/-- **ℤ^d `freeEnergyComplex` jointly analytic** (Λ-induced), on
`{Z ∈ slitPlane}`. -/
theorem freeEnergyComplex_analyticAt_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (z₀ : ℂ × ℂ × ℂ)
    (hZ : IsingModel.partitionFunctionComplex
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            z₀.1 z₀.2.1 z₀.2.2
          ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2) z₀ :=
  IsingModel.freeEnergyComplex_analyticAt_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z₀ hZ

end Ambient

end IsingModel
