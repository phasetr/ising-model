import IsingModel.Concrete.LatticeGraphBED
import IsingModel.ComplexAnalyticity
import IsingModel.AmbientComplexAnalyticity

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


/-- **ℤ^d `partitionFunction` analytic in `h`** at Λ-induced subgraph. -/
theorem partitionFunctionH_analyticAt_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℝ) :
    AnalyticAt ℝ
      (fun h => partitionFunctionΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩) h₀ :=
  IsingModel.partitionFunctionH_analyticAt
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `freeEnergyH` analytic on `(0, ∞)`** at Λ-induced subgraph. -/
theorem freeEnergyH_analyticOn_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℝ) :
    AnalyticOn ℝ
      (IsingModel.freeEnergyH
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β)
      (Set.Ioi 0) :=
  IsingModel.freeEnergyH_analyticOn
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `partitionFunction` analytic in `J`** at Λ-induced subgraph. -/
theorem partitionFunctionJ_analyticAt_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℝ) :
    AnalyticAt ℝ
      (fun J => partitionFunctionΛ (IsingModel.latticeGraph d) Λ ⟨J, h, β⟩) J₀ :=
  IsingModel.partitionFunctionJ_analyticAt
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀

/-- **ℤ^d `freeEnergyJ` analytic on `(0, ∞)`** at Λ-induced subgraph. -/
theorem freeEnergyJ_analyticOn_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β : ℝ) :
    AnalyticOn ℝ
      (IsingModel.freeEnergyJ
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β)
      (Set.Ioi 0) :=
  IsingModel.freeEnergyJ_analyticOn
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β

/-! #### Complex analyticity (GJ §4.6 Thm 4.6.2)

Direct ℤ^d forwarders for the complex-analyticity package in
`IsingModel/ComplexAnalyticity.lean`: per-variable / joint entire
analyticity of `partitionFunctionComplex`, its `slitPlane`-conditioned
`freeEnergyComplex` counterpart, and the real-complex compatibility
identities. -/

/-- **ℤ^d `partitionFunctionComplex` entire in `h`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β h₀ : ℂ) :
    AnalyticAt ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) h₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β h₀

/-- **ℤ^d `partitionFunctionComplex` entire in `J`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_J_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (h β J₀ : ℂ) :
    AnalyticAt ℂ (fun J => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) J₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_J
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) h β J₀

/-- **ℤ^d `partitionFunctionComplex` entire in `β`** (Λ-induced). -/
theorem partitionFunctionComplex_analyticAt_beta_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h β₀ : ℂ) :
    AnalyticAt ℂ (fun β => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) β₀ :=
  IsingModel.partitionFunctionComplex_analyticAt_beta
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β₀

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
