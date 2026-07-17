import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Locus

/-!
# Concrete Complex slitPlane-locus `*On` wrappers

Narrow child module for 3 ℤ^d slitPlane-locus `*On`-style wrappers
(`ContinuousOn`, `DifferentiableOn`, `AnalyticOn`) on `latticeGraph d`
extracted from `ComplexSlitPlane.lean`:

* `freeEnergyComplex_continuousOn_slitPlane_locus_latticeGraph`,
* `freeEnergyComplex_differentiableOn_slitPlane_locus_latticeGraph`,
* `freeEnergyComplex_analyticOn_slitPlane_locus_latticeGraph`.

Each result is a thin pass-through of the corresponding abstract
`IsingModel.freeEnergyComplex_{continuousOn,differentiableOn,analyticOn}_slitPlane_locus`
lemma at `Ambient.inducedGraph (IsingModel.latticeGraph d) Λ`. The
theorem names are unchanged from the former `ComplexSlitPlane`
declarations.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `f_ℂ` `ContinuousOn` slitPlane-locus in `h`** (Λ-induced). -/
theorem freeEnergyComplex_continuousOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    ContinuousOn (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_continuousOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `DifferentiableOn` slitPlane-locus in `h`**
(Λ-induced). -/
theorem freeEnergyComplex_differentiableOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    DifferentiableOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_differentiableOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `f_ℂ` `AnalyticOn` slitPlane-locus in `h`** (Λ-induced). -/
theorem freeEnergyComplex_analyticOn_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOn ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOn_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

end Ambient

end IsingModel
