import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.FugacityCalculus

/-!
# ℤ^d global analyticity and Lee-Yang-domain regularity of the complex partition function

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the analyticity of the complex partition function on a
neighbourhood of every point of the whole space, in the external field and jointly in
`(J, h, β)`, together with its continuity and its analyticity on `leeYangDomain` as a
function of the external field alone. No statement here carries a hypothesis, and the
parameters held fixed range over all of `ℂ`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOnNhd ℂ Set.univ` in `h`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOnNhd_univ_h_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β) Set.univ :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_univ_h
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d joint `AnalyticOnNhd ℂ Set.univ` for `partitionFunctionComplex`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOnNhd_univ_joint_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) :
    AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) z.1 z.2.1 z.2.2)
      Set.univ :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_univ_joint
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)

/-- **ℤ^d `partitionFunctionComplex` `ContinuousOn` on `leeYangDomain`**
(Λ-induced). -/
theorem partitionFunctionComplex_continuousOn_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    ContinuousOn (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_continuousOn_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOn` on `leeYangDomain`**
(Λ-induced). -/
theorem partitionFunctionComplex_analyticOn_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOn ℂ (fun h => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_analyticOn_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

end Ambient

end IsingModel
