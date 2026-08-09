import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Branches

/-!
# ℤ^d analyticity on the Lee-Yang domain and of the logarithmic derivative

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the analyticity of the complex free-energy density in the
external field at a real base point, and the analyticity on a neighbourhood of
`leeYangDomain` of the complex partition function and of its logarithmic derivative. The
free-energy statement is given for real `J`, `h₀` and `β` and carries no hypothesis; the
partition-function statement is given for arbitrary complex `J` and `β` and likewise carries
no hypothesis; the logarithmic-derivative statement is given for real `J` and `β` and assumes
`0 < β` and `0 < J`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `freeEnergyComplex` analytic in `h` at real `h₀`** (Λ-induced,
real-slice corollary; no ferromagnetic hypothesis). -/
theorem freeEnergyComplex_analyticAt_h_ofReal_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J h₀ β : ℝ) :
    AnalyticAt ℂ (fun h => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ))
      (h₀ : ℂ) :=
  IsingModel.freeEnergyComplex_analyticAt_h_ofReal
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h₀ β

/-- **ℤ^d `partitionFunctionComplex` `AnalyticOnNhd` on the Lee-Yang
domain** (Λ-induced): globally entire in `h`. -/
theorem partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ
        (fun h' => IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h' β)
      IsingModel.leeYangDomain :=
  IsingModel.partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d logarithmic derivative `Z'/Z` analytic on Lee-Yang domain**
(Λ-induced, ferromagnetic `β > 0`, `J > 0`): input to the Morera-based
branch construction of `log Z`. -/
theorem logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    AnalyticOnNhd ℂ (fun h : ℂ =>
        deriv (fun h' => IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h' (β : ℂ)) h
          / IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h (β : ℂ))
      IsingModel.leeYangDomain :=
  IsingModel.logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

end Ambient
end IsingModel
