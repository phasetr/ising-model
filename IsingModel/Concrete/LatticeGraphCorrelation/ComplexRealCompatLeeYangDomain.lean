import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Branches

/-!
# ℤ^d Lee-Yang domain analyticity wrappers

Narrow child module for three ℤ^d Λ-induced Lee-Yang-domain analyticity
wrappers extracted from `ComplexRealCompat.lean`:

* `freeEnergyComplex_analyticAt_h_ofReal_latticeGraph`,
* `partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph`,
* `logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph`.
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
