import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Subdomain

/-!
# ℤ^d Lee-Yang subdomain analyticity wrappers

Narrow child module for four ℤ^d Lee-Yang subdomain wrappers extracted
from `ComplexRealCompat.lean`:

* `partitionFunctionComplex_re_pos_of_leeYangSubdomain_latticeGraph`,
* `partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain_latticeGraph`,
* `freeEnergyComplex_analyticAt_h_of_leeYangSubdomain_latticeGraph`,
* `freeEnergyComplex_analyticOnNhd_leeYangSubdomain_latticeGraph`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `Re Z_ℂ > 0` on the Lee-Yang subdomain** (Λ-induced): for
`β > 0` and `h` with `β · |h.im| · |Λ| < π/2`,
`0 < Re(Z_ℂ G (J, h, β))`. Thin pass-through of
`IsingModel.partitionFunctionComplex_re_pos_of_leeYangSubdomain`. -/
theorem partitionFunctionComplex_re_pos_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2) :
    0 < (IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h (β : ℂ)).re :=
  IsingModel.partitionFunctionComplex_re_pos_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ

/-- **ℤ^d `Z_ℂ ∈ slitPlane` on the Lee-Yang subdomain** (Λ-induced):
corollary of the `Re Z > 0` result, feeding `Complex.log` analyticity. -/
theorem partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ∈ Complex.slitPlane :=
  IsingModel.partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ

/-- **ℤ^d `freeEnergyComplex` analytic in `h` on the Lee-Yang subdomain**
(Λ-induced). Finite-volume GJ §4.6 Thm 4.6.2 on the subdomain
`β · |Im h| · |Λ| < π/2`. -/
theorem freeEnergyComplex_analyticAt_h_of_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) {h : ℂ}
    (himπ : β * |h.im| * (Fintype.card (↑Λ : Type _) : ℝ) < Real.pi / 2) :
    AnalyticAt ℂ (fun h' => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
      (J : ℂ) h' (β : ℂ)) h :=
  IsingModel.freeEnergyComplex_analyticAt_h_of_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J himπ

/-- **ℤ^d `freeEnergyComplex` `AnalyticOnNhd` on the Lee-Yang subdomain**
(Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β : ℝ} (hβ : 0 < β) (J : ℝ) :
    AnalyticOnNhd ℂ (fun h' => IsingModel.freeEnergyComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h' (β : ℂ))
      (IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :=
  IsingModel.freeEnergyComplex_analyticOnNhd_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ J

end Ambient
end IsingModel
