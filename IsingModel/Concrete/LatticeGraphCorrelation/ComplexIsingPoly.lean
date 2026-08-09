import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.RealAxis

/-!
# ℤ^d Lee-Yang polynomial non-vanishing and the modulus at real parameters

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the identity of the modulus of the complex partition function
with the real partition function at a real parameter record, which carries no hypothesis, and
the non-vanishing of `isingEdgePoly` evaluated at `leeYangFugacityVec`, on its own and after
multiplication by `leeYangNormalization`. Each non-vanishing statement assumes an edge
activity in `[0, 1)`, `0 < β` and membership of the field in `leeYangDomain`; the normalised
form takes the complex coupling and the edge and site counts entering `leeYangNormalization`
as free parameters, unconstrained by the hypotheses.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d `‖Z_ℂ‖ = Z_ℝ` at real parameters (alias)** (Λ-induced). -/
theorem norm_partitionFunctionComplex_eq_partitionFunction_at_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ‖IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ)‖
      = IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p :=
  IsingModel.norm_partitionFunctionComplex_eq_partitionFunction_at_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d Lee-Yang polynomial evaluation is non-zero on the Lee-Yang
domain** (Λ-induced). -/
theorem isingEdgePoly_eval_leeYangFugacityVec_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    {β : ℝ} (hβ : 0 < β) {h : ℂ} (hh : h ∈ IsingModel.leeYangDomain) :
    (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
        (IsingModel.leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  IsingModel.isingEdgePoly_eval_leeYangFugacityVec_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) ht₀ ht₁ hβ hh

/-- **ℤ^d Lee-Yang normalisation · polynomial is non-zero on the
Lee-Yang domain** (Λ-induced): the Friedli-Velenik RHS factor is
non-zero. -/
theorem leeYangNormalization_mul_isingEdgePoly_eval_ne_zero_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (J : ℂ) {β : ℝ} (hβ : 0 < β) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain)
    (edgeCount siteCount : ℕ) :
    IsingModel.leeYangNormalization (β : ℂ) J h edgeCount siteCount
        * (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) t)).eval
            (IsingModel.leeYangFugacityVec (β : ℂ) h) ≠ 0 :=
  IsingModel.leeYangNormalization_mul_isingEdgePoly_eval_ne_zero
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
    ht₀ ht₁ J hβ hh edgeCount siteCount

end Ambient

end IsingModel
