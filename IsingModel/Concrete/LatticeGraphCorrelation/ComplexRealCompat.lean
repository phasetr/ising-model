import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Factorization

/-!
# ℤ^d real-complex compatibility and Lee-Yang non-vanishing (§4.6)

Instantiates at the subgraph induced on a fixed finite volume `Λ : Finset (Fin d → ℤ)` of
`IsingModel.latticeGraph d` the agreement of the complex partition function and free energy
with the real ones at a real parameter record, the membership of the partition function in
`Complex.slitPlane` on that real slice, and the Friedli-Velenik factorisation of the
partition function as `leeYangNormalization` times the evaluation of `isingEdgePoly` at
`leeYangFugacityVec`; none of those carries a hypothesis. It also instantiates the Lee-Yang
non-vanishing of the partition function, which assumes `0 < β`, `0 < J` and membership of the
field in `leeYangDomain`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d `partitionFunction` / `partitionFunctionComplex` real-complex
compatibility** (Λ-induced):
`↑(Z G p) = Z_ℂ G ↑p.J ↑p.h ↑p.β`. -/
theorem partitionFunction_ofReal_eq_partitionFunctionComplex_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ((IsingModel.partitionFunction
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ)
      = IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) :=
  IsingModel.partitionFunction_ofReal_eq_partitionFunctionComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `partitionFunctionComplex` in `slitPlane` on the real slice**
(Λ-induced). -/
theorem partitionFunctionComplex_mem_slitPlane_of_real_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) ∈ Complex.slitPlane :=
  IsingModel.partitionFunctionComplex_mem_slitPlane_of_real
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d `freeEnergy` / `freeEnergyComplex` real-complex compatibility**
(Λ-induced): `↑(f G p) = f_ℂ G ↑p.J ↑p.h ↑p.β`. -/
theorem freeEnergy_ofReal_eq_freeEnergyComplex_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (p : IsingParams ℝ) :
    ((IsingModel.freeEnergy
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p : ℝ) : ℂ)
      = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) :=
  IsingModel.freeEnergy_ofReal_eq_freeEnergyComplex
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) p

/-- **ℤ^d Friedli-Velenik factorisation** (Λ-induced):
`Z_ℂ G (J, h, β) = N(β, J, h, |E|, |ι|) · P_E(leeYangFugacityVec β h)`.
Thin pass-through of
`IsingModel.partitionFunctionComplex_eq_normalization_mul_isingEdgePoly`.
Combined with Lee-Yang nonvanishing of `P_E` this yields
`Z ≠ 0` on the Lee-Yang domain. -/
theorem partitionFunctionComplex_eq_normalization_mul_isingEdgePoly_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (β J : ℝ) (h : ℂ) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ)
      = IsingModel.leeYangNormalization (β : ℂ) (J : ℂ) h
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ).edgeFinset.card
          (Fintype.card (↑Λ : Type _))
        * (IsingModel.isingEdgePoly (IsingModel.graphToEdgeList
            (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
            (Real.exp (-2 * β * J)))).eval
              (IsingModel.leeYangFugacityVec (β : ℂ) h) :=
  IsingModel.partitionFunctionComplex_eq_normalization_mul_isingEdgePoly
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) β J h

/-- **ℤ^d Lee-Yang nonvanishing on the Lee-Yang domain** (Λ-induced,
ferromagnetic): for `β > 0`, `J > 0`, and `h ∈ leeYangDomain`,
`Z_ℂ G (J, h, β) ≠ 0`. GJ §4.6 Thm 4.6.2 core. Thin pass-through of
`IsingModel.partitionFunctionComplex_ne_zero_on_leeYangDomain`. -/
theorem partitionFunctionComplex_ne_zero_on_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangDomain) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hh

end Ambient

end IsingModel
