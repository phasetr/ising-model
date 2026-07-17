import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.Factorization

/-!
# Concrete real-complex compatibility / Lee-Yang domain wrappers

Narrow child module for concrete real-complex compatibility,
Lee-Yang-domain non-vanishing, and analyticity restriction wrappers on
`latticeGraph d`. Twelve theorems remain here including
`partitionFunction_ofReal_eq_partitionFunctionComplex_latticeGraph`,
`partitionFunctionComplex_mem_slitPlane_of_real_latticeGraph`,
`freeEnergy_ofReal_eq_freeEnergyComplex_latticeGraph`,
`partitionFunctionComplex_eq_normalization_mul_isingEdgePoly_latticeGraph`,
`partitionFunctionComplex_ne_zero_on_leeYangDomain_latticeGraph`,
`partitionFunctionComplex_re_pos_of_leeYangSubdomain_latticeGraph`, and
`freeEnergyComplex_analyticAt_h_of_leeYangSubdomain_latticeGraph`. The
ten `*_at_real_latticeGraph` real-axis evaluation wrappers
(`partitionFunctionComplex_at_real_pos`, `freeEnergyComplex_at_real`,
`norm_partitionFunctionComplex_at_real`, etc.) were carved out into
`ComplexRealCompatAtReal.lean` in PR #2121. Theorem names are
unchanged from the former `Complex` declarations.
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

/-! #### Lee-Yang domain / subdomain analyticity (GJ §4.6 Thm 4.6.2)

Direct ℤ^d forwarders for the Lee-Yang nonvanishing and free-energy
analyticity package from `IsingModel/ComplexAnalyticity.lean`:
Friedli-Velenik factorisation, Lee-Yang nonvanishing, `Re Z > 0` /
`slitPlane` on the subdomain, `freeEnergyComplex` analyticity on the
subdomain / real slice, and `logDeriv Z / Z` on the entire Lee-Yang
domain. These feed GJ §4.6 Thm 4.6.2 Vitali completion at ℤ^d. -/

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

/-! ## Moved: ℤ^d Lee-Yang subdomain analyticity wrappers

The four wrappers
`partitionFunctionComplex_re_pos_of_leeYangSubdomain_latticeGraph`,
`partitionFunctionComplex_mem_slitPlane_of_leeYangSubdomain_latticeGraph`,
`freeEnergyComplex_analyticAt_h_of_leeYangSubdomain_latticeGraph`,
`freeEnergyComplex_analyticOnNhd_leeYangSubdomain_latticeGraph` now live
in `ComplexRealCompatLeeYangSubdomain.lean`. -/


/-! ## Moved: Lee-Yang domain analyticity wrappers

The three `freeEnergyComplex_analyticAt_h_ofReal_latticeGraph`,
`partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph`,
`logDeriv_partitionFunctionComplex_analyticOnNhd_leeYangDomain_latticeGraph`
wrappers now live in `ComplexRealCompatLeeYangDomain.lean`. -/



/-! ## Moved: real-axis evaluation of the complex Z / f

The ten `*_at_real_latticeGraph` wrappers (`partitionFunctionComplex_at_real_pos`,
`freeEnergyComplex_at_real`, `freeEnergyComplex_ofReal_eq_freeEnergy`,
`{partitionFunctionComplex,freeEnergyComplex}_{re_pos,im_zero}_at_real`,
`log_partitionFunctionComplex_im_zero_at_real`,
`freeEnergyComplex_re_eq_freeEnergy_at_real`,
`norm_partitionFunctionComplex_at_real`, and
`partitionFunctionComplex_is_pos_real_at_real`) now live in
`ComplexRealCompatAtReal.lean`. -/


end Ambient

end IsingModel
