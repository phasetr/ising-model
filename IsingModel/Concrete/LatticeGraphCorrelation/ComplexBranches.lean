import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.DomainGeometry

/-!
# Concrete Complex log-branch construction wrappers

Narrow child module for concrete log Z / freeEnergyComplex local-branch
construction wrappers on `latticeGraph d`. Covers
`partitionFunctionComplex_ne_zero_on_leeYangSubdomain_latticeGraph`,
`partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain_latticeGraph`,
`freeEnergyComplex_analyticOnNhd_slitPlane_locus_latticeGraph`,
`isOpen_freeEnergy_analyticity_locus_latticeGraph`,
`exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph`,
`exists_logZ_holomorphic_branch_on_ball_latticeGraph`,
`exists_logZ_analytic_branch_on_ball_latticeGraph`,
`exists_logZ_analyticAt_of_leeYangDomain_latticeGraph`, and
`exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain_latticeGraph`.
The `exists_freeEnergyComplex_{analyticOnNhd,differentiableOn}_ball_latticeGraph`
ball wrappers now live in `ComplexBranchesFreeEnergyBall.lean`. The theorem
names are unchanged from the former `Complex` declarations.
-/

namespace IsingModel
namespace Ambient


/-- **ℤ^d `Z_ℂ ≠ 0` on `leeYangSubdomain`** (Λ-induced, ferromagnetic). -/
theorem partitionFunctionComplex_ne_zero_on_leeYangSubdomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) {h : ℂ}
    (hh : h ∈ IsingModel.leeYangSubdomain β (Fintype.card (↑Λ : Type _))) :
    IsingModel.partitionFunctionComplex
        (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
        (J : ℂ) h (β : ℂ) ≠ 0 :=
  IsingModel.partitionFunctionComplex_ne_zero_on_leeYangSubdomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hh

/-- **ℤ^d `Z_ℂ MapsTo ≠ 0` on `leeYangDomain`** (Λ-induced,
ferromagnetic): `Set.MapsTo` restatement of the Lee-Yang
non-vanishing. -/
theorem partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Set.MapsTo (fun h : ℂ => IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) (J : ℂ) h (β : ℂ))
      IsingModel.leeYangDomain {z : ℂ | z ≠ 0} :=
  IsingModel.partitionFunctionComplex_mapsTo_ne_zero_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ

/-- **ℤ^d `freeEnergyComplex` `AnalyticOnNhd` on the principal-branch
`slitPlane` analyticity locus** (Λ-induced). -/
theorem freeEnergyComplex_analyticOnNhd_slitPlane_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    AnalyticOnNhd ℂ (fun h => IsingModel.freeEnergyComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β)
      {h : ℂ | IsingModel.partitionFunctionComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.freeEnergyComplex_analyticOnNhd_slitPlane_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-- **ℤ^d `freeEnergy` analyticity locus is open** (Λ-induced). -/
theorem isOpen_freeEnergy_analyticity_locus_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ)) (J β : ℂ) :
    IsOpen {h : ℂ | IsingModel.partitionFunctionComplex
      (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J h β
        ∈ Complex.slitPlane} :=
  IsingModel.isOpen_freeEnergy_analyticity_locus
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) J β

/-! ## Moved: ℤ^d exists_logZ_* branch-on-ball wrappers

The four wrappers
`exists_logZ_branch_on_ball_of_leeYangDomain_latticeGraph`,
`exists_logZ_holomorphic_branch_on_ball_latticeGraph`,
`exists_logZ_analytic_branch_on_ball_latticeGraph`,
`exists_logZ_analyticAt_of_leeYangDomain_latticeGraph`
now live in `ComplexBranchesLogZ.lean`. -/

/-- **ℤ^d GJ §4.6 Thm 4.6.2 finite-volume (branch form)** (Λ-induced,
nonempty `Λ`, ferromagnetic): at every `h₀ ∈ leeYangDomain` there is an
`AnalyticAt` representative `f` with `exp(|Λ|·f) = Z` and
`f h₀ = freeEnergyComplex …`. -/
theorem exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain_latticeGraph
    (d : ℕ) (Λ : Finset (Fin d → ℤ))
    [Nonempty (↑Λ : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J)
    {h₀ : ℂ} (hmem : h₀ ∈ IsingModel.leeYangDomain) :
    ∃ f : ℂ → ℂ,
        AnalyticAt ℂ f h₀
      ∧ Complex.exp ((Fintype.card (↑Λ : Type _) : ℂ) * f h₀)
          = IsingModel.partitionFunctionComplex
              (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
              (J : ℂ) h₀ (β : ℂ)
      ∧ f h₀ = IsingModel.freeEnergyComplex
          (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ)
          (J : ℂ) h₀ (β : ℂ) :=
  IsingModel.exists_freeEnergyComplex_analyticAt_branch_of_leeYangDomain
    (Ambient.inducedGraph (IsingModel.latticeGraph d) Λ) hβ hJ hmem

/-! ## Moved: freeEnergyComplex local-branch ball wrappers

The two `exists_freeEnergyComplex_{analyticOnNhd,differentiableOn}_ball_latticeGraph`
wrappers now live in `ComplexBranchesFreeEnergyBall.lean`. -/



end Ambient

end IsingModel
