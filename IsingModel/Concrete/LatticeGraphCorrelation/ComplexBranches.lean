import IsingModel.Concrete.LatticeGraphBED.LatticeBoundaryBED
import IsingModel.ComplexAnalyticity.DomainGeometry

/-!
# ℤ^d Lee-Yang non-vanishing and the local branch of the complex free energy (§4.6)

All statements are instantiated at the subgraph induced on a fixed finite volume
`Λ : Finset (Fin d → ℤ)` of `IsingModel.latticeGraph d`. The complex partition function does
not vanish on `leeYangSubdomain`, and maps `leeYangDomain` into the non-zero complex numbers;
each of these assumes `0 < β` and `0 < J`. The locus in the external field on which the
partition function lies in `Complex.slitPlane` is open, and the complex free-energy density
is `AnalyticOnNhd` on that locus; each of these is stated for arbitrary complex `J` and `β`
and carries no hypothesis. At a point of `leeYangDomain` there is a representative analytic
at that point whose exponential, scaled by the cardinality of `Λ`, is the partition function
and whose value there is the principal-branch free energy; that statement assumes `Λ`
nonempty, `0 < β` and `0 < J`.
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

end Ambient

end IsingModel
