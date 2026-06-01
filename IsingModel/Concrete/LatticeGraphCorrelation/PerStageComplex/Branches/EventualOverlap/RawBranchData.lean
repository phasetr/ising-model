import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.LocalCoverPatch

/-!
# Raw eventual-overlap branch-data wrappers

This module contains the raw branch-data wrappers split from
`PerStageComplex.Branches.EventualOverlap`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d packaged local-cover branch-limit family from raw branch data**:
raw pointwise Lee-Yang local-cover branch data with locally uniform limits and
pairwise overlap compatibility can be bundled into
`LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_branchData
    (IsingModel.latticeGraph d) Λ J β hr hsub hbranch hconv hcompat

/-- **ℤ^d real-centred packaged local-cover branch-limit family from raw
branch data**: raw coherent Lee-Yang local-cover branch data, real-centre
membership, and centre normalisation can be bundled into
`LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_branchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_branchData
    (IsingModel.latticeGraph d) Λ p hp hr hsub hbranch hconv hcompat hcenter

end Ambient

end IsingModel
