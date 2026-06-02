import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap.RawBranchData

/-!
# Eventual-overlap local-family wrappers

This module contains the eventual-overlap local-family wrapper split from
`PerStageComplex.Branches.EventualOverlap.EventuallyEqOn`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d packaged local-cover branch-limit family from eventual overlap
data**: raw Lee-Yang local-cover branch data whose stage branches are
eventually equal on every overlap can be bundled into
`LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn_latticeGraph
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
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn
    (IsingModel.latticeGraph d) Λ J β hr hsub hbranch hconv hoverlap

end Ambient

end IsingModel
