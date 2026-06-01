import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen.FiniteSubseqCompactOpen.CompactOpen

/-!
# SubseqCompactOpen split — finite subsequence patch wrappers

Part of the split `IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen`
development.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d packaged finite subsequence branch-limit patching**: a compatible
`Ambient.LeeYangFiniteSubseqBranchLimitFamily` patches to one function
differentiable on the finite union of its balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n h0 r) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch
    (IsingModel.latticeGraph d) Λ J β n family

/-- **ℤ^d packaged finite subsequence branch-limit patching with real-centre
identification**: if one finite-cover ball is centred at the real field `p.h`,
then a compatible `Ambient.LeeYangFiniteSubseqBranchLimitFamily` patches on the
finite union of balls and the patched value at the real centre agrees with
`↑Ambient.freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    (family : Ambient.LeeYangFiniteSubseqBranchLimitFamily
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ) n h0 r)
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
      DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
      g (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
    (IsingModel.latticeGraph d) Λ p hBED hd n family i₀ hcenter hr

end Ambient
end IsingModel
