import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen.PointwiseAllStage.RealCover

/-!
# Pointwise-normalised all-stage compact geometry wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact real finite-cover geometry from pointwise-normalised
all-stage data**: compactness extracts finitely many all-stage Lee-Yang balls
covering `K`, with a selected centre at the real field. -/
theorem
    exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    Nonempty (Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data) :=
  Ambient.exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage compact finite geometry to compact
real-cover patch**: feeds compactness-extracted all-stage centres into the
compact real-cover patch bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStage_compactRealCOpen_patch_geom_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    {A : ∀ i : Fin geom.n,
      Set C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    {Fc : ∀ i : Fin geom.n, ℕ →
      C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      data.branchData.branchFamily (geom.center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (geom.center i) m)
        (data.branchData.branchFamily (geom.center j) m)
        (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
          ∩ Metric.ball (geom.center j : ℂ)
            (data.branchData.radius (geom.center j)))) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_geom
    (IsingModel.latticeGraph d) Λ p hBED hd data geom hA hFc_mem hFres hoverlap

end Ambient
end IsingModel
