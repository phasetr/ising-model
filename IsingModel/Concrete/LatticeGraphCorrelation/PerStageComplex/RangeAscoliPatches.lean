import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.SubseqCompactOpen

/-!
# ℤ^d range and branch-deviation Ascoli patch wrappers

Mechanical child split from `PerStageComplex.lean`.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d pointwise-normalised all-stage range-closure compact-open data to
compact real-cover patch**: compactness of the closure of the selected
stage-restriction range supplies the compact-open carrier for the all-stage
patch bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_latticeGraph
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
    (rangeClosure :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom rangeClosure

/-- **ℤ^d compact target to all-stage range-closure compact-open patch input**:
compactness of `K` extracts the finite all-stage geometry, and compactness of
each closure of the selected stage-restriction range yields the compact
real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage relatively compact range data to
compact real-cover patch**: compact carriers containing the selected
stage-restriction ranges supply compactness of the range closures. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpen_patch_latticeGraph
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
    (relCompact :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom relCompact

/-- **ℤ^d compact target to all-stage relatively compact range patch input**:
compactness of `K` extracts the finite all-stage geometry, and compact
carriers containing each selected stage-restriction range yield the compact
real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage Arzelà-Ascoli data to compact
real-cover patch**: compactness of the pointwise function-space image and
equicontinuity for the selected all-stage geometry supply compact-open
compactness via Arzelà-Ascoli. -/
theorem freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_latticeGraph
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
    (ascoli : Ambient.LeeYangPointwiseNormAllStageCompactRealAscoliData
      (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom ascoli

/-- **ℤ^d compact target to all-stage Arzelà-Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, and Ascoli-style
compact-open data for that geometry yields the compact real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage closed-product Ascoli data to compact
real-cover patch**: compact pointwise targets, closed pointwise image, and
equicontinuity for the selected all-stage geometry supply the Ascoli input. -/
theorem freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_latticeGraph
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
    (closedProduct :
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom closedProduct

/-- **ℤ^d compact target to all-stage closed-product Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, and closed-product
Ascoli data for that geometry yields the compact real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage norm-bounded closed-product Ascoli
data to compact real-cover patch**: pointwise norm bounds supply the compact
closed-ball targets required by the closed-product Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_latticeGraph
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
    (normBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom normBounded

/-- **ℤ^d compact target to all-stage norm-bounded closed-product Ascoli patch
input**: compactness of `K` extracts the finite all-stage geometry, and
norm-bounded closed-product Ascoli data for that geometry yields the compact
real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage range norm-bounded Ascoli data to
compact real-cover patch**: range carriers reduce the norm-bounded Ascoli
input to stagewise pointwise norm bounds for the selected continuous
restrictions. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_latticeGraph
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
    (rangeBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom rangeBounded

/-- **ℤ^d compact target to all-stage range norm-bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, and range
norm-bounded Ascoli data for that geometry yields the compact real-cover patch. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d pointwise-normalised all-stage range norm-bounded Ascoli data to a
relatively compact range patch**: closedness, stagewise norm bounds, and
equicontinuity make the actual stage-restriction range a compact carrier. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_latticeGraph
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
    (rangeBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom rangeBounded

/-- **ℤ^d compact target to all-stage range norm-bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry, and
range norm-bounded Ascoli data supplies compact carriers for the actual
stage-restriction ranges. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d branch norm-bounded Ascoli data to a relatively compact range
patch**: branch-family pointwise norm bounds are transported to the selected
continuous restrictions and then fed to the relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch_latticeGraph
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
    (branchBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom branchBounded

/-- **ℤ^d compact target to branch norm-bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry, and branch
norm-bounded Ascoli data supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d branch constant norm-bounded Ascoli data to a relatively compact
range patch**: ballwise constant branch-family bounds are converted to branch
pointwise bounds before applying the relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_latticeGraph
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
    (constBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom constBounded

/-- **ℤ^d compact target to branch constant norm-bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry, and
branch constant norm-bounded data supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-- **ℤ^d branch locally bounded Ascoli data to a relatively compact range
patch**: one branch-family bound is chosen on each selected ball and then fed
through the branch constant relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch_latticeGraph
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
    (locallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom locallyBounded

/-- **ℤ^d compact target to branch locally bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry, and branch
locally bounded data supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

set_option linter.style.longLine false in
/-- **ℤ^d branch locally bounded Ascoli data to a direct-range relatively
compact patch**: branch locally bounded data is converted directly to
relatively compact range data before applying the all-stage range patch
endpoint. -/
theorem
freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch_latticeGraph
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
    (locallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom locallyBounded

set_option linter.style.longLine false in
/-- **ℤ^d compact target to direct-range branch locally bounded patch input**:
compactness of `K` extracts the finite all-stage geometry; branch locally
bounded Ascoli data then feeds the direct relatively compact range route. -/
theorem
freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

set_option linter.style.longLine false in
/-- **ℤ^d branch-local data to direct-range patch via branch deviation**:
branch-local boundedness and an explicit principal free-energy local bound are
converted to branch-deviation data before patching. -/
theorem
freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch_latticeGraph
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
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      ‖Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
    (locallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom
    freeEnergy_bound locallyBounded

set_option linter.style.longLine false in
/-- **ℤ^d compact target to branch-local via-deviation direct-range patch
input**: compactness extracts finite all-stage geometry; branch-local
boundedness and an explicit principal free-energy local bound are then
converted to branch-deviation data before patching. -/
theorem
freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      (∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
        (_hz : z ∈ Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i))),
        ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C) →
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap branch locally bounded Ascoli data to a direct-range
relatively compact patch**: coherent selected-overlap equality is supplied by
the pointwise-normalised eventual-overlap package, while the remaining
branch-local Ascoli inputs feed the direct relatively compact range route. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (eventualData :
      Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ p)
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K
      (Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        (IsingModel.latticeGraph d) Λ p eventualData))
    (eventualLocallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K eventualData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i =>
          eventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd eventualData geom eventualLocallyBounded

set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap branch-local direct-range patch
input**: compactness extracts the selected all-stage finite geometry, and the
pointwise-normalised eventual-overlap package supplies coherent
selected-overlap equality for the branch-local Ascoli route. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (eventualData :
      Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ p) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K
        (Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          (IsingModel.latticeGraph d) Λ p eventualData),
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K eventualData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i =>
              eventualData.pointwiseData.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK eventualData

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap branch-local data to direct-range patch via branch
deviation**: branch-local boundedness and an explicit principal free-energy
local bound are converted to branch-deviation data, while eventual-overlap
data supplies selected-overlap equality. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (eventualData :
      Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ p)
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K
      (Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        (IsingModel.latticeGraph d) Λ p eventualData))
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (eventualData.pointwiseData.branchData.radius (geom.center i))),
      ‖Ambient.freeEnergyComplexAlongExhaustion
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
    (eventualLocallyBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K eventualData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i =>
          eventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd eventualData geom
    freeEnergy_bound eventualLocallyBounded

set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap branch-local via-deviation
direct-range patch input**: compactness extracts finite all-stage geometry,
branch-local boundedness is converted to branch-deviation data using the
explicit principal free-energy local bound, and eventual-overlap data supplies
selected overlap. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (eventualData :
      Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ p) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K
        (Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          (IsingModel.latticeGraph d) Λ p eventualData),
      (∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
        (_hz : z ∈ Metric.ball (geom.center i : ℂ)
          (eventualData.pointwiseData.branchData.radius (geom.center i))),
        ‖Ambient.freeEnergyComplexAlongExhaustion
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C) →
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K eventualData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i =>
              eventualData.pointwiseData.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK eventualData

/-- **ℤ^d branch-deviation locally bounded Ascoli data to a relatively compact
range patch**: local boundedness of the principal finite-volume free energy
and a uniform branch-deviation bound yield the branch locally bounded input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_latticeGraph
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
    (deviationBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom deviationBounded

/-- **ℤ^d compact target to branch-deviation locally bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry, and
branch-deviation locally bounded data supplies the relative-compactness input.
-/
theorem
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

set_option linter.style.longLine false in
/-- **ℤ^d branch-deviation Ascoli data to a direct-range relatively compact
patch**: branch-deviation data is converted directly to relatively compact
range data before applying the all-stage range patch endpoint. -/
theorem
freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch_latticeGraph
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
    (deviationBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom deviationBounded

set_option linter.style.longLine false in
/-- **ℤ^d compact target to direct-range branch-deviation patch input**:
compactness of `K` extracts the finite all-stage geometry; branch-deviation
Ascoli data then feeds the direct relatively compact range route. -/
theorem
freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

set_option linter.style.longLine false in
/-- **ℤ^d branch-deviation Ascoli data through the named branch-local
relatively compact patch route**: branch-deviation data first derives
branch-local boundedness, then uses the branch-local range conversion before
applying the all-stage range patch endpoint. -/
theorem
freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch_latticeGraph
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
    (deviationBounded :
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        (IsingModel.latticeGraph d) Λ p K data geom) :
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
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom deviationBounded

set_option linter.style.longLine false in
/-- **ℤ^d compact target to branch-deviation named via-local patch input**:
compactness of `K` extracts the finite all-stage geometry; branch-deviation
Ascoli data then feeds the named branch-local relatively compact range route.
-/
theorem
freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to branch-deviation relatively compact
patch input**: positive real ferromagnetic parameters construct the all-stage
branch data, compactness extracts finite geometry, and branch-deviation Ascoli
data feeds the relative-compactness route. -/
theorem
freeEnergyComplexAlongExhaustion_posRealBranchDeviationRelCompact_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K data,
        Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
            (IsingModel.latticeGraph d) Λ p K data geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posRealBranchDeviationRelCompact_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to direct-range branch-deviation patch
input**: positive real ferromagnetic parameters construct the all-stage branch
data, compactness extracts finite geometry, and branch-deviation Ascoli data
feeds the direct relatively compact range route. -/
theorem
freeEnergyComplexAlongExhaustion_posRealBranchDeviation_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K data,
        Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
            (IsingModel.latticeGraph d) Λ p K data geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posRealBranchDeviation_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to named via-local branch-deviation
direct-range patch input**: positive real ferromagnetic parameters construct
the all-stage branch data, compactness extracts finite geometry, and
branch-deviation Ascoli data feeds the named via-local range route. -/
theorem
freeEnergyComplexAlongExhaustion_posRealBranchDeviationViaLocal_directRange_patch_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K data,
        Ambient.LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
            (IsingModel.latticeGraph d) Λ p K data geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posRealBranchDeviationViaLocal_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

end Ambient

end IsingModel
