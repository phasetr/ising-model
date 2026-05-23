import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.RangeAscoliPatches.BranchRelCompact

/-!
# ℤ^d branch-local direct-range patch wrappers

This module contains branch-local and eventual-overlap direct-range wrappers
for the relatively compact patch layer.
-/

namespace IsingModel
namespace Ambient

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

end Ambient

end IsingModel
