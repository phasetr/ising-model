import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.EventualClosedBallPatches.ClosedBallDeviation

/-!
# Per-stage complex analyticity wrappers: EventualClosedBallDeviation

Consolidated `EventualClosedBallDeviation` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.
-/

namespace IsingModel
namespace Ambient

/-!
# ℤ^d eventual-overlap closed-ball branch-deviation direct-range patch endpoint

This module contains the non-compact-target direct-range wrapper split from
`PerStageComplex.EventualClosedBallPatches.EventualClosedBallDeviation.DirectRange`.
-/


set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap closed-ball branch-deviation data to direct-range
relatively compact patch**: coherent selected-overlap equality is supplied by
pointwise-normalised eventual-overlap data, while closed-ball containment and
branch-deviation Ascoli inputs remain explicit. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch_latticeGraph
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
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K
      (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
        closedEventualData).data)
    (closedEventualDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        (IsingModel.latticeGraph d) Λ p K closedEventualData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ
    closedEventualData geom closedEventualDeviation

/-!
# ℤ^d compact-target eventual-overlap closed-ball branch-deviation direct-range patch endpoint

This module contains the compact-target direct-range wrapper split from
`PerStageComplex.EventualClosedBallPatches.EventualClosedBallDeviation.DirectRange`.
-/


set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap closed-ball branch-deviation
direct-range patch input**: compactness extracts the selected finite geometry,
and pointwise-normalised eventual-overlap data supplies coherent
selected-overlap equality for the closed-ball branch-deviation route. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch_isCompact_latticeGraph
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K
        (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
          closedEventualData).data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
          (IsingModel.latticeGraph d) Λ p K closedEventualData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK
    closedEventualData

/-!
# ℤ^d eventual-overlap closed-ball branch-deviation direct-range patch wrappers

This compatibility module re-exports the eventual-overlap closed-ball
branch-deviation direct-range wrappers split into child modules.
-/

/-!
# ℤ^d positive-real direct-range closed-ball branch-deviation patch wrappers

This module contains the positive-real direct-range closed-ball
branch-deviation wrapper split from
`PerStageComplex.EventualClosedBallPatches.EventualClosedBallDeviation.PosReal`.
-/


set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to direct-range closed-ball
branch-deviation patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts finite
geometry, and branch-deviation data feeds the direct-range route. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_directRange_patch_isCompact_latticeGraph
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
    ∃ closedData :
        Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K closedData.data,
        Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            (IsingModel.latticeGraph d) Λ p K closedData geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap closed-ball branch-local data to direct-range patch
via branch deviation**: branch-local boundedness supplies branch-deviation data
through the closed-ball principal free-energy bound, while eventual-overlap data
supplies selected-overlap equality. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocalViaDeviationRelCompact_directRange_patch_latticeGraph
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
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K
      (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
        closedEventualData).data)
    (closedEventualLocal :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        (IsingModel.latticeGraph d) Λ p K closedEventualData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocalViaDeviationRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ
    closedEventualData geom closedEventualLocal

set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap closed-ball branch-local
via-deviation direct-range patch input**: compactness extracts the selected
finite geometry before branch-local data is converted to branch-deviation data
and patched. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocalViaDeviationRelCompact_directRange_patch_isCompact_latticeGraph
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K
        (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
          closedEventualData).data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
          (IsingModel.latticeGraph d) Λ p K closedEventualData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK
    closedEventualData

set_option linter.style.longLine false in
/-- **ℤ^d eventual-overlap closed-ball branch-deviation data to direct-range
patch via branch local boundedness**: branch-deviation bounds supply
branch-local boundedness through the closed-ball principal free-energy bound,
while eventual-overlap data supplies selected-overlap equality. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch_latticeGraph
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
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K
      (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
        closedEventualData).data)
    (closedEventualDeviation :
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        (IsingModel.latticeGraph d) Λ p K closedEventualData geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ
    closedEventualData geom closedEventualDeviation

set_option linter.style.longLine false in
/-- **ℤ^d compact target to eventual-overlap closed-ball branch-deviation
via-local direct-range patch input**: compactness extracts the selected finite
geometry before branch-deviation data is converted to branch-local boundedness
and patched. -/
theorem
freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch_isCompact_latticeGraph
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K
        (Ambient.LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)
          closedEventualData).data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
          (IsingModel.latticeGraph d) Λ p K closedEventualData geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK
    closedEventualData

/-!
# ℤ^d positive-real via-local closed-ball branch-deviation patch wrappers

This module contains the positive-real named via-local closed-ball
branch-deviation wrapper split from
`PerStageComplex.EventualClosedBallPatches.EventualClosedBallDeviation.PosReal`.
-/


set_option linter.style.longLine false in
/-- **ℤ^d positive-real compact target to named via-local direct-range
closed-ball branch-deviation patch input**: positive real ferromagnetic
parameters construct the closed-ball all-stage branch data, compactness
extracts finite geometry, and branch-deviation data feeds the named via-local
route. -/
theorem
freeEnergyComplexAlongExhaustion_posRealClosedBallDeviationViaLocal_directRange_patch_isCompact_latticeGraph
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
    ∃ closedData :
        Ambient.LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
          (IsingModel.latticeGraph d) Λ p K closedData.data,
        Ambient.LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            (IsingModel.latticeGraph d) Λ p K closedData geom →
          ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
              (IsingModel.latticeGraph d) Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) =
                ((Ambient.freeEnergyInfinite
                  (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_posRealClosedBallDeviationViaLocal_directRange_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hβ hJ hK hKsub hpK

/-!
# ℤ^d positive-real closed-ball branch-deviation patch wrappers

This compatibility module re-exports the positive-real closed-ball
branch-deviation wrappers split into child modules.
-/

/-!
# ℤ^d eventual-overlap closed-ball branch-deviation patch wrappers

This compatibility module re-exports the split eventual-overlap closed-ball
branch-deviation wrapper layer.
-/

end Ambient
end IsingModel
