import IsingModel.AmbientComplexAnalyticity.CompactPatches

/-!
# Ambient complex analyticity branch-deviation patches

Mechanical child split from `AmbientComplexAnalyticity.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Branch-deviation locally bounded Ascoli data to a relatively compact
range patch**: local boundedness of the principal finite-volume free energy,
together with a uniform branch-deviation bound, gives the branch local
boundedness input and hence the relative-compactness patch. -/
theorem freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (deviationBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        G Λ p K data geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toBranchLocallyBoundedData
      G Λ p K data geom deviationBounded)

/-- **Compact target to branch-deviation locally bounded relatively compact
patch input**: compactness of `K` extracts the finite all-stage geometry; the
branch-deviation locally bounded data then supplies the relative-compactness
input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
          G Λ p K data geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK data with
    ⟨geom⟩
  exact ⟨geom, fun deviationBounded =>
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch
      G Λ p hBED hd data geom deviationBounded⟩

set_option linter.style.longLine false in
/-- **Branch-deviation Ascoli data to a direct-range relatively compact
patch**: branch-deviation data is converted directly to relatively compact
range data before applying the all-stage range patch endpoint. -/
theorem freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (deviationBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        G Λ p K data geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData
      G Λ p K data geom deviationBounded)

set_option linter.style.longLine false in
/-- **Compact target to direct-range branch-deviation patch input**:
compactness of `K` extracts the finite all-stage geometry; branch-deviation
Ascoli data then feeds the direct relatively compact range route. -/
theorem
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
          G Λ p K data geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK data with
    ⟨geom⟩
  exact ⟨geom, fun deviationBounded =>
    freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch
      G Λ p hBED hd data geom deviationBounded⟩

set_option linter.style.longLine false in
/-- **Branch-deviation Ascoli data through the named branch-local relatively
compact patch route**: branch-deviation data first derives branch-local
boundedness, then uses the branch-local range conversion before applying the
all-stage range patch endpoint. -/
theorem freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (deviationBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        G Λ p K data geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData_viaLocal
      G Λ p K data geom deviationBounded)

set_option linter.style.longLine false in
/-- **Compact target to branch-deviation named via-local patch input**:
compactness of `K` extracts the finite all-stage geometry; branch-deviation
Ascoli data then feeds the named branch-local relatively compact range route.
-/
theorem
    freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
          G Λ p K data geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK data with
    ⟨geom⟩
  exact ⟨geom, fun deviationBounded =>
    freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch
      G Λ p hBED hd data geom deviationBounded⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to branch-deviation relatively compact
patch input**: positive real ferromagnetic parameters construct the all-stage
branch data, compactness extracts the finite geometry, and branch-deviation
Ascoli data then feeds the relative-compactness route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealBranchDeviationRelCompact_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ data : LeeYangPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
        LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
            G Λ p K data geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨data⟩
  rcases
      freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch_of_isCompact
        G Λ p hBED hd hK hKsub hpK data with
    ⟨geom, hgeom⟩
  exact ⟨data, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to direct-range branch-deviation patch
input**: positive real ferromagnetic parameters construct the all-stage branch
data, compactness extracts the finite geometry, and branch-deviation Ascoli
data then feeds the direct relatively compact range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealBranchDeviation_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ data : LeeYangPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
        LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
            G Λ p K data geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨data⟩
  rcases
      freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hK hKsub hpK data with
    ⟨geom, hgeom⟩
  exact ⟨data, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to named via-local branch-deviation
direct-range patch input**: positive real ferromagnetic parameters construct
the all-stage branch data, compactness extracts the finite geometry, and
branch-deviation Ascoli data then feeds the named via-local range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealBranchDeviationViaLocal_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ data : LeeYangPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data,
        LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
            G Λ p K data geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨data⟩
  rcases
      freeEnergyComplexAlongExhaustion_branchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hK hKsub hpK data with
    ⟨geom, hgeom⟩
  exact ⟨data, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap branch-deviation Ascoli data to a direct-range
relatively compact patch**: the eventual-overlap package supplies coherent
selected-overlap equality, while the remaining branch-deviation Ascoli inputs
are converted directly to relatively compact range data before applying the
all-stage range patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
        G Λ p K eventualData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i =>
          eventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData) geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData.toRangeRelCompactData
      G Λ p K eventualData geom eventualDeviation)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap branch-deviation direct-range patch
input**: compactness extracts the finite all-stage geometry from the all-stage
data underlying the pointwise-normalised eventual-overlap package; the
eventual-overlap package then supplies the selected overlap field for the
branch-deviation Ascoli route. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationRelCompact_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData),
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
          G Λ p K eventualData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i =>
              eventualData.pointwiseData.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData) with
    ⟨geom⟩
  exact ⟨geom, fun eventualDeviation =>
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationRelCompact_directRange_patch
      G Λ p hBED hd eventualData geom eventualDeviation⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap branch-deviation data to direct-range patch via branch
local boundedness**: branch-deviation data is first converted to branch-local
boundedness using the explicit principal free-energy bound carried by the
deviation package, and the selected-overlap field is then supplied from
pointwise-normalised eventual-overlap data. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationViaLocalRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
        G Λ p K eventualData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i =>
          eventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData) geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData.toRangeRelCompactData_viaLocal
      G Λ p K eventualData geom eventualDeviation)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap branch-deviation via-local direct-range
patch input**: compactness extracts finite all-stage geometry, branch-deviation
data is converted to branch-local boundedness using its explicit principal
free-energy bound, and eventual-overlap data supplies selected overlap. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData),
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
          G Λ p K eventualData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i =>
              eventualData.pointwiseData.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (eventualData.pointwiseData.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData) with
    ⟨geom⟩
  exact ⟨geom, fun eventualDeviation =>
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchDeviationViaLocalRelCompact_directRange_patch
      G Λ p hBED hd eventualData geom eventualDeviation⟩

end Ambient

end IsingModel
