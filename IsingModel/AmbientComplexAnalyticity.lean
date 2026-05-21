import IsingModel.AmbientComplexAnalyticity.CompactPatches

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

/-- **Closed-ball branch-deviation data to a relatively compact range patch**:
closed-ball all-stage branch data supplies the Lee-Yang local compactness
needed to bound the principal finite-volume free energies on each selected
ball.  The only remaining local-boundedness input is the uniform deviation of
the selected branch from that principal value. -/
theorem freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_branchDeviationRelCompact_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

/-- **Compact target to closed-ball branch-deviation relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry from the
underlying closed-ball branch data; the closed-ball branch-deviation data then
supplies the relative-compactness input with the principal free-energy bound
filled in automatically. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallDeviation =>
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩

/-- **Positive-real compact target to closed-ball branch-deviation relatively
compact patch input**: positive real ferromagnetic parameters construct the
closed-ball pointwise-normalised all-stage branch data, compactness of `K`
extracts the finite geometry, and closed-ball branch-deviation data then feeds
the PR #2745 closed-ball relative-compactness bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

open LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData in
/-- **Closed-ball branch-deviation to direct relatively compact patch**:
closed-ball branch-deviation data is first converted to relatively compact
range data through the direct closed-ball branch-local route, then fed to the
all-stage relatively compact range patch endpoint. -/
theorem freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd closedData.data geom
    (toRangeRelCompactData_closedBallLocal_direct
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

set_option linter.style.longLine false in
/-- **Compact target to direct closed-ball branch-deviation patch input**:
compactness extracts the finite all-stage geometry from closed-ball branch
data; closed-ball branch-deviation data then feeds the direct relatively compact
range route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallDeviation =>
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to direct closed-ball branch-deviation patch
input**: positive real ferromagnetic parameters construct the closed-ball
all-stage branch data, compactness extracts the finite geometry, and
closed-ball branch-deviation data then feeds the direct range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_direct_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_direct_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Closed-ball branch-deviation to direct-range relatively compact patch**:
closed-ball branch-deviation data is converted directly to relatively compact
range data through the direct closed-ball branch-local route, then fed to the
all-stage relatively compact range patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

set_option linter.style.longLine false in
/-- **Compact target to direct-range closed-ball branch-deviation patch input**:
compactness extracts the finite all-stage geometry from closed-ball branch
data; closed-ball branch-deviation data then feeds the direct-range relatively
compact route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallDeviation =>
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩

set_option linter.style.longLine false in
/-- **Closed-ball branch-deviation data through the named branch-local
direct-range patch route**: closed-ball branch-deviation data is converted to
relatively compact range data through the named via-local route, then fed to
the all-stage relatively compact range patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData_viaLocal_direct
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

set_option linter.style.longLine false in
/-- **Compact target to named via-local closed-ball branch-deviation patch
input**: compactness extracts the finite all-stage geometry from closed-ball
branch data; closed-ball branch-deviation data then feeds the named via-local
relatively compact route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallDeviation =>
    freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallDeviation⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap closed-ball branch-deviation data to direct-range
relatively compact patch**: closed-ball branch-deviation data is converted
directly to relatively compact range data, with coherent selected-overlap
equality supplied by the pointwise-normalised eventual-overlap package. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualDeviation)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap closed-ball branch-deviation
direct-range patch input**: compactness extracts finite all-stage geometry
from the closed-ball all-stage data underlying the pointwise-normalised
eventual-overlap package; the eventual-overlap package then supplies the
selected overlap field for the closed-ball branch-deviation route. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data,
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
          G Λ p K closedEventualData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data with
    ⟨geom⟩
  exact ⟨geom, fun closedEventualDeviation =>
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedEventualData geom closedEventualDeviation⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap closed-ball branch-local data to direct-range patch via
branch deviation**: closed-ball branch-local boundedness is first converted to
closed-ball branch-deviation data using the automatic closed-ball principal
free-energy bound, and the selected-overlap field is then supplied from
pointwise-normalised eventual-overlap data. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocalViaDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationRelCompact_directRange_patch
    G Λ p hBED hd hβ hJ closedEventualData geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchDeviationData
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualLocal)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap closed-ball branch-local via-deviation
direct-range patch input**: compactness extracts finite all-stage geometry,
branch-local boundedness is converted to branch-deviation input using the
closed-ball principal free-energy bound, and eventual-overlap data supplies
selected overlap. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data,
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
          G Λ p K closedEventualData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data with
    ⟨geom⟩
  exact ⟨geom, fun closedEventualLocal =>
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocalViaDeviationRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedEventualData geom closedEventualLocal⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap closed-ball branch-deviation data to direct-range patch
via branch local boundedness**: closed-ball branch-deviation data is first
converted to branch-local boundedness using the automatic closed-ball principal
free-energy bound, and the selected-overlap field is then supplied from
pointwise-normalised eventual-overlap data. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_viaLocal_direct
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualDeviation)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap closed-ball branch-deviation via-local
direct-range patch input**: compactness extracts finite all-stage geometry,
branch-deviation bounds are converted to branch-local boundedness using the
closed-ball principal free-energy bound, and eventual-overlap data supplies
selected overlap. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data,
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
          G Λ p K closedEventualData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data with
    ⟨geom⟩
  exact ⟨geom, fun closedEventualDeviation =>
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchDeviationViaLocalRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedEventualData geom closedEventualDeviation⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to direct-range closed-ball
branch-deviation patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and closed-ball branch-deviation data then feeds the
direct-range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviation_directRange_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to named via-local direct-range closed-ball
branch-deviation patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and closed-ball branch-deviation data then feeds the named
via-local direct-range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallDeviationViaLocal_directRange_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchDeviationViaLocalRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

/-- **Closed-ball branch local boundedness to relatively compact patch**:
branch-family local bounds combine with the closed-ball Lee-Yang principal
free-energy bound to supply the branch-deviation input, then feed the PR #2745
closed-ball relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_closedBallBranchDeviationRelCompact_patch
    G Λ p hBED hd hβ hJ closedData geom
    (LeeYangClosedBallBranchLocallyBoundedAscoliData.toClosedBallDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallLocal)

/-- **Compact target to closed-ball branch local-boundedness patch input**:
compactness extracts the finite all-stage geometry from closed-ball branch
data; branch-family local boundedness for that geometry then supplies the
closed-ball branch-deviation relative-compactness patch. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangClosedBallBranchLocallyBoundedAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallLocal =>
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallLocal⟩

/-- **Positive-real compact target to closed-ball branch local-boundedness
patch input**: positive real ferromagnetic parameters construct the closed-ball
all-stage branch data, compactness extracts the finite geometry, and branch
local boundedness then feeds the closed-ball relative-compactness bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocallyBounded_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangClosedBallBranchLocallyBoundedAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

/-- **Closed-ball branch local boundedness to direct relatively compact patch**:
closed-ball branch locally bounded data already contains the underlying
pointwise-normalised branch locally bounded Ascoli input, so it can feed the
branch locally bounded relative-compactness bridge directly without first
building the closed-ball branch-deviation package. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_direct_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangClosedBallBranchLocallyBoundedAscoliData.toBranchLocallyBoundedData
      G Λ p K closedData geom closedBallLocal)

set_option linter.style.longLine false in
/-- **Compact target to direct closed-ball branch local-boundedness patch
input**: compactness extracts the finite all-stage geometry from closed-ball
branch data; closed-ball branch locally bounded data then feeds the underlying
branch locally bounded relative-compactness bridge directly. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_direct_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangClosedBallBranchLocallyBoundedAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallLocal =>
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_direct_patch
      G Λ p hBED hd closedData geom closedBallLocal⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to direct closed-ball branch
local-boundedness patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and closed-ball branch local boundedness then feeds the
underlying branch locally bounded relative-compactness bridge directly. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocallyBounded_direct_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangClosedBallBranchLocallyBoundedAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_direct_patch_of_isCompact
        G Λ p hBED hd hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Closed-ball branch local boundedness to direct-range relatively compact
patch**: closed-ball branch locally bounded data is converted directly to the
relatively compact range package before applying the all-stage range patch
endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
      G Λ p K closedData geom closedBallLocal)

set_option linter.style.longLine false in
/-- **Compact target to direct-range closed-ball branch local-boundedness patch
input**: compactness extracts the finite all-stage geometry from closed-ball
branch data; closed-ball branch locally bounded data then feeds the direct
range relative-compactness route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangClosedBallBranchLocallyBoundedAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallLocal =>
    freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_directRange_patch
      G Λ p hBED hd closedData geom closedBallLocal⟩

set_option linter.style.longLine false in
/-- **Closed-ball branch-local data to direct-range patch via branch
deviation**: branch-local boundedness and the automatic closed-ball principal
free-energy bound are converted to closed-ball branch-deviation data before
feeding the directRange relatively compact route. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β)
    (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd closedData.data geom
    (LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation_direct
      G Λ p hBED hβ hJ K closedData geom closedBallLocal)

set_option linter.style.longLine false in
/-- **Compact target to closed-ball branch-local via-deviation direct-range
patch input**: compactness extracts finite all-stage geometry; branch-local
boundedness is converted to closed-ball branch-deviation data using the
automatic closed-ball principal free-energy bound, then routed through
directRange relative compactness. -/
theorem
    freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.data,
      LeeYangClosedBallBranchLocallyBoundedAscoliData
          G Λ p K closedData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.data with
    ⟨geom⟩
  exact ⟨geom, fun closedBallLocal =>
    freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch
      G Λ p hBED hd hβ hJ closedData geom closedBallLocal⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to closed-ball branch-local via-deviation
direct-range patch input**: positive real ferromagnetic parameters construct
closed-ball all-stage branch data; compactness extracts finite geometry; branch
local boundedness is converted through closed-ball branch-deviation data before
directRange patching. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocalViaDeviation_directRange_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangClosedBallBranchLocallyBoundedAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hβ hJ hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap closed-ball branch local boundedness to direct-range
relatively compact patch**: closed-ball branch local boundedness data is
converted directly to relatively compact range data, with coherent
selected-overlap equality supplied by the pointwise-normalised
eventual-overlap package. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i =>
          closedEventualData.pointwiseData.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedEventualData.pointwiseData.branchData.radius
              (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
      G Λ p K closedEventualData geom closedEventualLocal)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap closed-ball branch-local direct-range
patch input**: compactness extracts finite all-stage geometry from the
closed-ball all-stage data underlying the pointwise-normalised
eventual-overlap package; the eventual-overlap package then supplies the
selected overlap field for the closed-ball branch-local route. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data,
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
          G Λ p K closedEventualData geom →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i =>
              closedEventualData.pointwiseData.branchData.radius
                (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedEventualData.pointwiseData.branchData.radius
                  (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data with
    ⟨geom⟩
  exact ⟨geom, fun closedEventualLocal =>
    freeEnergyComplexAlongExhaustion_eventualOverlapClosedBallBranchLocallyBoundedRelCompact_directRange_patch
      G Λ p hBED hd closedEventualData geom closedEventualLocal⟩

set_option linter.style.longLine false in
/-- **Positive-real compact target to direct-range closed-ball branch
local-boundedness patch input**: positive real ferromagnetic parameters
construct the closed-ball all-stage branch data, compactness extracts the
finite geometry, and closed-ball branch local boundedness then feeds the direct
range route. -/
theorem
    freeEnergyComplexAlongExhaustion_posRealClosedBallBranchLocallyBounded_directRange_patch_of_isCompact
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
    ∃ closedData :
        LeeYangClosedBallPointwiseNormalisedAllStageBranchData
          G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        LeeYangClosedBallBranchLocallyBoundedAscoliData
            G Λ p K closedData geom →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with
    ⟨closedData⟩
  rcases
      freeEnergyComplexAlongExhaustion_closedBallBranchLocallyBoundedRelCompact_directRange_patch_of_isCompact
        G Λ p hBED hd hK hKsub hpK closedData with
    ⟨geom, hgeom⟩
  exact ⟨closedData, geom, hgeom⟩

/-- **Pointwise-normalised all-stage branch norm-bounded Ascoli data to a
compact real-cover patch**: branch-family pointwise norm bounds are
transported through the selected restriction identities and then fed to the
range norm-bounded Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (branchBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.toRangeNormBoundedData
      G Λ p K data geom branchBounded)

/-- **Compact target to all-stage branch norm-bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry; branch
norm-bounded Ascoli data for that geometry then yields the compact real-cover
patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
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
  exact ⟨geom, fun branchBounded =>
    freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch
      G Λ p hBED hd data geom branchBounded⟩

/-- **Pointwise-normalised all-stage branch constant norm-bounded Ascoli data
to a compact real-cover patch**: ballwise constant branch-family norm bounds
are turned into pointwise constant bounds and then fed to the branch
norm-bounded Ascoli package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (constBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageBranchNormBoundedAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData.toBranchNormBoundedData
      G Λ p K data geom constBounded)

/-- **Compact target to all-stage branch constant norm-bounded Ascoli patch
input**: compactness of `K` extracts the finite all-stage geometry; branch
constant norm-bounded Ascoli data for that geometry then yields the compact
real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  exact ⟨geom, fun constBounded =>
    freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
      G Λ p hBED hd data geom constBounded⟩

/-- **Pointwise-normalised all-stage branch locally bounded Ascoli data to a
compact real-cover patch**: existential ballwise branch-family bounds are
chosen as constants and then fed to the branch constant norm-bounded Ascoli
package. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (locallyBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageBranchConstNormBoundedAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toConstData
      G Λ p K data geom locallyBounded)

/-- **Compact target to all-stage branch locally bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry; branch locally
bounded Ascoli data for that geometry then yields the compact real-cover patch
endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
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
  exact ⟨geom, fun locallyBounded =>
    freeEnergyComplexAlongExhaustion_allStageBranchLocallyBoundedAscoliData_patch
      G Λ p hBED hd data geom locallyBounded⟩

/-- **Finite compact-open extraction to a real-centre patch**: compact-open
compactness on finitely many balls, eventual stage-level overlap equality, and
a selected ball centred at the real field `p.h` produce a patched function on
the finite union of balls whose value at `p.h` is `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen_patch_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m (h0 i) = freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (h0 i) (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)))
    (i₀ : Fin n)
    (hcenter : h0 i₀ = (p.h : ℂ))
    (hr : 0 < r i₀) :
    ∃ family : LeeYangFiniteSubseqBranchLimitFamily G Λ
        (p.J : ℂ) (p.β : ℂ) n h0 r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (family.limitFun i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
      G Λ (p.J : ℂ) (p.β : ℂ) n hA hFc_mem hFres hbranch hoverlap with
    ⟨family⟩
  exact ⟨family,
    freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_patch_real
      G Λ p hBED hd n family i₀ hcenter hr⟩

/-- **Finite Lee-Yang cover compact-open extraction package**: compact-open
compactness on finitely many Lee-Yang-domain balls, plus eventual stage-level
overlap equality, produces a finite Lee-Yang cover branch-limit family. The
balls are recorded with their positivity and containment in `leeYangDomain`
for later local-cover diagonalization. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ J
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j))) :
    Nonempty (LeeYangFiniteCoverBranchLimitFamily G Λ J β n center r) := by
  rcases freeEnergyComplexAlongExhaustion_finiteSubseqBranchLimitFamily_compactOpen
      G Λ J β n hA hFc_mem hFres hbranch hoverlap with
    ⟨family⟩
  exact ⟨{
    radius_pos := hr
    ball_subset := hsub
    family := family }⟩

/-- **Finite Lee-Yang cover compact-open extraction to a patch**:
compact-open compactness and eventual stage-level overlap equality produce
both the finite Lee-Yang cover package and a differentiable patch on the finite
union of its Lee-Yang balls. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ J
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j))) :
    ∃ cover : LeeYangFiniteCoverBranchLimitFamily G Λ J β n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) := by
  rcases freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
      G Λ J β n hr hsub hA hFc_mem hFres hbranch hoverlap with
    ⟨cover⟩
  exact ⟨cover,
    freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch
      G Λ J β n cover⟩

/-- **Finite Lee-Yang cover compact-open extraction to a real-centre patch**:
compact-open compactness and eventual stage-level overlap equality produce a
finite Lee-Yang cover package and a finite-union patch whose selected real
centre value is `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen_patch_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ cover : LeeYangFiniteCoverBranchLimitFamily
        G Λ (p.J : ℂ) (p.β : ℂ) n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
      G Λ (p.J : ℂ) (p.β : ℂ) n hr hsub hA hFc_mem hFres hbranch hoverlap with
    ⟨cover⟩
  exact ⟨cover,
    freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_patch_real
      G Λ p hBED hd n cover i₀ hcenter⟩

/-- **Finite Lee-Yang cover compact-open extraction to a real-centred package
and patch**: compact-open compactness and eventual stage-level overlap equality
produce a finite real-centred Lee-Yang cover package and a finite-union patch
whose selected real-centre value is `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_compactOpen_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)) ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteCoverBranchLimitFamily_compactOpen
      G Λ (p.J : ℂ) (p.β : ℂ) n hr hsub hA hFc_mem hFres hbranch hoverlap with
    ⟨cover⟩
  let realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center r :=
    { cover := cover
      realIndex := i₀
      real_center := hcenter }
  exact ⟨realCover,
    freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_patch
      G Λ p hBED hd n realCover⟩

/-- **Compact finite Lee-Yang cover compact-open extraction to a real-centred
package and compact-target patch**: compact-open compactness and eventual
stage-level overlap equality produce a compact finite real-centred Lee-Yang
cover package and a patch differentiable on the compact target. -/
theorem freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (K : Set ℂ) (n : ℕ)
    {center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}}
    {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n,
      Set C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i), ℂ)}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (hKcover : K ⊆
      ⋃ i : Fin n,
        Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
    (hr : ∀ i, 0 < r i)
    (hsub : ∀ i,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
        ⊆ IsingModel.leeYangDomain)
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))
        ∧ (∀ z ∈ Metric.ball
              ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
          ∩ Metric.ball
            ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r j)))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ compactCover :
        LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K n center r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball
            ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases freeEnergyComplexAlongExhaustion_finiteRealCoverFamily_compactOpen_patch
      G Λ p hBED hd n hr hsub hA hFc_mem hFres hbranch hoverlap i₀ hcenter with
    ⟨realCover, g, hg_eq, hg_diff, hg_real⟩
  let compactCover :
      LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K n center r :=
    { isCompact := hK
      subset_domain := hKsub
      real_mem := hpK
      cover_subset := hKcover
      realCover := realCover }
  exact ⟨compactCover, g, hg_eq, hg_diff.mono hKcover, hg_real⟩

/-- **Compact local-cover `Fin n` geometry compact-open extraction to a
compact-target patch**: once a compact local-cover finite geometry has been
enumerated, compact-open compactness and eventual stage-level overlap equality
produce the compact finite real-centred Lee-Yang cover package and a patch
differentiable on the compact target. This is a one-input geometry wrapper
around `freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch`. -/
theorem freeEnergyComplexAlongExhaustion_compactLocalCoverFinGeometry_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (K : Set ℂ)
    (geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K)
    {F : Fin geometry.n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin geometry.n,
      Set C(Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i), ℂ)}
    {Fc : ∀ i : Fin geometry.n, ℕ →
      C(Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball
        ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (geometry.r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))
        ∧ (∀ z ∈ Metric.ball
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (geometry.r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)
          ∩ Metric.ball
            ((geometry.center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r j))) :
    ∃ compactCover :
        LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K
          geometry.n geometry.center geometry.r,
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_compactFiniteRealCover_cOpenPatch
    G Λ p hBED hd K geometry.n geometry.isCompact geometry.subset_domain
    geometry.real_mem geometry.cover_subset geometry.radius_pos geometry.ball_subset
    hA hFc_mem hFres hbranch hoverlap geometry.realIndex geometry.real_center

/-- **Structured eventual-overlap data to compact-open compact-target patch**:
structured real eventual-overlap data first yields a compact local-cover
`Fin n` geometry over `K`; for that geometry, compact-open compactness of the
selected restrictions of the data's branch family, together with centre
normalisation at every selected finite-cover centre, produces a compact finite
real-centred Lee-Yang cover package and a patch differentiable on `K`.

The extra selected-centre normalisation hypothesis is explicit because
`LeeYangRealEventualOverlapBranchData` only normalises the real centre. -/
theorem freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangRealEventualOverlapBranchData G Λ p) :
    ∃ geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K,
      ∀ {A : ∀ i : Fin geometry.n,
          Set C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)}
        {Fc : ∀ i : Fin geometry.n, ℕ →
          C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)},
        (∀ i, IsCompact (A i)) →
        (∀ i m, Fc i m ∈ A i) →
        (∀ i m z
          (hz : z ∈ Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)),
          data.branchData.branchFamily (geometry.center i) m z =
            Fc i m ⟨z, hz⟩) →
        (∀ i m,
          data.branchData.branchFamily (geometry.center i) m
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m) →
        ∃ compactCover :
            LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K
              geometry.n geometry.center geometry.r,
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                  (geometry.r i))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  let realFamily : LeeYangRealBranchLimitFamily G Λ p :=
    { centre_mem := data.centre_mem
      family :=
        { data := fun h₀ =>
            { radius := data.branchData.radius h₀
              radius_pos := data.branchData.radius_pos h₀
              ball_subset := data.branchData.ball_subset h₀
              branchFamily := data.branchData.branchFamily h₀
              limitFun := data.branchData.limitFun h₀
              branch_spec := data.branchData.branch_spec h₀
              tendsto := data.branchData.tendsto h₀ }
          compatible :=
            IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
              (s := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
                Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))
              (F := data.branchData.branchFamily) (f := data.branchData.limitFun)
              data.branchData.tendsto data.branchData.overlap_eventually }
      centre_normalized := data.centre_normalized }
  classical
  rcases exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily
      G Λ p hK hKsub hpK realFamily with
    ⟨t, ht_real, ht_cover⟩
  let center : Fin t.card → {h : ℂ // h ∈ IsingModel.leeYangDomain} :=
    fun i => ((t.equivFin).symm i).1
  let r : Fin t.card → ℝ :=
    fun i => data.branchData.radius (center i)
  let realIndex : Fin t.card := t.equivFin ⟨⟨(p.h : ℂ), realFamily.centre_mem⟩, ht_real⟩
  let geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K :=
    { isCompact := hK
      subset_domain := hKsub
      real_mem := hpK
      realFamily := realFamily
      n := t.card
      center := center
      r := r
      radius_eq := by
        intro i
        rfl
      radius_pos := by
        intro i
        exact data.branchData.radius_pos (center i)
      ball_subset := by
        intro i
        exact data.branchData.ball_subset (center i)
      cover_subset := by
        intro z hzK
        rcases Set.mem_iUnion.mp (ht_cover hzK) with ⟨h₀, hz⟩
        rcases Set.mem_iUnion.mp hz with ⟨h₀_mem, hz_ball⟩
        let h₀' : t := ⟨h₀, h₀_mem⟩
        let i : Fin t.card := t.equivFin h₀'
        have hcenter : center i = h₀ := by
          simp [center, i, h₀']
        exact Set.mem_iUnion.mpr
          ⟨i, by
            dsimp [r]
            rw [hcenter]
            exact hz_ball⟩
      realIndex := realIndex
      real_center := by
        simp [center, realIndex] }
  refine ⟨geometry, ?_⟩
  intro A Fc hA hFc_mem hFres hcenter_normalized
  let F : Fin geometry.n → ℕ → ℂ → ℂ :=
    fun i => data.branchData.branchFamily (geometry.center i)
  have hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m)
          (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i))
        ∧ (∀ z ∈ Metric.ball
              ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (geometry.r i),
            Complex.exp
              ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) m)
        ∧ F i m
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ)
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                (p.β : ℂ) m := by
    intro i m
    rcases data.branchData.branch_spec (geometry.center i) m with ⟨han, hexp⟩
    have hradius : geometry.r i = data.branchData.radius (geometry.center i) := by
      simpa [realFamily] using geometry.radius_eq i
    refine ⟨?_, ?_, hcenter_normalized i m⟩
    · simpa [F, hradius] using han
    · simpa [F, hradius] using hexp
  have hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)
          ∩ Metric.ball
            ((geometry.center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r j)) := by
    intro i j
    have hradius_i : geometry.r i = data.branchData.radius (geometry.center i) := by
      simpa [realFamily] using geometry.radius_eq i
    have hradius_j : geometry.r j = data.branchData.radius (geometry.center j) := by
      simpa [realFamily] using geometry.radius_eq j
    simpa [F, hradius_i, hradius_j] using
      data.branchData.overlap_eventually (geometry.center i) (geometry.center j)
  exact freeEnergyComplexAlongExhaustion_compactLocalCoverFinGeometry_cOpenPatch
    G Λ p hBED hd K geometry hA hFc_mem hFres hbranch hoverlap

/-- **Pointwise-normalised eventual-overlap data to compact-open compact-target
patch**: the pointwise-normalised package supplies the selected-centre
normalisation required by
`freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch`.
Thus only compact-open compactness of the selected branch-family restrictions
and their continuous representatives remain as explicit compact-open inputs. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_cOpenPatch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    ∃ geometry : LeeYangCompactLocalCoverFinGeometry G Λ p K,
      ∀ {A : ∀ i : Fin geometry.n,
          Set C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)}
        {Fc : ∀ i : Fin geometry.n, ℕ →
          C(Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i), ℂ)},
        (∀ i, IsCompact (A i)) →
        (∀ i m, Fc i m ∈ A i) →
        (∀ i m z
          (hz : z ∈ Metric.ball
            ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
              (geometry.r i)),
          data.pointwiseData.branchData.branchFamily (geometry.center i) m z =
            Fc i m ⟨z, hz⟩) →
        ∃ compactCover :
            LeeYangCompactFiniteRealCoverBranchLimitFamily G Λ p K
              geometry.n geometry.center geometry.r,
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball
                ((geometry.center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
                  (geometry.r i))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  let realData : LeeYangRealEventualOverlapBranchData G Λ p :=
    LeeYangRealEventualOverlapBranchData.ofPointwiseNormalised G Λ p data
  rcases freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_cOpenPatch
      G Λ p hBED hd hK hKsub hpK realData with
    ⟨geometry, hgeometry⟩
  refine ⟨geometry, ?_⟩
  intro A Fc hA hFc_mem hFres
  refine hgeometry hA hFc_mem hFres ?_
  intro i m
  exact data.pointwiseData.centre_normalized (geometry.center i) m

/-- **Finite-ball compact-open diagonal extraction with local patching**:
if the finite Lee-Yang local limits obtained from compact-open extraction are
compatible on all pairwise ball overlaps, then they patch to one function on
the finite union of balls.  The stage-level overlap equality remains an
explicit hypothesis, inherited from
`freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m,
      AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))
        ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
            Complex.exp ((Fintype.card (↑(Λ.volume m) : Type _) : ℂ) * F i m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β m)
        ∧ F i m (h0 i) = freeEnergyComplexAlongExhaustion G Λ J (h0 i) β m)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ, ∃ g : ℂ → ℂ,
        (∀ i,
          (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
            fc ∈ A i ∧
              ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f i z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        (∀ i, Set.EqOn g (f i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) ∧
        ∀ i j, Set.EqOn (f i) (f j)
          (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)) := by
  rcases freeEnergyComplexAlongExhaustion_branchFamily_compactOpen_vitali_fin_ball_overlap
      G Λ J β n hA hFc_mem hFres hbranch hoverlap with
    ⟨σ, hσ, f, hlocal, hcompat⟩
  rcases IsingModel.exists_differentiableOn_iUnion_of_finite_eqOn
      n (s := fun i : Fin n => Metric.ball (h0 i) (r i)) (f := f)
      (hs := fun _ => Metric.isOpen_ball)
      (hdiff := fun i => (hlocal i).2.2)
      (hcompat := hcompat) with
    ⟨g, hg_eq, hg_diff⟩
  exact ⟨σ, hσ, f, g, hlocal, hg_eq, hg_diff, hcompat⟩

end Ambient

end IsingModel
