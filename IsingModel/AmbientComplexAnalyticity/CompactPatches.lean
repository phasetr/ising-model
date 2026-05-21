import IsingModel.AmbientComplexAnalyticity.AscoliData

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Compact finite subcover from pointwise-normalised all-stage data**:
on a compact target `K ⊆ leeYangDomain`, the point-indexed all-stage
Lee-Yang balls have a finite `Finset` subcover. -/
theorem exists_finset_cover_of_isCompact_pointwiseNormAllStageData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (data.branchData.radius h₀) := by
  classical
  refine hK.elim_finite_subcover
    (fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
      Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))
    (fun _ => Metric.isOpen_ball) ?_
  intro z hzK
  let h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} := ⟨z, hKsub hzK⟩
  exact Set.mem_iUnion.mpr ⟨h₀, Metric.mem_ball_self (data.branchData.radius_pos h₀)⟩

/-- **Real-centred compact finite subcover from pointwise-normalised all-stage
data**: on a compact target containing the real field, the point-indexed
all-stage Lee-Yang balls have a finite `Finset` subcover chosen to contain the
real Lee-Yang centre. -/
theorem exists_finset_cover_of_isCompact_pointwiseNormAllStageData_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ⟨(p.h : ℂ), hKsub hpK⟩ ∈ t ∧
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (data.branchData.radius h₀) := by
  classical
  rcases exists_finset_cover_of_isCompact_pointwiseNormAllStageData
      G Λ (p.J : ℂ) (p.β : ℂ) hK hKsub data with
    ⟨t, ht_cover⟩
  let hreal : {h : ℂ // h ∈ IsingModel.leeYangDomain} := ⟨(p.h : ℂ), hKsub hpK⟩
  refine ⟨insert hreal t, Finset.mem_insert_self hreal t, ?_⟩
  intro z hzK
  rcases Set.mem_iUnion.mp (ht_cover hzK) with ⟨h₀, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨h₀_mem, hz_ball⟩
  exact Set.mem_iUnion.mpr
    ⟨h₀, Set.mem_iUnion.mpr ⟨Finset.mem_insert_of_mem h₀_mem, hz_ball⟩⟩

/-- **Enumerated compact real finite-cover geometry from pointwise-normalised
all-stage data**: compactness extracts and enumerates finitely many all-stage
Lee-Yang balls covering `K`, retaining the real-centre index needed by the
compact real-cover patch bridge. -/
theorem exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    Nonempty (LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data) := by
  classical
  rcases exists_finset_cover_of_isCompact_pointwiseNormAllStageData_real
      G Λ p hK hKsub hpK data with
    ⟨t, ht_real, ht_cover⟩
  let center : Fin t.card → {h : ℂ // h ∈ IsingModel.leeYangDomain} :=
    fun i => ((t.equivFin).symm i).1
  let realIndex : Fin t.card := t.equivFin ⟨⟨(p.h : ℂ), hKsub hpK⟩, ht_real⟩
  refine ⟨
    { isCompact := hK
      subset_domain := hKsub
      real_mem := hpK
      n := t.card
      center := center
      radius_pos := ?_
      ball_subset := ?_
      cover_subset := ?_
      realIndex := realIndex
      real_center := ?_ }⟩
  · intro i
    exact data.branchData.radius_pos (center i)
  · intro i
    exact data.branchData.ball_subset (center i)
  · intro z hzK
    rcases Set.mem_iUnion.mp (ht_cover hzK) with ⟨h₀, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨h₀_mem, hz_ball⟩
    let h₀' : t := ⟨h₀, h₀_mem⟩
    let i : Fin t.card := t.equivFin h₀'
    have hcenter : center i = h₀ := by
      simp [center, i, h₀']
    exact Set.mem_iUnion.mpr
      ⟨i, by
        rw [hcenter]
        exact hz_ball⟩
  · simp [center, realIndex]

/-- **Pointwise-normalised all-stage compact real finite-cover geometry to
patch**: once compactness has extracted finite all-stage centres, compact-open
compactness and explicit eventual overlap equality feed the PR #2730 compact
real-cover patch bridge without restating the finite cover and real-centre
fields manually. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_geom
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
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
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCoverCOpen_patch
    G Λ p hBED hd K geom.n geom.center data geom.isCompact geom.subset_domain
    geom.real_mem geom.cover_subset hA hFc_mem hFres hoverlap geom.realIndex
    geom.real_center

/-- **Pointwise-normalised all-stage compact-open data to a compact real-cover
patch**: packaged compact-open data for the selected all-stage geometry feeds
the compact real-cover patch bridge directly. -/
theorem freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (cOpen : LeeYangPointwiseNormAllStageCompactRealCOpenData
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
  freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_geom
    G Λ p hBED hd data geom cOpen.isCompact cOpen.mem cOpen.restrict_eq
    cOpen.overlap_eventually

/-- **Compact target to packaged compact-open patch input**: compactness of `K`
extracts the finite all-stage geometry, after which a packaged compact-open
data input is enough to obtain the compact real-cover patch endpoint. -/
theorem freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealCOpenData G Λ p K data geom →
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
  exact ⟨geom, fun cOpen =>
    freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
      G Λ p hBED hd data geom cOpen⟩

/-- **Pointwise-normalised all-stage range-closure compact-open data to a
compact real-cover patch**: compactness of the closure of the selected
stage-restriction range supplies the compact-open carrier membership required
by the packaged compact-open patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeClosure :
      LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
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
  freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData.toCOpenData
      G Λ p K data geom rangeClosure)

/-- **Compact target to all-stage range-closure compact-open patch input**:
compactness of `K` extracts the finite all-stage geometry, after which
compactness of each closure of the actual stage-restriction range, restriction
identities, and coherent overlap equality suffice for the compact real-cover
patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
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
  exact ⟨geom, fun rangeClosure =>
    freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
      G Λ p hBED hd data geom rangeClosure⟩

/-- **Pointwise-normalised all-stage relatively compact range data to a
compact real-cover patch**: if the selected stage-restriction range lies in a
compact compact-open carrier, then the range closure is compact and the
range-closure compact-open patch bridge applies. -/
theorem freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (relCompact :
      LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
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
  freeEnergyComplexAlongExhaustion_allStageRangeClosureCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.toRangeClosureData
      G Λ p K data geom relCompact)

/-- **Compact target to all-stage relatively compact range patch input**:
compactness of `K` extracts the finite all-stage geometry, after which compact
carriers containing the selected restriction ranges, restriction identities,
and coherent overlap equality suffice for the compact real-cover patch
endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
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
  exact ⟨geom, fun relCompact =>
    freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
      G Λ p hBED hd data geom relCompact⟩

/-- **Pointwise-normalised all-stage Arzelà-Ascoli data to a compact real-cover
patch**: compactness of the pointwise function-space image plus equicontinuity
on the selected all-stage compact finite geometry supply compact-open
compactness via Arzelà-Ascoli, and the resulting compact-open package feeds the
compact real-cover patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (ascoli : LeeYangPointwiseNormAllStageCompactRealAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealAscoliData.toCOpenData
      G Λ p K data geom ascoli)

/-- **Compact target to all-stage Arzelà-Ascoli patch input**: compactness of
`K` extracts the finite all-stage geometry, after which compactness of the
pointwise function-space image, equicontinuity, restriction identities, and
coherent overlap equality for that geometry suffice to obtain the compact
real-cover patch endpoint. -/
theorem freeEnergyComplexAlongExhaustion_allStageAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealAscoliData G Λ p K data geom →
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
  exact ⟨geom, fun ascoli =>
    freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
      G Λ p hBED hd data geom ascoli⟩

/-- **Pointwise-normalised all-stage closed-product Ascoli data to a compact
real-cover patch**: compact pointwise target sets plus closedness of the
pointwise function-space image and equicontinuity supply the Ascoli data, which
then feeds the compact real-cover patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (closedProduct :
      LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData.toAscoliData
      G Λ p K data geom closedProduct)

/-- **Compact target to all-stage closed-product Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry, after which compact
pointwise targets, closed pointwise image, equicontinuity, restriction
identities, and coherent overlap equality for that geometry suffice to obtain
the compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
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
  exact ⟨geom, fun closedProduct =>
    freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
      G Λ p hBED hd data geom closedProduct⟩

/-- **Pointwise-normalised all-stage norm-bounded closed-product Ascoli data
to a compact real-cover patch**: pointwise norm bounds supply the compact
closed-ball targets required by the closed-product Ascoli package, and the
resulting data feeds the compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (normBounded :
      LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageClosedProductAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData.toClosedProductData
      G Λ p K data geom normBounded)

/-- **Compact target to all-stage norm-bounded closed-product Ascoli patch
input**: compactness of `K` extracts the finite all-stage geometry, after
which closed pointwise image, pointwise norm bounds, equicontinuity,
restriction identities, and coherent overlap equality suffice to obtain the
compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
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
  exact ⟨geom, fun normBounded =>
    freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
      G Λ p hBED hd data geom normBounded⟩

/-- **Pointwise-normalised all-stage range norm-bounded Ascoli data to a
compact real-cover patch**: range carriers reduce the norm-bounded Ascoli
input to stagewise pointwise norm bounds for the selected continuous
restrictions. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeBounded :
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  freeEnergyComplexAlongExhaustion_allStageNormBoundedAscoliData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData.toNormBoundedData
      G Λ p K data geom rangeBounded)

/-- **Compact target to all-stage range norm-bounded Ascoli patch input**:
compactness of `K` extracts the finite all-stage geometry; range
norm-bounded Ascoli data for that geometry then yields the compact real-cover
patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  exact ⟨geom, fun rangeBounded =>
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedAscoliData_patch
      G Λ p hBED hd data geom rangeBounded⟩

/-- **Pointwise-normalised all-stage range norm-bounded Ascoli data to a
relatively compact range patch**: closedness of the pointwise range image,
stagewise pointwise norm bounds, and equicontinuity make the actual
stage-restriction range a compact compact-open carrier, so the PR #2741
relatively compact range bridge applies. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeBounded :
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
    (LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData.toRangeRelCompactData
      G Λ p K data geom rangeBounded)

/-- **Compact target to all-stage range norm-bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry; range
norm-bounded Ascoli data then supplies the compact carrier input required by
the relatively compact range bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  exact ⟨geom, fun rangeBounded =>
    freeEnergyComplexAlongExhaustion_allStageRangeNormBoundedRelCompact_patch
      G Λ p hBED hd data geom rangeBounded⟩

/-- **Branch norm-bounded Ascoli data to a relatively compact range patch**:
branch-family pointwise norm bounds are transported to the selected continuous
restrictions, making the actual restriction range a compact carrier for the
relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch
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
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.toRangeRelCompactData
      G Λ p K data geom branchBounded)

/-- **Compact target to branch norm-bounded relatively compact patch input**:
compactness of `K` extracts the finite all-stage geometry; branch norm-bounded
Ascoli data then supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch_of_isCompact
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
    freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch
      G Λ p hBED hd data geom branchBounded⟩

/-- **Branch constant norm-bounded Ascoli data to a relatively compact range
patch**: ballwise constant branch-family bounds are converted to branch
pointwise bounds, then to the relatively compact range package. -/
theorem freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch
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
  freeEnergyComplexAlongExhaustion_branchNormBoundedRelCompact_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData.toBranchNormBoundedData
      G Λ p K data geom constBounded)

/-- **Compact target to branch constant norm-bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry; branch
constant norm-bounded Ascoli data then supplies the relative-compactness input.
-/
theorem
    freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch_of_isCompact
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
    freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch
      G Λ p hBED hd data geom constBounded⟩

/-- **Branch locally bounded Ascoli data to a relatively compact range patch**:
one branch-family bound is chosen on each selected ball and then fed through
the branch constant/norm-bounded relative-compactness bridge. -/
theorem freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch
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
  freeEnergyComplexAlongExhaustion_branchConstNormBoundedRelCompact_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toConstData
      G Λ p K data geom locallyBounded)

/-- **Compact target to branch locally bounded relatively compact patch
input**: compactness of `K` extracts the finite all-stage geometry; branch
locally bounded Ascoli data then supplies the relative-compactness input. -/
theorem
    freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch_of_isCompact
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
    freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_patch
      G Λ p hBED hd data geom locallyBounded⟩

set_option linter.style.longLine false in
/-- **Branch locally bounded Ascoli data to a direct-range relatively compact
patch**: branch locally bounded data is converted directly to the relatively
compact range package before applying the all-stage range patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch
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
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData
      G Λ p K data geom locallyBounded)

set_option linter.style.longLine false in
/-- **Compact target to direct-range branch locally bounded patch input**:
compactness of `K` extracts the finite all-stage geometry; branch locally
bounded Ascoli data then feeds the direct relatively compact range route. -/
theorem
    freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch_of_isCompact
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
    freeEnergyComplexAlongExhaustion_branchLocallyBoundedRelCompact_directRange_patch
      G Λ p hBED hd data geom locallyBounded⟩

set_option linter.style.longLine false in
/-- **Branch-local data to direct-range patch via branch deviation**:
branch-local boundedness and an explicit principal free-energy local bound are
first converted to branch-deviation data, then fed through the direct
branch-deviation relatively compact range route. -/
theorem
    freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {K : Set ℂ}
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
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
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation
      G Λ p K data geom freeEnergy_bound locallyBounded)

set_option linter.style.longLine false in
/-- **Compact target to branch-local via-deviation direct-range patch input**:
compactness extracts finite all-stage geometry; branch-local boundedness and an
explicit principal free-energy local bound are then converted to
branch-deviation data before patching. -/
theorem
    freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
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
      (∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
        (_hz : z ∈ Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i))),
        ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C) →
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
  exact ⟨geom, fun freeEnergy_bound locallyBounded =>
    freeEnergyComplexAlongExhaustion_branchLocalViaDeviationRelCompact_directRange_patch
      G Λ p hBED hd data geom freeEnergy_bound locallyBounded⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap branch locally bounded Ascoli data to a direct-range
relatively compact patch**: the eventual-overlap package supplies coherent
selected-overlap equality, while the remaining branch-local Ascoli inputs are
converted directly to relatively compact range data before applying the
all-stage range patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch
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
    (eventualLocallyBounded :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
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
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData.toRangeRelCompactData
      G Λ p K eventualData geom eventualLocallyBounded)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap branch-local direct-range patch
input**: compactness extracts the finite all-stage geometry from the all-stage
data underlying the pointwise-normalised eventual-overlap package; the
eventual-overlap package then supplies the selected overlap field for the
branch-local Ascoli route. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch_of_isCompact
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
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
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
  exact ⟨geom, fun eventualLocallyBounded =>
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocallyBoundedRelCompact_directRange_patch
      G Λ p hBED hd eventualData geom eventualLocallyBounded⟩

set_option linter.style.longLine false in
/-- **Eventual-overlap branch-local data to direct-range patch via branch
deviation**: branch-local boundedness and an explicit principal free-energy
local bound are first converted to branch-deviation data, while
eventual-overlap data supplies selected-overlap equality for the downstream
direct branch-deviation route. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch
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
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (eventualData.pointwiseData.branchData.radius (geom.center i))),
      ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
    (eventualLocallyBounded :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
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
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation
      G Λ p K eventualData geom freeEnergy_bound eventualLocallyBounded)

set_option linter.style.longLine false in
/-- **Compact target to eventual-overlap branch-local via-deviation
direct-range patch input**: compactness extracts finite all-stage geometry,
branch-local boundedness is converted to branch-deviation data using the
explicit principal free-energy local bound, and eventual-overlap data supplies
selected overlap. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch_of_isCompact
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
      (∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
        (_hz : z ∈ Metric.ball (geom.center i : ℂ)
          (eventualData.pointwiseData.branchData.radius (geom.center i))),
        ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C) →
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
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
  exact ⟨geom, fun freeEnergy_bound eventualLocallyBounded =>
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchLocalViaDeviationRelCompact_directRange_patch
      G Λ p hBED hd eventualData geom freeEnergy_bound eventualLocallyBounded⟩

end Ambient

end IsingModel
