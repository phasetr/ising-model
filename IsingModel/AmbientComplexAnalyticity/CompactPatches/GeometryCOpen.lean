import IsingModel.AmbientComplexAnalyticity.AscoliData

/-!
# Compact finite-cover geometry and compact-open patch wrappers

This module contains the finite-cover geometry extraction and packaged
compact-open patch wrappers for the ambient complex analyticity layer.
-/

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

end Ambient

end IsingModel
