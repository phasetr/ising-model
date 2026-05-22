import IsingModel.AmbientComplexAnalyticity.Vitali.LocalCoverPatching

/-!
# Ambient Complex Analyticity Vitali Compact Geometry

Mechanical child split from `AmbientComplexAnalyticity/Vitali.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Compact finite subcover from a packaged Lee-Yang local-cover family**:
on a compact target `K ⊆ leeYangDomain`, the open Lee-Yang balls carried by a
compatible `LeeYangLocalBranchLimitFamily` have a finite `Finset` subcover.
This is the topological finite-subcover step needed before later converting a
packaged local cover into finite-cover data. -/
theorem exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (family : LeeYangLocalBranchLimitFamily G Λ J β) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (family.data h₀).radius := by
  classical
  refine hK.elim_finite_subcover
    (fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
      Metric.ball (h₀ : ℂ) (family.data h₀).radius)
    (fun _ => Metric.isOpen_ball) ?_
  intro z hzK
  let h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} := ⟨z, hKsub hzK⟩
  exact Set.mem_iUnion.mpr ⟨h₀, Metric.mem_ball_self (family.data h₀).radius_pos⟩

/-- **Compact finite subcover from a real-centred packaged Lee-Yang local
cover**: on a compact target containing the real field, the packaged
real-centred local cover has a finite `Finset` subcover, and the finite set is
chosen to contain the real Lee-Yang centre. -/
theorem exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (_hpK : (p.h : ℂ) ∈ K)
    (realFamily : LeeYangRealBranchLimitFamily G Λ p) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ⟨(p.h : ℂ), realFamily.centre_mem⟩ ∈ t ∧
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius := by
  classical
  rcases exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily
      G Λ (p.J : ℂ) (p.β : ℂ) hK hKsub realFamily.family with
    ⟨t, ht_cover⟩
  let hreal : {h : ℂ // h ∈ IsingModel.leeYangDomain} :=
    ⟨(p.h : ℂ), realFamily.centre_mem⟩
  refine ⟨insert hreal t, Finset.mem_insert_self hreal t, ?_⟩
  intro z hzK
  rcases Set.mem_iUnion.mp (ht_cover hzK) with ⟨h₀, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨h₀_mem, hz_ball⟩
  exact Set.mem_iUnion.mpr
    ⟨h₀, Set.mem_iUnion.mpr ⟨Finset.mem_insert_of_mem h₀_mem, hz_ball⟩⟩

/-- **Enumerated compact local-cover finite geometry from a real-centred
packaged Lee-Yang local cover**: the finite `Finset` subcover supplied by
compactness can be enumerated by `Fin n`, retaining positive radii, ball
containment in `leeYangDomain`, the compact target cover, and a selected
real-centre index. -/
theorem exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (realFamily : LeeYangRealBranchLimitFamily G Λ p) :
    Nonempty (LeeYangCompactLocalCoverFinGeometry G Λ p K) := by
  classical
  rcases exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily
      G Λ p hK hKsub hpK realFamily with
    ⟨t, ht_real, ht_cover⟩
  let center : Fin t.card → {h : ℂ // h ∈ IsingModel.leeYangDomain} :=
    fun i => ((t.equivFin).symm i).1
  let r : Fin t.card → ℝ :=
    fun i => (realFamily.family.data (center i)).radius
  let realIndex : Fin t.card := t.equivFin ⟨⟨(p.h : ℂ), realFamily.centre_mem⟩, ht_real⟩
  refine ⟨
    { isCompact := hK
      subset_domain := hKsub
      real_mem := hpK
      realFamily := realFamily
      n := t.card
      center := center
      r := r
      radius_eq := ?_
      radius_pos := ?_
      ball_subset := ?_
      cover_subset := ?_
      realIndex := realIndex
      real_center := ?_ }⟩
  · intro i
    rfl
  · intro i
    exact (realFamily.family.data (center i)).radius_pos
  · intro i
    exact (realFamily.family.data (center i)).ball_subset
  · intro z hzK
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
  · simp [center, realIndex]

/-- **Compact local-cover `Fin n` geometry from structured eventual-overlap
branch data**: structured real-centred eventual-overlap branch data first
packages into `LeeYangRealBranchLimitFamily`, then compactness extracts and
enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangRealEventualOverlapBranchData G Λ p) :
    Nonempty (LeeYangCompactLocalCoverFinGeometry G Λ p K) := by
  rcases exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData
      G Λ p data with
    ⟨realFamily⟩
  exact exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily
    G Λ p hK hKsub hpK realFamily

/-- **Compact local-cover `Fin n` geometry from pointwise-normalised
eventual-overlap branch data**: pointwise-normalised real eventual-overlap data
projects to the structured real eventual-overlap package, then compactness
extracts and enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_pointwiseNormEventualData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    Nonempty (LeeYangCompactLocalCoverFinGeometry G Λ p K) :=
  exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData
    G Λ p hK hKsub hpK
      (LeeYangRealEventualOverlapBranchData.ofPointwiseNormalised G Λ p data)

/-- **Local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local cover of Lee-Yang balls whose branch
families converge locally uniformly to a common `f` makes `f` holomorphic on
`leeYangDomain`; at a real Lee-Yang centre it agrees with the real
infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ n,
            AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
                    = partitionFunctionComplexAlongExhaustion G Λ
                        (p.J : ℂ) z (p.β : ℂ) n)
              ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) n)
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover
      G Λ (p.J : ℂ) (p.β : ℂ) hlocal
  rcases hlocal (p.h : ℂ) hp with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hcenter :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr hbranch hconv
  exact ⟨hdiff, hcenter.2⟩

end Ambient

end IsingModel
