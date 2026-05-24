import IsingModel.AmbientComplexAnalyticity.CoverPatches.RealCover

/-!
# Cover patches split — compact local-cover geometry and real eventual-overlap patches

Part of the split cover-patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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


end Ambient
end IsingModel
