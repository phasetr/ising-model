import IsingModel.AmbientComplexAnalyticity.CoverPatches.LocalCover

/-!
# Cover patches split — pointwise-normalised eventual data and fin-ball patches

Part of the split cover-patches layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

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
