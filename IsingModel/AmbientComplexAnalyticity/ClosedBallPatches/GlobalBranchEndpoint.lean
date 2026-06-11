import IsingModel.AmbientComplexAnalyticity.ClosedBallPatches.GlobalBranchBounds
import IsingModel.AmbientComplexAnalyticity.CoverPatches.Pointwise

/-!
# The unconditional positive-real endpoint via the global branch (GJ §4.6 Thm 4.6.2)

The Vitali pipeline relaxed to the real-base-point normalisation: the all-centre principal
normalisation threaded through the existing compact-open extraction is never used by the
extraction itself (only the real-centre instance enters the final identification), so the
unnormalised twins below drop it, and the global branch (PR #3903) supplies every remaining
input — overlap is trivial for a single global function, the stage-uniform ball bounds come
from the segment-integral estimate, and the real-centre normalisation is the anchoring
`g(p.h) = F(p.h)`. The headline is the **unconditional** compact-target form of GJ
Theorem 4.6.2 for positive real ferromagnetic parameters.

* `compactOpen_vitali_fin_ball_unnormalised` (+ `_overlap`, `_patch`) — the compact-open
  diagonal extraction chain without the normalisation and exponential-identity conjuncts
  (fully generic in the analytic family).
* `exists_finset_cover_of_isCompact_allStageBranchData_real` — finite ball cover of a compact
  target with one ball centred at the real field.
* `freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_of_isCompact` —
  headline: positive real ferromagnetic parameters, bounded edge density, disjoint-tower
  hypotheses, and a compact Lee-Yang target containing the physical field produce a function
  holomorphic on the target whose value at the physical field is the infinite-volume free
  energy. **No analytic side hypotheses remain.**

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric

variable {V : Type*} [DecidableEq V]

/-- **Unnormalised finite-ball compact-open diagonal extraction**: the diagonal subsequence
with locally uniform limits and holomorphic limits, from compact carriers and the exponential
identity alone — the all-centre normalisation conjunct of the existing extraction is not
consumed by the construction and is dropped here. -/
theorem compactOpen_vitali_fin_ball_unnormalised
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m, AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, ∃ f : ℂ → ℂ,
        (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
          fc ∈ A i ∧
            ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f z = fc ⟨z, hz⟩) ∧
        TendstoLocallyUniformlyOn
          (fun m z => F i (σ m) z) f Filter.atTop (Metric.ball (h0 i) (r i)) ∧
        DifferentiableOn ℂ f (Metric.ball (h0 i) (r i)) := by
  letI : ∀ i : Fin n, LocallyCompactSpace (Metric.ball (h0 i) (r i)) :=
    fun _ => Metric.isOpen_ball.locallyCompactSpace
  rcases IsingModel.exists_subseq_fin_tendstoLocallyUniformlyOn_of_isCompact_compactOpen
      n (s := fun i : Fin n => Metric.ball (h0 i) (r i))
      (hs := fun _ => Metric.isOpen_ball)
      (A := A) (hA := hA) (Fc := Fc) (hFc_mem := hFc_mem)
      (F := F) (hF := hFres) with
    ⟨σ, hσ, hlim⟩
  refine ⟨σ, hσ, ?_⟩
  intro i
  rcases hlim i with ⟨fc, f, hfcA, hf_agree, hconv⟩
  have hdiff : DifferentiableOn ℂ f (Metric.ball (h0 i) (r i)) :=
    IsingModel.vitali_bridge Metric.isOpen_ball
      (fun m => (hbranch i (σ m)).differentiableOn) hconv
  exact ⟨f, ⟨fc, hfcA, hf_agree⟩, hconv, hdiff⟩

/-- **Unnormalised extraction with overlap compatibility**: eventual stage agreement on
pairwise ball intersections passes to the extracted local limits. -/
theorem compactOpen_vitali_fin_ball_overlap_unnormalised
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m, AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i)))
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ,
        (∀ i,
          (∃ fc : C(Metric.ball (h0 i) (r i), ℂ),
            fc ∈ A i ∧
              ∀ z (hz : z ∈ Metric.ball (h0 i) (r i)), f i z = fc ⟨z, hz⟩) ∧
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        ∀ i j, Set.EqOn (f i) (f j)
          (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j)) := by
  classical
  rcases compactOpen_vitali_fin_ball_unnormalised n hA hFc_mem hFres hbranch with
    ⟨σ, hσ, hlim⟩
  choose f hf using hlim
  refine ⟨σ, hσ, f, hf, ?_⟩
  refine IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn
    n (s := fun i : Fin n => Metric.ball (h0 i) (r i))
    (F := fun i m z => F i (σ m) z) (f := f) ?_ ?_
  · intro i
    exact (hf i).2.1
  · intro i j
    exact hσ.tendsto_atTop.eventually (hoverlap i j)

/-- **Unnormalised extraction with patching**: the extracted compatible local limits patch to
one function differentiable on the finite union of balls. -/
theorem compactOpen_vitali_fin_ball_patch_unnormalised
    (n : ℕ) {h0 : Fin n → ℂ} {r : Fin n → ℝ}
    {F : Fin n → ℕ → ℂ → ℂ}
    {A : ∀ i : Fin n, Set C(Metric.ball (h0 i) (r i), ℂ)}
    {Fc : ∀ i : Fin n, ℕ → C(Metric.ball (h0 i) (r i), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z (hz : z ∈ Metric.ball (h0 i) (r i)),
      F i m z = Fc i m ⟨z, hz⟩)
    (hbranch : ∀ i m, AnalyticOnNhd ℂ (F i m) (Metric.ball (h0 i) (r i)))
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (F i m) (F j m)
        (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : Fin n → ℂ → ℂ, ∃ g : ℂ → ℂ,
        (∀ i,
          TendstoLocallyUniformlyOn
            (fun m z => F i (σ m) z) (f i) Filter.atTop
              (Metric.ball (h0 i) (r i)) ∧
          DifferentiableOn ℂ (f i) (Metric.ball (h0 i) (r i))) ∧
        (∀ i, Set.EqOn g (f i) (Metric.ball (h0 i) (r i))) ∧
        DifferentiableOn ℂ g (⋃ i : Fin n, Metric.ball (h0 i) (r i)) := by
  rcases compactOpen_vitali_fin_ball_overlap_unnormalised n hA hFc_mem hFres hbranch
      hoverlap with
    ⟨σ, hσ, f, hlocal, hcompat⟩
  rcases IsingModel.exists_differentiableOn_iUnion_of_finite_eqOn
      n (s := fun i : Fin n => Metric.ball (h0 i) (r i)) (f := f)
      (hs := fun _ => Metric.isOpen_ball)
      (hdiff := fun i => (hlocal i).2.2)
      (hcompat := hcompat) with
    ⟨g, hg_eq, hg_diff⟩
  exact ⟨σ, hσ, f, g, fun i => ⟨(hlocal i).2.1, (hlocal i).2.2⟩, hg_eq, hg_diff⟩

/-- **Finite real-centred ball cover from all-stage branch data**: a compact Lee-Yang target
containing the real field is covered by finitely many selected balls, one of which is centred
at the real field. -/
theorem exists_finset_cover_of_isCompact_allStageBranchData_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : LeeYangAllStageBranchData G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ⟨(p.h : ℂ), hKsub hpK⟩ ∈ t ∧
      K ⊆ ⋃ h₀ ∈ t, Metric.ball (h₀ : ℂ) (data.radius h₀) := by
  classical
  have hcover : K ⊆ ⋃ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (data.radius h₀) := by
    intro z hz
    exact Set.mem_iUnion.mpr
      ⟨⟨z, hKsub hz⟩, Metric.mem_ball_self (data.radius_pos ⟨z, hKsub hz⟩)⟩
  rcases hK.elim_finite_subcover
      (fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
        Metric.ball (h₀ : ℂ) (data.radius h₀))
      (fun _ => Metric.isOpen_ball) hcover with
    ⟨t, ht⟩
  let hreal : {h : ℂ // h ∈ IsingModel.leeYangDomain} := ⟨(p.h : ℂ), hKsub hpK⟩
  refine ⟨insert hreal t, Finset.mem_insert_self hreal t, ?_⟩
  intro z hzK
  rcases Set.mem_iUnion₂.mp (ht hzK) with ⟨h₀, h₀_mem, hz_ball⟩
  exact Set.mem_iUnion₂.mpr ⟨h₀, Finset.mem_insert_of_mem h₀_mem, hz_ball⟩

set_option maxHeartbeats 800000 in
/-- **GJ Theorem 4.6.2, compact-target form (unconditional)**: for positive real
ferromagnetic parameters with bounded edge density and disjoint-tower hypotheses, and a
compact `K ⊆ leeYangDomain` containing the physical field, there is a function holomorphic on
`K` whose value at the physical field is the infinite-volume free energy. The proof covers
`K` by the halved global-branch balls, manufactures the compact-open carriers from the
closure-carrier compactness (stage-uniform global-branch bounds plus derived equicontinuity),
extracts a diagonal subsequence with patched holomorphic limit by the unnormalised chain
(overlap is trivial — every centre selects the same global function), and identifies the
value at the real centre through the anchored normalisation `g(p.h) = F(p.h)`. -/
theorem freeEnergyComplexAlongExhaustion_posReal_globalBranch_holomorphicExtension_of_isCompact
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β) (hJ : 0 < p.J)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g K ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  classical
  have hb : (p.h : ℂ) ∈ IsingModel.leeYangDomain := hKsub hpK
  obtain ⟨data₀, hdataEq, _hover⟩ :=
    exists_globalLeeYangAllStageBranchData G Λ hβ hJ ⟨(p.h : ℂ), hb⟩
  set data : LeeYangAllStageBranchData G Λ (p.J : ℂ) (p.β : ℂ) := data₀.half with hdata
  have hdataEq' : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ m,
      data.branchFamily h₀ m
        = globalBranchStage G Λ (p.J : ℂ) (p.β : ℂ) (p.h : ℂ) m :=
    fun h₀ m => hdataEq h₀ m
  -- finite real-centred cover by the halved balls
  obtain ⟨t, ht_real, ht_cover⟩ :=
    exists_finset_cover_of_isCompact_allStageBranchData_real G Λ p hK hKsub hpK data
  set n : ℕ := t.card with hn
  set center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain} :=
    fun i => ((t.equivFin).symm i).1 with hcenterdef
  set i₀ : Fin n := t.equivFin ⟨⟨(p.h : ℂ), hb⟩, ht_real⟩ with hi₀
  have hcenter : ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ) := by
    simp [hcenterdef, hi₀]
  have hKcover : K ⊆ ⋃ i : Fin n,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
        (data.radius (center i)) := by
    intro z hzK
    rcases Set.mem_iUnion₂.mp (ht_cover hzK) with ⟨h₀, h₀_mem, hz_ball⟩
    refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨h₀, h₀_mem⟩, ?_⟩
    have : center (t.equivFin ⟨h₀, h₀_mem⟩) = h₀ := by
      simp [hcenterdef]
    rw [this]
    exact hz_ball
  -- stage-uniform ball bounds: the halved closed ball is compact inside the domain
  have hclosed : ∀ i : Fin n,
      Metric.closedBall ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (data.radius (center i))
        ⊆ IsingModel.leeYangDomain := by
    intro i
    refine le_trans ?_ (data₀.ball_subset (center i))
    intro w hw
    have hw' : dist w ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
        ≤ data₀.radius (center i) / 2 := hw
    have hrpos := data₀.radius_pos (center i)
    exact Metric.mem_ball.mpr (by linarith)
  have hballbound : ∀ i : Fin n, ∃ C : ℝ, 0 ≤ C ∧ ∀ m,
      ∀ z ∈ Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
        (data.radius (center i)),
      ‖data.branchFamily (center i) m z‖ ≤ C := by
    intro i
    obtain ⟨C, hC0, hC⟩ :=
      exists_uniform_norm_globalBranchStage_on_isCompact G Λ hBED hβ hJ hb
        (isCompact_closedBall _ _) (hclosed i)
    refine ⟨C, hC0, fun m z hz => ?_⟩
    rw [hdataEq' (center i) m]
    exact hC m z (Metric.ball_subset_closedBall hz)
  choose Cb hCb0 hCb using hballbound
  -- compact-open carriers from the closure-carrier compactness
  set A : ∀ i : Fin n,
      Set C(Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
        (data.radius (center i)), ℂ) :=
    fun i => ContinuousMap.toFun ⁻¹'
      closure (ContinuousMap.toFun '' Set.range (branchRestricted G Λ data (center i)))
    with hA_def
  have hA : ∀ i, IsCompact (A i) := by
    intro i
    refine IsingModel.isCompact_closureCarrier_compactOpen_complex_of_norm_le_equicontinuous
      (fun _ => Cb i) ?_ ?_
    · rintro f ⟨m, rfl⟩ x
      rw [← branchRestricted_apply G Λ data (center i) m x x.2]
      exact hCb i m x x.2
    · exact equicontinuous_branchRestricted_range G Λ data (center i) (hCb0 i) (hCb i)
  have hFc_mem : ∀ i m, branchRestricted G Λ data (center i) m ∈ A i := by
    intro i m
    exact Set.mem_preimage.mpr
      (subset_closure (Set.mem_image_of_mem _ (Set.mem_range_self m)))
  have hFres : ∀ i m z
      (hz : z ∈ Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
        (data.radius (center i))),
      data.branchFamily (center i) m z = branchRestricted G Λ data (center i) m ⟨z, hz⟩ :=
    fun i m z hz => branchRestricted_apply G Λ data (center i) m z hz
  have hbranch : ∀ i m,
      AnalyticOnNhd ℂ (data.branchFamily (center i) m)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (data.radius (center i))) :=
    fun i m => (data.branch_spec (center i) m).1
  have hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn (data.branchFamily (center i) m) (data.branchFamily (center j) m)
        (Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            (data.radius (center i))
          ∩ Metric.ball ((center j : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
            (data.radius (center j))) := by
    intro i j
    refine Filter.Eventually.of_forall fun m => ?_
    rw [hdataEq' (center i) m, hdataEq' (center j) m]
    exact Set.eqOn_refl _ _
  -- diagonal extraction and patching
  obtain ⟨σ, hσ, f, g, hlocal, hg_eq, hg_diff⟩ :=
    compactOpen_vitali_fin_ball_patch_unnormalised n hA hFc_mem hFres hbranch hoverlap
  -- identification at the real centre
  have hr₀ : 0 < data.radius (center i₀) := data.radius_pos (center i₀)
  have hbranch₀ : ∀ m,
      AnalyticOnNhd ℂ (data.branchFamily (center i₀) (σ m))
          (Metric.ball (p.h : ℂ) (data.radius (center i₀)))
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) (data.radius (center i₀)),
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) *
                data.branchFamily (center i₀) (σ m) z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ data.branchFamily (center i₀) (σ m) (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m) := by
    intro m
    refine ⟨?_, ?_, ?_⟩
    · have := (data.branch_spec (center i₀) (σ m)).1
      rwa [hcenter] at this
    · intro z hz
      have hz' : z ∈ Metric.ball
          ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
          (data.radius (center i₀)) := by rwa [hcenter]
      exact (data.branch_spec (center i₀) (σ m)).2 z hz'
    · rw [hdataEq' (center i₀) (σ m)]
      exact globalBranchStage_base G Λ (p.J : ℂ) (p.β : ℂ) (p.h : ℂ) (σ m)
  have hconv₀ : TendstoLocallyUniformlyOn
      (fun m z => data.branchFamily (center i₀) (σ m) z) (f i₀) Filter.atTop
      (Metric.ball (p.h : ℂ) (data.radius (center i₀))) := by
    have := (hlocal i₀).1
    rwa [hcenter] at this
  have hid :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      G Λ p hBED hd hr₀ hσ hbranch₀ hconv₀
  refine ⟨g, hg_diff.mono hKcover, ?_⟩
  have hmem₀ : (p.h : ℂ) ∈ Metric.ball
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)
      (data.radius (center i₀)) := by
    rw [hcenter]
    exact Metric.mem_ball_self hr₀
  rw [hg_eq i₀ hmem₀]
  exact hid.2

end Ambient

end IsingModel
