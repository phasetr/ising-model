import IsingModel.AmbientComplexAnalyticity.Vitali.BranchFamilies

/-!
# Ambient Complex Analyticity Vitali Local Cover Patching

Mechanical child split from `AmbientComplexAnalyticity/Vitali.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointed local-cover branch-family patching handoff on `leeYangDomain`**:
if every Lee-Yang point carries a ball, a branch family on that ball, a local
limit, and the local limits are compatible on all ball overlaps, then these
pointed local limits patch to one function differentiable on the whole
Lee-Yang domain. This is a convenience assembly wrapper around the open-cover
patching handoff, using the balls centred at the points of `leeYangDomain` as
the cover. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_localCover_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain := by
  classical
  exact freeEnergyComplexAlongExhaustion_branchFamily_openCover_patch
    (G := G) (Λ := Λ) (J := J) (β := β)
    (U := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
      Metric.ball (h₀ : ℂ) (r h₀))
    (F := F) (f := f)
    (fun _ => Metric.isOpen_ball)
    (by
      intro z hz
      let hcenter : {h : ℂ // h ∈ IsingModel.leeYangDomain} := ⟨z, hz⟩
      have hball : z ∈ Metric.ball (hcenter : ℂ) (r hcenter) :=
        Metric.mem_ball_self (hr hcenter)
      have _hz_domain : z ∈ IsingModel.leeYangDomain := hsub hcenter hball
      exact Set.mem_iUnion.mpr ⟨hcenter, hball⟩)
    hbranch hconv hcompat

/-- **Structured pointed local-cover branch-limit patching handoff on
`leeYangDomain`**: a family of `LeeYangLocalBranchLimit` data indexed by the
points of `leeYangDomain`, together with pairwise compatibility of the packaged
local limits on ball overlaps, patches to one function differentiable on
`leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      LeeYangLocalBranchLimit G Λ J β h₀)
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (data h₀).limitFun (data h₁).limitFun
        (Metric.ball (h₀ : ℂ) (data h₀).radius
          ∩ Metric.ball (h₁ : ℂ) (data h₁).radius)) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  freeEnergyComplexAlongExhaustion_branchFamily_localCover_patch
    (G := G) (Λ := Λ) (J := J) (β := β)
    (F := fun h₀ => (data h₀).branchFamily)
    (f := fun h₀ => (data h₀).limitFun)
    (r := fun h₀ => (data h₀).radius)
    (fun h₀ => (data h₀).radius_pos)
    (fun h₀ => (data h₀).ball_subset)
    (fun h₀ n => (data h₀).branch_spec n)
    (fun h₀ => (data h₀).tendsto)
    hcompat

/-- **Packaged structured local-cover branch-limit patching handoff on
`leeYangDomain`**: a compatible `LeeYangLocalBranchLimitFamily` patches to one
function differentiable on `leeYangDomain`. This is the single-argument
version of `freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch`
for the later coherent local-cover extraction endpoint. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (family : LeeYangLocalBranchLimitFamily G Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch
    G Λ J β family.data family.compatible

/-- **Structured eventual-overlap local-cover patching handoff on
`leeYangDomain`**: a structured eventual-overlap package supplies compatible
local limits by turning eventual stage-level overlap equality into equality of
the locally-uniform limits, then patches those local limits to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : LeeYangEventualOverlapBranchData G Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  freeEnergyComplexAlongExhaustion_branchFamily_localCover_patch
    (G := G) (Λ := Λ) (J := J) (β := β)
    data.radius_pos data.ball_subset data.branch_spec data.tendsto
    (IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
      (s := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
        Metric.ball (h₀ : ℂ) (data.radius h₀))
      (F := data.branchFamily) (f := data.limitFun)
      data.tendsto data.overlap_eventually)

/-- **Pointwise-normalised eventual-overlap local-cover patching handoff on
`leeYangDomain`**: the pointwise-normalised package exposes the underlying
structured eventual-overlap data, whose local limits patch to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : LeeYangPointwiseNormalisedEventualOverlapBranchData G Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.branchData.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch
    G Λ J β data.branchData

/-- **Structured eventual-overlap local-cover family and patching handoff on
`leeYangDomain`**: a structured eventual-overlap package first produces the
compatible `LeeYangLocalBranchLimitFamily`, then patches the same local limits
to one differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : LeeYangEventualOverlapBranchData G Λ J β) :
    ∃ family : LeeYangLocalBranchLimitFamily G Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain := by
  let hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (data.limitFun h₀) (data.limitFun h₁)
        (Metric.ball (h₀ : ℂ) (data.radius h₀)
          ∩ Metric.ball (h₁ : ℂ) (data.radius h₁)) :=
    IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
      (s := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
        Metric.ball (h₀ : ℂ) (data.radius h₀))
      (F := data.branchFamily) (f := data.limitFun)
      data.tendsto data.overlap_eventually
  let family : LeeYangLocalBranchLimitFamily G Λ J β :=
    { data := fun h₀ =>
        { radius := data.radius h₀
          radius_pos := data.radius_pos h₀
          ball_subset := data.ball_subset h₀
          branchFamily := data.branchFamily h₀
          limitFun := data.limitFun h₀
          branch_spec := data.branch_spec h₀
          tendsto := data.tendsto h₀ }
      compatible := hcompat }
  rcases freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_patch
      G Λ J β family with
    ⟨g, hg_eq, hg_diff⟩
  exact ⟨family, g, by simpa [family] using hg_eq, hg_eq, hg_diff⟩

/-- **Pointwise-normalised eventual-overlap local-cover family and patching
handoff on `leeYangDomain`**: the pointwise-normalised package exposes the
underlying structured eventual-overlap data, which produces the compatible
local-cover family and the patched differentiable function. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_family_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : LeeYangPointwiseNormalisedEventualOverlapBranchData G Λ J β) :
    ∃ family : LeeYangLocalBranchLimitFamily G Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch
    G Λ J β data.branchData

/-- **Structured local-cover branch-limit patching with real-axis
identification**: if the packaged local-cover data are compatible and the
package centred at a real Lee-Yang field is normalised to the finite-volume
free-energy sequence at that centre, then the patched function agrees there
with the real infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitData_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (data : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      LeeYangLocalBranchLimit G Λ (p.J : ℂ) (p.β : ℂ) h₀)
    (hcenter : ∀ n,
      (data ⟨(p.h : ℂ), hp⟩).branchFamily n (p.h : ℂ)
        = freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (data h₀).limitFun (data h₁).limitFun
        (Metric.ball (h₀ : ℂ) (data h₀).radius
          ∩ Metric.ball (h₁ : ℂ) (data h₁).radius)) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  let h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} := ⟨(p.h : ℂ), hp⟩
  rcases freeEnergyComplexAlongExhaustion_branchLimitData_localCover_patch
      G Λ (p.J : ℂ) (p.β : ℂ) data hcompat with
    ⟨g, hg_eq, hg_diff⟩
  have hball : (p.h : ℂ) ∈ Metric.ball (h₀ : ℂ) (data h₀).radius :=
    Metric.mem_ball_self (data h₀).radius_pos
  have hpoint :=
    TendstoLocallyUniformlyOn.tendsto_at (data h₀).tendsto hball
  have hbranch_eq :
      (fun n => (data h₀).branchFamily n (p.h : ℂ))
        = fun n => freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n := by
    funext n
    simpa [h₀] using hcenter n
  rw [hbranch_eq] at hpoint
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  have hlimit :
      (data h₀).limitFun (p.h : ℂ)
        = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
    tendsto_nhds_unique hpoint hreal
  have hg_center : g (p.h : ℂ) = (data h₀).limitFun (p.h : ℂ) :=
    hg_eq h₀ hball
  exact ⟨g, hg_eq, hg_diff, hg_center.trans hlimit⟩

/-- **Packaged structured local-cover branch-limit patching with real-axis
identification**: a compatible `LeeYangLocalBranchLimitFamily` patches to a
differentiable function on `leeYangDomain`; if the package centred at a real
Lee-Yang field is normalised to the finite-volume free-energy sequence, the
patched function agrees there with the real infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (family : LeeYangLocalBranchLimitFamily G Λ (p.J : ℂ) (p.β : ℂ))
    (hcenter : ∀ n,
      (family.data ⟨(p.h : ℂ), hp⟩).branchFamily n (p.h : ℂ)
        = freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_branchLimitData_localCover_real
    G Λ p hBED hd hp family.data hcenter family.compatible

/-- **Real-centred packaged structured local-cover branch-limit endpoint**:
a `LeeYangRealBranchLimitFamily` patches to a differentiable function on
`leeYangDomain`, and the packaged centre normalisation identifies its value at
the real centre with the real infinite-volume free energy. This is the
single-input endpoint expected after the coherent local-cover extraction. -/
theorem freeEnergyComplexAlongExhaustion_realBranchLimitFamily_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (realFamily : LeeYangRealBranchLimitFamily G Λ p) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (realFamily.family.data h₀).limitFun
          (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
      g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_branchLimitFamily_localCover_real
    G Λ p hBED hd realFamily.centre_mem realFamily.family realFamily.centre_normalized

/-- **Raw branch-data local-cover patching with real-axis identification**:
raw coherent local-cover branch data package into
`LeeYangRealBranchLimitFamily`, then the packaged endpoint patches the local
limits to one differentiable function on `leeYangDomain` and identifies its
real-centre value with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchData_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ realFamily : LeeYangRealBranchLimitFamily G Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  let realFamily : LeeYangRealBranchLimitFamily G Λ p :=
    { centre_mem := hp
      family :=
        { data := fun h₀ =>
            { radius := r h₀
              radius_pos := hr h₀
              ball_subset := hsub h₀
              branchFamily := F h₀
              limitFun := f h₀
              branch_spec := hbranch h₀
              tendsto := hconv h₀ }
          compatible := hcompat }
      centre_normalized := hcenter }
  rcases freeEnergyComplexAlongExhaustion_realBranchLimitFamily_localCover_real
      G Λ p hBED hd realFamily with
    ⟨g, hpatch, hdiff, hvalue⟩
  refine ⟨realFamily, g, ?_, hpatch, hdiff, hvalue⟩
  intro h₀
  simpa [realFamily] using hpatch h₀

/-- **Eventual-overlap raw branch-data local-cover patching with real-axis
identification**: raw coherent local-cover branch data whose stage branches
are eventually equal on every overlap package into
`LeeYangRealBranchLimitFamily`, then patch to a function differentiable on
`leeYangDomain` and identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_branchData_eventuallyEqOn_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp
              ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ realFamily : LeeYangRealBranchLimitFamily G Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  exact freeEnergyComplexAlongExhaustion_branchData_localCover_real
    G Λ p hBED hd hp hr hsub hbranch hconv
    (IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
      (s := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
        Metric.ball (h₀ : ℂ) (r h₀))
      (F := F) (f := f) hconv hoverlap)
    hcenter

/-- **Structured eventual-overlap branch-data local-cover patching with
real-axis identification**: a real-centred
`LeeYangRealEventualOverlapBranchData` package is converted to
`LeeYangRealBranchLimitFamily`, then patched to a function differentiable on
`leeYangDomain` and identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (data : LeeYangRealEventualOverlapBranchData G Λ p) :
    ∃ realFamily : LeeYangRealBranchLimitFamily G Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  exact freeEnergyComplexAlongExhaustion_branchData_eventuallyEqOn_localCover_real
    G Λ p hBED hd data.centre_mem
    data.branchData.radius_pos data.branchData.ball_subset
    data.branchData.branch_spec data.branchData.tendsto
    data.branchData.overlap_eventually data.centre_normalized

/-- **Pointwise-normalised eventual-overlap data local-cover patching with
real-axis identification**: pointwise-normalised eventual-overlap data projects
to the real-centred structured package, then patches to a function
differentiable on `leeYangDomain` and identified at the real centre.  The
pointwise normalisation supplies the real-centre normalisation needed by the
structured endpoint. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (data : LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    ∃ realFamily : LeeYangRealBranchLimitFamily G Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.pointwiseData.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.pointwiseData.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  let realData : LeeYangRealEventualOverlapBranchData G Λ p :=
    LeeYangRealEventualOverlapBranchData.ofPointwiseNormalised G Λ p data
  simpa [realData, LeeYangRealEventualOverlapBranchData.ofPointwiseNormalised] using
    freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real
      G Λ p hBED hd realData

end Ambient

end IsingModel
