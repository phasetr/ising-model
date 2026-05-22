import IsingModel.AmbientComplexAnalyticity.Vitali.Bridge

/-!
# Ambient Complex Analyticity Vitali Branch Data

Mechanical child split from `AmbientComplexAnalyticity/Vitali.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Structured local branch-limit data on a Lee-Yang ball**: for one point
of `leeYangDomain`, this packages a positive ball radius contained in the
domain, a per-stage branch family on that ball, its local limit, the
finite-stage exponential partition-function identity, and locally uniform
convergence to the limit. -/
structure LeeYangLocalBranchLimit
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) where
  /-- Radius of the Lee-Yang ball carrying the local branch family. -/
  radius : ℝ
  /-- The local branch ball has positive radius. -/
  radius_pos : 0 < radius
  /-- The local branch ball is contained in `leeYangDomain`. -/
  ball_subset : Metric.ball (h₀ : ℂ) radius ⊆ IsingModel.leeYangDomain
  /-- Per-stage local branch family on the Lee-Yang ball. -/
  branchFamily : ℕ → ℂ → ℂ
  /-- Locally uniform limit of the branch family on the Lee-Yang ball. -/
  limitFun : ℂ → ℂ
  /-- Per-stage holomorphicity and exponential partition-function identity on
  the Lee-Yang ball. -/
  branch_spec : ∀ n,
    AnalyticOnNhd ℂ (branchFamily n) (Metric.ball (h₀ : ℂ) radius)
      ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) radius,
          Complex.exp
            ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branchFamily n z)
            = partitionFunctionComplexAlongExhaustion G Λ J z β n)
  /-- Locally uniform convergence of the branch family to `limitFun` on the
  Lee-Yang ball. -/
  tendsto :
    TendstoLocallyUniformlyOn branchFamily limitFun Filter.atTop
      (Metric.ball (h₀ : ℂ) radius)

/-- **Compatible structured local-cover branch-limit family on
`leeYangDomain`**: this is the packaged endpoint expected from the later
coherent local-cover extraction. It contains one `LeeYangLocalBranchLimit`
package at every Lee-Yang point and the pairwise compatibility of the packaged
local limits on all ball overlaps. -/
structure LeeYangLocalBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) where
  /-- Point-indexed local branch-limit data on Lee-Yang balls. -/
  data : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
    LeeYangLocalBranchLimit G Λ J β h₀
  /-- Pairwise compatibility of the packaged local limits on ball overlaps. -/
  compatible : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
    Set.EqOn (data h₀).limitFun (data h₁).limitFun
      (Metric.ball (h₀ : ℂ) (data h₀).radius
        ∩ Metric.ball (h₁ : ℂ) (data h₁).radius)

/-- **Real-centred compatible structured local-cover branch-limit family**:
for real parameters `p`, this packages a compatible Lee-Yang local-cover
branch-limit family together with membership of the real centre `p.h` in the
Lee-Yang domain and the centre normalisation needed to identify the patched
limit with `freeEnergyInfinite`. -/
structure LeeYangRealBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) where
  /-- The real centre belongs to `leeYangDomain`. -/
  centre_mem : (p.h : ℂ) ∈ IsingModel.leeYangDomain
  /-- Compatible structured local-cover branch-limit data at the real
  parameters. -/
  family : LeeYangLocalBranchLimitFamily G Λ (p.J : ℂ) (p.β : ℂ)
  /-- The branch family centred at the real field is normalised to the
  finite-volume free-energy sequence at that centre. -/
  centre_normalized : ∀ n,
    (family.data ⟨(p.h : ℂ), centre_mem⟩).branchFamily n (p.h : ℂ)
      = freeEnergyComplexAlongExhaustion G Λ
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n

/-- **All-stage Lee-Yang local branch data**: the pre-Montel branch-choice
package. It records a Lee-Yang ball at every centre and a selected analytic
finite-stage logarithm branch on that ball for every stage, but does not yet
assert locally uniform convergence or overlap coherence. -/
structure LeeYangAllStageBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) where
  /-- Radius of the point-indexed Lee-Yang ball. -/
  radius : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ
  /-- Every local-cover radius is positive. -/
  radius_pos : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < radius h₀
  /-- Every local-cover ball stays inside `leeYangDomain`. -/
  ball_subset : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
    Metric.ball (h₀ : ℂ) (radius h₀) ⊆ IsingModel.leeYangDomain
  /-- Per-centre, per-stage selected local branch family. -/
  branchFamily :
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ
  /-- Per-stage holomorphicity and exponential partition-function identity on
  every selected local-cover ball. -/
  branch_spec : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
    AnalyticOnNhd ℂ (branchFamily h₀ n) (Metric.ball (h₀ : ℂ) (radius h₀))
      ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (radius h₀),
          Complex.exp
            ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branchFamily h₀ n z)
            = partitionFunctionComplexAlongExhaustion G Λ J z β n)

/-- **Pointwise-normalised all-stage Lee-Yang local branch data**: all-stage
branch-choice data whose selected branch at every Lee-Yang centre agrees with
the principal finite-volume free-energy value at that centre. This is the
unconditional pre-Montel input that the later normal-family/diagonal step must
turn into locally uniform limits and coherent overlap data. -/
structure LeeYangPointwiseNormalisedAllStageBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) where
  /-- The underlying all-stage local branch choices. -/
  branchData : LeeYangAllStageBranchData G Λ J β
  /-- Every Lee-Yang centre is normalised to the corresponding finite-volume
  free-energy value. -/
  centre_normalized : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
    branchData.branchFamily h₀ n (h₀ : ℂ)
      = freeEnergyComplexAlongExhaustion G Λ J (h₀ : ℂ) β n

/-- **Eventual-overlap Lee-Yang local-cover branch data**: a structured
input package for the post-Montel local-cover endpoint. It contains the
point-indexed Lee-Yang balls, the selected per-stage branches, their local
limits, locally uniform convergence, and coherent eventual stage-level overlap
equality. -/
structure LeeYangEventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) where
  /-- Radius of the point-indexed Lee-Yang ball. -/
  radius : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ
  /-- Every local-cover radius is positive. -/
  radius_pos : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < radius h₀
  /-- Every local-cover ball stays inside `leeYangDomain`. -/
  ball_subset : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
    Metric.ball (h₀ : ℂ) (radius h₀) ⊆ IsingModel.leeYangDomain
  /-- Per-centre, per-stage local branch family. -/
  branchFamily :
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ
  /-- Per-centre locally uniform limit. -/
  limitFun : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ
  /-- Per-stage holomorphicity and exponential partition-function identity on
  every local-cover ball. -/
  branch_spec : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
    AnalyticOnNhd ℂ (branchFamily h₀ n) (Metric.ball (h₀ : ℂ) (radius h₀))
      ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (radius h₀),
          Complex.exp
            ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * branchFamily h₀ n z)
            = partitionFunctionComplexAlongExhaustion G Λ J z β n)
  /-- Locally uniform convergence on every local-cover ball. -/
  tendsto : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
    TendstoLocallyUniformlyOn (branchFamily h₀) (limitFun h₀) Filter.atTop
      (Metric.ball (h₀ : ℂ) (radius h₀))
  /-- Coherent eventual stage-level equality on every pairwise ball overlap. -/
  overlap_eventually : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
    ∀ᶠ n in Filter.atTop,
      Set.EqOn (branchFamily h₀ n) (branchFamily h₁ n)
        (Metric.ball (h₀ : ℂ) (radius h₀) ∩ Metric.ball (h₁ : ℂ) (radius h₁))

/-- **Real-centred eventual-overlap Lee-Yang local-cover branch data**:
eventual-overlap local-cover branch data at real parameters, together with
membership of the real centre in `leeYangDomain` and centre normalisation to
the finite-volume free-energy sequence. -/
structure LeeYangRealEventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) where
  /-- The real centre belongs to `leeYangDomain`. -/
  centre_mem : (p.h : ℂ) ∈ IsingModel.leeYangDomain
  /-- The structured eventual-overlap branch data at the real parameters. -/
  branchData : LeeYangEventualOverlapBranchData G Λ (p.J : ℂ) (p.β : ℂ)
  /-- The branch family centred at the real field is normalised to the
  finite-volume free-energy sequence at that centre. -/
  centre_normalized : ∀ n,
    branchData.branchFamily ⟨(p.h : ℂ), centre_mem⟩ n (p.h : ℂ)
      = freeEnergyComplexAlongExhaustion G Λ
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n

/-- **Pointwise-normalised eventual-overlap Lee-Yang local-cover branch data**:
a structured eventual-overlap input whose selected branch at every Lee-Yang
centre is normalised to the finite-volume free-energy value at that centre.
This is stronger than the real-centred package, which only normalises the real
field. -/
structure LeeYangPointwiseNormalisedEventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) where
  /-- The underlying coherent eventual-overlap branch data. -/
  branchData : LeeYangEventualOverlapBranchData G Λ J β
  /-- Every Lee-Yang centre is normalised to the corresponding finite-volume
  free-energy value. -/
  centre_normalized : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
    branchData.branchFamily h₀ n (h₀ : ℂ)
      = freeEnergyComplexAlongExhaustion G Λ J (h₀ : ℂ) β n

/-- **Closed-ball pointwise-normalised all-stage branch data**: the same
pre-Montel all-stage branch-choice package as
`LeeYangPointwiseNormalisedAllStageBranchData`, with the extra guarantee that
each selected Lee-Yang radius also has its closed ball inside the domain.  This
is the local compactness shape consumed by the automatic free-energy bound
handoff. -/
structure LeeYangClosedBallPointwiseNormalisedAllStageBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) where
  /-- The underlying pointwise-normalised all-stage branch package. -/
  data : LeeYangPointwiseNormalisedAllStageBranchData G Λ J β
  /-- Every selected branch radius has its closed ball inside `leeYangDomain`. -/
  closedBall_subset :
    ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.closedBall (h₀ : ℂ) (data.branchData.radius h₀) ⊆
        IsingModel.leeYangDomain

/-- **Closed-ball pointwise-normalised eventual-overlap branch data**:
pointwise-normalised eventual-overlap branch data whose selected radii also
have closed balls contained in `leeYangDomain`.  This is the post-Montel
closed-ball analogue of
`LeeYangClosedBallPointwiseNormalisedAllStageBranchData`; it keeps the
closed-ball containment input explicit while carrying coherent eventual
overlap data. -/
structure LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) where
  /-- The underlying pointwise-normalised eventual-overlap branch package. -/
  pointwiseData : LeeYangPointwiseNormalisedEventualOverlapBranchData G Λ J β
  /-- Every selected eventual-overlap branch radius has its closed ball inside
  `leeYangDomain`. -/
  closedBall_subset :
    ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.closedBall (h₀ : ℂ) (pointwiseData.branchData.radius h₀) ⊆
        IsingModel.leeYangDomain

/-- **Real pointwise-normalised eventual-overlap Lee-Yang local-cover branch
data**: pointwise-normalised eventual-overlap branch data at real parameters,
together with membership of the real field in the Lee-Yang domain. -/
structure LeeYangRealPointwiseNormalisedEventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) where
  /-- The real centre belongs to `leeYangDomain`. -/
  centre_mem : (p.h : ℂ) ∈ IsingModel.leeYangDomain
  /-- The pointwise-normalised structured eventual-overlap branch data at the
  real parameters. -/
  pointwiseData :
    LeeYangPointwiseNormalisedEventualOverlapBranchData G Λ (p.J : ℂ) (p.β : ℂ)

end Ambient

end IsingModel
