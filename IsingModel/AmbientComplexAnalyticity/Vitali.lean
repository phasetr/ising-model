import IsingModel.AmbientComplexAnalyticity.Basic

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-! ## Real-axis convergence to `freeEnergyInfinite`

The real-axis half of the Vitali identification: at real parameters,
`freeEnergyComplexAlongExhaustion G Λ ↑p.J ↑p.h ↑p.β n` converges to
`↑(freeEnergyInfinite G Λ p)` as `n → ∞`. Combined with the Montel
extraction (Step 3) and holomorphic-uniqueness (Step 5-6), this pins
down the Vitali limit on the Lee-Yang (sub)domain. -/

/-- **Real-axis convergence of `freeEnergyComplexAlongExhaustion`**
(under `DisjointTowerHypotheses` + `BoundedEdgeDensity`). Pointwise
limit for the Vitali identification at real parameters. -/
theorem freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p) :
    Filter.Tendsto
      (fun n => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      Filter.atTop
      (nhds ((freeEnergyInfinite G Λ p : ℝ) : ℂ)) := by
  have h_real := freeEnergyAlongExhaustion_tendsto_of_disjointTowerHypotheses
    G Λ p hBED hd
  have h_eq : (fun n => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
      = fun n => ((freeEnergyAlongExhaustion G Λ p n : ℝ) : ℂ) := by
    funext n
    exact freeEnergyComplexAlongExhaustion_at_real_eq_ofReal G Λ p n
  rw [h_eq]
  exact (Complex.continuous_ofReal.tendsto _).comp h_real

/-! ## Conditional Vitali assembly

The next statements package the final Vitali handoff for the
along-exhaustion complex free energy. The hard analytic input remains
the locally uniform convergence of the finite-volume branch family; once
that input is supplied, these lemmas turn it into holomorphicity of the
infinite-volume candidate and identify the real-positive slice with the
Fekete `freeEnergyInfinite` limit. -/

/-- **Conditional Vitali assembly on an open set** for
`freeEnergyComplexAlongExhaustion`: a locally uniform limit of
per-stage holomorphic complex free energies is holomorphic on the same
open set. This is the along-exhaustion specialization of
`IsingModel.vitali_bridge`. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    {U : Set ℂ} (hU : IsOpen U) (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ J h β n) U)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ J h β n)
      f Filter.atTop U) :
    DifferentiableOn ℂ f U :=
  IsingModel.vitali_bridge hU hF hconv

/-- **Conditional Vitali assembly on `leeYangDomain`** for
`freeEnergyComplexAlongExhaustion`. This is the named Step 5 handoff in
the infinite-volume proof of GJ §4.6 Thm 4.6.2: after the branch-family
locally-uniform convergence is available on the Lee-Yang domain, the
limit is holomorphic there. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ J h β n)
      IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ J h β n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain :=
  IsingModel.vitali_bridge_leeYangDomain hF hconv

/-- **Real-axis identification of a locally uniform Vitali limit**:
if the complex along-exhaustion free energies converge locally uniformly
on `leeYangDomain` to `f`, then at any real parameter `p.h` belonging to
`leeYangDomain`, the value of `f` is the cast of the real
`freeEnergyInfinite` limit. -/
theorem freeEnergyComplexAlongExhaustion_limit_eq_freeEnergyInfinite_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      f Filter.atTop IsingModel.leeYangDomain) :
    f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hpoint := TendstoLocallyUniformlyOn.tendsto_at hconv hp
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  exact tendsto_nhds_unique hpoint hreal

/-- **Conditional Vitali assembly with real-axis identification**:
combines holomorphicity of the locally uniform Lee-Yang limit with its
identification on the real-positive slice via the real
`freeEnergyInfinite` limit. -/
theorem freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain_identified_at_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ
      (fun h => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      IsingModel.leeYangDomain)
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hconv : TendstoLocallyUniformlyOn
      (fun n h => freeEnergyComplexAlongExhaustion G Λ
        (p.J : ℂ) h (p.β : ℂ) n)
      f Filter.atTop IsingModel.leeYangDomain) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  ⟨freeEnergyComplexAlongExhaustion_vitali_bridge_leeYangDomain
      G Λ (p.J : ℂ) (p.β : ℂ) hF hconv,
    freeEnergyComplexAlongExhaustion_limit_eq_freeEnergyInfinite_at_real
      G Λ p hBED hd hp hconv⟩

/-! ## Local branch-family Vitali assembly

The preceding Lee-Yang-domain bridge is phrased for the principal
`freeEnergyComplexAlongExhaustion` sequence. The full Lee-Yang proof uses
locally chosen logarithm branches instead. The next wrappers package the
local handoff: once a coherent branch family on a Lee-Yang ball is known to
converge locally uniformly, Vitali gives holomorphicity of the local limit,
and the PR #2675 basepoint normalisation identifies the centre value with the
real-axis Fekete limit. -/

/-- **Local branch-family Vitali bridge on a ball**: if a chosen per-stage
branch family is analytic on a ball and converges locally uniformly there,
then its limit is holomorphic on that ball. The exponential and basepoint
clauses are retained in `hbranch` so the hypothesis matches the strong
Lee-Yang branch witnesses used in the later normal-family step. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n)
        ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β n)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  IsingModel.vitali_bridge Metric.isOpen_ball
    (fun n => (hbranch n).1.differentiableOn) hconv

/-- **Local branch-family Vitali bridge with centre identification**:
for a ball centred at the real parameter `p.h`, a locally-uniform limit of
normalised branch witnesses is holomorphic on the ball and agrees at the
centre with the real infinite-volume free energy. The remaining external
input is the coherent locally-uniform convergence of the chosen branches. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_ball_identified_at_center
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {r : ℝ} (hr : 0 < r)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ n,
      AnalyticOnNhd ℂ (F n) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) n)
        ∧ F n (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n)
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
      G Λ (p.J : ℂ) (p.β : ℂ) hbranch hconv
  have hcenter : (p.h : ℂ) ∈ Metric.ball (p.h : ℂ) r := Metric.mem_ball_self hr
  have hpoint := TendstoLocallyUniformlyOn.tendsto_at hconv hcenter
  have hbranch_eq :
      (fun n => F n (p.h : ℂ))
        = fun n => freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n := by
    funext n
    exact (hbranch n).2.2
  rw [hbranch_eq] at hpoint
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  exact ⟨hdiff, tendsto_nhds_unique hpoint hreal⟩

/-- **Local-cover branch-family Vitali bridge on `leeYangDomain`**:
if every Lee-Yang point has a ball on which a chosen branch family converges
locally uniformly to the same function `f`, then `f` is holomorphic on the
whole Lee-Yang domain. This globalises the PR #2676 ball handoff while leaving
the coherent local branch construction as an explicit hypothesis. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ n,
            AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
                    = partitionFunctionComplexAlongExhaustion G Λ J z β n)
              ∧ F n h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β n)
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain := by
  intro h₀ hmem
  rcases hlocal h₀ hmem with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hdiff_ball :=
    freeEnergyComplexAlongExhaustion_branchFamily_vitali_bridge_ball
      G Λ J β hbranch hconv
  exact (hdiff_ball.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-- **Open-cover branch-family patching handoff on `leeYangDomain`**:
if a Lee-Yang open cover carries local branch-family limits which are
compatible on overlaps, then the local limits patch to one function
differentiable on `leeYangDomain`. This is the cover-level patching analogue of
the local-cover Vitali handoff; the coherent cover and compatibility data
remain explicit hypotheses. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_openCover_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {α : Type*} {U : α → Set ℂ}
    {F : α → ℕ → ℂ → ℂ} {f : α → ℂ → ℂ}
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : IsingModel.leeYangDomain ⊆ ⋃ i, U i)
    (hbranch : ∀ i n,
      AnalyticOnNhd ℂ (F i n) (U i)
        ∧ (∀ z ∈ U i,
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F i n z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β n))
    (hconv : ∀ i, TendstoLocallyUniformlyOn (F i) (f i) Filter.atTop (U i))
    (hcompat : ∀ i j, Set.EqOn (f i) (f j) (U i ∩ U j)) :
    ∃ g : ℂ → ℂ,
      (∀ i, Set.EqOn g (f i) (U i)) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain := by
  have hdiff : ∀ i, DifferentiableOn ℂ (f i) (U i) := by
    intro i
    exact IsingModel.vitali_bridge (hUopen i)
      (fun n => (hbranch i n).1.differentiableOn) (hconv i)
  rcases IsingModel.exists_differentiableOn_iUnion_of_eqOn
      (s := U) (f := f) hUopen hdiff hcompat with
    ⟨g, hg_eq, hg_diff⟩
  exact ⟨g, hg_eq, hg_diff.mono hcover⟩

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

/-- **Pointwise-normalised all-stage branch data from positive real
parameters**: for ferromagnetic real `J` and positive real `β`, the finite
Lee-Yang logarithm branch theorem supplies a selected normalised local branch
at every Lee-Yang centre and every stage. This constructs the pre-Montel data
package; locally uniform subsequential limits and coherent overlap equality
remain separate inputs. -/
theorem exists_leeYangPointwiseNormalisedAllStageBranchData_of_positive_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (LeeYangPointwiseNormalisedAllStageBranchData G Λ (J : ℂ) (β : ℂ)) := by
  classical
  choose r hr hsub using
    fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
      IsingModel.leeYangDomain_ball_subset h₀.property
  have hbranch_exists :
      ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
        ∃ f : ℂ → ℂ,
            AnalyticOnNhd ℂ f (Metric.ball (h₀ : ℂ) (r h₀))
          ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
              Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
                = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) n)
          ∧ f (h₀ : ℂ)
              = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) (h₀ : ℂ) (β : ℂ) n := by
    intro h₀ n
    exact
      freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_strong
        G Λ hβ hJ n (h₀ := (h₀ : ℂ)) (r := r h₀) (hr h₀) (hsub h₀)
  choose F hF using hbranch_exists
  refine ⟨
    { branchData :=
        { radius := r
          radius_pos := hr
          ball_subset := hsub
          branchFamily := F
          branch_spec := ?_ }
      centre_normalized := ?_ }⟩
  · intro h₀ n
    exact ⟨(hF h₀ n).1, (hF h₀ n).2.1⟩
  · intro h₀ n
    exact (hF h₀ n).2.2

/-- **Closed-ball pointwise-normalised all-stage branch data from positive real
parameters**: choose the local Lee-Yang radii by the closed-ball domain lemma,
then use the corresponding open balls for the finite-stage logarithm branches.
The resulting package keeps the closed-ball containment for later compact
local boundedness handoffs. -/
theorem
    exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    {β J : ℝ} (hβ : 0 < β) (hJ : 0 < J) :
    Nonempty
      (LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (J : ℂ) (β : ℂ)) := by
  classical
  choose r hr hclosed using
    fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
      IsingModel.leeYangDomain_closedBall_subset h₀.property
  have hball : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain := by
    intro h₀
    exact Metric.ball_subset_closedBall.trans (hclosed h₀)
  have hbranch_exists :
      ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
        ∃ f : ℂ → ℂ,
            AnalyticOnNhd ℂ f (Metric.ball (h₀ : ℂ) (r h₀))
          ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
              Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * f z)
                = partitionFunctionComplexAlongExhaustion G Λ (J : ℂ) z (β : ℂ) n)
          ∧ f (h₀ : ℂ)
              = freeEnergyComplexAlongExhaustion G Λ (J : ℂ) (h₀ : ℂ) (β : ℂ) n := by
    intro h₀ n
    exact
      freeEnergyComplexAlongExhaustion_analyticOnNhd_branch_ball_all_stages_strong
        G Λ hβ hJ n (h₀ := (h₀ : ℂ)) (r := r h₀) (hr h₀) (hball h₀)
  choose F hF using hbranch_exists
  refine ⟨
    { data :=
        { branchData :=
            { radius := r
              radius_pos := hr
              ball_subset := hball
              branchFamily := F
              branch_spec := ?_ }
          centre_normalized := ?_ }
      closedBall_subset := hclosed }⟩
  · intro h₀ n
    exact ⟨(hF h₀ n).1, (hF h₀ n).2.1⟩
  · intro h₀ n
    exact (hF h₀ n).2.2

/-- **Finite compact-open subsequence branch-limit family**: for finitely many
Lee-Yang balls, this packages the output expected after a finite compact-open
diagonal extraction: one strictly increasing stage map, a local branch family
and locally uniform limit on every ball, centre normalisation along the
subsequence, and pairwise compatibility of the local limits on overlaps. -/
structure LeeYangFiniteSubseqBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ) (h0 : Fin n → ℂ) (r : Fin n → ℝ) where
  /-- Strictly increasing subsequence of finite-volume stages. -/
  stage : ℕ → ℕ
  /-- The selected stage map tends to infinity. -/
  stage_strict : StrictMono stage
  /-- Per-ball local branch family indexed by the extracted stages. -/
  branchFamily : Fin n → ℕ → ℂ → ℂ
  /-- Per-ball locally uniform branch limit. -/
  limitFun : Fin n → ℂ → ℂ
  /-- Per-stage holomorphicity and exponential partition-function identity on
  each finite-cover ball, with the selected stage index. -/
  branch_spec : ∀ i m,
    AnalyticOnNhd ℂ (branchFamily i m) (Metric.ball (h0 i) (r i))
      ∧ (∀ z ∈ Metric.ball (h0 i) (r i),
          Complex.exp
            ((Fintype.card (↑(Λ.volume (stage m)) : Type _) : ℂ) *
              branchFamily i m z)
            = partitionFunctionComplexAlongExhaustion G Λ J z β (stage m))
  /-- The branch family is normalised at each ball centre along the selected
  stage map. -/
  centre_normalized : ∀ i m,
    branchFamily i m (h0 i)
      = freeEnergyComplexAlongExhaustion G Λ J (h0 i) β (stage m)
  /-- Locally uniform convergence on every finite-cover ball. -/
  tendsto : ∀ i,
    TendstoLocallyUniformlyOn (branchFamily i) (limitFun i) Filter.atTop
      (Metric.ball (h0 i) (r i))
  /-- Holomorphicity of every local limit on its ball. -/
  differentiable : ∀ i, DifferentiableOn ℂ (limitFun i) (Metric.ball (h0 i) (r i))
  /-- Pairwise compatibility of the local limits on ball overlaps. -/
  compatible : ∀ i j,
    Set.EqOn (limitFun i) (limitFun j)
      (Metric.ball (h0 i) (r i) ∩ Metric.ball (h0 j) (r j))

/-- **Finite Lee-Yang cover subsequence branch-limit family**: a finite
Lee-Yang-domain cover package whose centres lie in `leeYangDomain`, whose
balls remain inside `leeYangDomain`, and whose local branch limits are carried
by a compatible `LeeYangFiniteSubseqBranchLimitFamily`. This is the finite
geometry expected from the later diagonal local-cover extraction. -/
structure LeeYangFiniteCoverBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (r : Fin n → ℝ) where
  /-- Every finite-cover Lee-Yang ball has positive radius. -/
  radius_pos : ∀ i, 0 < r i
  /-- Every finite-cover ball stays inside the Lee-Yang domain. -/
  ball_subset : ∀ i,
    Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
      ⊆ IsingModel.leeYangDomain
  /-- The finite subsequence branch-limit family on the underlying centres. -/
  family : LeeYangFiniteSubseqBranchLimitFamily G Λ J β n
    (fun i => ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ)) r

/-- **Finite real-centred Lee-Yang cover branch-limit family**: a finite
Lee-Yang cover branch-limit package for real parameters, together with the
finite-cover index whose centre is the real field `p.h`. This is the finite
real-centred shape expected from the later diagonal local-cover extraction. -/
structure LeeYangFiniteRealCoverBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (r : Fin n → ℝ) where
  /-- The underlying finite Lee-Yang cover branch-limit package. -/
  cover : LeeYangFiniteCoverBranchLimitFamily
    G Λ (p.J : ℂ) (p.β : ℂ) n center r
  /-- The selected finite-cover index centred at the real field. -/
  realIndex : Fin n
  /-- The selected finite-cover centre is the real field `p.h`. -/
  real_center :
    ((center realIndex : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)

/-- **Compact finite real-centred Lee-Yang cover branch-limit family**: a
finite real-centred Lee-Yang cover branch-limit package together with a compact
target set `K ⊆ leeYangDomain` covered by the finite balls. This is the
compact-target finite-cover handoff expected before a later finite-subcover
extraction from a genuine local cover. -/
structure LeeYangCompactFiniteRealCoverBranchLimitFamily
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (r : Fin n → ℝ) where
  /-- The compact target set. -/
  isCompact : IsCompact K
  /-- The compact target stays inside the Lee-Yang domain. -/
  subset_domain : K ⊆ IsingModel.leeYangDomain
  /-- The real field belongs to the compact target. -/
  real_mem : (p.h : ℂ) ∈ K
  /-- The finite Lee-Yang balls cover the compact target. -/
  cover_subset : K ⊆
    ⋃ i : Fin n,
      Metric.ball ((center i : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) (r i)
  /-- The underlying finite real-centred Lee-Yang cover package. -/
  realCover : LeeYangFiniteRealCoverBranchLimitFamily G Λ p n center r

/-- **Compact local-cover finite geometry**: a compact target, a real-centred
packaged Lee-Yang local-cover family, and a `Fin n` enumeration of finitely
many of its local-cover balls covering the target. This is the enumerated
geometry obtained from compactness before a later construction of finite
branch-limit package data. -/
structure LeeYangCompactLocalCoverFinGeometry
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ) where
  /-- The compact target set. -/
  isCompact : IsCompact K
  /-- The compact target stays inside the Lee-Yang domain. -/
  subset_domain : K ⊆ IsingModel.leeYangDomain
  /-- The real field belongs to the compact target. -/
  real_mem : (p.h : ℂ) ∈ K
  /-- The source real-centred packaged local-cover family. -/
  realFamily : LeeYangRealBranchLimitFamily G Λ p
  /-- Number of selected centres in the finite subcover. -/
  n : ℕ
  /-- Selected Lee-Yang centres, indexed by `Fin n`. -/
  center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}
  /-- Selected radii, indexed by `Fin n`. -/
  r : Fin n → ℝ
  /-- The selected radii are exactly the radii from the source local-cover
  package at the selected centres. -/
  radius_eq : ∀ i, r i = (realFamily.family.data (center i)).radius
  /-- Every selected ball has positive radius. -/
  radius_pos : ∀ i, 0 < r i
  /-- Every selected ball stays inside the Lee-Yang domain. -/
  ball_subset : ∀ i,
    Metric.ball (center i : ℂ) (r i) ⊆ IsingModel.leeYangDomain
  /-- The selected finite balls cover the compact target. -/
  cover_subset : K ⊆ ⋃ i : Fin n, Metric.ball (center i : ℂ) (r i)
  /-- The selected finite-cover index centred at the real field. -/
  realIndex : Fin n
  /-- The selected finite-cover centre is the real field `p.h`. -/
  real_center : (center realIndex : ℂ) = (p.h : ℂ)

/-- **Packaged local-cover branch-limit family from raw branch data**: raw
pointwise Lee-Yang local-cover branch data with locally uniform limits and
pairwise overlap compatibility can be bundled into
`LeeYangLocalBranchLimitFamily`. This is the direct packaging shape expected
from a later coherent Montel/diagonal extraction. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
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
    Nonempty (LeeYangLocalBranchLimitFamily G Λ J β) := by
  refine ⟨
    { data := fun h₀ =>
        { radius := r h₀
          radius_pos := hr h₀
          ball_subset := hsub h₀
          branchFamily := F h₀
          limitFun := f h₀
          branch_spec := hbranch h₀
          tendsto := hconv h₀ }
      compatible := hcompat }⟩

/-- **Real-centred packaged local-cover branch-limit family from raw branch
data**: raw coherent Lee-Yang local-cover branch data, together with real
centre membership and centre normalisation, can be bundled into
`LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_branchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
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
    Nonempty (LeeYangRealBranchLimitFamily G Λ p) := by
  exact ⟨
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
      centre_normalized := hcenter }⟩

/-- **Packaged local-cover branch-limit family from eventual overlap data**:
raw pointwise Lee-Yang local-cover branch data whose stage branches are
eventually equal on every pairwise overlap can be bundled into
`LeeYangLocalBranchLimitFamily`. Locally uniform convergence turns the
eventual overlap equalities into compatibility of the local limits. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
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
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    Nonempty (LeeYangLocalBranchLimitFamily G Λ J β) := by
  exact exists_leeYangLocalBranchLimitFamily_of_branchData G Λ J β
    hr hsub hbranch hconv
    (IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
      (s := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
        Metric.ball (h₀ : ℂ) (r h₀))
      (F := F) (f := f) hconv hoverlap)

/-- **Real-centred packaged local-cover branch-limit family from eventual
overlap data**: raw coherent Lee-Yang local-cover branch data, eventual
stage-level equality on every overlap, and real-centre normalisation can be
bundled into `LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_branchData_eventuallyEqOn
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
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
    Nonempty (LeeYangRealBranchLimitFamily G Λ p) := by
  exact exists_leeYangRealBranchLimitFamily_of_branchData G Λ p hp
    hr hsub hbranch hconv
    (IsingModel.pairwise_eqOn_of_tendstoLocallyUniformlyOn_of_eventuallyEqOn_indexed
      (s := fun h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain} =>
        Metric.ball (h₀ : ℂ) (r h₀))
      (F := F) (f := f) hconv hoverlap)
    hcenter

/-- **Packaged local-cover branch-limit family from structured
eventual-overlap branch data**: the structured local-cover input
`LeeYangEventualOverlapBranchData` packages directly into
`LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : LeeYangEventualOverlapBranchData G Λ J β) :
    Nonempty (LeeYangLocalBranchLimitFamily G Λ J β) := by
  exact exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn
    G Λ J β data.radius_pos data.ball_subset data.branch_spec data.tendsto
    data.overlap_eventually

/-- **Packaged local-cover branch-limit family from pointwise-normalised
eventual-overlap branch data**: the pointwise-normalised package exposes the
underlying structured eventual-overlap branch data, which packages directly
into `LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_pointwiseNormEventualData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : LeeYangPointwiseNormalisedEventualOverlapBranchData G Λ J β) :
    Nonempty (LeeYangLocalBranchLimitFamily G Λ J β) :=
  exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData
    G Λ J β data.branchData

/-- **Real-centred packaged local-cover branch-limit family from structured
eventual-overlap branch data**: the real-centred structured local-cover input
`LeeYangRealEventualOverlapBranchData` packages directly into
`LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : LeeYangRealEventualOverlapBranchData G Λ p) :
    Nonempty (LeeYangRealBranchLimitFamily G Λ p) := by
  exact exists_leeYangRealBranchLimitFamily_of_branchData_eventuallyEqOn
    G Λ p data.centre_mem
    data.branchData.radius_pos data.branchData.ball_subset
    data.branchData.branch_spec data.branchData.tendsto
    data.branchData.overlap_eventually data.centre_normalized

/-- **Real-centred eventual-overlap data from pointwise-normalised data**:
pointwise normalisation at every Lee-Yang centre supplies the real-centre
normalisation required by `LeeYangRealEventualOverlapBranchData`. -/
def LeeYangRealEventualOverlapBranchData.ofPointwiseNormalised
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    LeeYangRealEventualOverlapBranchData G Λ p :=
  { centre_mem := data.centre_mem
    branchData := data.pointwiseData.branchData
    centre_normalized := by
      intro n
      exact data.pointwiseData.centre_normalized
        ⟨(p.h : ℂ), data.centre_mem⟩ n }

/-- Forget the locally uniform limits and coherent eventual-overlap fields of
pointwise-normalised eventual-overlap data, retaining only the underlying
pointwise-normalised all-stage branch choices. -/
def LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : LeeYangPointwiseNormalisedEventualOverlapBranchData G Λ J β) :
    LeeYangPointwiseNormalisedAllStageBranchData G Λ J β where
  branchData :=
    { radius := data.branchData.radius
      radius_pos := data.branchData.radius_pos
      ball_subset := data.branchData.ball_subset
      branchFamily := data.branchData.branchFamily
      branch_spec := data.branchData.branch_spec }
  centre_normalized := data.centre_normalized

/-- Forget the locally uniform limits, coherent eventual-overlap fields, and
real-centre membership of real pointwise-normalised eventual-overlap data,
retaining the underlying pointwise-normalised all-stage branch choices. -/
def LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    LeeYangPointwiseNormalisedAllStageBranchData G Λ (p.J : ℂ) (p.β : ℂ) :=
  LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData
    G Λ (p.J : ℂ) (p.β : ℂ) data.pointwiseData

/-- Forget locally uniform limits and coherent eventual-overlap fields from
closed-ball pointwise-normalised eventual-overlap data, retaining the
closed-ball all-stage branch package. -/
def LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData G Λ J β) :
    LeeYangClosedBallPointwiseNormalisedAllStageBranchData G Λ J β where
  data :=
    LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData
      G Λ J β data.pointwiseData
  closedBall_subset := data.closedBall_subset

/-- **Real-centred packaged local-cover branch-limit family from
pointwise-normalised eventual-overlap branch data**: pointwise-normalised real
eventual-overlap data projects to the structured real eventual-overlap package,
then packages into `LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_pointwiseNormEventualData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p) :
    Nonempty (LeeYangRealBranchLimitFamily G Λ p) :=
  exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData
    G Λ p (LeeYangRealEventualOverlapBranchData.ofPointwiseNormalised G Λ p data)

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

/-! ## Subsequence local branch-family Vitali assembly

The actual Montel step is expected to produce a locally uniformly convergent
subsequence of local Lee-Yang logarithm branches. The next wrappers are the
subsequence-indexed variants of the preceding local branch-family handoffs:
the stage at branch-family index `m` is `σ m`, where `σ` is strictly
increasing. -/

/-- **Subsequence local branch-family Vitali bridge on a ball**: if a
Montel-extracted subsequence of per-stage branch witnesses is analytic on a
Lee-Yang ball and converges locally uniformly there, then its limit is
holomorphic on that ball. The branch identities are written at stage `σ m`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {h₀ : ℂ} {r : ℝ}
    {σ : ℕ → ℕ}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
        ∧ (∀ z ∈ Metric.ball h₀ r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
        ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f (Metric.ball h₀ r) :=
  IsingModel.vitali_bridge Metric.isOpen_ball
    (fun m => (hbranch m).1.differentiableOn) hconv

/-- **Subsequence local branch-family Vitali bridge with centre
identification**: for a ball centred at the real parameter `p.h`, a locally
uniform limit of subsequence branch witnesses is holomorphic on the ball and
agrees at the centre with the real infinite-volume free energy. The real-axis
convergence is composed with the strictly increasing index map `σ`. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {r : ℝ} (hr : 0 < r)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hbranch : ∀ m,
      AnalyticOnNhd ℂ (F m) (Metric.ball (p.h : ℂ) r)
        ∧ (∀ z ∈ Metric.ball (p.h : ℂ) r,
            Complex.exp
              ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
              = partitionFunctionComplexAlongExhaustion G Λ
                  (p.J : ℂ) z (p.β : ℂ) (σ m))
        ∧ F m (p.h : ℂ)
            = freeEnergyComplexAlongExhaustion G Λ
                (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop
      (Metric.ball (p.h : ℂ) r)) :
    DifferentiableOn ℂ f (Metric.ball (p.h : ℂ) r) ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ (p.J : ℂ) (p.β : ℂ) hbranch hconv
  have hcenter : (p.h : ℂ) ∈ Metric.ball (p.h : ℂ) r := Metric.mem_ball_self hr
  have hpoint := TendstoLocallyUniformlyOn.tendsto_at hconv hcenter
  have hbranch_eq :
      (fun m => F m (p.h : ℂ))
        = fun m => freeEnergyComplexAlongExhaustion G Λ
            (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m) := by
    funext m
    exact (hbranch m).2.2
  rw [hbranch_eq] at hpoint
  have hreal :=
    freeEnergyComplexAlongExhaustion_tendsto_at_real_of_disjointTowerHypotheses
      G Λ p hBED hd
  have hreal_subseq :
      Filter.Tendsto
        (fun m => freeEnergyComplexAlongExhaustion G Λ
          (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) (σ m))
        Filter.atTop
        (nhds ((freeEnergyInfinite G Λ p : ℝ) : ℂ)) := by
    simpa [Function.comp_def] using hreal.comp hσ.tendsto_atTop
  exact ⟨hdiff, tendsto_nhds_unique hpoint hreal_subseq⟩

/-- **Subsequence local-cover branch-family Vitali bridge on
`leeYangDomain`**: if every Lee-Yang point has a ball on which a
subsequence-indexed branch family converges locally uniformly to the same
function `f`, then `f` is holomorphic on the whole Lee-Yang domain. This is
the handoff shape expected after a Montel diagonal extraction. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (J β : ℂ) {σ : ℕ → ℕ} {f : ℂ → ℂ}
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = partitionFunctionComplexAlongExhaustion G Λ J z β (σ m))
              ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ J h₀ β (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain := by
  intro h₀ hmem
  rcases hlocal h₀ hmem with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hdiff_ball :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_bridge_ball
      G Λ J β hbranch hconv
  exact (hdiff_ball.differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

/-- **Subsequence local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local Lee-Yang cover of subsequence branch
families converging locally uniformly to a common `f` makes `f` holomorphic on
`leeYangDomain`, and at a real Lee-Yang centre it agrees with the real
infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover_real
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ m,
            AnalyticOnNhd ℂ (F m) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume (σ m)) : Type _) : ℂ) * F m z)
                    = partitionFunctionComplexAlongExhaustion G Λ
                        (p.J : ℂ) z (p.β : ℂ) (σ m))
              ∧ F m h₀ = freeEnergyComplexAlongExhaustion G Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) (σ m))
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  have hdiff :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_localCover
      G Λ (p.J : ℂ) (p.β : ℂ) hlocal
  rcases hlocal (p.h : ℂ) hp with ⟨r, hr, _hsub, F, hbranch, hconv⟩
  have hcenter :=
    freeEnergyComplexAlongExhaustion_subseq_branchFamily_vitali_ball_identified_at_center
      (V := V) G Λ p hBED hd hr hσ hbranch hconv
  exact ⟨hdiff, hcenter.2⟩

end Ambient

end IsingModel
