import IsingModel.AmbientComplexAnalyticity.Vitali.BranchData

/-!
# Ambient Complex Analyticity Vitali Branch Families

Mechanical child split from `AmbientComplexAnalyticity/Vitali.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

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

end Ambient

end IsingModel
