import IsingModel.AmbientComplexAnalyticity.Vitali.BranchUniformBounds
import IsingModel.AmbientComplexAnalyticity.Vitali.BranchFamilies
import IsingModel.AmbientComplexAnalyticity.AscoliData.ClosureConversions
import IsingModel.AmbientComplexAnalyticity.CompactPatches.RangeAscoli
import IsingModel.AmbientComplexAnalyticity.CompactPatches.GeometryCOpen

/-!
# Overlap-only endpoint — composing the supplied Ascoli inputs (GJ §4.6 Thm 4.6.2)

Composition of the three supplied Ascoli inputs (Issue #628): the unconditional stage-uniform
branch bound on halved balls (Borel–Carathéodory half-radius route), the derived
equicontinuity, and the closedness-free relative-compactness constructor. The resulting
positive-real endpoint assumes only the **eventual branch overlap** predicate — the single
remaining analytic hypothesis of the conditional Vitali pipeline.

* `LeeYangAllStageBranchData.OverlapEventually` — geometry-free overlap predicate.
* `LeeYangAllStageBranchData.OverlapEventually.half` — halving preserves overlap.
* `...RangeRelCompactCOpenData.ofHalfUniformBoundOverlap` — relative-compactness data for the
  halved branch data from positive real parameters and overlap alone.
* `freeEnergyComplexAlongExhaustion_closedBallUniformBoundOverlap_patch` (+ `_of_isCompact`) —
  geometry-level composed patches.
* `freeEnergyComplexAlongExhaustion_posRealUniformBoundOverlap_patch_of_isCompact` — headline:
  positive real parameters and a compact target reduce the patch input to overlap only.
* `freeEnergyComplexAlongExhaustion_posRealOverlap_holomorphicExtension_of_isCompact` —
  consumer form: overlap gives a holomorphic `g` on `K` with `g (p.h) = freeEnergyInfinite`.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6,
Theorem 4.6.2, pp. 68–70.
-/

namespace IsingModel

namespace Ambient

open Metric

variable {V : Type*} [DecidableEq V]

/-- **Eventual branch overlap**: for every pair of Lee–Yang centres, the selected per-stage
branches eventually (in the stage) agree on the intersection of the selected balls. This is
the geometry-free branch-consistency predicate — the single remaining analytic input of the
overlap-only endpoint. -/
def LeeYangAllStageBranchData.OverlapEventually {G : SimpleGraph V} {Λ : Exhaustion V}
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β) : Prop :=
  ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
    ∀ᶠ m in Filter.atTop,
      Set.EqOn (data.branchFamily h₀ m) (data.branchFamily h₁ m)
        (Metric.ball (h₀ : ℂ) (data.radius h₀) ∩ Metric.ball (h₁ : ℂ) (data.radius h₁))

/-- **Halving preserves eventual overlap**: the halved balls intersect inside the original
balls and the branch family is unchanged, so eventual agreement restricts. -/
theorem LeeYangAllStageBranchData.OverlapEventually.half {G : SimpleGraph V}
    {Λ : Exhaustion V} [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    {data : LeeYangAllStageBranchData G Λ J β}
    (h : data.OverlapEventually) : data.half.OverlapEventually := by
  intro h₀ h₁
  filter_upwards [h h₀ h₁] with m hm
  exact hm.mono (Set.inter_subset_inter
    (Metric.ball_subset_ball
      (by have := data.radius_pos h₀; change _ / 2 ≤ _; linarith))
    (Metric.ball_subset_ball
      (by have := data.radius_pos h₁; change _ / 2 ≤ _; linarith)))

/-- **Relative compactness from positive real parameters and overlap**: the stage-uniform
branch bound on halved balls (Borel–Carathéodory route) feeds the closedness-free
closure-carrier constructor, so the halved data's relative-compactness input needs only the
eventual overlap of the halved branches. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.ofHalfUniformBoundOverlap
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (K : Set ℂ)
    (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J)
    (closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.half.data)
    (hover : closedData.half.data.branchData.OverlapEventually) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.half.data geom :=
  LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.ofClosedBallUniformBound
    G Λ p K closedData.half geom
    (fun i => by
      obtain ⟨C, hC0, hC⟩ :=
        exists_uniform_branchFamily_bound_half G Λ hBED hβ hJ closedData (geom.center i)
      exact ⟨C, hC0, fun m z hz => (hC m z hz).1⟩)
    (fun i j => hover (geom.center i) (geom.center j))

/-- **Overlap-only composed patch (geometry level)**: with positive real ferromagnetic
parameters and a finite geometry on the halved branch data, eventual overlap of the halved
branches alone yields the compact real-cover patch conclusion. -/
theorem freeEnergyComplexAlongExhaustion_closedBallUniformBoundOverlap_patch
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ)
    (hBED : BoundedEdgeDensity G Λ)
    (hd : DisjointTowerHypotheses G Λ p)
    (hβ : 0 < p.β) (hJ : 0 < p.J)
    {K : Set ℂ}
    (closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.half.data)
    (hover : closedData.half.data.branchData.OverlapEventually) :
    ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
        G Λ p K geom.n geom.center
        (fun i => closedData.half.data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (closedData.half.data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) :=
  freeEnergyComplexAlongExhaustion_allStageRangeRelCompactCOpenData_patch
    G Λ p hBED hd closedData.half.data geom
    (LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.ofHalfUniformBoundOverlap
      G Λ p K hBED hβ hJ closedData geom hover)

/-- **Overlap-only composed patch from a compact target**: compactness of `K` extracts the
finite geometry on the halved branch data; eventual overlap then suffices. -/
theorem freeEnergyComplexAlongExhaustion_closedBallUniformBoundOverlap_patch_of_isCompact
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
    (hpK : (p.h : ℂ) ∈ K)
    (closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
        G Λ p K closedData.half.data,
      closedData.half.data.branchData.OverlapEventually →
        ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
            G Λ p K geom.n geom.center
            (fun i => closedData.half.data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (closedData.half.data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
      G Λ p hK hKsub hpK closedData.half.data with ⟨geom⟩
  exact ⟨geom, fun hover =>
    freeEnergyComplexAlongExhaustion_closedBallUniformBoundOverlap_patch
      G Λ p hBED hd hβ hJ closedData geom hover⟩

/-- **Positive-real overlap-only patch endpoint**: positive real ferromagnetic parameters
construct the (halved) closed-ball all-stage branch data and compactness extracts the finite
geometry, after which **eventual branch overlap is the only remaining hypothesis** for the
compact real-cover patch conclusion. This shrinks the Ascoli-structure hypothesis of the
earlier positive-real endpoints to its overlap component. -/
theorem freeEnergyComplexAlongExhaustion_posRealUniformBoundOverlap_patch_of_isCompact
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
    ∃ closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ),
      ∃ geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
          G Λ p K closedData.data,
        closedData.data.branchData.OverlapEventually →
          ∃ compactCover : LeeYangCompactFiniteRealCoverBranchLimitFamily
              G Λ p K geom.n geom.center
              (fun i => closedData.data.branchData.radius (geom.center i)),
            ∃ g : ℂ → ℂ,
              (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
                (Metric.ball (geom.center i : ℂ)
                  (closedData.data.branchData.radius (geom.center i)))) ∧
              DifferentiableOn ℂ g K ∧
              g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  rcases exists_leeYangClosedBallPointwiseNormalisedAllStageBranchData_of_positive_real
      G Λ hβ hJ with ⟨closedData₀⟩
  rcases freeEnergyComplexAlongExhaustion_closedBallUniformBoundOverlap_patch_of_isCompact
      G Λ p hBED hd hβ hJ hK hKsub hpK closedData₀ with ⟨geom, hgeom⟩
  exact ⟨closedData₀.half, geom, hgeom⟩

/-- **Positive-real overlap-only holomorphic extension**: the consumer form of the headline —
under positive real ferromagnetic parameters and a compact Lee–Yang target containing the
physical field, eventual branch overlap alone produces a holomorphic function on `K` whose
value at the physical field is the infinite-volume free energy. -/
theorem freeEnergyComplexAlongExhaustion_posRealOverlap_holomorphicExtension_of_isCompact
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
    ∃ closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ),
      closedData.data.branchData.OverlapEventually →
        ∃ g : ℂ → ℂ,
          DifferentiableOn ℂ g K ∧
          g (p.h : ℂ) = ((freeEnergyInfinite G Λ p : ℝ) : ℂ) := by
  obtain ⟨closedData, _geom, hgeom⟩ :=
    freeEnergyComplexAlongExhaustion_posRealUniformBoundOverlap_patch_of_isCompact
      G Λ p hBED hd hβ hJ hK hKsub hpK
  refine ⟨closedData, fun hover => ?_⟩
  obtain ⟨_, g, _, hg, hgh⟩ := hgeom hover
  exact ⟨g, hg, hgh⟩

end Ambient

end IsingModel
