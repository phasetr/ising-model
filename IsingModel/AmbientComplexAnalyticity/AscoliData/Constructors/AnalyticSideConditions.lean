import IsingModel.Analysis.HolomorphicEquicontinuity
import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.BranchLocallyBounded

/-!
# Discharging the Ascoli side conditions from a stage-uniform bound (GJ §4.6 Thm 4.6.2)

The subject is a Lee–Yang branch family. A `LeeYangAllStageBranchData G Λ J β` assigns to each
base point `h₀` of the Lee–Yang domain a positive radius whose ball stays inside that domain and,
at each stage `m`, a function on `ℂ` that is analytic on the ball and for which `Complex.exp` of
the cardinality of the stage volume times its value is the stage partition function there.

Restricting such a branch to its own ball produces a `ContinuousMap` on the ball's subtype, the
continuity coming from the analyticity carried by the branch specification, and evaluating that
restriction reproduces evaluation of the branch. When the branch family is bounded on the ball by
a single nonnegative constant uniformly in the stage, the restrictions are equicontinuous as a
range carrier: a uniformly bounded analytic family on a ball has a Schwarz-type derivative bound,
hence a uniform local Lipschitz estimate, hence equicontinuity, and equicontinuity transfers
along the coercion of the range.

That is what the Ascoli-data constructors here spend. Each is stated over a finite ball geometry
covering a compact target `K`, indexed by `Fin geom.n` with centres in the Lee–Yang domain, and
takes as hypotheses the closedness of each range image, a stage-uniform norm bound on each
selected ball, and eventual agreement of the branches on overlaps; the branch-deviation form takes
in addition a bound on the deviation of each branch from the stage free energy. From these the
continuous restrictions, the restriction identity and the equicontinuity are computed rather than
assumed, and in the norm-bounded form the pointwise bound field is the stage-uniform constant
supplied for that ball.

References: Glimm–Jaffe, *Quantum Physics*, 2nd ed. (Springer, 1987), §4.6, Theorem 4.6.2.
-/

namespace IsingModel

open Metric

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Canonical continuous restriction of a stage branch** to its selected Lee–Yang ball: the
branch is analytic on the ball (`branch_spec`), hence continuous, and the subtype restriction
is a `ContinuousMap`. -/
noncomputable def branchRestricted (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) (m : ℕ) :
    C(Metric.ball (h₀ : ℂ) (data.radius h₀), ℂ) :=
  ⟨(Metric.ball (h₀ : ℂ) (data.radius h₀)).restrict (data.branchFamily h₀ m),
    ((data.branch_spec h₀ m).1.continuousOn).restrict⟩

/-- The canonical restriction agrees with the branch family. -/
theorem branchRestricted_apply (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) (m : ℕ) (z : ℂ)
    (hz : z ∈ Metric.ball (h₀ : ℂ) (data.radius h₀)) :
    data.branchFamily h₀ m z = branchRestricted G Λ data h₀ m ⟨z, hz⟩ := rfl

/-- **The canonical restrictions of a stage-uniformly bounded branch family are equicontinuous
as a range carrier**: the Schwarz/Lipschitz estimates apply to the underlying analytic family,
and equicontinuity transfers to the range. -/
theorem equicontinuous_branchRestricted_range (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet] {J β : ℂ}
    (data : LeeYangAllStageBranchData G Λ J β)
    (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ m, ∀ z ∈ Metric.ball (h₀ : ℂ) (data.radius h₀),
      ‖data.branchFamily h₀ m z‖ ≤ C) :
    Equicontinuous ((↑) : Set.range (branchRestricted G Λ data h₀) →
      Metric.ball (h₀ : ℂ) (data.radius h₀) → ℂ) := by
  refine equicontinuous_range_coe _ ?_
  exact equicontinuous_restrict_of_analyticOnNhd_of_bounded hC
    (fun m => (data.branch_spec h₀ m).1) hb

/-- **Closed-ball branch-deviation Ascoli data from a stage-uniform bound**: reduces the six
fields of `LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData` to four
inputs — range-image closedness, the stage-uniform norm bound, the branch-deviation bound, and
eventual overlap coherence. The continuous restrictions, the restriction identity, and the
equicontinuity are derived from the branch analyticity and the Schwarz/Lipschitz estimates. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.ofUniformBound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData : LeeYangClosedBallPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K closedData.data)
    (hclosed : ∀ i : Fin geom.n, IsClosed (ContinuousMap.toFun ''
      Set.range (branchRestricted G Λ closedData.data.branchData (geom.center i))))
    (hbound : ∀ i : Fin geom.n, ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ∀ z ∈ Metric.ball
        ((geom.center i : ℂ)) (closedData.data.branchData.radius (geom.center i)),
        ‖closedData.data.branchData.branchFamily (geom.center i) m z‖ ≤ C)
    (hdev : ∀ i : Fin geom.n, ∃ D : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball ((geom.center i : ℂ))
        (closedData.data.branchData.radius (geom.center i))),
      ‖closedData.data.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ D)
    (hover : ∀ i j : Fin geom.n, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (closedData.data.branchData.branchFamily (geom.center i) m)
        (closedData.data.branchData.branchFamily (geom.center j) m)
        (Metric.ball ((geom.center i : ℂ))
            (closedData.data.branchData.radius (geom.center i))
          ∩ Metric.ball ((geom.center j : ℂ))
            (closedData.data.branchData.radius (geom.center j)))) :
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
      G Λ p K closedData geom where
  restricted i := branchRestricted G Λ closedData.data.branchData (geom.center i)
  toFun_image_closed := hclosed
  branch_deviation_bound := hdev
  equicontinuous i := by
    obtain ⟨C, hC0, hCb⟩ := hbound i
    exact equicontinuous_branchRestricted_range G Λ closedData.data.branchData
      (geom.center i) hC0 hCb
  restrict_eq i m z hz :=
    branchRestricted_apply G Λ closedData.data.branchData (geom.center i) m z hz
  overlap_eventually := hover

/-- **Branch norm-bounded Ascoli data from a stage-uniform bound**: the norm-bounded variant of
`ofUniformBound` — the same three derivable fields, with the pointwise `bound` taken to be the
stage-uniform constant on each selected ball. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.ofUniformBound
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (hclosed : ∀ i : Fin geom.n, IsClosed (ContinuousMap.toFun ''
      Set.range (branchRestricted G Λ data.branchData (geom.center i))))
    (hbound : ∀ i : Fin geom.n, ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ∀ z ∈ Metric.ball
        ((geom.center i : ℂ)) (data.branchData.radius (geom.center i)),
        ‖data.branchData.branchFamily (geom.center i) m z‖ ≤ C)
    (hover : ∀ i j : Fin geom.n, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (geom.center i) m)
        (data.branchData.branchFamily (geom.center j) m)
        (Metric.ball ((geom.center i : ℂ)) (data.branchData.radius (geom.center i))
          ∩ Metric.ball ((geom.center j : ℂ))
            (data.branchData.radius (geom.center j)))) :
    LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
      G Λ p K data geom where
  restricted i := branchRestricted G Λ data.branchData (geom.center i)
  bound i := fun _ => (hbound i).choose
  toFun_image_closed := hclosed
  branch_norm_le i m z hz := (hbound i).choose_spec.2 m z hz
  equicontinuous i :=
    equicontinuous_branchRestricted_range G Λ data.branchData (geom.center i)
      (hbound i).choose_spec.1 (hbound i).choose_spec.2
  restrict_eq i m z hz :=
    branchRestricted_apply G Λ data.branchData (geom.center i) m z hz
  overlap_eventually := hover

end Ambient

end IsingModel
