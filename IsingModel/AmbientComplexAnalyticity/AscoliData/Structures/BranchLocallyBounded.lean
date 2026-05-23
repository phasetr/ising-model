import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.BranchNormBounded

/-!
# Ascoli data structures split — branch locally-bounded Ascoli data

Part of the split ambient Ascoli-data structures layer (Issue #1850).
-/

namespace IsingModel
namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage branch locally bounded Ascoli data**:
a local-boundedness version of the branch constant norm-bounded Ascoli input.
It asks only for the existence of one real norm bound on each selected
Lee--Yang ball, leaving the actual constants to be chosen by the conversion to
the constant-bound package. -/
structure LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The original branch family is uniformly bounded on each selected ball. -/
  branch_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    ‖data.branchData.branchFamily (geom.center i) m z‖ ≤ C
  /-- Every range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    data.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩
  /-- Selected branch families are eventually equal on pairwise overlaps. -/
  overlap_eventually : ∀ i j, ∀ᶠ m in Filter.atTop,
    Set.EqOn
      (data.branchData.branchFamily (geom.center i) m)
      (data.branchData.branchFamily (geom.center j) m)
      (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
        ∩ Metric.ball (geom.center j : ℂ)
          (data.branchData.radius (geom.center j)))

/-- **Eventual-overlap branch locally bounded Ascoli data**: a variant of
`LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData` whose
coherent selected-overlap input is supplied by pointwise-normalised
eventual-overlap data.  The branch local bounds and remaining Ascoli side
conditions are still explicit. -/
structure
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData)) where
  /-- Continuous restrictions of each selected stage branch on the selected
  ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (eventualData.pointwiseData.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every selected range carrier is
  closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The selected branch family is uniformly bounded on each selected ball. -/
  branch_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (eventualData.pointwiseData.branchData.radius (geom.center i))),
    ‖eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ ≤ C
  /-- Every selected range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (eventualData.pointwiseData.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original eventual-overlap
  branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (eventualData.pointwiseData.branchData.radius (geom.center i))),
    eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩

/-- **Pointwise-normalised all-stage branch-deviation locally bounded Ascoli
data**: a bridge input that separates local boundedness of the selected branch
family into two estimates: local boundedness of the principal finite-volume
free energy on the selected ball, and a uniform bound on the deviation of the
chosen local logarithm branch from that principal value.  Together these imply
the branch locally bounded Ascoli package. -/
structure
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The principal finite-volume free energies are uniformly bounded on each
  selected ball. -/
  freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C
  /-- The selected local branch differs from the principal finite-volume
  free energy by a uniformly bounded amount on each selected ball. -/
  branch_deviation_bound : ∀ i : Fin geom.n, ∃ D : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    ‖data.branchData.branchFamily (geom.center i) m z
        - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ D
  /-- Every range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    data.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩
  /-- Selected branch families are eventually equal on pairwise overlaps. -/
  overlap_eventually : ∀ i j, ∀ᶠ m in Filter.atTop,
    Set.EqOn
      (data.branchData.branchFamily (geom.center i) m)
      (data.branchData.branchFamily (geom.center j) m)
      (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
        ∩ Metric.ball (geom.center j : ℂ)
          (data.branchData.radius (geom.center j)))

/-- **Eventual-overlap branch-deviation Ascoli data**: a variant of
`LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData` whose
coherent selected-overlap input is supplied by pointwise-normalised
eventual-overlap data.  The remaining Ascoli side conditions and deviation
estimates are still explicit. -/
structure
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData)) where
  /-- Continuous restrictions of each selected stage branch on the selected
  ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (eventualData.pointwiseData.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every selected range carrier is
  closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The principal finite-volume free energies are uniformly bounded on each
  selected ball. -/
  freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (eventualData.pointwiseData.branchData.radius (geom.center i))),
    ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C
  /-- The selected local branch differs from the principal finite-volume
  free energy by a uniformly bounded amount on each selected ball. -/
  branch_deviation_bound : ∀ i : Fin geom.n, ∃ D : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (eventualData.pointwiseData.branchData.radius (geom.center i))),
    ‖eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z
        - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ D
  /-- Every selected range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (eventualData.pointwiseData.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original eventual-overlap
  branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (eventualData.pointwiseData.branchData.radius (geom.center i))),
    eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩

/-- **Closed-ball branch-deviation Ascoli data**: a variant of
`LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData` for
closed-ball all-stage branch choices.  It keeps the closed-ball containment
from the branch data and therefore omits the principal finite-volume
free-energy bound; that bound is supplied automatically by the Lee-Yang
closed-ball locally bounded free-energy theorem. -/
structure
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data) where
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (closedData.data.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The selected local branch differs from the principal finite-volume
  free energy by a uniformly bounded amount on each selected ball. -/
  branch_deviation_bound : ∀ i : Fin geom.n, ∃ D : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedData.data.branchData.radius (geom.center i))),
    ‖closedData.data.branchData.branchFamily (geom.center i) m z
        - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ D
  /-- Every range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (closedData.data.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedData.data.branchData.radius (geom.center i))),
    closedData.data.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩
  /-- Selected branch families are eventually equal on pairwise overlaps. -/
  overlap_eventually : ∀ i j, ∀ᶠ m in Filter.atTop,
    Set.EqOn
      (closedData.data.branchData.branchFamily (geom.center i) m)
      (closedData.data.branchData.branchFamily (geom.center j) m)
      (Metric.ball (geom.center i : ℂ)
          (closedData.data.branchData.radius (geom.center i))
        ∩ Metric.ball (geom.center j : ℂ)
          (closedData.data.branchData.radius (geom.center j)))

/-- **Eventual-overlap closed-ball branch-deviation Ascoli data**: a
closed-ball branch-deviation Ascoli input whose coherent selected-overlap
field is supplied by pointwise-normalised eventual-overlap data.  The
closed-ball containment, branch-deviation bounds, and remaining Ascoli side
conditions are still explicit. -/
structure
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data) where
  /-- Continuous restrictions of each selected stage branch on the selected
  ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (closedEventualData.pointwiseData.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every selected range carrier is
  closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The selected local branch differs from the principal finite-volume
  free energy by a uniformly bounded amount on each selected ball. -/
  branch_deviation_bound : ∀ i : Fin geom.n, ∃ D : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedEventualData.pointwiseData.branchData.radius (geom.center i))),
    ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z
        - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ D
  /-- Every selected range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (closedEventualData.pointwiseData.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original eventual-overlap
  branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedEventualData.pointwiseData.branchData.radius (geom.center i))),
    closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩

/-- **Closed-ball branch locally bounded Ascoli data**: a closed-ball variant
where the selected branch family itself is locally bounded on each selected
Lee--Yang ball.  The closed-ball Lee-Yang bound supplies the principal
finite-volume free-energy bound, so this input can be converted to the
closed-ball branch-deviation package by the triangle inequality. -/
structure
    LeeYangClosedBallBranchLocallyBoundedAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data) where
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (closedData.data.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The original closed-ball branch family is uniformly bounded on each
  selected ball. -/
  branch_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedData.data.branchData.radius (geom.center i))),
    ‖closedData.data.branchData.branchFamily (geom.center i) m z‖ ≤ C
  /-- Every range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (closedData.data.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedData.data.branchData.radius (geom.center i))),
    closedData.data.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩
  /-- Selected branch families are eventually equal on pairwise overlaps. -/
  overlap_eventually : ∀ i j, ∀ᶠ m in Filter.atTop,
    Set.EqOn
      (closedData.data.branchData.branchFamily (geom.center i) m)
      (closedData.data.branchData.branchFamily (geom.center j) m)
      (Metric.ball (geom.center i : ℂ)
          (closedData.data.branchData.radius (geom.center i))
        ∩ Metric.ball (geom.center j : ℂ)
          (closedData.data.branchData.radius (geom.center j)))

/-- **Eventual-overlap closed-ball branch locally bounded Ascoli data**:
a closed-ball branch-local Ascoli input whose coherent selected-overlap field
is supplied by pointwise-normalised eventual-overlap data.  The closed-ball
containment, branch local bounds, and remaining Ascoli side conditions are
still explicit. -/
structure
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data) where
  /-- Continuous restrictions of each selected stage branch on the selected
  ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (closedEventualData.pointwiseData.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every selected range carrier is
  closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- The selected closed-ball branch family is uniformly bounded on each
  selected ball. -/
  branch_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedEventualData.pointwiseData.branchData.radius (geom.center i))),
    ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ ≤ C
  /-- Every selected range carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : Set.range (restricted i) →
        Metric.ball (geom.center i : ℂ)
          (closedEventualData.pointwiseData.branchData.radius (geom.center i)) → ℂ)
  /-- The continuous restriction agrees with the original eventual-overlap
  branch family. -/
  restrict_eq : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (closedEventualData.pointwiseData.branchData.radius (geom.center i))),
    closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z =
      restricted i m ⟨z, hz⟩

end Ambient
end IsingModel
