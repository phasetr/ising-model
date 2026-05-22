import IsingModel.AmbientComplexAnalyticity.AscoliData.CompactOpenConversions

/-!
# Ambient complex analyticity Ascoli branch conversions

Mechanical child split from `AmbientComplexAnalyticity/AscoliData.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

namespace LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData

/-- Convert eventual-overlap branch locally bounded Ascoli data into the
ordinary branch locally bounded package by taking the coherent selected-overlap
field from the underlying pointwise-normalised eventual-overlap data. -/
noncomputable def toBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualLocallyBounded :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
      G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData) geom where
  restricted := eventualLocallyBounded.restricted
  toFun_image_closed := eventualLocallyBounded.toFun_image_closed
  branch_bound := by
    simpa [LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      eventualLocallyBounded.branch_bound
  equicontinuous := eventualLocallyBounded.equicontinuous
  restrict_eq := by
    simpa [LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      eventualLocallyBounded.restrict_eq
  overlap_eventually := by
    intro i j
    simpa [LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      eventualData.pointwiseData.branchData.overlap_eventually
        (geom.center i) (geom.center j)

/-- Convert eventual-overlap branch locally bounded Ascoli data into
relatively compact range data by first deriving the ordinary branch locally
bounded package with its overlap field supplied from eventual-overlap data. -/
noncomputable def toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualLocallyBounded :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData) geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData
    G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData) geom
    (toBranchLocallyBoundedData
      G Λ p K eventualData geom eventualLocallyBounded)

end LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData

/-- Convert all-stage branch-deviation locally bounded Ascoli data into branch
locally bounded Ascoli data by combining the principal free-energy bound and
the branch-deviation bound with the triangle inequality. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (deviationBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
      G Λ p K data geom where
  restricted := deviationBounded.restricted
  toFun_image_closed := deviationBounded.toFun_image_closed
  branch_bound := fun i => by
    rcases deviationBounded.freeEnergy_bound i with ⟨C, hC⟩
    rcases deviationBounded.branch_deviation_bound i with ⟨D, hD⟩
    refine ⟨D + C, ?_⟩
    intro m z hz
    let F := freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m
    calc
      ‖data.branchData.branchFamily (geom.center i) m z‖ =
          ‖(data.branchData.branchFamily (geom.center i) m z - F) + F‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖data.branchData.branchFamily (geom.center i) m z - F‖ + ‖F‖ :=
          norm_add_le _ _
      _ ≤ D + C := add_le_add (hD m z hz) (hC m z hz)
  equicontinuous := deviationBounded.equicontinuous
  restrict_eq := deviationBounded.restrict_eq
  overlap_eventually := deviationBounded.overlap_eventually

/-- Convert all-stage branch-deviation locally bounded Ascoli data into
relatively compact range data by first deriving branch local boundedness. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (deviationBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData
    G Λ p K data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toBranchLocallyBoundedData
      G Λ p K data geom deviationBounded)

set_option linter.style.longLine false in
/-- Convert all-stage branch-deviation Ascoli data into relatively compact
range data through the named branch-local route.  This restates the existing
branch-deviation range conversion with the intermediate route exposed. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData_viaLocal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (deviationBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData
    G Λ p K data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toBranchLocallyBoundedData
      G Λ p K data geom deviationBounded)

namespace LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData

/-- Convert all-stage branch locally bounded Ascoli data into branch-deviation
Ascoli data when an explicit local bound for the principal finite-volume free
energy is supplied. -/
noncomputable def toBranchDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
    (locallyBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
      G Λ p K data geom where
  restricted := locallyBounded.restricted
  toFun_image_closed := locallyBounded.toFun_image_closed
  freeEnergy_bound := freeEnergy_bound
  branch_deviation_bound := fun i => by
    rcases locallyBounded.branch_bound i with ⟨B, hB⟩
    rcases freeEnergy_bound i with ⟨C, hC⟩
    refine ⟨B + C, ?_⟩
    intro m z hz
    calc
      ‖data.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖
          ≤ ‖data.branchData.branchFamily (geom.center i) m z‖ +
              ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ := by
            exact norm_sub_le _ _
      _ ≤ B + C := add_le_add (hB m z hz) (hC m z hz)
  equicontinuous := locallyBounded.equicontinuous
  restrict_eq := locallyBounded.restrict_eq
  overlap_eventually := locallyBounded.overlap_eventually

/-- Convert all-stage branch locally bounded Ascoli data to relatively compact
range data through the branch-deviation route, using an explicit principal
free-energy local bound. -/
noncomputable def toRangeRelCompactData_viaDeviation
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
    (locallyBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData
    G Λ p K data geom
    (toBranchDeviationData
      G Λ p K data geom freeEnergy_bound locallyBounded)

end LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData

namespace LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData

/-- Convert eventual-overlap branch-deviation Ascoli data into the ordinary
branch-deviation Ascoli package by taking the coherent selected-overlap field
from the underlying pointwise-normalised eventual-overlap data. -/
noncomputable def toBranchDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
      G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData) geom where
  restricted := eventualDeviation.restricted
  toFun_image_closed := eventualDeviation.toFun_image_closed
  freeEnergy_bound := eventualDeviation.freeEnergy_bound
  branch_deviation_bound := by
    simpa [LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      eventualDeviation.branch_deviation_bound
  equicontinuous := eventualDeviation.equicontinuous
  restrict_eq := by
    simpa [LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      eventualDeviation.restrict_eq
  overlap_eventually := by
    intro i j
    simpa [LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      eventualData.pointwiseData.branchData.overlap_eventually
        (geom.center i) (geom.center j)

/-- Convert eventual-overlap branch-deviation Ascoli data into relatively
compact range data by first deriving the ordinary branch-deviation package
with its overlap field supplied from the eventual-overlap input. -/
noncomputable def toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData) geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData
    G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData) geom
    (toBranchDeviationData
      G Λ p K eventualData geom eventualDeviation)

/-- Convert eventual-overlap branch-deviation Ascoli data into the
eventual-overlap branch-local package by combining the supplied principal
free-energy bound with the branch-deviation bound.  The selected-overlap field
is still supplied only by the eventual-overlap data when the downstream
ordinary branch-local package is formed. -/
noncomputable def toBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
      G Λ p K eventualData geom where
  restricted := eventualDeviation.restricted
  toFun_image_closed := eventualDeviation.toFun_image_closed
  branch_bound := fun i => by
    rcases eventualDeviation.freeEnergy_bound i with ⟨C, hC⟩
    rcases eventualDeviation.branch_deviation_bound i with ⟨D, hD⟩
    refine ⟨D + C, ?_⟩
    intro m z hz
    let F := freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m
    calc
      ‖eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ =
          ‖(eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z - F)
              + F‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z - F‖ +
            ‖F‖ := norm_add_le _ _
      _ ≤ D + C := add_le_add (hD m z hz) (hC m z hz)
  equicontinuous := eventualDeviation.equicontinuous
  restrict_eq := eventualDeviation.restrict_eq

set_option linter.style.longLine false in
/-- Convert eventual-overlap branch-deviation Ascoli data to relatively compact
range data through the branch-local route. -/
noncomputable def toRangeRelCompactData_viaLocal
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (eventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData) geom :=
  LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData.toRangeRelCompactData
    G Λ p K eventualData geom
    (toBranchLocallyBoundedData
      G Λ p K eventualData geom eventualDeviation)

end LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData

namespace LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData

set_option linter.style.longLine false in
/-- Convert eventual-overlap branch locally bounded Ascoli data into the
eventual-overlap branch-deviation package when an explicit local bound for the
principal finite-volume free energy is supplied.  The selected-overlap field is
still supplied only by the eventual-overlap data when the downstream ordinary
branch-deviation package is formed. -/
noncomputable def toBranchDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (eventualData.pointwiseData.branchData.radius (geom.center i))),
      ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
    (eventualLocallyBounded :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData
      G Λ p K eventualData geom where
  restricted := eventualLocallyBounded.restricted
  toFun_image_closed := eventualLocallyBounded.toFun_image_closed
  freeEnergy_bound := freeEnergy_bound
  branch_deviation_bound := fun i => by
    rcases eventualLocallyBounded.branch_bound i with ⟨B, hB⟩
    rcases freeEnergy_bound i with ⟨C, hC⟩
    refine ⟨B + C, ?_⟩
    intro m z hz
    calc
      ‖eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖
          ≤ ‖eventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ +
              ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ := by
            exact norm_sub_le _ _
      _ ≤ B + C := add_le_add (hB m z hz) (hC m z hz)
  equicontinuous := eventualLocallyBounded.equicontinuous
  restrict_eq := eventualLocallyBounded.restrict_eq

set_option linter.style.longLine false in
/-- Convert eventual-overlap branch locally bounded Ascoli data to relatively
compact range data through the branch-deviation route, using an explicit
principal free-energy local bound. -/
noncomputable def toRangeRelCompactData_viaDeviation
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (eventualData :
      LeeYangRealPointwiseNormalisedEventualOverlapBranchData G Λ p)
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
        G Λ p eventualData))
    (freeEnergy_bound : ∀ i : Fin geom.n, ∃ C : ℝ, ∀ m z
      (_hz : z ∈ Metric.ball (geom.center i : ℂ)
        (eventualData.pointwiseData.branchData.radius (geom.center i))),
      ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ ≤ C)
    (eventualLocallyBounded :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData
        G Λ p K eventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangRealPointwiseNormalisedEventualOverlapBranchData.toAllStageData
          G Λ p eventualData) geom :=
  LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchDeviationAscoliData.toRangeRelCompactData
    G Λ p K eventualData geom
    (toBranchDeviationData
      G Λ p K eventualData geom freeEnergy_bound eventualLocallyBounded)

end LeeYangPointwiseNormAllStageCompactRealEventualOverlapBranchLocallyBoundedAscoliData

end Ambient

end IsingModel
