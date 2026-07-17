import IsingModel.AmbientComplexAnalyticity.AscoliData.Structures.BranchLocallyBounded

/-!
# Ambient complex analyticity Ascoli compact-open conversions

Mechanical child split from `AmbientComplexAnalyticity/AscoliData.lean`.
-/

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- Convert all-stage range-closure compact-open data into direct compact-open
data by taking the carrier to be the compact closure of the restriction range.
-/
def LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData.toCOpenData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeClosure :
      LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealCOpenData G Λ p K data geom where
  carrier := fun i => closure (Set.range (rangeClosure.restricted i))
  restricted := rangeClosure.restricted
  isCompact := rangeClosure.isCompact_closure
  mem := fun _ m => subset_closure ⟨m, rfl⟩
  restrict_eq := rangeClosure.restrict_eq
  overlap_eventually := rangeClosure.overlap_eventually

/-- Convert all-stage relatively compact range data into range-closure
compact-open data by compactness of closed subsets of compact carriers. -/
def
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData.toRangeClosureData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (relCompact :
      LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
      G Λ p K data geom where
  restricted := relCompact.restricted
  isCompact_closure := fun i =>
    (relCompact.isCompact_carrier i).of_isClosed_subset isClosed_closure
      (closure_minimal (relCompact.range_subset i)
        (relCompact.isCompact_carrier i).isClosed)
  restrict_eq := relCompact.restrict_eq
  overlap_eventually := relCompact.overlap_eventually

/-- Convert all-stage Arzelà-Ascoli data into direct compact-open data by
applying the project-local compact-open Arzelà-Ascoli handoff on each selected
ball. -/
def LeeYangPointwiseNormAllStageCompactRealAscoliData.toCOpenData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (ascoli : LeeYangPointwiseNormAllStageCompactRealAscoliData
      G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealCOpenData G Λ p K data geom where
  carrier := ascoli.carrier
  restricted := ascoli.restricted
  isCompact := fun i =>
    IsingModel.isCompact_compactOpen_complex_of_isCompact_toFun_image_equicontinuous
      (ascoli.toFun_image_compact i) (ascoli.equicontinuous i)
  mem := ascoli.mem
  restrict_eq := ascoli.restrict_eq
  overlap_eventually := ascoli.overlap_eventually

/-- Convert all-stage closed-product Ascoli data into direct Ascoli data by
using Tychonoff compactness for the closed pointwise function-space image on
each selected ball. -/
def LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData.toAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (closedProduct :
      LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealAscoliData G Λ p K data geom where
  carrier := closedProduct.carrier
  restricted := closedProduct.restricted
  toFun_image_compact := fun i =>
    IsingModel.isCompact_toFun_image_complex_of_isClosed_subset_pi_compacts
      (closedProduct.valueCompact i)
      (closedProduct.valueCompact_isCompact i)
      (closedProduct.toFun_image_closed i)
      (closedProduct.value_mem i)
  equicontinuous := closedProduct.equicontinuous
  mem := closedProduct.mem
  restrict_eq := closedProduct.restrict_eq
  overlap_eventually := closedProduct.overlap_eventually

/-- Convert all-stage norm-bounded closed-product Ascoli data into the
closed-product Ascoli package by taking the pointwise compact targets to be
closed complex balls centered at zero. -/
def
    LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData.toClosedProductData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (normBounded :
      LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
      G Λ p K data geom where
  carrier := normBounded.carrier
  restricted := normBounded.restricted
  valueCompact := fun i x => Metric.closedBall (0 : ℂ) (normBounded.bound i x)
  valueCompact_isCompact := fun i x => isCompact_closedBall (0 : ℂ) (normBounded.bound i x)
  toFun_image_closed := normBounded.toFun_image_closed
  value_mem := fun i f hf x => by
    simpa [Metric.mem_closedBall, dist_eq_norm] using normBounded.norm_le i f hf x
  equicontinuous := normBounded.equicontinuous
  mem := normBounded.mem
  restrict_eq := normBounded.restrict_eq
  overlap_eventually := normBounded.overlap_eventually

/-- Convert all-stage range norm-bounded Ascoli data into the general
norm-bounded package by taking each carrier to be the range of the selected
stage restrictions. -/
def
    LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData.toNormBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeBounded :
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
      G Λ p K data geom where
  carrier := fun i => Set.range (rangeBounded.restricted i)
  restricted := rangeBounded.restricted
  bound := rangeBounded.bound
  toFun_image_closed := rangeBounded.toFun_image_closed
  norm_le := fun i f hf x => by
    rcases hf with ⟨m, rfl⟩
    exact rangeBounded.norm_le i m x
  equicontinuous := rangeBounded.equicontinuous
  mem := fun i m => ⟨m, rfl⟩
  restrict_eq := rangeBounded.restrict_eq
  overlap_eventually := rangeBounded.overlap_eventually

/-- Convert all-stage range norm-bounded Ascoli data into relatively compact
range data by using the actual range as the compact carrier. -/
def
    LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData.toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (rangeBounded :
      LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K data geom where
  carrier := fun i => Set.range (rangeBounded.restricted i)
  restricted := rangeBounded.restricted
  isCompact_carrier := fun i =>
    IsingModel.isCompact_compactOpen_range_complex_of_isClosed_norm_le_equicontinuous
      (rangeBounded.restricted i) (rangeBounded.bound i)
      (rangeBounded.toFun_image_closed i) (rangeBounded.norm_le i)
      (rangeBounded.equicontinuous i)
  range_subset := fun _ => subset_rfl
  restrict_eq := rangeBounded.restrict_eq
  overlap_eventually := rangeBounded.overlap_eventually

/-- Convert all-stage branch norm-bounded Ascoli data into the range
norm-bounded package by transporting branch-family norm bounds across the
selected restriction identities. -/
def
    LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.toRangeNormBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (branchBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
      G Λ p K data geom where
  restricted := branchBounded.restricted
  bound := branchBounded.bound
  toFun_image_closed := branchBounded.toFun_image_closed
  norm_le := fun i m x => by
    simpa [branchBounded.restrict_eq i m (x : ℂ) x.property] using
      branchBounded.branch_norm_le i m (x : ℂ) x.property
  equicontinuous := branchBounded.equicontinuous
  restrict_eq := branchBounded.restrict_eq
  overlap_eventually := branchBounded.overlap_eventually

/-- Convert all-stage branch norm-bounded Ascoli data into relatively compact
range data by transporting branch bounds to the selected restrictions, then
using the actual restriction range as the compact carrier. -/
def
    LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (branchBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K data geom :=
  LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData.toRangeRelCompactData
    G Λ p K data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.toRangeNormBoundedData
      G Λ p K data geom branchBounded)

/-- Convert all-stage branch constant norm-bounded Ascoli data into the
branch norm-bounded package by turning each selected ball's constant bound into
a pointwise constant bound function. -/
def
    LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData.toBranchNormBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (constBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
      G Λ p K data geom where
  restricted := constBounded.restricted
  bound := fun i _ => constBounded.bound i
  toFun_image_closed := constBounded.toFun_image_closed
  branch_norm_le := fun i m z hz => constBounded.branch_norm_le i m z hz
  equicontinuous := constBounded.equicontinuous
  restrict_eq := constBounded.restrict_eq
  overlap_eventually := constBounded.overlap_eventually

/-- Convert all-stage branch constant norm-bounded Ascoli data into relatively
compact range data by viewing each constant as a pointwise branch bound. -/
def
    LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData.toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (constBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData.toRangeRelCompactData
    G Λ p K data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData.toBranchNormBoundedData
      G Λ p K data geom constBounded)

/-- Convert all-stage branch locally bounded Ascoli data into the constant
norm-bounded package by choosing one bound for each selected ball. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toConstData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (locallyBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
      G Λ p K data geom where
  restricted := locallyBounded.restricted
  bound := fun i => Classical.choose (locallyBounded.branch_bound i)
  toFun_image_closed := locallyBounded.toFun_image_closed
  branch_norm_le := fun i m z hz =>
    (Classical.choose_spec (locallyBounded.branch_bound i)) m z hz
  equicontinuous := locallyBounded.equicontinuous
  restrict_eq := locallyBounded.restrict_eq
  overlap_eventually := locallyBounded.overlap_eventually

/-- Convert all-stage branch locally bounded Ascoli data into relatively
compact range data by choosing one branch-family bound per selected ball. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K data)
    (locallyBounded :
      LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
        G Λ p K data geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData.toRangeRelCompactData
    G Λ p K data geom
    (LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toConstData
      G Λ p K data geom locallyBounded)

end Ambient

end IsingModel
