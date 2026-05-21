import IsingModel.AmbientComplexAnalyticity.CompactOpen

namespace IsingModel

namespace Ambient

variable {V : Type*} [DecidableEq V]

/-- **Pointwise-normalised all-stage compact real finite-cover geometry**: a
compact target `K ⊆ leeYangDomain`, pointwise-normalised all-stage branch data,
and a finite enumeration of all-stage Lee-Yang balls covering `K`, with one
selected centre equal to the real field. This is the compactness-only
finite-subcover geometry that feeds the compact real-cover patch bridge before
Montel compactness or coherent branch selection is proved. -/
structure LeeYangPointwiseNormAllStageCompactRealFinGeometry
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ)) where
  /-- The compact target set. -/
  isCompact : IsCompact K
  /-- The compact target stays inside the Lee-Yang domain. -/
  subset_domain : K ⊆ IsingModel.leeYangDomain
  /-- The real field belongs to the compact target. -/
  real_mem : (p.h : ℂ) ∈ K
  /-- Number of selected all-stage centres in the finite subcover. -/
  n : ℕ
  /-- Selected Lee-Yang centres, indexed by `Fin n`. -/
  center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain}
  /-- Every selected all-stage radius is positive. -/
  radius_pos : ∀ i, 0 < data.branchData.radius (center i)
  /-- Every selected all-stage ball stays inside the Lee-Yang domain. -/
  ball_subset : ∀ i,
    Metric.ball (center i : ℂ) (data.branchData.radius (center i)) ⊆
      IsingModel.leeYangDomain
  /-- The selected finite all-stage balls cover the compact target. -/
  cover_subset : K ⊆
    ⋃ i : Fin n, Metric.ball (center i : ℂ) (data.branchData.radius (center i))
  /-- The selected finite-cover index centred at the real field. -/
  realIndex : Fin n
  /-- The selected finite-cover centre is the real field `p.h`. -/
  real_center : (center realIndex : ℂ) = (p.h : ℂ)

/-- **Pointwise-normalised all-stage compact-open data**: the exact finite
compact-open package expected from a Montel extraction on the selected
all-stage Lee-Yang balls. It stores compact sets of continuous restrictions,
stage membership, the restriction identities back to the branch family, and
the coherent eventual equality on overlaps. The structure deliberately keeps
Montel compactness and coherent branch selection as inputs. -/
structure LeeYangPointwiseNormAllStageCompactRealCOpenData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Compact-open carrier for the restrictions on the selected ball. -/
  carrier : ∀ i : Fin geom.n,
    Set C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Compactness of every selected compact-open carrier. -/
  isCompact : ∀ i, IsCompact (carrier i)
  /-- Every stage restriction lies in the selected compact-open carrier. -/
  mem : ∀ i m, restricted i m ∈ carrier i
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

/-- **Pointwise-normalised all-stage range-closure compact-open data**: a
compact-open package in which the selected carrier is fixed to be the closure
of the actual stage-restriction range.  This is the direct compact-open shape
expected from a Montel relative-compactness statement: compactness is supplied
for the closure of the range, and stage membership follows automatically. -/
structure LeeYangPointwiseNormAllStageCompactRealRangeClosureCOpenData
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
  /-- Compactness of the compact-open closure of the actual restriction range. -/
  isCompact_closure : ∀ i,
    IsCompact (closure (Set.range (restricted i)))
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

/-- **Pointwise-normalised all-stage relatively compact range data**: a
Montel-style compact-open package in which the actual stage-restriction range
is only required to lie in a compact carrier.  The closure of the range is then
compact because compact subsets of the continuous-map space are closed and the
range closure is a closed subset of the compact carrier. -/
structure LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Compact-open carrier containing the selected restriction range. -/
  carrier : ∀ i : Fin geom.n,
    Set C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Compactness of the carrier containing the selected restriction range. -/
  isCompact_carrier : ∀ i, IsCompact (carrier i)
  /-- The actual stage-restriction range lies in the compact carrier. -/
  range_subset : ∀ i, Set.range (restricted i) ⊆ carrier i
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

/-- **Pointwise-normalised all-stage Arzelà-Ascoli data**: an Ascoli-style
replacement for direct compact-open compactness on the selected all-stage
Lee-Yang balls.  For each selected ball it stores a compact-open carrier of
continuous restrictions together with compactness of its pointwise
function-space image and equicontinuity; mathlib's Arzelà-Ascoli theorem then
supplies compact-open compactness.  This is still a pre-Montel input: it does
not prove the equicontinuity or compactness of the pointwise function-space
image from holomorphy and local boundedness. -/
structure LeeYangPointwiseNormAllStageCompactRealAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Carrier of selected continuous restrictions. -/
  carrier : ∀ i : Fin geom.n,
    Set C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- The pointwise function-space image of every carrier is compact. -/
  toFun_image_compact : ∀ i,
    IsCompact (ContinuousMap.toFun '' carrier i)
  /-- Every carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : carrier i →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
  /-- Every stage restriction lies in the selected carrier. -/
  mem : ∀ i m, restricted i m ∈ carrier i
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

/-- **Pointwise-normalised all-stage closed-product Ascoli data**: a
Tychonoff-style refinement of the Ascoli input on selected all-stage Lee-Yang
balls.  Instead of directly assuming compactness of the `ContinuousMap.toFun`
image, it records compact pointwise target sets, closedness of the function
image inside the pointwise product, and equicontinuity.  This is still a
pre-Montel input: it does not prove closedness, equicontinuity, or the compact
pointwise bounds from holomorphy and local boundedness. -/
structure LeeYangPointwiseNormAllStageCompactRealClosedProductAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Carrier of selected continuous restrictions. -/
  carrier : ∀ i : Fin geom.n,
    Set C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Compact pointwise target set at each point of every selected ball. -/
  valueCompact : ∀ i : Fin geom.n,
    Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)) → Set ℂ
  /-- Every pointwise target set is compact. -/
  valueCompact_isCompact : ∀ i x, IsCompact (valueCompact i x)
  /-- The pointwise function-space image of every carrier is closed. -/
  toFun_image_closed : ∀ i, IsClosed (ContinuousMap.toFun '' carrier i)
  /-- Every carrier element lands in the selected pointwise compact target. -/
  value_mem : ∀ i f, f ∈ carrier i → ∀ x, f x ∈ valueCompact i x
  /-- Every carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : carrier i →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
  /-- Every stage restriction lies in the selected carrier. -/
  mem : ∀ i m, restricted i m ∈ carrier i
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

/-- **Pointwise-normalised all-stage norm-bounded closed-product Ascoli
data**: a specialisation of the closed-product Ascoli input where the compact
pointwise target sets are closed complex balls supplied by pointwise norm
bounds.  This narrows the remaining normal-family input to closedness of the
pointwise function-space image, pointwise norm bounds, equicontinuity, and
coherent overlap equality. -/
structure LeeYangPointwiseNormAllStageCompactRealNormBoundedAscoliData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (data : LeeYangPointwiseNormalisedAllStageBranchData
      G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K data) where
  /-- Carrier of selected continuous restrictions. -/
  carrier : ∀ i : Fin geom.n,
    Set C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Continuous restrictions of each stage branch on the selected ball. -/
  restricted : ∀ i : Fin geom.n, ℕ →
    C(Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)), ℂ)
  /-- Pointwise real-valued norm bound for each selected ball. -/
  bound : ∀ i : Fin geom.n,
    Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)) → ℝ
  /-- The pointwise function-space image of every carrier is closed. -/
  toFun_image_closed : ∀ i, IsClosed (ContinuousMap.toFun '' carrier i)
  /-- Every carrier element satisfies the selected pointwise norm bound. -/
  norm_le : ∀ i f, f ∈ carrier i → ∀ x, ‖f x‖ ≤ bound i x
  /-- Every carrier is equicontinuous. -/
  equicontinuous : ∀ i,
    Equicontinuous
      ((↑) : carrier i →
        Metric.ball (geom.center i : ℂ)
          (data.branchData.radius (geom.center i)) → ℂ)
  /-- Every stage restriction lies in the selected carrier. -/
  mem : ∀ i m, restricted i m ∈ carrier i
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

/-- **Pointwise-normalised all-stage range norm-bounded Ascoli data**: a
range-specialised version of the norm-bounded Ascoli input where each carrier
is fixed to the actual sequence range of the continuous restrictions.  A
stagewise norm bound therefore supplies the carrier-wide bound required by the
norm-bounded package. -/
structure LeeYangPointwiseNormAllStageCompactRealRangeNormBoundedAscoliData
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
  /-- Pointwise real-valued norm bound for each selected ball. -/
  bound : ∀ i : Fin geom.n,
    Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)) → ℝ
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- Every stage restriction satisfies the selected pointwise norm bound. -/
  norm_le : ∀ i m, ∀ x, ‖restricted i m x‖ ≤ bound i x
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

/-- **Pointwise-normalised all-stage branch norm-bounded Ascoli data**: a
branch-family version of the range norm-bounded Ascoli input where the
pointwise norm bounds are stated on the original selected branch functions.
The restriction identities transport those bounds to the continuous
restrictions consumed by the range package. -/
structure LeeYangPointwiseNormAllStageCompactRealBranchNormBoundedAscoliData
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
  /-- Pointwise real-valued norm bound for each selected ball. -/
  bound : ∀ i : Fin geom.n,
    Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i)) → ℝ
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- Every original branch function satisfies the selected pointwise norm bound. -/
  branch_norm_le : ∀ i m z
    (hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    ‖data.branchData.branchFamily (geom.center i) m z‖ ≤ bound i ⟨z, hz⟩
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

/-- **Pointwise-normalised all-stage branch constant norm-bounded Ascoli data**:
a constant-bound version of the branch norm-bounded Ascoli input.  It asks for
one real norm bound on each selected Lee--Yang ball, rather than a bound
function depending on the point of the ball. -/
structure LeeYangPointwiseNormAllStageCompactRealBranchConstNormBoundedAscoliData
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
  /-- One real-valued norm bound for each selected ball. -/
  bound : Fin geom.n → ℝ
  /-- The pointwise function-space image of every range carrier is closed. -/
  toFun_image_closed : ∀ i,
    IsClosed (ContinuousMap.toFun '' Set.range (restricted i))
  /-- Every original branch function satisfies the selected ballwise norm bound. -/
  branch_norm_le : ∀ i m z
    (_hz : z ∈ Metric.ball (geom.center i : ℂ)
      (data.branchData.radius (geom.center i))),
    ‖data.branchData.branchFamily (geom.center i) m z‖ ≤ bound i
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

/-- Convert closed-ball branch-deviation Ascoli data into the PR #2744
branch-deviation package by supplying the principal finite-volume free-energy
bound from the closed-ball Lee-Yang local boundedness theorem. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData
      G Λ p K closedData.data geom where
  restricted := closedBallDeviation.restricted
  toFun_image_closed := closedBallDeviation.toFun_image_closed
  freeEnergy_bound := fun i => by
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨C + Real.pi, ?_⟩
    intro m z hz
    exact hC m z hz
  branch_deviation_bound := closedBallDeviation.branch_deviation_bound
  equicontinuous := closedBallDeviation.equicontinuous
  restrict_eq := closedBallDeviation.restrict_eq
  overlap_eventually := closedBallDeviation.overlap_eventually

/-- Convert closed-ball branch-deviation Ascoli data into relatively compact
range data by first supplying the automatic principal free-energy bound. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchDeviationAscoliData.toRangeRelCompactData
    G Λ p K closedData.data geom
    (LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

namespace LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

/-- Convert closed-ball branch-deviation Ascoli data into closed-ball branch
locally bounded Ascoli data by combining the automatic closed-ball principal
free-energy bound with the supplied branch-deviation bound. -/
noncomputable def toClosedBallBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangClosedBallBranchLocallyBoundedAscoliData
      G Λ p K closedData geom where
  restricted := closedBallDeviation.restricted
  toFun_image_closed := closedBallDeviation.toFun_image_closed
  branch_bound := fun i => by
    rcases closedBallDeviation.branch_deviation_bound i with ⟨D, hD⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨D + (C + Real.pi), ?_⟩
    intro m z hz
    let F := freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m
    calc
      ‖closedData.data.branchData.branchFamily (geom.center i) m z‖ =
          ‖(closedData.data.branchData.branchFamily (geom.center i) m z - F) + F‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖closedData.data.branchData.branchFamily (geom.center i) m z - F‖ + ‖F‖ :=
          norm_add_le _ _
      _ ≤ D + (C + Real.pi) := add_le_add (hD m z hz) (hC m z hz)
  equicontinuous := closedBallDeviation.equicontinuous
  restrict_eq := closedBallDeviation.restrict_eq
  overlap_eventually := closedBallDeviation.overlap_eventually

end LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

namespace LeeYangClosedBallBranchLocallyBoundedAscoliData

/-- Convert closed-ball branch local boundedness into the underlying
pointwise-normalised branch locally bounded Ascoli package.  This direct
conversion forgets only the closed-ball containment data and keeps the same
restriction, boundedness, equicontinuity, and overlap inputs. -/
noncomputable def toBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData
      G Λ p K closedData.data geom where
  restricted := closedBallLocal.restricted
  toFun_image_closed := closedBallLocal.toFun_image_closed
  branch_bound := closedBallLocal.branch_bound
  equicontinuous := closedBallLocal.equicontinuous
  restrict_eq := closedBallLocal.restrict_eq
  overlap_eventually := closedBallLocal.overlap_eventually

/-- Convert closed-ball branch local boundedness directly into relatively
compact range data by forgetting the closed-ball containment data and reusing
the underlying branch locally bounded Ascoli conversion. -/
noncomputable def toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealBranchLocallyBoundedAscoliData.toRangeRelCompactData
    G Λ p K closedData.data geom
    (toBranchLocallyBoundedData
      G Λ p K closedData geom closedBallLocal)

/-- Convert closed-ball branch local boundedness into closed-ball
branch-deviation data.  The deviation estimate follows from the local branch
bound and the closed-ball Lee-Yang principal free-energy bound. -/
noncomputable def toClosedBallDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
      G Λ p K closedData geom where
  restricted := closedBallLocal.restricted
  toFun_image_closed := closedBallLocal.toFun_image_closed
  branch_deviation_bound := fun i => by
    rcases closedBallLocal.branch_bound i with ⟨B, hB⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨B + (C + Real.pi), ?_⟩
    intro m z hz
    calc
      ‖closedData.data.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖
          ≤ ‖closedData.data.branchData.branchFamily (geom.center i) m z‖ +
              ‖freeEnergyComplexAlongExhaustion
                G Λ (p.J : ℂ) z (p.β : ℂ) m‖ := by
            exact norm_sub_le _ _
      _ ≤ B + (C + Real.pi) := by
            exact add_le_add (hB m z hz) (hC m z hz)
  equicontinuous := closedBallLocal.equicontinuous
  restrict_eq := closedBallLocal.restrict_eq
  overlap_eventually := closedBallLocal.overlap_eventually

/-- Convert closed-ball branch local boundedness into relatively compact range
data by deriving the closed-ball branch-deviation package first. -/
noncomputable def toRangeRelCompactData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData
    G Λ p hBED hβ hJ K closedData geom
    (toClosedBallDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallLocal)

end LeeYangClosedBallBranchLocallyBoundedAscoliData

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch local boundedness into the
ordinary closed-ball branch locally bounded package by taking the coherent
selected-overlap field from the underlying pointwise-normalised
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangClosedBallBranchLocallyBoundedAscoliData G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom where
  restricted := closedEventualLocal.restricted
  toFun_image_closed := closedEventualLocal.toFun_image_closed
  branch_bound := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualLocal.branch_bound
  equicontinuous := closedEventualLocal.equicontinuous
  restrict_eq := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualLocal.restrict_eq
  overlap_eventually := by
    intro i j
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualData.pointwiseData.branchData.overlap_eventually
        (geom.center i) (geom.center j)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch local boundedness directly
into relatively compact range data by first deriving the ordinary closed-ball
branch locally bounded package with its overlap field supplied from
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom :=
  LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchLocallyBoundedData
      G Λ p K closedEventualData geom closedEventualLocal)

namespace LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

/-- Convert closed-ball branch-deviation Ascoli data into relatively compact
range data through the direct closed-ball branch-local route. -/
noncomputable def toRangeRelCompactData_closedBallLocal_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    G Λ p K closedData geom
    (toClosedBallBranchLocallyBoundedData
      G Λ p hBED hβ hJ K closedData geom closedBallDeviation)

/-- Direct-route alias for the closed-ball branch-deviation Ascoli data to
relatively compact range data conversion.  This keeps the public name parallel
to `LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct`
while using the same branch-local route. -/
noncomputable def toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  toRangeRelCompactData_closedBallLocal_direct
    G Λ p hBED hβ hJ K closedData geom closedBallDeviation

set_option linter.style.longLine false in
/-- Named via-local direct-route alias for the closed-ball branch-deviation
Ascoli data to relatively compact range data conversion.  This restates the
existing closed-ball branch-local route with the intermediate route exposed.
-/
noncomputable def toRangeRelCompactData_viaLocal_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallDeviation :
      LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  toRangeRelCompactData_closedBallLocal_direct
    G Λ p hBED hβ hJ K closedData geom closedBallDeviation

end LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData

set_option linter.style.longLine false in
/-- Convert closed-ball branch local boundedness into relatively compact range
data through the direct closed-ball branch-deviation route.  This keeps the
closed-ball branch-deviation boundary visible while using the directRange
relative-compactness conversion. -/
noncomputable def
    LeeYangClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedData :
      LeeYangClosedBallPointwiseNormalisedAllStageBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry
      G Λ p K closedData.data)
    (closedBallLocal :
      LeeYangClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K closedData.data geom :=
  LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    G Λ p hBED hβ hJ K closedData geom
    (LeeYangClosedBallBranchLocallyBoundedAscoliData.toClosedBallDeviationData
      G Λ p hBED hβ hJ K closedData geom closedBallLocal)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data into the
ordinary closed-ball branch-deviation package by taking the coherent
selected-overlap field from the underlying pointwise-normalised
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom where
  restricted := closedEventualDeviation.restricted
  toFun_image_closed := closedEventualDeviation.toFun_image_closed
  branch_deviation_bound := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualDeviation.branch_deviation_bound
  equicontinuous := closedEventualDeviation.equicontinuous
  restrict_eq := by
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualDeviation.restrict_eq
  overlap_eventually := by
    intro i j
    simpa [LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData,
      LeeYangPointwiseNormalisedEventualOverlapBranchData.toAllStageData] using
      closedEventualData.pointwiseData.branchData.overlap_eventually
        (geom.center i) (geom.center j)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data directly into
relatively compact range data by first deriving the ordinary closed-ball
branch-deviation package with its overlap field supplied from
eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom :=
  LeeYangPointwiseNormAllStageCompactRealClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    G Λ p hBED hβ hJ K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData) geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchDeviationData
      G Λ p K closedEventualData geom closedEventualDeviation)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-local data into the
eventual-overlap closed-ball branch-deviation package by combining the
explicit branch bound with the automatic closed-ball principal free-energy
bound.  The selected-overlap field is still left to the eventual-overlap
package consumed by the downstream conversion. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchDeviationData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
      G Λ p K closedEventualData geom where
  restricted := closedEventualLocal.restricted
  toFun_image_closed := closedEventualLocal.toFun_image_closed
  branch_deviation_bound := fun i => by
    rcases closedEventualLocal.branch_bound i with ⟨B, hB⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedEventualData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨B + (C + Real.pi), ?_⟩
    intro m z hz
    calc
      ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z
          - freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖
          ≤ ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ +
              ‖freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m‖ := by
            exact norm_sub_le _ _
      _ ≤ B + (C + Real.pi) := by
            exact add_le_add (hB m z hz) (hC m z hz)
  equicontinuous := closedEventualLocal.equicontinuous
  restrict_eq := closedEventualLocal.restrict_eq

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-local data to relatively
compact range data through the branch-deviation route.  This records the
triangle-inequality path parallel to the ordinary closed-ball branch-local
conversion, while the selected overlap is supplied by eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_viaDeviation_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualLocal :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom :=
  LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_direct
    G Λ p hBED hβ hJ K closedEventualData geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toClosedBallBranchDeviationData
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualLocal)

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data into the
eventual-overlap closed-ball branch-local package by combining the supplied
deviation bound with the automatic closed-ball principal free-energy bound.
The selected-overlap field is still supplied only by the eventual-overlap data
when the downstream ordinary closed-ball branch-local package is formed. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchLocallyBoundedData
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData
      G Λ p K closedEventualData geom where
  restricted := closedEventualDeviation.restricted
  toFun_image_closed := closedEventualDeviation.toFun_image_closed
  branch_bound := fun i => by
    rcases closedEventualDeviation.branch_deviation_bound i with ⟨D, hD⟩
    rcases exists_norm_freeEnergyComplexAlongExhaustion_le_leeYang_on_ball
        G Λ hBED hβ hJ (closedEventualData.closedBall_subset (geom.center i)) with
      ⟨C, hC⟩
    refine ⟨D + (C + Real.pi), ?_⟩
    intro m z hz
    let F := freeEnergyComplexAlongExhaustion G Λ (p.J : ℂ) z (p.β : ℂ) m
    calc
      ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z‖ =
          ‖(closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z - F)
              + F‖ := by
            rw [sub_add_cancel]
      _ ≤ ‖closedEventualData.pointwiseData.branchData.branchFamily (geom.center i) m z - F‖ +
            ‖F‖ := norm_add_le _ _
      _ ≤ D + (C + Real.pi) := add_le_add (hD m z hz) (hC m z hz)
  equicontinuous := closedEventualDeviation.equicontinuous
  restrict_eq := closedEventualDeviation.restrict_eq

set_option linter.style.longLine false in
/-- Convert eventual-overlap closed-ball branch-deviation data to relatively
compact range data through the branch-local route.  This records the closed-ball
triangle-inequality route from deviation bounds to branch-local boundedness,
with selected overlap supplied downstream by eventual-overlap data. -/
noncomputable def
    LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toRangeRelCompactData_viaLocal_direct
    (G : SimpleGraph V) (Λ : Exhaustion V)
    [∀ n, Fintype (inducedGraph G (Λ.volume n)).edgeSet]
    [∀ n, Nonempty (↑(Λ.volume n) : Type _)]
    (p : IsingParams ℝ) (hBED : BoundedEdgeDensity G Λ)
    (hβ : 0 < p.β) (hJ : 0 < p.J) (K : Set ℂ)
    (closedEventualData :
      LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData
        G Λ (p.J : ℂ) (p.β : ℂ))
    (geom : LeeYangPointwiseNormAllStageCompactRealFinGeometry G Λ p K
      (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
        G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data)
    (closedEventualDeviation :
      LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData
        G Λ p K closedEventualData geom) :
    LeeYangPointwiseNormAllStageCompactRealRangeRelCompactCOpenData
      G Λ p K
        (LeeYangClosedBallPointwiseNormalisedEventualOverlapBranchData.toClosedBallAllStageData
          G Λ (p.J : ℂ) (p.β : ℂ) closedEventualData).data geom :=
  LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchLocallyBoundedAscoliData.toRangeRelCompactData_direct
    G Λ p K closedEventualData geom
    (LeeYangPointwiseNormAllStageCompactRealEventualOverlapClosedBallBranchDeviationAscoliData.toClosedBallBranchLocallyBoundedData
      G Λ p hBED hβ hJ K closedEventualData geom closedEventualDeviation)

end Ambient

end IsingModel
