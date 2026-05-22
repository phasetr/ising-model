import IsingModel.AmbientComplexAnalyticity.CompactOpen

/-!
# Ambient complex analyticity Ascoli data structures

Mechanical child split from `AmbientComplexAnalyticity/AscoliData.lean`.
-/

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

end Ambient

end IsingModel
