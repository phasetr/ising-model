import IsingModel.AmbientComplexAnalyticity.CompactOpen

/-!
# Ascoli data structures split — finite-cover geometry and range compact-open data

Part of the split ambient Ascoli-data structures layer (Issue #1850).
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


end Ambient
end IsingModel
