import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.RealCompact.StructuredPatch

/-!
# Real branch-family compact-geometry wrappers

This module contains finite-subcover and compact local-cover geometry wrappers
for real-centred branch families.
-/

namespace IsingModel
namespace Ambient

/-- **ℤ^d compact finite subcover from a packaged Lee-Yang local-cover
family**: a compact target in `leeYangDomain` is covered by finitely many of
the packaged Lee-Yang local-cover balls. -/
theorem exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (family : Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (family.data h₀).radius :=
  Ambient.exists_finset_cover_of_isCompact_leeYangLocalBranchLimitFamily
    (IsingModel.latticeGraph d) Λ J β hK hKsub family

/-- **ℤ^d compact finite subcover from a real-centred packaged Lee-Yang local
cover**: a compact target containing the real field is covered by finitely many
packaged Lee-Yang local-cover balls, with the real centre included in the
finite set. -/
theorem exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (realFamily : Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :
    ∃ t : Finset {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ⟨(p.h : ℂ), realFamily.centre_mem⟩ ∈ t ∧
      K ⊆ ⋃ h₀ ∈ t,
        Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius :=
  Ambient.exists_finset_cover_of_isCompact_leeYangRealBranchLimitFamily
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK realFamily

/-- **ℤ^d compact local-cover finite geometry from a real-centred packaged
Lee-Yang local cover**: the finite subcover of a compact target is enumerated
over `Fin n`, retaining positive radii, Lee-Yang ball containment, target
coverage, and a selected real-centre index. -/
theorem exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (realFamily : Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_leeYangRealBranchLimitFamily
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK realFamily

/-- **ℤ^d compact local-cover `Fin n` geometry from structured
eventual-overlap branch data**: structured real-centred eventual-overlap branch
data first packages into a real branch-limit family, then compactness extracts
and enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_realEventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

/-- **ℤ^d compact local-cover `Fin n` geometry from pointwise-normalised
eventual-overlap branch data**: pointwise-normalised real eventual-overlap data
projects to the structured real package, then compactness extracts and
enumerates a finite local-cover geometry over `K`. -/
theorem exists_compactLocalCoverFinGeometry_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangCompactLocalCoverFinGeometry
      (IsingModel.latticeGraph d) Λ p K) :=
  Ambient.exists_compactLocalCoverFinGeometry_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

end Ambient

end IsingModel
