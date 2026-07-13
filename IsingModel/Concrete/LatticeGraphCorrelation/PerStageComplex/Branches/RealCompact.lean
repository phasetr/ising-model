import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.EventualOverlap

/-!
# Per-stage complex analyticity wrappers: RealCompact

Consolidated `RealCompact` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.
-/

namespace IsingModel
namespace Ambient

/-!
# Raw branch-data real patch wrapper

This module contains the real-axis local-cover patch wrapper for raw branch
data split from `PerStageComplex.Branches.RealCompact.RawPatch`.
-/


/-- **ℤ^d raw branch-data local-cover patching with real-axis
identification**: raw coherent local-cover branch data package into
`LeeYangRealBranchLimitFamily`, then patch to a function differentiable on
`leeYangDomain` and identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_branchData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
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
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp hr hsub hbranch hconv hcompat hcenter

/-!
# Eventual-overlap raw branch-data real patch wrapper

This module contains the real-axis local-cover patch wrapper for raw branch
data with eventual equality on overlaps split from
`PerStageComplex.Branches.RealCompact.RawPatch`.
-/


/-- **ℤ^d eventual-overlap raw branch-data local-cover patching with real-axis
identification**: raw local-cover branch data whose stage branches are
eventually equal on every overlap package into `LeeYangRealBranchLimitFamily`,
then patch to a differentiable function identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_branchData_eventuallyEqOn_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
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
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ (p.J : ℂ) z (p.β : ℂ) n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁)))
    (hcenter : ∀ n,
      F ⟨(p.h : ℂ), hp⟩ n (p.h : ℂ)
        = Ambient.freeEnergyComplexAlongExhaustion
            (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.h : ℂ) (p.β : ℂ) n) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (f h₀) (Metric.ball (h₀ : ℂ) (r h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchData_eventuallyEqOn_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp hr hsub hbranch hconv hoverlap hcenter

/-!
# Raw branch-data real patch wrappers

## Compatibility re-export

The raw branch-data real patch wrappers are split into
`RawPatch/BranchData.lean` and `RawPatch/EventuallyEqOn.lean`. This module
preserves the old import path.
-/

/-!
# Structured eventual-overlap real patch wrappers

This module contains the structured eventual-overlap real-axis local-cover
patch wrapper split from `PerStageComplex.Branches.RealCompact.StructuredPatch`.
-/


/-- **ℤ^d structured eventual-overlap branch-data local-cover patching with
real-axis identification**: a real-centred structured local-cover package is
converted to `Ambient.LeeYangRealBranchLimitFamily`, then patched and
identified at the real centre. -/
theorem freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_realEventualOverlapBranchData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd data

/-!
# Pointwise-normalised eventual-overlap real patch wrappers

This module contains the pointwise-normalised eventual-overlap real-axis
local-cover patch wrapper split from
`PerStageComplex.Branches.RealCompact.StructuredPatch`.
-/


/-- **ℤ^d pointwise-normalised eventual-overlap data local-cover patching with
real-axis identification**: pointwise-normalised structured data projects to
the real-centred structured package, then patches and identifies the real
centre. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    ∃ realFamily : Ambient.LeeYangRealBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.pointwiseData.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.pointwiseData.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (realFamily.family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (realFamily.family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd data

/-!
# Structured eventual-overlap real patch wrappers

## Compatibility re-export

The structured eventual-overlap real patch wrappers are split into
`StructuredPatch/Structured.lean` and `StructuredPatch/Pointwise.lean`.
This module preserves the old import path.
-/

/-!
# Compact finite subcover wrapper for local branch-limit families

This module contains the finite-subcover wrapper for packaged local-cover
families split from
`PerStageComplex.Branches.RealCompact.CompactGeometry.FinsetCover`.
-/


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

/-!
# Compact finite subcover wrapper for real-centred branch-limit families

This module contains the finite-subcover wrapper for real-centred packaged
local-cover families split from
`PerStageComplex.Branches.RealCompact.CompactGeometry.FinsetCover`.
-/


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

/-!
# Real branch-family compact finite-subcover wrappers

## Compatibility re-export

The compact finite-subcover wrappers are split into
`FinsetCover/LocalFamily.lean` and `FinsetCover/RealFamily.lean`. This module
preserves the old import path.
-/

/-!
# Real branch-family compact `Fin n` geometry wrapper

This module contains the compact local-cover finite-geometry wrapper split from
`PerStageComplex.Branches.RealCompact.CompactGeometry`.
-/


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

/-!
# Compact geometry wrapper for structured eventual-overlap data

This module contains the compact local-cover `Fin n` geometry wrapper for
structured eventual-overlap data split from
`PerStageComplex.Branches.RealCompact.CompactGeometry.EventualDataGeometry`.
-/


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

/-!
# Compact geometry wrapper for pointwise-normalised eventual-overlap data

This module contains the compact local-cover `Fin n` geometry wrapper for
pointwise-normalised eventual-overlap data split from
`PerStageComplex.Branches.RealCompact.CompactGeometry.EventualDataGeometry`.
-/


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

/-!
# Real eventual-overlap compact geometry wrappers

## Compatibility re-export

The eventual-overlap compact geometry wrappers are split into
`EventualDataGeometry/Structured.lean` and
`EventualDataGeometry/Pointwise.lean`. This module preserves the old import
path.
-/

/-!
# Real branch-family compact-geometry wrappers

## Compatibility re-export

The real branch-family compact-geometry wrappers are split into
`CompactGeometry/FinsetCover.lean`, `CompactGeometry/FinGeometry.lean`, and
`CompactGeometry/EventualDataGeometry.lean`. This module preserves the old
import path.
-/

/-!
# Real local-cover Vitali wrappers

This module contains the real-axis local-cover branch-family Vitali wrapper.
-/


/-- **ℤ^d local-cover branch-family Vitali bridge with real-axis
identification**: a coherent local Lee-Yang ball cover with locally-uniform
convergence to a common `f` makes `f` holomorphic on `leeYangDomain`, and at a
real Lee-Yang centre it agrees with `↑freeEnergyInfinite`. -/
theorem freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover_real_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {f : ℂ → ℂ}
    (hp : (p.h : ℂ) ∈ IsingModel.leeYangDomain)
    (hlocal : ∀ h₀ ∈ IsingModel.leeYangDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball h₀ r ⊆ IsingModel.leeYangDomain ∧
        ∃ F : ℕ → ℂ → ℂ,
          (∀ n,
            AnalyticOnNhd ℂ (F n) (Metric.ball h₀ r)
              ∧ (∀ z ∈ Metric.ball h₀ r,
                  Complex.exp
                    ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F n z)
                    = Ambient.partitionFunctionComplexAlongExhaustion
                        (IsingModel.latticeGraph d) Λ
                        (p.J : ℂ) z (p.β : ℂ) n)
              ∧ F n h₀ = Ambient.freeEnergyComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ
                  (p.J : ℂ) h₀ (p.β : ℂ) n)
          ∧ TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball h₀ r)) :
    DifferentiableOn ℂ f IsingModel.leeYangDomain ∧
      f (p.h : ℂ) =
        ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_branchFamily_vitali_localCover_real
    (IsingModel.latticeGraph d) Λ p hBED hd hp hlocal

/-!
# Real-axis and compact-cover wrappers

Compatibility umbrella for the split real-axis and compact-cover wrapper layer.
-/

end Ambient
end IsingModel
