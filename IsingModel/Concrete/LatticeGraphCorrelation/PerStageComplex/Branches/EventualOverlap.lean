import IsingModel.Concrete.LatticeGraphCorrelation.PerStageComplex.Branches.LocalCoverPatch

/-!
# Per-stage complex analyticity wrappers: EventualOverlap

Consolidated `EventualOverlap` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.
-/

namespace IsingModel
namespace Ambient

/-!
# Raw branch-data local-family wrappers

This module contains the raw branch-data local-family wrapper split from
`PerStageComplex.Branches.EventualOverlap.RawBranchData`.
-/


/-- **ℤ^d packaged local-cover branch-limit family from raw branch data**:
raw pointwise Lee-Yang local-cover branch data with locally uniform limits and
pairwise overlap compatibility can be bundled into
`LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hcompat : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Set.EqOn (f h₀) (f h₁)
        (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_branchData
    (IsingModel.latticeGraph d) Λ J β hr hsub hbranch hconv hcompat

/-!
# Raw branch-data real-family wrappers

This module contains the raw branch-data real-family wrapper split from
`PerStageComplex.Branches.EventualOverlap.RawBranchData`.
-/


/-- **ℤ^d real-centred packaged local-cover branch-limit family from raw
branch data**: raw coherent Lee-Yang local-cover branch data, real-centre
membership, and centre normalisation can be bundled into
`LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_branchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
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
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_branchData
    (IsingModel.latticeGraph d) Λ p hp hr hsub hbranch hconv hcompat hcenter

/-!
# Raw eventual-overlap branch-data wrappers

## Compatibility re-export

The raw eventual-overlap branch-data wrappers are split into
`RawBranchData/LocalFamily.lean` and `RawBranchData/RealFamily.lean`. This
module preserves the old import path.
-/

/-!
# Eventual-overlap local-family wrappers

This module contains the eventual-overlap local-family wrapper split from
`PerStageComplex.Branches.EventualOverlap.EventuallyEqOn`.
-/


/-- **ℤ^d packaged local-cover branch-limit family from eventual overlap
data**: raw Lee-Yang local-cover branch data whose stage branches are
eventually equal on every overlap can be bundled into
`LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    {r : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℝ}
    {F : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℕ → ℂ → ℂ}
    {f : (h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) → ℂ → ℂ}
    (hr : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, 0 < r h₀)
    (hsub : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      Metric.ball (h₀ : ℂ) (r h₀) ⊆ IsingModel.leeYangDomain)
    (hbranch : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}, ∀ n,
      AnalyticOnNhd ℂ (F h₀ n) (Metric.ball (h₀ : ℂ) (r h₀))
        ∧ (∀ z ∈ Metric.ball (h₀ : ℂ) (r h₀),
            Complex.exp ((Fintype.card (↑(Λ.volume n) : Type _) : ℂ) * F h₀ n z)
              = Ambient.partitionFunctionComplexAlongExhaustion
                  (IsingModel.latticeGraph d) Λ J z β n))
    (hconv : ∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      TendstoLocallyUniformlyOn (F h₀) (f h₀) Filter.atTop
        (Metric.ball (h₀ : ℂ) (r h₀)))
    (hoverlap : ∀ h₀ h₁ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
      ∀ᶠ n in Filter.atTop,
        Set.EqOn (F h₀ n) (F h₁ n)
          (Metric.ball (h₀ : ℂ) (r h₀) ∩ Metric.ball (h₁ : ℂ) (r h₁))) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_branchData_eventuallyEqOn
    (IsingModel.latticeGraph d) Λ J β hr hsub hbranch hconv hoverlap

/-!
# Eventual-overlap real-family wrappers

This module contains the eventual-overlap real-family wrapper split from
`PerStageComplex.Branches.EventualOverlap.EventuallyEqOn`.
-/


/-- **ℤ^d real-centred packaged local-cover branch-limit family from eventual
overlap data**: raw Lee-Yang local-cover branch data whose stage branches are
eventually equal on every overlap, plus real-centre normalisation, can be
bundled into `LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_branchData_eventuallyEqOn_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
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
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_branchData_eventuallyEqOn
    (IsingModel.latticeGraph d) Λ p hp hr hsub hbranch hconv hoverlap hcenter

/-!
# Eventually equal overlap branch-data wrappers

## Compatibility re-export

The eventual-overlap branch-data wrappers are split into
`EventuallyEqOn/LocalFamily.lean` and `EventuallyEqOn/RealFamily.lean`. This
module preserves the old import path.
-/

/-!
# Structured eventual-overlap branch-data family wrappers

This module contains the structured eventual-overlap branch-data family
wrappers split from `PerStageComplex.Branches.EventualOverlap.StructuredFamily`.
-/


/-- **ℤ^d packaged local-cover branch-limit family from structured
eventual-overlap branch data**: the structured local-cover input packages
directly into `Ambient.LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_eventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d real-centred packaged local-cover branch-limit family from
structured eventual-overlap branch data**: the real-centred structured
local-cover input packages directly into `Ambient.LeeYangRealBranchLimitFamily`.
-/
theorem exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : Ambient.LeeYangRealEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_realEventualOverlapBranchData
    (IsingModel.latticeGraph d) Λ p data

/-!
# Pointwise-normalised eventual-overlap branch-data family wrappers

This module contains the pointwise-normalised eventual-overlap family wrappers
split from `PerStageComplex.Branches.EventualOverlap.StructuredFamily`.
-/


/-- **ℤ^d packaged local-cover branch-limit family from pointwise-normalised
eventual-overlap branch data**: the pointwise-normalised package exposes the
underlying structured eventual-overlap branch data, which packages directly
into `Ambient.LeeYangLocalBranchLimitFamily`. -/
theorem exists_leeYangLocalBranchLimitFamily_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    Nonempty (Ambient.LeeYangLocalBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β) :=
  Ambient.exists_leeYangLocalBranchLimitFamily_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ J β data

/-- **ℤ^d real-centred packaged local-cover branch-limit family from
pointwise-normalised eventual-overlap branch data**: pointwise-normalised real
eventual-overlap data projects to the structured real package, then packages
directly into `Ambient.LeeYangRealBranchLimitFamily`. -/
theorem exists_leeYangRealBranchLimitFamily_of_pointwiseNormEventualData_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (data : Ambient.LeeYangRealPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ p) :
    Nonempty (Ambient.LeeYangRealBranchLimitFamily
      (IsingModel.latticeGraph d) Λ p) :=
  Ambient.exists_leeYangRealBranchLimitFamily_of_pointwiseNormEventualData
    (IsingModel.latticeGraph d) Λ p data

/-!
# Structured eventual-overlap family wrappers

## Compatibility re-export

The structured and pointwise-normalised eventual-overlap branch-family wrappers
are split into `StructuredFamily/Structured.lean` and
`StructuredFamily/Pointwise.lean`. This module preserves the old import path.
-/

/-!
# Structured eventual-overlap local-cover patch wrapper

This module contains the structured eventual-overlap local-cover patch wrapper
split from `PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.Patch`.
-/


/-- **ℤ^d structured eventual-overlap local-cover patching handoff on
`leeYangDomain`**: structured eventual-overlap data patch directly to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data

/-!
# Pointwise-normalised eventual-overlap local-cover patch wrapper

This module contains the pointwise-normalised eventual-overlap local-cover patch
wrapper split from
`PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.Patch`.
-/


/-- **ℤ^d pointwise-normalised eventual-overlap local-cover patching handoff
on `leeYangDomain`**: pointwise-normalised structured data expose the
underlying eventual-overlap package, whose local limits patch to one
differentiable function on `leeYangDomain`. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ g : ℂ → ℂ,
      (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
        Set.EqOn g (data.branchData.limitFun h₀)
          (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
      DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_patch
    (IsingModel.latticeGraph d) Λ J β data

/-!
# Eventual-overlap local-cover patch wrappers

## Compatibility re-export

The eventual-overlap local-cover patch wrappers are split into
`Patch/Structured.lean` and `Patch/Pointwise.lean`. This module preserves the
old import path.
-/

/-!
# Structured eventual-overlap local-cover family patch wrappers

This module contains the structured eventual-overlap family-and-patching
wrapper split from
`PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.FamilyPatch`.
-/


/-- **ℤ^d structured eventual-overlap local-cover family and patching handoff
on `leeYangDomain`**: structured eventual-overlap data produce both the
compatible local-cover family and one differentiable patch. -/
theorem
    freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ family : Ambient.LeeYangLocalBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_eventualOverlapBranchData_localCover_family_patch
    (IsingModel.latticeGraph d) Λ J β data

/-!
# Pointwise-normalised eventual-overlap local-cover family patch wrappers

This module contains the pointwise-normalised eventual-overlap family-and-
patching wrapper split from
`PerStageComplex.Branches.EventualOverlap.LocalCoverPatch.FamilyPatch`.
-/


/-- **ℤ^d pointwise-normalised eventual-overlap local-cover family and
patching handoff on `leeYangDomain`**: pointwise-normalised structured data
produce both the compatible local-cover family and one differentiable patch. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_family_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ)
    (data : Ambient.LeeYangPointwiseNormalisedEventualOverlapBranchData
      (IsingModel.latticeGraph d) Λ J β) :
    ∃ family : Ambient.LeeYangLocalBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β,
      ∃ g : ℂ → ℂ,
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (data.branchData.limitFun h₀)
            (Metric.ball (h₀ : ℂ) (data.branchData.radius h₀))) ∧
        (∀ h₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain},
          Set.EqOn g (family.data h₀).limitFun
            (Metric.ball (h₀ : ℂ) (family.data h₀).radius)) ∧
        DifferentiableOn ℂ g IsingModel.leeYangDomain :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormEventualData_localCover_family_patch
    (IsingModel.latticeGraph d) Λ J β data

/-!
# Eventual-overlap local-cover family patch wrappers

## Compatibility re-export

The eventual-overlap local-cover family patch wrappers are split into
`FamilyPatch/Structured.lean` and `FamilyPatch/Pointwise.lean`. This module
preserves the old import path.
-/

/-!
# Eventual-overlap local-cover patch wrappers

## Compatibility re-export

The eventual-overlap local-cover patch wrappers are split into
`LocalCoverPatch/Patch.lean` and `LocalCoverPatch/FamilyPatch.lean`. This module
preserves the old import path.
-/

/-!
# Eventual-overlap branch-family wrappers

Compatibility umbrella for the split eventual-overlap branch-family wrapper layer.
-/

end Ambient
end IsingModel
