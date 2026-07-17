import IsingModel.Lattice
import IsingModel.AmbientComplexAnalyticity.CompactPatches.GeometryCOpen

/-!
# Per-stage complex analyticity wrappers: PointwiseAllStage

Consolidated `PointwiseAllStage` wrappers for the GJ §17.5.2 / §4.6
Vitali–Montel route (per-stage complex partition-function
analyticity).  Merged from the former one-declaration-per-file
fragments; declarations and proofs are unchanged.
-/

namespace IsingModel
namespace Ambient

/-!
# Pointwise-normalised all-stage finite cover package wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d pointwise-normalised all-stage data to finite Lee-Yang cover
package**: restricts pre-Montel all-stage branch choices to finitely many
Lee-Yang centres, then packages the finite compact-open subsequence extraction
as a finite Lee-Yang cover branch-limit family. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    Nonempty (Ambient.LeeYangFiniteCoverBranchLimitFamily
      (IsingModel.latticeGraph d) Λ J β n center
      (fun i => data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-!
# Pointwise-normalised all-stage finite cover patch wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d pointwise-normalised all-stage data to finite Lee-Yang cover patch**:
restricts pre-Montel all-stage branch choices to finitely many Lee-Yang
centres, builds the finite Lee-Yang cover package, and patches the compatible
local limits on the finite union of selected balls. -/
theorem freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (J β : ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ J β)
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j)))) :
    ∃ cover : Ambient.LeeYangFiniteCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ J β n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ J β n center data hA hFc_mem hFres hoverlap

/-!
# Pointwise-normalised all-stage finite cover wrappers

## Compatibility re-export

The pointwise-normalised all-stage finite-cover wrappers are split into
`PointwiseAllStage/FinCover/Package.lean` and
`PointwiseAllStage/FinCover/Patch.lean`. This module preserves the old import
path.
-/

/-!
# Pointwise-normalised all-stage finite real-cover wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d pointwise-normalised all-stage data to finite real-centred
Lee-Yang cover patch**: restricts all-stage branch choices to finitely many
Lee-Yang centres and uses a selected real-centre index to identify the patched
value with `↑Ambient.freeEnergyInfinite`. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ realCover : Ambient.LeeYangFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g
          (⋃ i : Fin n,
            Metric.ball (center i : ℂ) (data.branchData.radius (center i))) ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_finRealCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ p hBED hd n center data hA hFc_mem hFres
    hoverlap i₀ hcenter

/-!
# Pointwise-normalised all-stage compact real-cover wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d pointwise-normalised all-stage data to compact real-centred
Lee-Yang cover patch**: for a compact target covered by finitely many selected
all-stage Lee-Yang balls, produces the compact finite real-centred cover
package and a patch differentiable on the compact target. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    (K : Set ℂ) (n : ℕ)
    (center : Fin n → {h : ℂ // h ∈ IsingModel.leeYangDomain})
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    {A : ∀ i : Fin n,
      Set C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    {Fc : ∀ i : Fin n, ℕ →
      C(Metric.ball (center i : ℂ) (data.branchData.radius (center i)), ℂ)}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (hKcover : K ⊆
      ⋃ i : Fin n,
        Metric.ball (center i : ℂ) (data.branchData.radius (center i)))
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (center i : ℂ) (data.branchData.radius (center i))),
      data.branchData.branchFamily (center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (center i) m)
        (data.branchData.branchFamily (center j) m)
        (Metric.ball (center i : ℂ) (data.branchData.radius (center i))
          ∩ Metric.ball (center j : ℂ) (data.branchData.radius (center j))))
    (i₀ : Fin n)
    (hcenter :
      ((center i₀ : {h : ℂ // h ∈ IsingModel.leeYangDomain}) : ℂ) = (p.h : ℂ)) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K n center
        (fun i => data.branchData.radius (center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (center i : ℂ) (data.branchData.radius (center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCoverCOpen_patch
    (IsingModel.latticeGraph d) Λ p hBED hd K n center data hK hKsub hpK
    hKcover hA hFc_mem hFres hoverlap i₀ hcenter

/-!
# Pointwise-normalised all-stage real-cover wrappers

Compatibility module re-exporting the pointwise-normalised all-stage real-cover
child modules.
-/

/-!
# Pointwise-normalised all-stage compact geometry extraction wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d compact real finite-cover geometry from pointwise-normalised
all-stage data**: compactness extracts finitely many all-stage Lee-Yang balls
covering `K`, with a selected centre at the real field. -/
theorem
    exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ) {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    Nonempty (Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data) :=
  Ambient.exists_pointwiseNormAllStageCompactRealFinGeometry_of_isCompact
    (IsingModel.latticeGraph d) Λ p hK hKsub hpK data

/-!
# Pointwise-normalised all-stage compact geometry patch wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d pointwise-normalised all-stage compact finite geometry to compact
real-cover patch**: feeds compactness-extracted all-stage centres into the
compact real-cover patch bridge. -/
theorem
    freeEnergyComplexAlongExhaustion_pointwiseNormAllStage_compactRealCOpen_patch_geom_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    {A : ∀ i : Fin geom.n,
      Set C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    {Fc : ∀ i : Fin geom.n, ℕ →
      C(Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i)), ℂ)}
    (hA : ∀ i, IsCompact (A i))
    (hFc_mem : ∀ i m, Fc i m ∈ A i)
    (hFres : ∀ i m z
      (hz : z ∈ Metric.ball (geom.center i : ℂ)
        (data.branchData.radius (geom.center i))),
      data.branchData.branchFamily (geom.center i) m z = Fc i m ⟨z, hz⟩)
    (hoverlap : ∀ i j, ∀ᶠ m in Filter.atTop,
      Set.EqOn
        (data.branchData.branchFamily (geom.center i) m)
        (data.branchData.branchFamily (geom.center j) m)
        (Metric.ball (geom.center i : ℂ) (data.branchData.radius (geom.center i))
          ∩ Metric.ball (geom.center j : ℂ)
            (data.branchData.radius (geom.center j)))) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_pointwiseNormAllStageData_compactRealCOpen_patch_geom
    (IsingModel.latticeGraph d) Λ p hBED hd data geom hA hFc_mem hFres hoverlap

/-!
# Pointwise-normalised all-stage compact geometry wrappers

Compatibility module re-exporting the pointwise-normalised all-stage compact
geometry child modules.
-/

/-!
# Pointwise-normalised all-stage compact-open data patch wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d pointwise-normalised all-stage compact-open data to compact
real-cover patch**: packaged compact-open data for the selected all-stage
geometry feeds the compact real-cover patch bridge. -/
theorem freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ))
    (geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
      (IsingModel.latticeGraph d) Λ p K data)
    (cOpen : Ambient.LeeYangPointwiseNormAllStageCompactRealCOpenData
      (IsingModel.latticeGraph d) Λ p K data geom) :
    ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
        (IsingModel.latticeGraph d) Λ p K geom.n geom.center
        (fun i => data.branchData.radius (geom.center i)),
      ∃ g : ℂ → ℂ,
        (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
          (Metric.ball (geom.center i : ℂ)
            (data.branchData.radius (geom.center i)))) ∧
        DifferentiableOn ℂ g K ∧
        g (p.h : ℂ) =
          ((Ambient.freeEnergyInfinite (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageCOpenData_patch
    (IsingModel.latticeGraph d) Λ p hBED hd data geom cOpen

/-!
# Pointwise-normalised all-stage compact-target compact-open data wrappers

Part of the split pointwise-normalised all-stage packaging layer.
-/


/-- **ℤ^d compact target to packaged all-stage compact-open patch input**:
compactness of `K` extracts the finite all-stage geometry, and packaged
compact-open data then yields the compact real-cover patch endpoint. -/
theorem
    freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_of_isCompact_latticeGraph
    (d : ℕ) (Λ : Ambient.Exhaustion (Fin d → ℤ))
    [∀ n, Fintype (Ambient.inducedGraph
        (IsingModel.latticeGraph d) (Λ.volume n)).edgeSet]
    (p : IsingParams ℝ)
    (hBED : Ambient.BoundedEdgeDensity (IsingModel.latticeGraph d) Λ)
    (hd : Ambient.DisjointTowerHypotheses (IsingModel.latticeGraph d) Λ p)
    {K : Set ℂ}
    (hK : IsCompact K)
    (hKsub : K ⊆ IsingModel.leeYangDomain)
    (hpK : (p.h : ℂ) ∈ K)
    (data : Ambient.LeeYangPointwiseNormalisedAllStageBranchData
      (IsingModel.latticeGraph d) Λ (p.J : ℂ) (p.β : ℂ)) :
    ∃ geom : Ambient.LeeYangPointwiseNormAllStageCompactRealFinGeometry
        (IsingModel.latticeGraph d) Λ p K data,
      Ambient.LeeYangPointwiseNormAllStageCompactRealCOpenData
          (IsingModel.latticeGraph d) Λ p K data geom →
        ∃ compactCover : Ambient.LeeYangCompactFiniteRealCoverBranchLimitFamily
            (IsingModel.latticeGraph d) Λ p K geom.n geom.center
            (fun i => data.branchData.radius (geom.center i)),
          ∃ g : ℂ → ℂ,
            (∀ i, Set.EqOn g (compactCover.realCover.cover.family.limitFun i)
              (Metric.ball (geom.center i : ℂ)
                (data.branchData.radius (geom.center i)))) ∧
            DifferentiableOn ℂ g K ∧
            g (p.h : ℂ) =
              ((Ambient.freeEnergyInfinite
                (IsingModel.latticeGraph d) Λ p : ℝ) : ℂ) :=
  Ambient.freeEnergyComplexAlongExhaustion_allStageCOpenData_patch_of_isCompact
    (IsingModel.latticeGraph d) Λ p hBED hd hK hKsub hpK data

/-!
# Pointwise-normalised all-stage compact-open data wrappers

Compatibility module re-exporting the pointwise-normalised all-stage
compact-open data child modules.
-/

/-!
# SubseqCompactOpen split — pointwise-normalised all-stage packaging

Compatibility umbrella for the split pointwise-normalised all-stage packaging
layer.
-/

end Ambient
end IsingModel
